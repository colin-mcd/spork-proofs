import SporkProofs.Syntax
import SporkProofs.Semantics

structure Extra where
  offset : Nat
  bsig : BlockSig

@[simp] def inlinedArgs (extra : Extra) (scope : Nat) (args : List Var) : List Var :=
  args ++ (List.range' scope extra.bsig.arity).map Var.mk

@[simp] def inlinedCont (extra : Extra) (scope : Nat) : Cont -> Cont
  | .mk b args => .mk (b + extra.offset) (inlinedArgs extra scope args)

@[simp] def inlinedCode (bret : BlockIdx) (extra : Extra) (scope : Nat) : Code -> Code
  | .stmt e c =>
    .stmt e (inlinedCode bret extra scope.succ c)
  | .goto bnext =>
    .goto (inlinedCont extra scope bnext)
  | .ite cond bthen belse =>
    .ite cond
         (inlinedCont extra scope bthen)
         (inlinedCont extra scope belse)
  | .call h args bret =>
    .call h args (inlinedCont extra scope bret)
  | .retn args =>
    .goto (.mk bret (inlinedArgs extra scope args))
  | .spork bbody hspwn args =>
    .spork (inlinedCont extra scope bbody) hspwn args
  | .spoin bunpr bprom =>
    .spoin (inlinedCont extra scope bunpr)
           (inlinedCont extra scope bprom)

@[simp] def inlinedBlock (bret : BlockIdx) (extra : Extra) (b : Block) : Block :=
  Block.mk (b.bsig + extra.bsig) (inlinedCode bret extra b.bsig.arity b.code)

theorem inlinedArgsRangeWF :
    (extraArity : Nat) -> (scope : Nat) ->
    IVec (·.WF (scope + extraArity)) ((List.range' scope extraArity).map Var.mk)
  | 0, scope => .nil
  | .succ extraArity, scope =>
    .cons (.mk (by simp))
          (Nat.add_succ scope extraArity ▸
           Nat.succ_add scope extraArity ▸
           inlinedArgsRangeWF extraArity scope.succ)

theorem inlinedArgsWF' (extra : Extra) {scope : Nat} : {args : List Var} ->
                       IVec (·.WF scope) args -> IVec (·.WF (scope + extra.bsig.arity)) args
  | [], .nil => .nil
  | _a :: _args, .cons awf argswf =>
    .cons (Var.WF.mk (Nat.lt_add_right extra.bsig.arity awf.idx))
          (inlinedArgsWF' extra argswf)

theorem inlinedArgsWF (extra : Extra) {scope : Nat} {args : List Var}
                      (wf : IVec (·.WF scope) args) :
                      IVec (·.WF (scope + extra.bsig.arity)) (inlinedArgs extra scope args) :=
  (inlinedArgsWF' extra wf).append (inlinedArgsRangeWF extra.bsig.arity scope)

theorem inlinedContWFRets
        {bsigs bsigs' bsig rets} (extra : Extra) {c : Cont}
        (bslen : bsigs.length = extra.offset)
        (wf : c.WFRets bsigs' bsig rets) :
        (inlinedCont extra bsig.arity c).WFRets
          (bsigs ++ bsigs'.map (· + extra.bsig)) (bsig + extra.bsig) rets :=
  .mk (by simp[← bslen, Nat.add_comm c.b bsigs.length, wf.blt])
      (by simp[wf.bsig, Nat.add_comm c.b extra.offset, ← bslen]
          show BlockSig.mk (c.args.length + rets + extra.bsig.arity)
                           (bsig.sporkNest ++ extra.bsig.sporkNest) =
               BlockSig.mk (c.args.length + extra.bsig.arity + rets)
                           (bsig.sporkNest ++ extra.bsig.sporkNest)
          rw[Nat.add_assoc, Nat.add_comm rets extra.bsig.arity, ← Nat.add_assoc])
      (inlinedArgsWF extra wf.args)

theorem inlinedContWF
        {bsigs bsigs' bsig} (extra : Extra) {c : Cont}
        (bslen : bsigs.length = extra.offset)
        (wf : c.WF bsigs' bsig) :
        (inlinedCont extra bsig.arity c).WF
          (bsigs ++ bsigs'.map (· + extra.bsig)) (bsig + extra.bsig) :=
  (inlinedContWFRets extra bslen wf.cast0).cast0

theorem inlinedAtomWF {Γ : Nat} (extraArity : Nat) : {a : Atom} -> a.WF Γ -> a.WF (Γ + extraArity)
  | .val _v, _wf => .val
  | .var _v, wf => .var (.mk (Nat.lt_add_right extraArity wf.vwf.idx))

theorem inlinedExprWF {Γ : Nat} (extraArity : Nat) : {e : Expr} -> e.WF Γ -> e.WF (Γ + extraArity)
  | .nop _a, .nop awf =>
    .nop (inlinedAtomWF extraArity awf)
  | .uop _o _a, .uop awf =>
    .uop (inlinedAtomWF extraArity awf)
  | .bop _o _a _b, .bop awf bwf =>
    .bop (inlinedAtomWF extraArity awf) (inlinedAtomWF extraArity bwf)

theorem inlinedCodeWF
    {fsigs bsigs bsigs' ret ret' bsig bret}
    (bretlt : bret < bsigs.length)
    (extra : Extra)
    (bretsig : bsigs[bret] = ⟨ret + extra.bsig.arity, extra.bsig.sporkNest⟩)
    (bslen : bsigs.length = extra.offset) :
    {c : Code} ->
    c.WF fsigs bsigs' ret bsig ->
    (inlinedCode bret extra bsig.arity c).WF
      fsigs (bsigs ++ bsigs'.map (· + extra.bsig)) ret' (bsig + extra.bsig)
  | .stmt e c, wf =>
    .stmt (inlinedExprWF extra.bsig.arity wf.stmt_expr)
          (by simpa[Nat.add_right_comm bsig.arity extra.bsig.arity 1]
              using inlinedCodeWF (bsig := bsig.bind) bretlt extra bretsig bslen (wf.stmt_code))
  | .goto bnext, wf =>
    .goto (inlinedContWF extra bslen wf.goto_bnext)
  | .ite cond bthen belse, wf =>
    .ite (inlinedAtomWF extra.bsig.arity wf.ite_cond)
         (inlinedContWF extra bslen wf.ite_bthen)
         (inlinedContWF extra bslen wf.ite_belse)
  | .call h args bret', wf =>
    .call wf.call_flt
          (wf.call_arity)
          (inlinedArgsWF' extra wf.call_args)
          (inlinedContWFRets extra bslen wf.call_bret)
  | .retn args, .retn sn_nil len argswf =>
    let x : bret < (bsigs ++ bsigs').length :=
      by simp[Nat.lt_add_right bsigs'.length bretlt]
    .goto (.mk (by simp[Nat.lt_add_right bsigs'.length bretlt])
               (by simp[← len]
                   rw[List.getElem_append_left (bs := bsigs'.map (· + extra.bsig)) bretlt]
                   simp[sn_nil, bretsig])
               (inlinedArgsWF extra argswf))
  | .spork bbody hspwn args, wf =>
    .spork wf.spork_flt
           wf.spork_arity
           (inlinedArgsWF' extra wf.spork_args)
           (inlinedContWF extra bslen wf.spork_bbody)
  | .spoin bunpr bprom, wf =>
    .spoin (by simp[wf.spoin_sn_nonnil])
           (by simp[List.tail_append_of_ne_nil wf.spoin_sn_nonnil]
               exact inlinedContWF extra bslen wf.spoin_bunpr)
           (by simp[List.tail_append_of_ne_nil wf.spoin_sn_nonnil,
                    List.head_append_left wf.spoin_sn_nonnil]
               exact inlinedContWFRets extra bslen wf.spoin_bprom)

theorem inlinedBlockWF
    {fsigs bsigs bsigs' ret ret' bret}
    (bretlt : bret < bsigs.length)
    (extra : Extra)
    (bretsig : bsigs[bret] = ⟨ret + extra.bsig.arity, extra.bsig.sporkNest⟩)
    (bslen : bsigs.length = extra.offset)
    {b : Block}
    (wf : b.WF fsigs bsigs' ret) :
    (inlinedBlock bret extra b).WF
      fsigs (bsigs ++ bsigs'.map (· + extra.bsig)) ret' :=
  .mk (inlinedCodeWF bretlt extra bretsig bslen wf.1)

@[simp] def inlinedFuncBody (g : Func) (bret : Cont) (sporks : SporkSig) (offset : Nat) : List Block :=
  g.blocks.map (inlinedBlock bret.b (.mk offset (.mk bret.args.length sporks)))

theorem inlinedFuncBodyWF
          {fsigs bsigs ret g bret sporks}
          (bretlt : bret.b < bsigs.length)
          (bretsig : bsigs[bret.b] = ⟨g.fsig.ret + bret.args.length, sporks⟩)
          (wf : g.WF fsigs) :
          IVec (·.WF fsigs (bsigs ++ List.map (· + .mk bret.args.length sporks) g.bsigs) ret)
               (inlinedFuncBody g bret sporks bsigs.length) :=
  wf.blocks.from_map'
    (inlinedBlock bret.b (.mk bsigs.length (.mk bret.args.length sporks)))
    (λ _b => inlinedBlockWF bretlt (.mk bsigs.length (.mk bret.args.length sporks)) bretsig rfl)

@[simp] def replaceCallInCode (g : FuncIdx) (offset : Nat) (c : Code) : Option (Code × Cont) :=
  let (e, ⟨t, _p⟩) := c.split
  match t with
    | .call h args bret =>
      if h = g then
        some (Code.join e (Code.goto (.mk offset (args ++ bret.args))), bret)
      else
        none
    | _ => none


@[simp] def inlinedFuncH (g : Func) (gidx : FuncIdx) :
                 List Block -> List Block -> List Block -> List Block
  | bacc, [], gacc => bacc ++ gacc
  | bacc, .mk bsig c :: bs, gacc =>
    let (b', gacc') :=
      (replaceCallInCode gidx
          (bacc ++ [Block.mk bsig c] ++ bs ++ gacc).length c).elim
        (.mk bsig c, [])
        (λ (c', bret) =>
          (.mk bsig c',
           inlinedFuncBody g bret bsig.sporkNest
             (bacc ++ [Block.mk bsig c'] ++ bs ++ gacc).length))
    inlinedFuncH g gidx (bacc ++ [b']) bs (gacc ++ gacc')

theorem inlinedFuncHWF
        {fsigs fsig g gidx bacc gacc} :
        {bs : List Block} ->
        g.WF fsigs ->
        (_ : gidx < fsigs.length) ->
        fsigs[gidx] = g.fsig ->
        (Func.mk fsig (bacc ++ bs ++ gacc)).WF fsigs ->
        (Func.mk fsig (inlinedFuncH g gidx bacc bs gacc)).WF fsigs
  | [], gwf, glt, gsig, wf => List.append_nil bacc ▸ wf
  | .mk bsig c :: bs, gwf, glt, gsig, wf => by
    simp
    match cspliteq : c.split with
      | (es, ⟨t, t_neq_stmt⟩) =>
        cases t <;> simp <;> try (apply inlinedFuncHWF gwf glt gsig; simpa using wf)
        · case call h args bret =>
          if heqg : h ≠ gidx then
            simp[heqg]
            apply inlinedFuncHWF gwf glt gsig
            simpa using wf
          else
            let heqg := Decidable.of_not_not heqg
            rw[heqg]
            simp[heqg] at cspliteq
            simp
            let c' : Code :=
              .join es (.goto (.mk (bacc.length + (bs.length + gacc.length + 1))
                                   (args ++ bret.args)))
            let gacc' := inlinedFuncBody g bret bsig.sporkNest
                           (bacc ++ [Block.mk bsig c'] ++ bs ++ gacc).length
            let bsigs := (bacc ++ Block.mk bsig c' :: bs ++ gacc ++ gacc').map (·.bsig)
            let wf' := wf.blocks.get ⟨bacc.length, by simp⟩
            simp at wf'
            let cwf := wf'.code
            let splitwf := Code.WF.split_wf cwf
            simp[cspliteq] at splitwf
            let c'wf : c'.WF fsigs bsigs fsig.ret bsig := by
              simp[c', bsigs]
              apply Code.WF.join_wf
              · exact λ ⟨i, il⟩ => splitwf.1 ⟨i, by simp_all⟩
              · apply Code.WF.goto; apply Cont.WF.mk <;> simp
                · simp[gacc']
                  let gh := gwf.head.get0eq
                  simp at gh; rw[gh]; simp
                  show g.fsig.arity = args.length
                  exact gsig ▸ splitwf.2.call_arity
                · exact splitwf.2.call_args.append splitwf.2.call_bret.args
                · match gacc'eq : gacc' with
                    | [] => simp[gacc'] at gacc'eq
                            let ghead := gwf.head.headtail
                            simp[gacc'eq] at ghead
                    | _ :: _ => simp
            let b'wf : (Block.mk bsig c').WF fsigs bsigs fsig.ret := .mk c'wf
            let wfblocks := wf.blocks
            let ⟨tmp, gaccwf⟩ := wf.blocks.unappend
            let ⟨baccwf, tmp'⟩ := tmp.unappend
            let bswf := tmp'.tail
            let helper {l : List Block} (v : IVec (Block.WF fsigs (List.map (fun x => x.bsig) (Func.mk fsig (bacc ++ Block.mk bsig c :: bs ++ gacc)).blocks) (Func.mk fsig (bacc ++ Block.mk bsig c :: bs ++ gacc)).fsig.ret) l) : IVec (Block.WF fsigs (List.map (fun x => x.bsig) (Func.mk fsig (bacc ++ [Block.mk bsig c'] ++ bs ++ (gacc ++ gacc'))).blocks) (Func.mk fsig (bacc ++ [Block.mk bsig c'] ++ bs ++ (gacc ++ gacc'))).fsig.ret) l :=
              v.map (λ b x => by simpa using x.weakening_bsigs (bsigs' := gacc'.map (·.bsig)))
            let wf'' : Func.WF fsigs (.mk fsig (bacc ++ [.mk bsig c'] ++ bs
                                                  ++ (gacc ++ gacc'))) := by
              apply Func.WF.mk
              · apply IVec.append
                · apply IVec.append
                  · apply IVec.append
                    · exact helper baccwf
                    · apply IVec.singleton
                      simpa[bsigs] using b'wf
                  · exact helper bswf
                · apply IVec.append
                  · exact helper gaccwf
                  · simp[gacc']; let x := @inlinedFuncBodyWF fsigs ((bacc ++ [Block.mk bsig c'] ++ bs ++ gacc).map (·.bsig)) fsig.ret g bret bsig.sporkNest (by simpa using splitwf.2.call_bret.blt) (by simpa[gsig, Nat.add_comm] using splitwf.2.call_bret.bsig) gwf; simp at x; exact x
              · cases bacc <;> simp <;> simp at wf <;>
                apply HeadIs.mk <;> simpa using wf.head.get0eq
            simpa[c', gacc']
            using @inlinedFuncHWF fsigs fsig g gidx (gacc ++ gacc') bs
                                  gwf glt gsig (bacc := bacc ++ [.mk bsig c']) wf''

/--
Inline each call to g in the body of f
-/
def inlinedFunc (f g : Func) (gidx : FuncIdx) : Func :=
  .mk f.fsig (inlinedFuncH g gidx [] f.blocks [])

theorem inlinedFuncWF {fsigs} {f g : Func} {gidx : FuncIdx}
                      (gwf : g.WF fsigs) (glt : gidx < fsigs.length)
                      (gsig : fsigs[gidx] = g.fsig) (wf : f.WF fsigs) :
                      (inlinedFunc f g gidx).WF fsigs :=
  inlinedFuncHWF gwf glt gsig ((List.append_nil f.blocks).symm ▸ wf)
