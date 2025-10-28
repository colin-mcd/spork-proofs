import SporkProofs.Syntax
import SporkProofs.Semantics
import SporkProofs.WFSyntax
import SporkProofs.WFSemantics

abbrev x := Nat

structure Extra where
  offset : Nat
  Γ : Nat
  r : Nat
  σ : List Nat

namespace Extra
  @[simp] def add (bsig : BlockSig) (extra : Extra) : BlockSig :=
    ⟨bsig.Γ + extra.Γ, extra.r, bsig.σ ++ extra.σ⟩
  @[simp] def spork (extra : Extra) (r : Nat) : Extra :=
    Extra.mk extra.offset 0 r []
  theorem add_spork_comm {bsig : BlockSig} {extra : Extra} {s : Nat} :
                         (extra.add bsig).spork s = extra.add (bsig.spork s) :=
    by simp; exact ⟨rfl, rfl⟩
end Extra

@[simp] def inlinedArgs (extra : Extra) (scope : Nat) (args : List Var) : List Var :=
  args ++ (List.range' scope extra.Γ).map Var.mk

@[simp] def inlinedCont (extra : Extra) (scope : Nat) : Cont -> Cont
  | .mk b args => .mk (b + extra.offset) (inlinedArgs extra scope args)  

@[simp] def inlinedCode (B: List BlockSig) (bret : BlockIdx) (extra : Extra) (scope : Nat) : Code -> Code
  | .stmt e c =>
    .stmt e (inlinedCode B bret extra scope.succ c)
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
  | .spork bbody bspwn =>
    .spork (inlinedCont extra scope bbody) (inlinedCont (extra.spork B[bspwn.b]!.r) scope bspwn)
  | .spoin bunpr bprom =>
    .spoin (inlinedCont extra scope bunpr)
           (inlinedCont extra scope bprom)

@[simp] def inlinedBlock (B : List BlockSig) (bret : BlockIdx) (extra : Extra) (b : Block) : Block :=
  Block.mk (extra.add b.bsig) (inlinedCode B bret extra b.bsig.Γ b.code)

theorem inlinedArgsRangeWF :
    (extraArity : Nat) -> (scope : Nat) ->
    IVec ((scope + extraArity) ⊢ · WF-var) ((List.range' scope extraArity).map Var.mk)
  | 0, scope => .nil
  | .succ extraArity, scope =>
    .cons (.mk (by simp))
          (Nat.add_succ scope extraArity ▸
           Nat.succ_add scope extraArity ▸
           inlinedArgsRangeWF extraArity scope.succ)

theorem inlinedArgsWF' (extra : Extra) {scope : Nat} : {args : List Var} ->
                       IVec (scope ⊢ · WF-var) args -> IVec ((scope + extra.Γ) ⊢ · WF-var) args
  | _args, wf => wf.weaken

theorem inlinedArgsWF (extra : Extra) {scope : Nat} {args : List Var}
                      (wf : IVec (scope ⊢ · WF-var) args) :
                      IVec ((scope + extra.Γ) ⊢ · WF-var) (inlinedArgs extra scope args) :=
  (inlinedArgsWF' extra wf).append (inlinedArgsRangeWF extra.Γ scope)

theorem inlinedContWFRets
        {bsigs bsigs' bsig rets} (extra : Extra) {c : Cont}
        (bslen : bsigs.length = extra.offset)
        (wf : bsigs'; bsig ⊢ c(rets) WF-cont) :
        (bsigs ++ bsigs'.map extra.add); (extra.add bsig) ⊢ (inlinedCont extra bsig.Γ c)(rets) WF-cont :=
  .mk (by simp[← bslen, Nat.add_comm c.b bsigs.length, wf.blt])
      (by simp[wf.bsig, Nat.add_comm c.b extra.offset, ← bslen]
          rw[Nat.add_assoc, Nat.add_comm rets extra.Γ, ← Nat.add_assoc])
      (inlinedArgsWF extra wf.args)

theorem inlinedContWF
        {bsigs bsigs' bsig} (extra : Extra) {c : Cont}
        (bslen : bsigs.length = extra.offset)
        (wf : bsigs'; bsig ⊢ c WF-cont) :
        (bsigs ++ bsigs'.map extra.add); (extra.add bsig) ⊢ (inlinedCont extra bsig.Γ c) WF-cont :=
  (inlinedContWFRets extra bslen wf.cast0).cast0

theorem inlinedCodeWF
    {fsigs bsigs bsigs' bsig bret}
    (bretlt : bret < bsigs.length)
    (extra : Extra)
    (bretsig : bsigs[bret] = ⟨bsig.r + extra.Γ, bsig.r, extra.σ⟩)
--    (bretsig : (bsigs[bret].Γ = bsig.r + extra.Γ) ∧ (bsigs[bret].r = bsig.r) ∧ (bsigs[bret].σ = extra.σ))
    (bslen : bsigs.length = extra.offset) :
    {c : Code} ->
    fsigs; bsigs'; bsig ⊢ c WF-code ->
    fsigs; (bsigs ++ bsigs'.map extra.add); (extra.add bsig) ⊢
      (inlinedCode bsigs bret extra bsig.Γ c) WF-code
  | .stmt e c, wf =>
    .stmt wf.stmt_expr.weaken
          (by simpa[Nat.add_right_comm bsig.Γ extra.Γ 1]
              using inlinedCodeWF (bsig := bsig.bind) bretlt extra
                                  bretsig bslen (wf.stmt_code))
  | .goto bnext, wf =>
    .goto (inlinedContWF extra bslen wf.goto_bnext)
  | .ite cond bthen belse, wf =>
    .ite wf.ite_cond.weaken
         (inlinedContWF extra bslen wf.ite_bthen)
         (inlinedContWF extra bslen wf.ite_belse)
  | .call h args bret', wf =>
    .call wf.call_flt
          (wf.call_arity)
          (inlinedArgsWF' extra wf.call_args)
          (inlinedContWFRets extra bslen wf.call_bret)
  | .retn args, .retn len sn_nil argswf =>
    .goto (.mk (by simp[Nat.lt_add_right bsigs'.length bretlt])
               (by simp only [getters]
                   rw[List.getElem_append_left (bs := bsigs'.map extra.add) bretlt]
                   simp[sn_nil]
                   rw[← len, bretsig]
                   simp
                   exact sorry)
               (inlinedArgsWF extra argswf))
  | .spork bbody bspwn, wf =>
    .spork (Extra.add_spork_comm ▸
            inlinedContWF extra bslen
              (by show bsigs'; (bsig.spork (bsigs ++ bsigs'.map extra.add)[bspwn.b + extra.offset]!.r) ⊢ bbody WF-cont
                  rw[← bslen]
                  rw[getElem!_pos (bsigs ++ bsigs'.map extra.add) (bspwn.b + bsigs.length)
                       (by simp[bslen, Nat.add_comm bspwn.b extra.offset]
                           exact wf.spork_bspwn.blt)]
                  rw[← List.getElem_append_right' (l₁ := bsigs) (l₂ := bsigs'.map extra.add)
                         (i := bspwn.b) (List.length_map (as := bsigs') extra.add ▸
                                         wf.spork_bspwn.blt)]
                  let h : ((bsigs'.map extra.add)[bspwn.b]'
                             (bsigs'.length_map extra.add ▸ wf.spork_bspwn.blt)).r =
                          bsigs'[bspwn.b]!.r :=
                    List.getElem_map extra.add ▸
                    --congrArg (·.r) bretsig ▸
                    by simp
                  rw[h]
                  exact wf.spork_bbody))
           (--(bsigs ++ List.map (fun bsig => Extra.add bsig extra) bsigs')[(inlinedCont extra bsig.Γ bspwn).b]!
            by
              let iclt : (inlinedCont extra bsig.Γ bspwn).b < bsigs.length :=
                sorry
              let l : (bsigs ++ List.map (fun bsig => Extra.add bsig extra) bsigs')[(inlinedCont extra bsig.Γ bspwn).b]! = bsigs[(inlinedCont extra bsig.Γ bspwn).b]! :=
                by rw[getElem!_pos (bsigs ++ bsigs'.map extra.add) (inlinedCont extra bsig.Γ bspwn).b (by simp at iclt ⊢; exact Nat.lt_add_right bsigs'.length iclt)]
                   rw[List.getElem_append_left (as := bsigs) (bs := bsigs'.map extra.add) (i := (inlinedCont extra bsig.Γ bspwn).b) iclt]
                   symm
                   exact getElem!_pos bsigs (inlinedCont extra bsig.Γ bspwn).b iclt
              rw[getElem!_pos bsigs (inlinedCont extra bsig.Γ bspwn).b iclt] at l
              rw[l]
              let bspwn' := inlinedContWF (extra.spork bsigs[(inlinedCont extra bsig.Γ bspwn).b].r) bslen wf.spork_bspwn
              simpa using bspwn')
    -- .spork wf.spork_flt
    --        wf.spork_arity
    --        (inlinedArgsWF' extra wf.spork_args)
    --        (inlinedContWF extra bslen wf.spork_bbody)
  | .spoin bunpr bprom, wf =>
    .spoin (λ x => by simp at x; exact wf.spoin_oblg x.1)
           (by simp[List.tail_append_of_ne_nil wf.spoin_oblg]
               exact inlinedContWF extra bslen wf.spoin_bunpr)
           (by simp[List.tail_append_of_ne_nil wf.spoin_oblg,
                    List.head_append_left wf.spoin_oblg]
               exact inlinedContWFRets extra bslen wf.spoin_bprom)

l

theorem inlinedBlockWF
    {fsigs bsigs bsigs' bret}
    (bretlt : bret < bsigs.length)
    (extra : Extra)
    (bslen : bsigs.length = extra.offset)
    {b : Block}
    (bretsig : (bsigs[bret].Γ ≤ b.bsig.Γ + extra.Γ) ∧ (bsigs[bret].σ = extra.σ))
--    (bretsig : bsigs[bret] = ⟨b.bsig.r + extra.Γ, extra.r, extra.σ⟩)
    (wf : fsigs; bsigs' ⊢ b WF-block) :
    fsigs; (bsigs ++ bsigs'.map extra.add) ⊢ (inlinedBlock bsigs bret extra b) WF-block :=
  .mk (inlinedCodeWF bsigs bretlt extra bretsig bslen wf.1)

@[simp] def inlinedFuncBody (g : Func) (bret : Cont) (σ : List Nat) (offset : Nat) : List Block :=
  g.blocks.map (inlinedBlock bret.b (.mk offset bret.args.length σ))

theorem inlinedFuncBodyWF
          {fsigs bsigs ret g bret σ}
          (bretlt : bret.b < bsigs.length)
          (bretsig : bsigs[bret.b] = ⟨bret.args.length, ret, σ⟩)
          (wf : fsigs ⊢ g WF-func) :
          IVec (fsigs; (bsigs ++ g.B.map (Extra.mk bsigs.length bret.args.length σ).add) ⊢ · WF-block)
               (inlinedFuncBody g bret σ bsigs.length) :=
  wf.blocks.from_map'
    (inlinedBlock bret.b (.mk bsigs.length bret.args.length σ))
    (λ _b => inlinedBlockWF bretlt (.mk bsigs.length bret.args.length σ) rfl
               ⟨congrArg BlockSig.Γ bretsig ▸ by simp,
                congrArg BlockSig.σ bretsig⟩)

@[simp] def replaceCallInCode (g : FuncIdx) (offset : Nat) (c : Code) : Option (Code × Cont) :=
  let (e, ⟨t, _p⟩) := c.split
  match t with
    | .call h args bret =>
      if h = g then
        some (Code.merge e (Code.goto (.mk offset (args ++ bret.args))), bret)
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
           inlinedFuncBody g bret bsig.σ
             (bacc ++ [Block.mk bsig c'] ++ bs ++ gacc).length))
    inlinedFuncH g gidx (bacc ++ [b']) bs (gacc ++ gacc')

theorem inlinedFuncHWF
        {fsigs fsig g gidx bacc gacc} :
        {bs : List Block} ->
        fsigs ⊢ g WF-func ->
        (_ : gidx < fsigs.length) ->
        fsigs[gidx] = g.fsig ->
        fsigs ⊢ Func.mk fsig (bacc ++ bs ++ gacc) WF-func ->
        fsigs ⊢ Func.mk fsig (inlinedFuncH g gidx bacc bs gacc) WF-func
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
              .merge es (.goto (.mk (bacc.length + (bs.length + gacc.length + 1))
                                   (args ++ bret.args)))
            let gacc' := inlinedFuncBody g bret bsig.σ
                           (bacc ++ [Block.mk bsig c'] ++ bs ++ gacc).length
            let bsigs := (bacc ++ Block.mk bsig c' :: bs ++ gacc ++ gacc').map (·.bsig)
            let wf' := wf.blocks.get ⟨bacc.length, by simp⟩
            simp at wf'
            let cwf := wf'.code
            let splitwf := Code.WF.split_wf cwf
            simp[cspliteq] at splitwf
            let c'wf : fsigs; bsigs; bsig ⊢ c' WF-code := by
              simp[c', bsigs]
              apply Code.WF.merge_wf
              · exact λ ⟨i, il⟩ => splitwf.1 ⟨i, by simp_all⟩
              · apply Code.WF.goto
                apply Cont.WF.mk <;> simp
                · simp[gacc']
                  let gh := gwf.head.get0eq
                  simp at gh; rw[gh]; simp
                  --show g.fsig.arity = args.length
                  --exact gsig ▸ splitwf.2.call_arity
                  exact gsig ▸ ⟨splitwf.2.call_arity, sorry, rfl⟩ 
                · exact splitwf.2.call_args.append splitwf.2.call_bret.args
                · match gacc'eq : gacc' with
                    | [] => simp[gacc'] at gacc'eq
                            let ghead := gwf.head.headtail
                            simp[gacc'eq] at ghead
                    | _ :: _ => simp
            let b'wf : fsigs; bsigs ⊢ ⟨bsig, c'⟩ WF-block := .mk c'wf
            let wfblocks := wf.blocks
            let ⟨tmp, gaccwf⟩ := wf.blocks.unappend
            let ⟨baccwf, tmp'⟩ := tmp.unappend
            let bswf := tmp'.tail
            let helper {l : List Block} (v : IVec (fsigs; ((bacc ++ Block.mk bsig c :: bs ++ gacc).map Block.bsig) ⊢ · WF-block) l) : IVec (Block.WF fsigs ((bacc ++ [Block.mk bsig c'] ++ bs ++ (gacc ++ gacc')).map Block.bsig)) l :=
              v.map (λ b x => by simpa using x.weaken_B (B' := gacc'.map (·.bsig)))
            let wf'' : fsigs ⊢ ⟨fsig, bacc ++ [.mk bsig c'] ++ bs ++ (gacc ++ gacc')⟩ WF-func := by
              apply Blocks.WF.mk
              · apply IVec.append
                · apply IVec.append
                  · apply IVec.append
                    · exact helper baccwf
                    · apply IVec.singleton
                      simpa[bsigs] using b'wf
                  · exact helper bswf
                · apply IVec.append
                  · exact helper gaccwf
                  · simp[gacc']; let x := @inlinedFuncBodyWF fsigs ((bacc ++ [Block.mk bsig c'] ++ bs ++ gacc).map (·.bsig)) ((bacc.map Block.bsig ++ bsig :: (bs.map Block.bsig ++ gacc.map Block.bsig))[bret.b]'sorry).r g bret bsig.σ (by simpa using splitwf.2.call_bret.blt)
                      --(by simpa[gsig, Nat.add_comm] using splitwf.2.call_bret.bsig)
                      (by simp[gsig, Nat.add_comm];
                          rw[splitwf.2.call_bret.bsig]
                          exact sorry)
                      gwf; simp at x; exact x
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
                      (gwf : fsigs ⊢ g WF-func) (glt : gidx < fsigs.length)
                      (gsig : fsigs[gidx] = g.fsig) (wf : fsigs ⊢ f WF-func) :
                      fsigs ⊢ inlinedFunc f g gidx WF-func :=
  inlinedFuncHWF gwf glt gsig ((List.append_nil f.blocks).symm ▸ wf)

namespace Program
  def inlineCallsInFunc : (P : Program) -> (fidx gidx : FuncIdx) -> (g : Func) -> Program
    | .mk funs, fidx, gidx, g =>
      .mk (funs.mapIdx (λ i f => if i = fidx then inlinedFunc f g gidx else f))

  def inlineCalls : (P : Program) -> (gidx : FuncIdx) -> (g : Func) -> Program
    | .mk funs, gidx, g => .mk (funs.mapIdx (λ i f => if i = gidx then f else inlinedFunc f g gidx))

end Program
