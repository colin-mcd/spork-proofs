import SporkProofs.Syntax
import SporkProofs.Semantics
import SporkProofs.WFSyntax
import SporkProofs.WFSemantics

@[simp] def inlinedArgs (bret : Cont) (scope : Nat) (args : List Var) : List Var :=
  args ++ (List.range' scope bret.args.length).map Var.mk

@[simp] def inlinedCont (B B' : BlockSigs) (bret : Cont) (scope : Nat) (c : Cont) : Cont :=
  .mk (c.b + B.length)
      (if B'[c.b]!.r.isExit then c.args else (inlinedArgs bret scope c.args))

@[simp] def inlinedCode (B B': BlockSigs) (bret : Cont) (scope : Nat) : Code -> Code
  | .stmt e c =>
    .stmt e (inlinedCode B B' bret scope.succ c)
  | .goto bnext =>
    .goto (inlinedCont B B' bret scope bnext)
  | .ite cond bthen belse =>
    .ite cond
         (inlinedCont B B' bret scope bthen)
         (inlinedCont B B' bret scope belse)
  | .call h args bret' =>
    .call h args (inlinedCont B B' bret scope bret')
  | .retn args =>
    .goto (.mk bret.b (inlinedArgs bret scope args))
  | .spork bbody bspwn =>
    .spork (inlinedCont B B' bret scope bbody)
           (inlinedCont B B' bret scope bspwn)
  | .spoin bunpr bprom =>
    .spoin (inlinedCont B B' bret scope bunpr)
           (inlinedCont B B' bret scope bprom)

def extraadd (B : BlockSigs) (bret : Cont) (bsig : BlockSig) :=
  if bsig.r.isExit then
    bsig
  else
    .mk (bsig.Γ + bret.args.length) B[bret.b]!.r (bsig.σ ++ B[bret.b]!.σ)

theorem add_exit {B bret} : {bsig : BlockSig} -> bsig.r.isExit -> extraadd B bret bsig = bsig
  | ⟨_Γ, .exit _n, _σ⟩, _isexit => rfl

theorem add_retn {B bret} : {bsig : BlockSig} -> bsig.r.isRetn -> extraadd B bret bsig = ⟨bsig.Γ + bret.args.length, B[bret.b]!.r, bsig.σ ++ B[bret.b]!.σ⟩
  | ⟨_Γ, .retn _n, _σ⟩, _isexit => rfl

theorem add_σ {B bret} : {bsig : BlockSig} -> ∃ σ', (extraadd B bret bsig).σ = bsig.σ ++ σ'
  | ⟨Γ, .exit n, σ⟩ => ⟨[], by simp[extraadd]⟩
  | ⟨Γ, .retn n, σ⟩ => ⟨B[bret.b]!.σ, rfl⟩

theorem add_σ_nil {B bret} : {bsig : BlockSig} -> bsig.σ ≠ [] -> (extraadd B bret bsig).σ ≠ []
  | ⟨Γ, .exit n, σ⟩, nn => nn
  | ⟨Γ, .retn n, σ⟩, nn => by
    simp[extraadd]
    intro x
    contradiction

theorem add_spork_comm {B bret bsig s} :
                       (extraadd B bret bsig).spork s = extraadd B bret (bsig.spork s) :=
  by simp[BlockSig.spork]
     cases h : bsig
     · case mk Γ r σ =>
       cases r
       · case retn n => simp[extraadd]
       · case exit n => rfl
theorem add_spoin_comm {B bret bsig} (σnn : bsig.σ ≠ []) :
                       (extraadd B bret bsig).spoin = extraadd B bret bsig.spoin :=
  by simp[BlockSig.spork, extraadd]
     cases h : bsig
     · case mk Γ r σ =>
       cases req : r
       · case retn n =>
         cases h' : σ
         · case nil => nomatch σnn (h ▸ h')
         · case cons σh σt => simp
       · case exit n => rfl

@[simp] def inlinedBlock (B B' : BlockSigs) (bret : Cont) (b : Block) : Block :=
  if b.bsig.r.isExit then b.offset_B B.length else
    Block.mk (extraadd B bret b.bsig) (inlinedCode B B' bret b.bsig.Γ b.code)

theorem inlinedArgsRangeWF :
    (extraArity : Nat) -> (scope : Nat) ->
    IVec ((scope + extraArity) ⊢ · WF-var) ((List.range' scope extraArity).map Var.mk)
  | 0, scope => .nil
  | .succ extraArity, scope =>
    .cons (.mk (by simp))
          (Nat.add_succ scope extraArity ▸
           Nat.succ_add scope extraArity ▸
           inlinedArgsRangeWF extraArity scope.succ)

theorem inlinedArgsWF' (bret : Cont) {scope : Nat} : {args : List Var} ->
                       IVec (scope ⊢ · WF-var) args -> IVec ((scope + bret.args.length) ⊢ · WF-var) args
  | _args, wf => wf.weaken

theorem inlinedArgsWF (bret : Cont) {scope : Nat} {args : List Var}
                      (wf : IVec (scope ⊢ · WF-var) args) :
                      IVec ((scope + bret.args.length) ⊢ · WF-var) (inlinedArgs bret scope args) :=
  (inlinedArgsWF' bret wf).append (inlinedArgsRangeWF bret.args.length scope)

theorem inlinedContWFRets
        {B B' bsig rets} {bret c : Cont}
        (wf : B'; bsig ⊢ c(rets) WF-cont) :
        (B ++ B'.map (extraadd B bret)); (extraadd B bret bsig) ⊢ (inlinedCont B B' bret bsig.Γ c)(rets) WF-cont :=
  match bsig with
    | ⟨Γ, .exit n, σ⟩ =>
      let h := congrArg BlockSig.r wf.bsig
      by simp at h
         exact
      .mk (by simp[Nat.add_comm B.length, getElem!_pos B' c.b wf.blt, h]
              exact wf.blt)
          (by simp[-List.getElem!_eq_getElem?_getD, getElem!_pos B' c.b wf.blt, h]
              show extraadd B bret (B'[c.b]'wf.blt) =
                   BlockSig.mk (c.args.length + rets) (ResultSig.exit n) σ
              rw[add_exit (by rw[h]; rfl)]
              exact wf.bsig)
          (by simpa[getElem!_pos B' c.b wf.blt, h] using wf.args)
    | ⟨Γ, .retn n, σ⟩ =>
      .mk (by simp[Nat.add_comm c.b B.length, wf.blt])
          (by simp[-List.getElem!_eq_getElem?_getD,
                   getElem!_pos B' c.b wf.blt, wf.bsig,
                   Nat.add_comm c.b B.length, extraadd]
              rw[Nat.add_assoc, Nat.add_comm rets bret.args.length, ← Nat.add_assoc])
          (by simpa[getElem!_pos B' c.b wf.blt, wf.bsig, extraadd]
              using inlinedArgsWF bret wf.args)

theorem inlinedContWF
        {B B' bsig} {bret c : Cont}
        (wf : B'; bsig ⊢ c WF-cont) :
        (B ++ B'.map (extraadd B bret)); (extraadd B bret bsig) ⊢ (inlinedCont B B' bret bsig.Γ c) WF-cont :=
  (inlinedContWFRets wf.cast0).cast0

theorem inlinedContExit {B B' : BlockSigs} {bret scope} {c : Cont}
                        (isexit : B'[c.b]!.r.isExit) :
                        inlinedCont B B' bret scope c = c.offset_B B.length :=
  by simp[Cont.offset_B, -List.getElem!_eq_getElem?_getD, -ResultSig.isExit]
     intro isexitfalse
     rw[isexitfalse] at isexit
     contradiction

theorem inlinedContMapWFRets {B B' : BlockSigs} {bsig : BlockSig} {c rets bret}
                             (isexit : bsig.r.isExit) (wf : B'; bsig ⊢ c(rets) WF-cont) :
                             (B'.map (extraadd B bret)); (extraadd B bret bsig) ⊢ c(rets) WF-cont :=
  (add_exit isexit).symm ▸
  .mk ((List.length_map (extraadd B bret)).symm ▸ wf.blt)
      (wf.bsig ▸
       List.getElem_map (extraadd B bret) ▸
       add_exit (wf.bsig ▸ isexit))
      wf.args

theorem inlinedContMapWF {B B' : BlockSigs} {bsig : BlockSig} {c bret}
                         (isexit : bsig.r.isExit) (wf : B'; bsig ⊢ c WF-cont) :
                         (B'.map (extraadd B bret)); (extraadd B bret bsig) ⊢ c WF-cont :=
  (inlinedContMapWFRets isexit wf.cast0).cast0

@[simp] theorem inlinedContb {B B' bret scope c} :
                             (inlinedCont B B' bret scope c).b = c.b + B.length :=
  rfl

theorem expand_bsig_retn : {bsig : BlockSig} ->
                           bsig.r.isRetn -> bsig = ⟨bsig.Γ, .retn bsig.r.n, bsig.σ⟩
  | ⟨_Γ, .retn _n, _σ⟩, _isretn => rfl
theorem expand_bsig_exit : {bsig : BlockSig} -> bsig.r.isExit ->
                           bsig = ⟨bsig.Γ, .exit bsig.r.n, bsig.σ⟩
  | ⟨_Γ, .exit _n, _σ⟩, _isretn => rfl
theorem expand_list {α} : {l : List α} -> (nn : l ≠ []) -> l = l.head nn :: l.tail
  | _h :: _t, _nn => rfl
theorem List.head!_eq_head {α} [Inhabited α] : {l : List α} -> (nn : l ≠ []) -> l.head nn = l.head!
  | _h :: _t, _nn => rfl

theorem inlinedCodeWF
    {fsigs B B' bsig bretsigΓ}
    -- (extra : Extra)
    (bret : Cont)
    (isretn : bsig.r.isRetn)
    (bretwf : B; ⟨bretsigΓ, B[bret.b]!.r, B[bret.b]!.σ⟩ ⊢ bret(bsig.r.n) WF-cont) :
    -- (bretlt : bret < B.length)
    -- (bretsig : B[bret] = ⟨bsig.r.n + extra.Γ, bsig.r, extra.σ⟩)
--    (bretsig : (B[bret].Γ = bsig.r + extra.Γ) ∧ (B[bret].r = bsig.r) ∧ (B[bret].σ = extra.σ))
    -- (bslen : B.length = extra.offset)
    -- (req : extra.r = bsig.r) :
    {c : Code} ->
    fsigs; B'; bsig ⊢ c WF-code ->
    fsigs; (B ++ B'.map (extraadd B bret)); (extraadd B bret bsig) ⊢
      (inlinedCode B B' bret bsig.Γ c) WF-code
  | .stmt e c, wf =>
    let z := inlinedCodeWF (bsig := bsig.bind) bret isretn bretwf wf.stmt_code
    expand_bsig_retn isretn ▸
    .stmt wf.stmt_expr.weaken
          (by rw[expand_bsig_retn isretn] at z
              simpa[Nat.add_right_comm, extraadd] using z)
  | .goto bnext, wf =>
    .goto (inlinedContWF wf.goto_bnext)
  | .ite cond bthen belse, wf =>
    .ite (expand_bsig_retn isretn ▸ wf.ite_cond.weaken)
         (inlinedContWF wf.ite_bthen)
         (inlinedContWF wf.ite_belse)
  | .call h args bret', wf =>
    .call wf.call_flt
          (wf.call_arity)
          (expand_bsig_retn isretn ▸ inlinedArgsWF' bret wf.call_args)
          (inlinedContWFRets wf.call_bret)
  | .retn args, .retn len sn_nil argswf =>
    expand_bsig_retn isretn ▸
    .goto (.mk (by simp[Nat.lt_add_right B'.length bretwf.blt])
               (by rw[extraadd]
                   simp only [getters]
                   rw[List.getElem_append_left bretwf.blt]
                   --simp only [getters]
                   --rw[← len]
                   rw[sn_nil]
                   let x := bretwf.bsig
                   rw (occs := [2]) [len] at x
                   rw[x]
                   simp[Nat.add_comm]
                   
                   )
               (inlinedArgsWF bret argswf))
  | .spork bbody bspwn, wf =>
    let bspwnexit : (B'[bspwn.b]'wf.spork_bspwn.blt).r.isExit = true :=
      congrArg BlockSig.r wf.spork_bspwn.bsig ▸
      getElem!_pos B' bspwn.b wf.spork_bspwn.blt ▸
      by simp[BlockSig.spwn]
    .spork (inlinedContb ▸
            by --simp only [extraadd.eq_1]
               --simp only [getters]
               rw[getElem!_pos (B ++ B'.map (extraadd B bret)) (bspwn.b + B.length)
                     (by simp[Nat.add_comm bspwn.b B.length]
                         exact wf.spork_bspwn.blt)]
               rw[← List.getElem_append_right' (l₁ := B)
                      (l₂ := B'.map (extraadd B bret))
                      (List.length_map (as := B') (extraadd B bret) ▸
                       wf.spork_bspwn.blt)]
               rw[List.getElem_map]
               let x := congrArg BlockSig.r wf.spork_bspwn.bsig
               simp only [getters, BlockSig.spwn] at x
               rw[@expand_bsig_exit (B'[bspwn.b]'wf.spork_bspwn.blt) (x ▸ rfl)]
               rw[x]
               simp[extraadd])
           (add_spork_comm ▸
            inlinedContWF
              (by rw[inlinedContb,
                     getElem!_pos (B ++ B'.map (extraadd B bret)) (bspwn.b + B.length)
                       (by simp[Nat.add_comm bspwn.b B.length]
                           exact wf.spork_bspwn.blt),
                     ← List.getElem_append_right' (l₁ := B) (l₂ := B'.map (extraadd B bret))
                         (i := bspwn.b) (List.length_map (as := B') (extraadd B bret) ▸
                                         wf.spork_bspwn.blt)]
                  let h : ((B'.map (extraadd B bret))[bspwn.b]'
                             (B'.length_map (extraadd B bret) ▸ wf.spork_bspwn.blt)).r =
                          B'[bspwn.b]!.r :=
                    List.getElem_map (extraadd B bret) ▸
                    let y := wf.spork_bspwn.bsig
                    by rw[add_exit bspwnexit]
                       rw[← getElem!_pos B' bspwn.b wf.spork_bspwn.blt]
                  rw[h]
                  exact wf.spork_bbody))
           (let y := inlinedContWF wf.spork_bspwn
            by rw[BlockSig.spwn,
                  inlinedContb,
                  getElem!_pos (B ++ B'.map (extraadd B bret)) (bspwn.b + B.length)
                    (by simpa[Nat.add_comm bspwn.b B.length]
                        using wf.spork_bspwn.blt),
                  ← List.getElem_append_right' B _,
                  List.getElem_map (extraadd B bret)
                    (h := (List.length_map (extraadd B bret)).symm ▸ wf.spork_bspwn.blt),
                  add_exit bspwnexit]               
               rw[BlockSig.spwn,
                  add_exit rfl,
                  getElem!_pos B' bspwn.b wf.spork_bspwn.blt] at y
               simp only [getters] at y
               rw[add_retn isretn]
               exact y.weaken_Γ)
  | .spoin bunpr bprom, wf =>
    .spoin (λ x => by rw[add_retn isretn] at x
                      simp at x
                      exact wf.spoin_oblg x.1)
           (add_spoin_comm wf.spoin_oblg ▸
            inlinedContWF wf.spoin_bunpr)
           (let x : bsig.spoin.Γ = bsig.Γ := rfl
            let ⟨σ', σ_σ'⟩ := add_σ (B := B) (bret := bret) (bsig := bsig)
            let y : bsig.σ.head wf.spoin_oblg =
                    (extraadd B bret bsig).σ.head (add_σ_nil wf.spoin_oblg) :=
              List.head!_eq_head wf.spoin_oblg ▸
              List.head!_eq_head (add_σ_nil wf.spoin_oblg) ▸
              σ_σ' ▸
              expand_list wf.spoin_oblg ▸
              rfl
            y ▸
            add_spoin_comm wf.spoin_oblg ▸
            x ▸
            inlinedContWFRets wf.spoin_bprom)

theorem offsetCodeWF
    {fsigs B B' bret bsig}
    (isexit : bsig.r.isExit) :
    {c : Code} ->
    fsigs; B'; bsig ⊢ c WF-code ->
    fsigs; (B ++ B'.map (extraadd B bret)); (extraadd B bret bsig) ⊢
      (c.offset_B B.length) WF-code
  | .stmt e c, wf =>
    .stmt ((add_exit isexit).symm ▸ wf.stmt_expr)
          (let x := offsetCodeWF (bsig := bsig.bind) isexit wf.stmt_code
           by rw[@add_exit B bret bsig isexit]
              rw[@add_exit B bret bsig.bind isexit] at x
              exact x)
  | .goto bnext, wf =>
    .goto (inlinedContMapWF isexit wf.goto_bnext).weaken_Bᵣ
  | .ite cond bthen belse, wf =>
    .ite ((add_exit isexit).symm ▸ wf.ite_cond)
         (inlinedContMapWF isexit wf.ite_bthen).weaken_Bᵣ
         (inlinedContMapWF isexit wf.ite_belse).weaken_Bᵣ
  | .call h args bret', wf =>
    .call wf.call_flt
          wf.call_arity
          ((add_exit isexit).symm ▸ wf.call_args)
          (inlinedContMapWFRets isexit wf.call_bret).weaken_Bᵣ
  | .retn args, wf =>
    (add_exit isexit).symm ▸ 
    .retn wf.retn_length wf.retn_oblg wf.retn_args
  | .spork bbody bspwn, wf =>
    (add_exit isexit).symm ▸
    let bspwnlt : bspwn.b < B'.length :=
      wf.spork_bspwn.blt
    let x : (B ++ B'.map (extraadd B bret))[(Cont.offset_B (List.length B) bspwn).b]! =
            (B'.map (extraadd B bret))[bspwn.b]! :=
      Cont.offset_B_b ▸
      getElem!_pos (B ++ B'.map (extraadd B bret)) (bspwn.b + B.length)
        (List.length_append ▸
         Nat.add_comm bspwn.b B.length ▸
         Nat.add_lt_add_iff_left.mpr
           ((List.length_map (extraadd B bret)).symm ▸ bspwnlt)) ▸
      List.getElem_append_right' B (List.length_map (extraadd B bret) ▸ bspwnlt) ▸
      (getElem!_pos (B'.map (extraadd B bret)) bspwn.b
        ((List.length_map (extraadd B bret)).symm ▸ bspwnlt)).symm
    let y : (B'.map (extraadd B bret))[bspwn.b]! = B'[bspwn.b]! :=
      getElem!_pos (B'.map (extraadd B bret)) bspwn.b
        ((List.length_map (extraadd B bret)).symm ▸ bspwnlt) ▸
      getElem!_pos B' bspwn.b bspwnlt ▸
      List.getElem_map (extraadd B bret) ▸
      add_exit (bsig := B'[bspwn.b])
        (getElem!_pos B' bspwn.b bspwnlt ▸ wf.spork_exit)
    .spork (x ▸ y ▸ wf.spork_exit)
           (x ▸ add_exit (bsig := bsig.spork (B'.map (extraadd B bret))[bspwn.b]!.r.n) isexit ▸
           (inlinedContMapWF (bsig := bsig.spork (B'.map (extraadd B bret))[bspwn.b]!.r.n) isexit
             (y ▸ wf.spork_bbody)).weaken_Bᵣ)
           (x ▸ add_exit (bsig := bsig.spwn (B'.map (extraadd B bret))[bspwn.b]!.r.n) rfl ▸
             (inlinedContMapWF (bsig := bsig.spwn (B'.map (extraadd B bret))[bspwn.b]!.r.n)
               rfl (y ▸ wf.spork_bspwn)).weaken_Bᵣ)
  | .spoin bunpr bprom, wf =>
    (add_exit isexit).symm ▸ 
    .spoin (wf.spoin_oblg)
           (add_exit (bsig := bsig.spoin) isexit ▸
            (inlinedContMapWF (bsig := bsig.spoin) isexit wf.spoin_bunpr).weaken_Bᵣ)
           (add_exit (bsig := bsig.spoin) isexit ▸
            (inlinedContMapWFRets (bsig := bsig.spoin) isexit wf.spoin_bprom).weaken_Bᵣ)

theorem inlinedBlockWF
    {fsigs B B' bret b bretsigΓ}
    (bretwf : B; ⟨bretsigΓ, B[bret.b]!.r, B[bret.b]!.σ⟩ ⊢ bret(b.bsig.r.n) WF-cont)
    (wf : fsigs; B' ⊢ b WF-block) :
    fsigs; (B ++ B'.map (extraadd B bret)) ⊢ (inlinedBlock B B' bret b) WF-block :=
  if isexit : b.bsig.r.isExit then
    by rw[inlinedBlock, isexit]
       simp only [↓reduceIte]
       apply Block.WF.mk
       simp only [Block.offset_B, getters]
       let x := offsetCodeWF (B := B) (bret := bret) isexit wf.code
       rw[add_exit isexit] at x
       exact x
  else
    let isretn : b.bsig.r.isRetn := b.bsig.r.not_isExit_isRetn isexit
    .mk (by simp only [inlinedBlock, Block.offset_B, isexit,
                       Bool.false_eq_true, reduceIte, getters]
            exact inlinedCodeWF bret isretn bretwf wf.code)

@[simp] def inlinedFuncBody (B : BlockSigs) (g : Func) (bret : Cont) : List Block :=
  g.blocks.map (inlinedBlock B g.B bret)

theorem inlinedFuncBodyWF
          {fsigs B g bret bretsigΓ}
          (bretwf : B; ⟨bretsigΓ, B[bret.b]!.r, B[bret.b]!.σ⟩ ⊢ bret(g.fsig.ret) WF-cont)
          (wf : fsigs ⊢ g WF-func) :
          IVec (λ b => (fsigs; (B ++ g.B.map (extraadd B bret)) ⊢ b WF-block) /- ∧
                       (B[bret.b]!.r.isRetn -> b.bsig.r.isRetn -> b.bsig.r = B[bret.b]!.r)-/)
               (inlinedFuncBody B g bret) :=
  let bretlt : bret.b < B.length :=
    bretwf.blt
  let x : B[bret.b]! = B[bret.b] :=
    getElem!_pos B bret.b bretlt
  let Γeq : bret.args.length + g.fsig.ret = B[bret.b].Γ :=
    by simpa only [getters] using congrArg BlockSig.Γ bretwf.bsig.symm
  by simpa[← x, -List.getElem!_eq_getElem?_getD] using
    (wf.blocks.zip wf.retns).from_map'
      (inlinedBlock B g.B bret)
      λ (b : Block) ⟨wf', req'⟩ =>
        if isexit : b.bsig.r.isExit then
          by rw[inlinedBlock, isexit]
             --apply And.intro
             · apply Block.WF.mk
               simpa[add_exit isexit]
               using offsetCodeWF isexit wf'.code
             -- · intro bretisretn isretn
             --   cases h : b.bsig.r <;>
             --   (simp at isretn isexit
             --    rw[h] at isretn isexit
             --    contradiction)
        else by
          let isretn := ResultSig.not_isExit_isRetn isexit
          -- apply And.intro
          · simpa[x]
            using @inlinedBlockWF fsigs B g.B bret b bretsigΓ (req' isretn ▸ bretwf) wf'
          -- · intro bretisretn _
          --   simp only [inlinedBlock]
          --   rw[(Bool.not_eq_not (b := false)).mp isexit]
          --   simp only [Bool.false_eq_true, reduceIte, getters]
          --   rw[add_retn isretn]
          --   simp only [getters]

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
           inlinedFuncBody ((bacc ++ [Block.mk bsig c'] ++ bs ++ gacc).map Block.bsig) g bret))
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
            have heqg := Decidable.of_not_not heqg
            rw[heqg]
            simp[heqg] at cspliteq
            simp
            let c' : Code :=
              .merge es (.goto (.mk (bacc.length + (bs.length + gacc.length + 1))
                                   (args ++ bret.args)))
            let gacc' := inlinedFuncBody ((bacc ++ [Block.mk bsig c'] ++ bs ++ gacc).map
                                            Block.bsig) g bret
            let B := (bacc ++ Block.mk bsig c' :: bs ++ gacc ++ gacc').map (·.bsig)
            have wf' := wf.blocks.get ⟨bacc.length, by simp⟩
            simp at wf'
            have cwf := wf'.code
            have splitwf := Code.WF.split_wf cwf
            simp[cspliteq] at splitwf
            have c'wf : fsigs; B; bsig ⊢ c' WF-code := by
              simp[c', B]
              apply Code.WF.merge_wf
              · exact λ ⟨i, il⟩ => splitwf.1 ⟨i, by simp_all⟩
              · apply Code.WF.goto
                apply Cont.WF.mk <;> simp
                · simp[gacc']
                  have gh := gwf.head.get0eq
                  simp at gh; rw[gh]; simp[extraadd, -List.getElem!_eq_getElem?_getD]
                  have req := congrArg BlockSig.r splitwf.2.call_bret.bsig
                  have σeq := congrArg BlockSig.σ splitwf.2.call_bret.bsig
                  rw[getElem!_pos _ bret.b splitwf.2.call_bret.blt]
                  exact gsig ▸ ⟨splitwf.2.call_arity, req, σeq⟩
                · exact splitwf.2.call_args.append splitwf.2.call_bret.args
                · match gacc'eq : gacc' with
                    | [] => simp[gacc'] at gacc'eq
                            simpa[gacc'eq] using gwf.head.headtail
                    | _ :: _ => simp
            have b'wf : fsigs; B ⊢ ⟨bsig, c'⟩ WF-block := .mk c'wf
            have wfblocks := wf.blocks
            have ⟨tmp, gaccwf⟩ := wf.blocks.unappend
            have ⟨baccwf, tmp'⟩ := tmp.unappend
            have bswf := tmp'.tail
            have helper {l : List Block}
                       (v : IVec (fsigs; ((bacc ++ Block.mk bsig c :: bs ++ gacc).map
                                            Block.bsig) ⊢ · WF-block) l) :
                       IVec (Block.WF fsigs ((bacc ++ [Block.mk bsig c'] ++ bs ++
                                                   (gacc ++ gacc')).map Block.bsig)) l :=
              v.map (λ b x => by simpa using x.weaken_Bₗ (B' := gacc'.map (·.bsig)))
            have wf'' : fsigs ⊢ ⟨fsig, bacc ++ [.mk bsig c'] ++
                                         bs ++ (gacc ++ gacc')⟩ WF-func := by
              apply Blocks.WF.mk
              · apply IVec.append
                · apply IVec.append
                  · apply IVec.append
                    · exact helper baccwf
                    · apply IVec.singleton
                      simpa[B] using b'wf
                  · exact helper bswf
                · apply IVec.append
                  · exact helper gaccwf
                  · simp[gacc']
                    have x := @inlinedFuncBodyWF fsigs
                                ((bacc ++ [Block.mk bsig c'] ++ bs ++ gacc).map (·.bsig))
                                g bret
                                -- (by have Γeq : (bret.args.length + fsigs[gidx].ret) =
                                --                (bsig.binds es.length).Γ := by
                                --       simp[BlockSig.binds]
                                --       rw[gsig]
                                --       exact splitwf.2.call_bret.bsig
                                --     have y : (bacc.map Block.bsig ++ bsig :: (bs.map Block.bsig ++ gacc.map Block.bsig))[bret.b]! = bsig.binds es.length :=
                                --       getElem!_pos (bacc.map Block.bsig ++ bsig :: (bs.map Block.bsig ++ gacc.map Block.bsig)) bret.b splitwf.2.call_bret.blt ▸
                                --       splitwf.2.call_bret.bsig ▸
                                --       Γeq ▸
                                --       rfl
                                --     simpa[gsig, y, -List.getElem!_eq_getElem?_getD] using splitwf.2.call_bret)
                                (bsig.binds es.length).Γ
                                (by -- have y : (bacc.map Block.bsig ++ bsig :: (bs.map Block.bsig ++ gacc.map Block.bsig))[bret.b]! = bsig.binds es.length :=
                                    --   getElem!_pos (bacc.map Block.bsig ++ bsig :: (bs.map Block.bsig ++ gacc.map Block.bsig)) bret.b splitwf.2.call_bret.blt ▸
                                    --   splitwf.2.call_bret.bsig ▸
                                    --   Γeq ▸
                                    --   rfl
                                    have x : (bacc.map Block.bsig ++ ([Block.mk bsig c'].map Block.bsig ++ (bs.map Block.bsig ++ gacc.map Block.bsig))); (bsig.binds es.length) ⊢ bret ( g.fsig.ret ) WF-cont := gsig ▸ splitwf.2.call_bret
                                    have y : ((bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc))).map Block.bsig); (bsig.binds es.length) ⊢ bret ( g.fsig.ret ) WF-cont :=
                                      List.map_append.symm ▸
                                      List.map_append.symm ▸
                                      List.map_append.symm ▸
                                      x
                                    have bretlt' : bret.b < (List.map Block.bsig (bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc)))).length := by simpa using splitwf.2.call_bret.blt
                                    have bretlt'' : bret.b < (bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc))).length := by simpa using splitwf.2.call_bret.blt
                                    have z : (bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc)))[bret.b].bsig = BlockSig.mk (bret.args.length + g.fsig.ret) (bsig.binds es.length).r (bsig.binds es.length).σ := List.getElem_map Block.bsig (h := bretlt') ▸ y.bsig
                                    have zr : (bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc)))[bret.b].bsig.r = (bsig.binds es.length).r := congrArg (a₂ := BlockSig.mk (bret.args.length + g.fsig.ret) (bsig.binds es.length).r (bsig.binds es.length).σ) BlockSig.r z
                                    have zσ : (bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc)))[bret.b].bsig.σ = (bsig.binds es.length).σ := congrArg (a₂ := BlockSig.mk (bret.args.length + g.fsig.ret) (bsig.binds es.length).r (bsig.binds es.length).σ) BlockSig.σ z
                                    rw[List.append_assoc]
                                    rw[List.append_assoc]
                                    rw[getElem!_pos (List.map (fun x => x.bsig) (bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc)))) bret.b (by simpa using bretlt')]
                                    rw[y.bsig]
                                    simpa using x
                                )
                                --(by simpa[gsig, Nat.add_comm] using splitwf.2.call_bret.bsig)
                                gwf
                    -- have x := x.unzip.1
                    have fh : g.blocks.map (extraadd (bacc.map Block.bsig ++ bsig :: (bs.map Block.bsig ++ gacc.map Block.bsig)) bret ∘ Block.bsig) =
                             g.blocks.map (Block.bsig ∘ inlinedBlock (bacc.map Block.bsig ++ bsig :: (bs.map Block.bsig ++ gacc.map Block.bsig)) (g.blocks.map Block.bsig ) bret) :=
                      List.map_eq_map_iff.mpr
                        λ a ain => by simp[extraadd]; cases a.bsig.r <;> simp
                    simpa[fh, extraadd] using x
              · have x : IVec (fun b => b.bsig.r.isRetn = true →
                                       b.bsig.r = ResultSig.retn fsig.ret)
                             (bacc ++ Block.mk bsig c' :: bs ++ gacc) :=
                  List.append_cons bacc (Block.mk bsig c') bs ▸
                  List.append_assoc (bacc ++ [Block.mk bsig c']) bs gacc ▸
                  (List.append_assoc (bacc ++ [Block.mk bsig c]) bs gacc ▸
                   List.append_cons bacc (Block.mk bsig c) bs ▸
                    wf.retns).peephole λ a isretn => (by simp at a isretn; exact a isretn)
                have z : IVec (fun b => b.bsig.r.isRetn = true →
                                        b.bsig.r = ResultSig.retn fsig.ret)
                              (bacc ++ Block.mk bsig c' :: bs ++ gacc ++ gacc') :=
                  x.append $ by
                    simp only [gacc', inlinedFuncBody]
                    apply IVec.from_map_list
                    intro a isretn
                    simp[-ResultSig.isExit, -ResultSig.isRetn] at isretn ⊢
                    cases h : a.bsig.r
                    · case retn n =>
                      simp[h] at isretn ⊢
                      rw[add_retn (bsig := a.bsig) (h ▸ rfl)] at isretn ⊢
                      simp only [getters] at isretn ⊢
                      have isretn' : (bacc.map Block.bsig ++ ([Block.mk bsig c].map Block.bsig ++ (bs.map Block.bsig ++ gacc.map Block.bsig)))[bret.b]!.r.isRetn := isretn
                      have bretlt := splitwf.2.call_bret.blt
                      have bretlt' : bret.b < (bacc ++ Block.mk bsig c :: bs ++ gacc).length :=
                        by simpa using bretlt
                      have x : (bacc ++ ⟨bsig, c⟩ :: bs ++ gacc)[bret.b].bsig.r =
                               ResultSig.retn fsig.ret :=
                        wf.retns⁅bret.b⁆ (by
                          show (bacc ++ Block.mk bsig c :: bs ++ gacc)[bret.b].bsig.r.isRetn = true
                          rw[← List.map_append, ← List.map_append, ← List.map_append] at isretn'
                          rw[getElem!_pos (List.map Block.bsig (bacc ++ ([Block.mk bsig c] ++ (bs ++ gacc)))) bret.b (by simpa using bretlt')] at isretn'
                          rw[List.getElem_map Block.bsig] at isretn'
                          simpa using isretn')
                      show (bacc.map Block.bsig ++ ([Block.mk bsig c].map Block.bsig ++
                             (bs.map Block.bsig ++ gacc.map Block.bsig)))[bret.b]!.r =
                           ResultSig.retn fsig.ret
                      rw[← List.map_append, ← List.map_append, ← List.map_append]
                      rw[getElem!_pos _ bret.b (by simpa using bretlt)]
                      rw[List.getElem_map]
                      simpa using x
                    · case exit n =>
                      simp[h] at isretn
                simpa[-ResultSig.isRetn] using z
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
