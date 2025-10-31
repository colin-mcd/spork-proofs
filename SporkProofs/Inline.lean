import SporkProofs.Syntax
import SporkProofs.Semantics
import SporkProofs.WFSyntax
import SporkProofs.WFSemantics

/-!
Defines an approach to inlining function definitions
and proves that the result is well-formed.
-/

@[simp] def inlinedArgs (bret : Cont) (scope : Nat) (args : List Var) : List Var :=
  args ++ (List.range' scope bret.args.length).map Var.mk

@[simp] def Cont.inlined (c : Cont) (B B' : BlockSigs) (bret : Cont) (scope : Nat) : Cont :=
  .mk (c.b + B.length)
      (if B'[c.b]!.r.isExit then c.args else (inlinedArgs bret scope c.args))

@[simp] def Code.inlined (B B': BlockSigs) (bret : Cont) (scope : Nat) : Code -> Code
  | .stmt e c =>
    .stmt e (c.inlined B B' bret scope.succ)
  | .goto bnext =>
    .goto (bnext.inlined B B' bret scope)
  | .ite cond bthen belse =>
    .ite cond
         (bthen.inlined B B' bret scope)
         (belse.inlined B B' bret scope)
  | .call h args bret' =>
    .call h args (bret'.inlined B B' bret scope)
  | .retn args =>
    .goto (.mk bret.b (inlinedArgs bret scope args))
  | .spork bbody bspwn =>
    .spork (bbody.inlined B B' bret scope)
           (bspwn.inlined B B' bret scope)
  | .spoin bunpr bprom =>
    .spoin (bunpr.inlined B B' bret scope)
           (bprom.inlined B B' bret scope)

/--
Determines the new bsig of an inlined block:
- if the old bsig was exiting (i.e. down a spawn path), it remains the same
- if the old bsig was returning (i.e. part of the main function body),
  update the bsig to have the additional args stored in bret since
  it will need to pass around those until the return, and also prepend
  the caller's spork obligation to this block's
-/
def BlockSig.inlined (B : BlockSigs) (bret : Cont) (bsig : BlockSig) :=
  if bsig.r.isExit then
    bsig
  else
    .mk (bsig.Γ + bret.args.length) B[bret.b]!.r (bsig.σ ++ B[bret.b]!.σ)

theorem BlockSig.inlined_exit
    {B bret} : {bsig : BlockSig} -> bsig.r.isExit ->
    bsig.inlined B bret = bsig
  | ⟨_Γ, .exit _n, _σ⟩, _isexit => rfl

theorem BlockSig.inlined_retn
    {B bret} : {bsig : BlockSig} -> bsig.r.isRetn ->
    bsig.inlined B bret = ⟨bsig.Γ + bret.args.length, B[bret.b]!.r, bsig.σ ++ B[bret.b]!.σ⟩
  | ⟨_Γ, .retn _n, _σ⟩, _isexit => rfl

theorem BlockSig.inlined_σ {B bret} : {bsig : BlockSig} ->
                           ∃ σ', (bsig.inlined B bret).σ = bsig.σ ++ σ'
  | ⟨Γ, .exit n, σ⟩ => ⟨[], by simp[BlockSig.inlined]⟩
  | ⟨Γ, .retn n, σ⟩ => ⟨B[bret.b]!.σ, rfl⟩

theorem BlockSig.inlined_σ_nil {B bret} : {bsig : BlockSig} -> bsig.σ ≠ [] ->
                               (bsig.inlined B bret).σ ≠ []
  | ⟨Γ, .exit n, σ⟩, nn => nn
  | ⟨Γ, .retn n, σ⟩, nn => by
    simp[BlockSig.inlined]
    intro x
    contradiction

theorem BlockSig.inlined_spork_comm
    {B bret s} {bsig : BlockSig} :
    (bsig.inlined B bret).spork s = (bsig.spork s).inlined B bret :=
  by simp[BlockSig.spork]
     cases h : bsig
     · case mk Γ r σ =>
       cases r
       · case retn n => simp[BlockSig.inlined]
       · case exit n => rfl

theorem BlockSig.inlined_spoin_comm
    {B bret} {bsig : BlockSig} (σnn : bsig.σ ≠ []) :
    (bsig.inlined B bret).spoin = bsig.spoin.inlined B bret :=
  by simp[BlockSig.spork, BlockSig.inlined]
     cases h : bsig
     · case mk Γ r σ =>
       cases req : r
       · case retn n =>
         cases h' : σ
         · case nil => nomatch σnn (h ▸ h')
         · case cons σh σt => simp
       · case exit n => rfl

/-- only make changes if part of the main function body (i.e. non-exiting) -/
@[simp] def Block.inlined (B B' : BlockSigs) (bret : Cont) (b : Block) : Block :=
  if b.bsig.r.isExit then b.offset_B B.length else
    Block.mk (b.bsig.inlined B bret) (b.code.inlined B B' bret b.bsig.Γ)

def Block.inlined_ext {B B' bret} : Block.inlined B B' bret = (·.inlined B B' bret) := rfl

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
                       IVec (scope ⊢ · WF-var) args ->
                       IVec ((scope + bret.args.length) ⊢ · WF-var) args
  | _args, wf => wf.weaken

theorem inlinedArgsWF (bret : Cont) {scope : Nat} {args : List Var}
                      (wf : IVec (scope ⊢ · WF-var) args) :
                      IVec ((scope + bret.args.length) ⊢ · WF-var)
                           (inlinedArgs bret scope args) :=
  (inlinedArgsWF' bret wf).append (inlinedArgsRangeWF bret.args.length scope)

theorem Cont.WFRets.inlined
        {B B' bsig rets} {bret c : Cont}
        (wf : B'; bsig ⊢ c(rets) WF-cont) :
        (B ++ B'.map (·.inlined B bret));
          (bsig.inlined B bret) ⊢ (c.inlined B B' bret bsig.Γ)(rets) WF-cont :=
  match bsig with
    | ⟨Γ, .exit n, σ⟩ =>
      have h := congrArg BlockSig.r wf.bsig
      by simp at h
         exact
      .mk (by simp[Nat.add_comm B.length, getElem!_pos B' c.b wf.blt, h]
              exact wf.blt)
          (by simp[-List.getElem!_eq_getElem?_getD, getElem!_pos B' c.b wf.blt, h]
              show (B'[c.b]'wf.blt).inlined B bret =
                   BlockSig.mk (c.args.length + rets) (ResultSig.exit n) σ
              rw[(B'[c.b]'wf.blt).inlined_exit (by rw[h]; rfl)]
              exact wf.bsig)
          (by simpa[getElem!_pos B' c.b wf.blt, h] using wf.args)
    | ⟨Γ, .retn n, σ⟩ =>
      .mk (by simp[Nat.add_comm c.b B.length, wf.blt])
          (by simp[-List.getElem!_eq_getElem?_getD,
                   getElem!_pos B' c.b wf.blt, wf.bsig,
                   Nat.add_comm c.b B.length, BlockSig.inlined]
              rw[Nat.add_assoc, Nat.add_comm rets bret.args.length, ← Nat.add_assoc])
          (by simpa[getElem!_pos B' c.b wf.blt, wf.bsig, BlockSig.inlined]
              using inlinedArgsWF bret wf.args)

theorem Cont.WF.inlined
        {B B' bsig} {bret c : Cont}
        (wf : B'; bsig ⊢ c WF-cont) :
        (B ++ B'.map (·.inlined B bret));
          (bsig.inlined B bret) ⊢ (c.inlined B B' bret bsig.Γ) WF-cont :=
  wf.cast0.inlined.cast0

-- theorem Cont.inlined_exit {B B' : BlockSigs} {bret scope} {c : Cont}
--                           (isexit : B'[c.b]!.r.isExit) :
--                           c.inlined B B' bret scope = c.offset_B B.length :=
--   by simp[Cont.offset_B, -List.getElem!_eq_getElem?_getD, -ResultSig.isExit]
--      intro isexitfalse
--      rw[isexitfalse] at isexit
--      contradiction

--inlinedContMapWFRets
theorem Cont.WFRets.inlined_map
    {B B' : BlockSigs} {bsig : BlockSig} {c rets bret}
    (isexit : bsig.r.isExit) (wf : B'; bsig ⊢ c(rets) WF-cont) :
    (B'.map (·.inlined B bret)); (bsig.inlined B bret) ⊢ c(rets) WF-cont :=
  (bsig.inlined_exit isexit).symm ▸
  .mk ((List.length_map (BlockSig.inlined B bret)).symm ▸ wf.blt)
      (wf.bsig ▸
       List.getElem_map (BlockSig.inlined B bret) ▸
       BlockSig.inlined_exit (wf.bsig ▸ isexit))
      wf.args

theorem Cont.WF.inlined_map
    {B B' : BlockSigs} {bsig : BlockSig} {c bret}
    (isexit : bsig.r.isExit) (wf : B'; bsig ⊢ c WF-cont) :
    (B'.map (·.inlined B bret)); (bsig.inlined B bret) ⊢ c WF-cont :=
  (wf.cast0.inlined_map isexit).cast0

@[simp] theorem Cont.inlined_b {B B' bret scope} {c : Cont} :
                               (c.inlined B B' bret scope).b = c.b + B.length :=
  rfl

theorem BlockSig.expand_retn :
    {bsig : BlockSig} -> bsig.r.isRetn -> bsig = ⟨bsig.Γ, .retn bsig.r.n, bsig.σ⟩
  | ⟨_Γ, .retn _n, _σ⟩, _isretn => rfl
theorem BlockSig.expand_exit :
    {bsig : BlockSig} -> bsig.r.isExit -> bsig = ⟨bsig.Γ, .exit bsig.r.n, bsig.σ⟩
  | ⟨_Γ, .exit _n, _σ⟩, _isretn => rfl

theorem List.expand {α} : {l : List α} -> (nn : l ≠ []) -> l = l.head nn :: l.tail
  | _h :: _t, _nn => rfl
theorem List.head!_eq_head {α} [Inhabited α] : {l : List α} -> (nn : l ≠ []) ->
                           l.head nn = l.head!
  | _h :: _t, _nn => rfl

theorem Code.WF.inlined
    {fsigs B B' bsig bretsigΓ}
    (bret : Cont)
    (isretn : bsig.r.isRetn)
    (bretwf : B; ⟨bretsigΓ, B[bret.b]!.r, B[bret.b]!.σ⟩ ⊢ bret(bsig.r.n) WF-cont) :
    {c : Code} ->
    fsigs; B'; bsig ⊢ c WF-code ->
    fsigs; (B ++ B'.map (·.inlined B bret)); (bsig.inlined B bret) ⊢
      (c.inlined B B' bret bsig.Γ) WF-code
  | .stmt e c, wf =>
    have z := wf.stmt_code.inlined (bsig := bsig.bind) bret isretn bretwf
    BlockSig.expand_retn isretn ▸
    .stmt wf.stmt_expr.weaken
          (by rw[BlockSig.expand_retn isretn] at z
              simpa[Nat.add_right_comm, BlockSig.inlined] using z)
  | .goto bnext, wf =>
    .goto wf.goto_bnext.inlined
  | .ite cond bthen belse, wf =>
    .ite (BlockSig.expand_retn isretn ▸ wf.ite_cond.weaken)
         wf.ite_bthen.inlined
         wf.ite_belse.inlined
  | .call h args bret', wf =>
    .call wf.call_flt
          wf.call_arity
          (BlockSig.expand_retn isretn ▸ inlinedArgsWF' bret wf.call_args)
          wf.call_bret.inlined
  | .retn args, .retn len sn_nil argswf =>
    BlockSig.expand_retn isretn ▸
    .goto (.mk (by simp[Nat.lt_add_right B'.length bretwf.blt])
               (by rw[BlockSig.inlined]
                   simp only [getters]
                   rw[List.getElem_append_left bretwf.blt]
                   rw[sn_nil]
                   have x := bretwf.bsig
                   rw (occs := [2]) [len] at x
                   rw[x]
                   simp[Nat.add_comm])
               (inlinedArgsWF bret argswf))
  | .spork bbody bspwn, wf =>
    have bspwnexit : (B'[bspwn.b]'wf.spork_bspwn.blt).r.isExit = true :=
      congrArg BlockSig.r wf.spork_bspwn.bsig ▸
      getElem!_pos B' bspwn.b wf.spork_bspwn.blt ▸
      by simp[BlockSig.spwn]
    .spork (Cont.inlined_b ▸
            by rw[getElem!_pos (B ++ B'.map (·.inlined B bret)) (bspwn.b + B.length)
                     (by simp[Nat.add_comm bspwn.b B.length]
                         exact wf.spork_bspwn.blt),
                  ← List.getElem_append_right' (l₁ := B)
                      (l₂ := B'.map (·.inlined B bret))
                      (List.length_map (as := B') (BlockSig.inlined B bret) ▸
                       wf.spork_bspwn.blt),
                  List.getElem_map]
               have x := congrArg BlockSig.r wf.spork_bspwn.bsig
               simp only [getters, BlockSig.spwn] at x
               rw[(B'[bspwn.b]'wf.spork_bspwn.blt).expand_exit (x ▸ rfl)]
               rw[x]
               simp[BlockSig.inlined])
           (BlockSig.inlined_spork_comm ▸
            Cont.WF.inlined
              (by rw[Cont.inlined_b,
                     getElem!_pos (B ++ B'.map (·.inlined B bret)) (bspwn.b + B.length)
                       (by simp[Nat.add_comm bspwn.b B.length]
                           exact wf.spork_bspwn.blt),
                     ← List.getElem_append_right' (l₁ := B) (l₂ := B'.map (·.inlined B bret))
                         (i := bspwn.b) (List.length_map (as := B') (·.inlined B bret) ▸
                                         wf.spork_bspwn.blt)]
                  have h : ((B'.map (BlockSig.inlined B bret))[bspwn.b]'
                             (B'.length_map (·.inlined B bret) ▸ wf.spork_bspwn.blt)).r =
                          B'[bspwn.b]!.r :=
                    List.getElem_map (BlockSig.inlined B bret) ▸
                    have y := wf.spork_bspwn.bsig
                    by rw[BlockSig.inlined_exit bspwnexit]
                       rw[← getElem!_pos B' bspwn.b wf.spork_bspwn.blt]
                  rw[h]
                  exact wf.spork_bbody))
           (have y := wf.spork_bspwn.inlined
            by rw[BlockSig.spwn,
                  Cont.inlined_b,
                  getElem!_pos (B ++ B'.map (·.inlined B bret)) (bspwn.b + B.length)
                    (by simpa[Nat.add_comm bspwn.b B.length]
                        using wf.spork_bspwn.blt),
                  ← List.getElem_append_right' B _,
                  List.getElem_map (BlockSig.inlined B bret)
                    (h := (List.length_map (BlockSig.inlined B bret)).symm ▸
                          wf.spork_bspwn.blt),
                  BlockSig.inlined_exit bspwnexit]
               rw[BlockSig.spwn,
                  BlockSig.inlined_exit rfl,
                  getElem!_pos B' bspwn.b wf.spork_bspwn.blt] at y
               simp only [getters] at y
               rw[BlockSig.inlined_retn isretn]
               exact y.weaken_Γ)
  | .spoin bunpr bprom, wf =>
    .spoin (λ x => by rw[BlockSig.inlined_retn isretn] at x
                      simp at x
                      exact wf.spoin_oblg x.1)
           (BlockSig.inlined_spoin_comm wf.spoin_oblg ▸
            wf.spoin_bunpr.inlined)
           (have ⟨σ', σ_σ'⟩ := BlockSig.inlined_σ (B := B) (bret := bret) (bsig := bsig)
            have y : bsig.σ.head wf.spoin_oblg =
                    (bsig.inlined B bret).σ.head (BlockSig.inlined_σ_nil wf.spoin_oblg) :=
              List.head!_eq_head wf.spoin_oblg ▸
              List.head!_eq_head (BlockSig.inlined_σ_nil wf.spoin_oblg) ▸
              σ_σ' ▸
              List.expand wf.spoin_oblg ▸
              rfl
            y ▸
            BlockSig.inlined_spoin_comm wf.spoin_oblg ▸
            wf.spoin_bprom.inlined)

theorem Code.WF.inlined_offset
    {fsigs B B' bret bsig}
    (isexit : bsig.r.isExit) :
    {c : Code} ->
    fsigs; B'; bsig ⊢ c WF-code ->
    fsigs; (B ++ B'.map (·.inlined B bret)); (bsig.inlined B bret) ⊢
      (c.offset_B B.length) WF-code
  | .stmt e c, wf =>
    .stmt ((BlockSig.inlined_exit isexit).symm ▸ wf.stmt_expr)
          (have x := wf.stmt_code.inlined_offset (bsig := bsig.bind) isexit
           by rw[bsig.inlined_exit isexit]
              rw[bsig.bind.inlined_exit isexit] at x
              exact x)
  | .goto bnext, wf =>
    .goto (wf.goto_bnext.inlined_map isexit).weaken_Bᵣ
  | .ite cond bthen belse, wf =>
    .ite ((BlockSig.inlined_exit isexit).symm ▸ wf.ite_cond)
         (wf.ite_bthen.inlined_map isexit).weaken_Bᵣ
         (wf.ite_belse.inlined_map isexit).weaken_Bᵣ
  | .call h args bret', wf =>
    .call wf.call_flt
          wf.call_arity
          ((BlockSig.inlined_exit isexit).symm ▸ wf.call_args)
          (wf.call_bret.inlined_map isexit).weaken_Bᵣ
  | .retn args, wf =>
    (BlockSig.inlined_exit isexit).symm ▸
    .retn wf.retn_length wf.retn_oblg wf.retn_args
  | .spork bbody bspwn, wf =>
    (BlockSig.inlined_exit isexit).symm ▸
    have bspwnlt : bspwn.b < B'.length :=
      wf.spork_bspwn.blt
    have x : (B ++ B'.map (·.inlined B bret))[(bspwn.offset_B (List.length B)).b]! =
            (B'.map (·.inlined B bret))[bspwn.b]! :=
      bspwn.offset_B_b ▸
      getElem!_pos (B ++ B'.map (·.inlined B bret)) (bspwn.b + B.length)
        (List.length_append ▸
         Nat.add_comm bspwn.b B.length ▸
         Nat.add_lt_add_iff_left.mpr
           ((List.length_map (BlockSig.inlined B bret)).symm ▸ bspwnlt)) ▸
      List.getElem_append_right' B (List.length_map (BlockSig.inlined B bret) ▸ bspwnlt) ▸
      (getElem!_pos (B'.map (·.inlined B bret)) bspwn.b
        ((List.length_map (BlockSig.inlined B bret)).symm ▸ bspwnlt)).symm
    have y : (B'.map (·.inlined B bret))[bspwn.b]! = B'[bspwn.b]! :=
      getElem!_pos (B'.map (·.inlined B bret)) bspwn.b
        ((List.length_map (BlockSig.inlined B bret)).symm ▸ bspwnlt) ▸
      getElem!_pos B' bspwn.b bspwnlt ▸
      List.getElem_map (BlockSig.inlined B bret) ▸
      --BlockSig.inlined_exit (bsig := B'[bspwn.b])
      B'[bspwn.b].inlined_exit
        (getElem!_pos B' bspwn.b bspwnlt ▸ wf.spork_exit)
    .spork (x ▸ y ▸ wf.spork_exit)
           (x ▸
            (bsig.spork (B'.map (BlockSig.inlined B bret))[bspwn.b]!.r.n).inlined_exit isexit ▸
            ((y ▸ wf.spork_bbody).inlined_map
                (bsig := bsig.spork (B'.map (BlockSig.inlined B bret))[bspwn.b]!.r.n)
                isexit).weaken_Bᵣ)
           (x ▸ (bsig.spwn (B'.map (BlockSig.inlined B bret))[bspwn.b]!.r.n).inlined_exit rfl ▸
             ((y ▸ wf.spork_bspwn).inlined_map
                (bsig := bsig.spwn (B'.map (BlockSig.inlined B bret))[bspwn.b]!.r.n)
                rfl).weaken_Bᵣ)
  | .spoin bunpr bprom, wf =>
    (BlockSig.inlined_exit isexit).symm ▸
    .spoin wf.spoin_oblg
           (bsig.spoin.inlined_exit isexit ▸
            (wf.spoin_bunpr.inlined_map (bsig := bsig.spoin) isexit).weaken_Bᵣ)
           (bsig.spoin.inlined_exit isexit ▸
            (wf.spoin_bprom.inlined_map (bsig := bsig.spoin) isexit).weaken_Bᵣ)

theorem Block.WF.inlined
    {fsigs B B' bret b bretsigΓ}
    (bretwf : B; ⟨bretsigΓ, B[bret.b]!.r, B[bret.b]!.σ⟩ ⊢ bret(b.bsig.r.n) WF-cont)
    (wf : fsigs; B' ⊢ b WF-block) :
    fsigs; (B ++ B'.map (·.inlined B bret)) ⊢ (b.inlined B B' bret) WF-block :=
  if isexit : b.bsig.r.isExit then
    by rw[Block.inlined, isexit]
       simp only [↓reduceIte]
       apply Block.WF.mk
       simp only [Block.offset_B, getters]
       have x := wf.code.inlined_offset (B := B) (bret := bret) isexit
       rw[BlockSig.inlined_exit isexit] at x
       exact x
  else
    have isretn : b.bsig.r.isRetn := b.bsig.r.not_isExit_isRetn isexit
    .mk (by simp only [Block.inlined, Block.offset_B, isexit,
                       Bool.false_eq_true, reduceIte, getters]
            exact wf.code.inlined bret isretn bretwf)

@[simp] def Func.inlined_body (B : BlockSigs) (g : Func) (bret : Cont) : List Block :=
  g.blocks.map (·.inlined B g.B bret)

theorem Func.WF.inlined_body
          {fsigs B g bret bretsigΓ}
          (bretwf : B; ⟨bretsigΓ, B[bret.b]!.r, B[bret.b]!.σ⟩ ⊢ bret(g.fsig.ret) WF-cont)
          (wf : fsigs ⊢ g WF-func) :
          IVec (λ b => (fsigs; (B ++ g.B.map (·.inlined B bret)) ⊢ b WF-block))
               (g.inlined_body B bret) :=
  have bretlt : bret.b < B.length :=
    bretwf.blt
  have x : B[bret.b]! = B[bret.b] :=
    getElem!_pos B bret.b bretlt
  have Γeq : bret.args.length + g.fsig.ret = B[bret.b].Γ :=
    by simpa only [getters] using congrArg BlockSig.Γ bretwf.bsig.symm
  by simpa[← x, -List.getElem!_eq_getElem?_getD] using
    (wf.blocks.zip wf.retns).from_map'
      (·.inlined B g.B bret)
      λ (b : Block) ⟨wf', req'⟩ =>
        if isexit : b.bsig.r.isExit then
          by simp only
             rw[Block.inlined, isexit]
             apply Block.WF.mk
             simpa[BlockSig.inlined_exit isexit]
             using wf'.code.inlined_offset isexit
        else by
          have isretn := ResultSig.not_isExit_isRetn isexit
          simpa[x]
          using @wf'.inlined fsigs B g.B bret b bretsigΓ (req' isretn ▸ bretwf)

@[simp] def Func.inlined_h
    (g : Func) (gidx : FuncIdx) :
    List Block -> List Block -> List Block -> List Block
  | bacc, [], gacc => bacc ++ gacc
  | bacc, .mk bsig c :: bs, gacc =>
    let (b', gacc') := match c.split with
      | (e, ⟨.call h args bret, _notstmt⟩) =>
        if h = gidx then
          let B := bacc ++ [Block.mk bsig c] ++ bs ++ gacc
          let c' := Code.merge e (Code.goto (.mk B.length (args ++ bret.args)))
          (.mk bsig c',
           g.inlined_body (B.map Block.bsig) bret)
        else
          (.mk bsig c, [])
      | _ => (.mk bsig c, [])
    g.inlined_h gidx (bacc ++ [b']) bs (gacc ++ gacc')


theorem Func.WF.inlined_h
        {fsigs fsig g gidx bacc gacc} :
        {bs : List Block} ->
        fsigs ⊢ g WF-func ->
        (_ : gidx < fsigs.length) ->
        fsigs[gidx] = g.fsig ->
        fsigs ⊢ Func.mk fsig (bacc ++ bs ++ gacc) WF-func ->
        fsigs ⊢ Func.mk fsig (g.inlined_h gidx bacc bs gacc) WF-func
  | [], gwf, glt, gsig, wf => List.append_nil bacc ▸ wf
  | .mk bsig c :: bs, gwf, glt, gsig, wf => by
    simp
    match cspliteq : c.split with
    | (es, ⟨t, t_neq_stmt⟩) =>
      cases t <;> simp <;> try (apply gwf.inlined_h glt gsig; simpa using wf)
      · case call h args bret =>
        if heqg : h ≠ gidx then
          simp[heqg]
          apply gwf.inlined_h glt gsig
          simpa using wf
        else
          have heqg := Decidable.of_not_not heqg
          rw[heqg]
          simp[heqg] at cspliteq
          simp
          let c' : Code :=
            .merge es (.goto (.mk (bacc.length + (bs.length + gacc.length + 1))
                                 (args ++ bret.args)))
          let gacc' := g.inlined_body ((bacc ++ [Block.mk bsig c'] ++ bs ++ gacc).map
                                          Block.bsig) bret
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
                simp at gh; rw[gh]; simp[BlockSig.inlined, -List.getElem!_eq_getElem?_getD]
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
                  have x := @gwf.inlined_body fsigs
                    ((bacc ++ [Block.mk bsig c'] ++ bs ++ gacc).map (·.bsig))
                    g bret
                    (bsig.binds es.length).Γ
                    (by have y : ((bacc++([Block.mk bsig c']++(bs++gacc))).map Block.bsig);
                                   (bsig.binds es.length) ⊢ bret(g.fsig.ret) WF-cont :=
                          List.map_append.symm ▸
                          List.map_append.symm ▸
                          List.map_append.symm ▸
                          gsig ▸ splitwf.2.call_bret
                        have bretlt' : bret.b < ((bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc))
                                                  ).map Block.bsig).length :=
                          by simpa using splitwf.2.call_bret.blt
                        have bretlt'' : bret.b < (bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc))
                                                  ).length :=
                          by simpa using splitwf.2.call_bret.blt
                        have z : (bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc)))[bret.b].bsig =
                                 BlockSig.mk (bret.args.length + g.fsig.ret)
                                             (bsig.binds es.length).r
                                             (bsig.binds es.length).σ :=
                          List.getElem_map Block.bsig (h := bretlt') ▸
                          y.bsig
                        have zr : (bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc)))[bret.b].bsig.r
                                  = (bsig.binds es.length).r :=
                          congrArg (a₂ := BlockSig.mk (bret.args.length + g.fsig.ret)
                                                      (bsig.binds es.length).r
                                                      (bsig.binds es.length).σ) BlockSig.r z
                        have zσ : (bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc)))[bret.b].bsig.σ
                                  = (bsig.binds es.length).σ :=
                          congrArg (a₂ := BlockSig.mk (bret.args.length + g.fsig.ret)
                                                      (bsig.binds es.length).r
                                                      (bsig.binds es.length).σ) BlockSig.σ z
                        rw[List.append_assoc,
                           List.append_assoc,
                           getElem!_pos ((bacc ++ ([Block.mk bsig c'] ++ (bs ++ gacc))).map
                                           Block.bsig) bret.b (by simpa using bretlt'),
                           y.bsig]
                        exact y)
                  have fh : g.blocks.map (BlockSig.inlined (bacc.map Block.bsig ++ bsig ::
                              (bs.map Block.bsig ++ gacc.map Block.bsig)) bret ∘ Block.bsig) =
                            g.blocks.map (Block.bsig ∘ Block.inlined (bacc.map Block.bsig ++
                              bsig :: (bs.map Block.bsig ++ gacc.map Block.bsig))
                                (g.blocks.map Block.bsig) bret) :=
                    List.map_eq_map_iff.mpr
                      λ a ain => by simp[BlockSig.inlined]; cases a.bsig.r <;> simp
                  simpa[fh, Block.inlined_ext] using x
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
                  simp only [gacc', Func.inlined_body]
                  apply IVec.from_map_list
                  intro a isretn
                  simp[-ResultSig.isExit, -ResultSig.isRetn] at isretn ⊢
                  cases h : a.bsig.r
                  · case retn n =>
                    simp[h] at isretn ⊢
                    rw[a.bsig.inlined_retn (h ▸ rfl)] at isretn ⊢
                    simp only [getters] at isretn ⊢
                    have isretn' : (bacc.map Block.bsig ++ ([Block.mk bsig c].map Block.bsig ++
                                     (bs.map Block.bsig ++ gacc.map Block.bsig))
                                     )[bret.b]!.r.isRetn := isretn
                    have bretlt := splitwf.2.call_bret.blt
                    have bretlt' : bret.b < (bacc ++ Block.mk bsig c :: bs ++ gacc).length :=
                      by simpa using bretlt
                    have x : (bacc ++ ⟨bsig, c⟩ :: bs ++ gacc)[bret.b].bsig.r =
                             ResultSig.retn fsig.ret :=
                      wf.retns⁅bret.b⁆ (by
                        show (bacc ++ Block.mk bsig c :: bs ++ gacc)[bret.b].bsig.r.isRetn
                        rw[← List.map_append, ← List.map_append, ← List.map_append] at isretn'
                        rw[getElem!_pos (List.map Block.bsig (bacc ++ ([Block.mk bsig c] ++
                             (bs ++ gacc)))) bret.b (by simpa using bretlt')] at isretn'
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
          using @gwf.inlined_h fsigs fsig g gidx (gacc ++ gacc') bs
                                  glt gsig (bacc := bacc ++ [.mk bsig c']) wf''

/--
Inline each call to g in the body of f
-/
def Func.inline (f g : Func) (gidx : FuncIdx) : Func :=
  .mk f.fsig (g.inlined_h gidx [] f.blocks [])

/--
Inlining a function in the body of another preserves well-formedness
-/
theorem Func.WF.inline
    {fsigs f g gidx}
    (glt : gidx < fsigs.length)
    (gsig : fsigs[gidx] = g.fsig)
    (fwf : fsigs ⊢ f WF-func)
    (gwf : fsigs ⊢ g WF-func) :
    fsigs ⊢ f.inline g gidx WF-func :=
  gwf.inlined_h glt gsig ((List.append_nil f.blocks).symm ▸ fwf)

