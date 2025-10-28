import SporkProofs.Syntax
import SporkProofs.Semantics
import SporkProofs.WFSyntax
import SporkProofs.WFSemantics

namespace Step
  theorem preserve_retjoin_stack_cons
    {P K f ρ₁ ρ₂ X₁ X₂ c₁ c₂}
    (req : P[f]!.B[c₁]!.r = P[f]!.B[c₂]!.r) :
      CallStack.retjoin P (K ⬝ ⟨f, ρ₁, X₁, c₁⟩) =
      CallStack.retjoin P (K ⬝ ⟨f, ρ₂, X₂, c₂⟩)
    := by simp at req; cases K <;> simp[req]

  @[simp] theorem preserve_retjoin_stack_cons_cons {P K k k'} :
      (K ⬝ k ⬝ k').retjoin P = (K ⬝ k).retjoin P :=
    by cases K <;> rfl

  @[simp] theorem preserve_retjoin_stack_cons_nonnil {P K k} :
      K ≠ ∅ → (K ⬝ k).retjoin P = K.retjoin P := by
    cases K <;> intro nn
    · case nil => contradiction
    · case cons => rfl

  theorem stack_append_left_nonnil : (s t : CallStack) -> (h : s ≠ ∅) -> s ++ t ≠ ∅
    | s, .nil, h => h
    | s, K ⬝ k, h => by simp

  @[simp] theorem preserve_retjoin_stack_append {P K k} : {K' : CallStack} ->
      CallStack.retjoin P (K ⬝ k ++ K') = CallStack.retjoin P (K ⬝ k)
    | .nil => rfl
    | K' ⬝ k' => preserve_retjoin_stack_cons_nonnil
                   (stack_append_left_nonnil (K ⬝ k) K' (by simp)) ▸
                 preserve_retjoin_stack_append (K' := K')

  theorem preserve_retjoin {P : Program} : {R R' : ThreadTree} ->
                         P ⊢ R ↦ R' -> P ⊢ R WF-tree ->
                         R.retjoin P = R'.retjoin P
  | R, R', s => by
    cases s <;> intro Rwf
    · case congr_parent Rp Rp' Rc s =>
        simp only [ThreadTree.retjoin]; match Rwf with
          | .node Rpwf Rcwf Rpp Rcp => exact preserve_retjoin s Rpwf
    · case congr_child Rp Rc Rc' s =>
        rfl
    · case stmt f K ρ X b e v c a =>
      apply preserve_retjoin_stack_cons
      rfl
    · case goto f K ρ X b bnext =>
      apply preserve_retjoin_stack_cons
      let flt : f < P.size := Rwf.get.K.current.flt
      let x := congrArg (·.2) Rwf.get.c.goto_bnext.bsig
      simp at x
      rw[getElem!_pos P f flt,
         getElem!_pos P[f].B bnext.b Rwf.get.c.goto_bnext.blt,
         getElem!_pos P[f].B b (let y := Rwf.get.K.current.blt
                                by simp at y; rw[List.length_map]; exact y)]
      simp; exact x.symm
    · case ite_true f K ρ X b cond bthen belse n a neq0 =>
      apply preserve_retjoin_stack_cons
      let flt := Rwf.get.K.current.flt
      rw[getElem!_pos P f flt]
      rw[getElem!_pos P[f].B bthen.b Rwf.get.c.ite_bthen.blt]
      rw[getElem!_pos P[f].B b (let y := Rwf.get.K.current.blt
                                by simp at y; rw[List.length_map]; exact y)]
      exact congrArg (·.2) Rwf.get.c.ite_bthen.bsig.symm
    · case ite_false f K ρ X b cond bthen belse a =>
      apply preserve_retjoin_stack_cons
      let flt := Rwf.get.K.current.flt
      rw[getElem!_pos P f flt]
      rw[getElem!_pos P[f].B belse.b Rwf.get.c.ite_belse.blt]
      rw[getElem!_pos P[f].B b (let y := Rwf.get.K.current.blt
                                by simp at y; rw[List.length_map]; exact y)]
      exact congrArg (·.2) Rwf.get.c.ite_belse.bsig.symm
    · case call f g K ρ b X x bret =>
      apply preserve_retjoin_stack_cons
      let flt := Rwf.get.K.current.flt
      rw[getElem!_pos P f flt]
      rw[getElem!_pos P[f].B bret.b Rwf.get.c.call_bret.blt]
      rw[getElem!_pos P[f].B b (let y := Rwf.get.K.current.blt
                                by simp at y; rw[List.length_map]; exact y)]
      exact congrArg (·.2) Rwf.get.c.call_bret.bsig.symm
    · case retn f g K ρ X Y y b bret =>
      apply preserve_retjoin_stack_cons (K := K)
      simp
    · case spork f K ρ X b bbody bspwn =>
      apply preserve_retjoin_stack_cons
      let flt := Rwf.get.K.current.flt
      rw[getElem!_pos P f flt]
      rw[getElem!_pos P[f].B bbody.b Rwf.get.c.spork_bbody.blt]
      rw[getElem!_pos P[f].B b (let y := Rwf.get.K.current.blt
                                by simp at y; rw[List.length_map]; exact y)]
      exact congrArg (·.2) Rwf.get.c.spork_bbody.bsig.symm
    · case promote f unpr bspwn prom X K b K' C u p =>
      let flt := Rwf.get.K.current.flt
      simp
      apply preserve_retjoin_stack_cons
      simp
    · case spoin_unpr f K ρ bspwn X b bunpr bprom =>
      apply preserve_retjoin_stack_cons
      let flt := Rwf.get.K.current.flt
      rw[getElem!_pos P f flt]
      rw[getElem!_pos P[f].B bunpr.b Rwf.get.c.spoin_bunpr.blt]
      rw[getElem!_pos P[f].B b (let y := Rwf.get.K.current.blt
                                by simp at y; rw[List.length_map]; exact y)]
      exact congrArg (·.2) Rwf.get.c.spoin_bunpr.bsig.symm
    · case spoin_prom f g K ρ X b b' bunpr bprom Y y bspwn u =>
      apply preserve_retjoin_stack_cons
      let flt := Rwf.parent.get.K.current.flt
      rw[getElem!_pos P f flt]
      rw[getElem!_pos P[f].B bprom.b Rwf.parent.get.c.spoin_bprom.blt]
      rw[getElem!_pos P[f].B b (let y := Rwf.parent.get.K.current.blt
                                by simp at y; rw[List.length_map]; exact y)]
      exact congrArg (·.2) Rwf.parent.get.c.spoin_bprom.bsig.symm

    -- · case promote f unpr g prom X K c K' u p =>
    --     simp; rw[preserve_retjoin_stack_cons]

  theorem preserve_prom {P : Program} : {R R' : ThreadTree} ->
                         P ⊢ R ↦ R' -> P ⊢ R WF-tree -> R.prom = R'.prom
  | R, R', s => by
    cases s <;> intro Rwf <;> try simp <;> try rfl
    · case congr_parent Rp Rp' Rc Rp_Rp' =>
      rw[preserve_prom Rp_Rp' Rwf.parent]
    · case promote f unpr g prom X K c K' u p =>
      simp[p]

  open CallStack in
  theorem preserve_promsig {P : Program} : {R R' : ThreadTree} ->
                            P ⊢ R ↦ R' -> P ⊢ R WF-tree -> R.promsig P = R'.promsig P
  | R, R', s => by
    cases s <;> intro Rwf <;> try simp <;> try rfl
    · case congr_parent Rp Rp' Rc Rp_Rp' =>
      rw[preserve_promsig Rp_Rp' Rwf.parent]
    · case promote f unpr bspwn prom X K b K' c u p =>
      simp[CallStack.prom_promsig_nil.mp p]

  theorem goto_rets!h
      {P} {K k} {bnext : Cont} {r r' : Nat}
      (kwf : P; K; r' ⊢ k WF-frame)
      (bnext_wf : P[k.f]!.B; (k.bsig! P) ⊢ bnext(r) WF-cont) :
      P; K; r ⊢ ⟨k.f, k.ρ, k.X[bnext.args]!, bnext.b⟩ WF-frame :=
    let req : P[k.f]!.B[bnext.b]!.r = P[k.f]!.B[k.b]!.r :=
      congrArg BlockSig.r bnext_wf.bsig! ▸
      getElem!_pos P k.f kwf.flt ▸
      rfl
    StackFrame.WF.goto_rets! kwf.flt kwf.ρwf
      (getElem!_pos P k.f kwf.flt ▸ req ▸ bnext_wf)

  theorem goto!h
      {P} {K k} {bnext : Cont}
      (kwf : P; K ⊢ k WF-frame)
      (bnext_wf : P[k.f]!.B; (k.bsig! P) ⊢ bnext WF-cont) :
      P; K ⊢ ⟨k.f, k.ρ, k.X[bnext.args]!, bnext.b⟩ WF-frame :=
    goto_rets!h kwf bnext_wf.cast0
  
  open ThreadTree.WF (thread node) in
  theorem preservation {P : Program} (Pwf : P WF-program) :
                       {R R' : ThreadTree} ->
                       P ⊢ R WF-tree -> P ⊢ R ↦ R' -> P ⊢ R' WF-tree := by
    intro R R' wf R_R'
    cases R_R' <;>
    cases wf <;>
    try (apply thread) <;>
    try (apply Thread.WF.fromStack! Pwf)

    · case congr_parent Rp Rp' Rc Rp_Rp' Rpwf Rcwf Rcp Rpp =>
        exact node (preservation Pwf Rpwf Rp_Rp') Rcwf (preserve_promsig Rp_Rp' Rpwf ▸ Rpp) Rcp

    · case congr_child Rp Rc Rc' Rc_Rc' Rpwf Rcwf Rcp Rpp =>
        exact node Rpwf (preservation Pwf Rcwf Rc_Rc')
                        (preserve_retjoin Rc_Rc' Rcwf ▸ Rpp)
                        (preserve_prom Rc_Rc' Rcwf ▸ Rcp)

    · case stmt f K ρ X b e v c a wf =>
        exact match wf with
           | .mk (Kwf ⬝wf (.mk flt blt bsig ρwf)) (.stmt ewf cwf) =>
             .mk (Kwf ⬝wf (.mk flt blt
                    ⟨by simpa using Nat.le_trans bsig.1 (Nat.le_add_right X.length 1), bsig.2⟩ ρwf))
                 (by simp[BlockSig.bind] at cwf; simp; exact cwf)

    · case goto f K ρ X b bnext wf =>
        apply (· ⬝wf ·)
        · apply goto!h wf.K.current wf.c!.goto_bnext
        · let h : P[f]!.B[bnext.b]! = _ := wf.c!.goto_bnext.bsig!
          simpa only [StackFrame.ret!, getters, h] using wf.K.tail

    · case ite_true f K ρ X b cond bthen belse n cond_n neq0 wf =>
        apply (· ⬝wf ·)
        · apply goto!h wf.K.current wf.c!.ite_bthen
        · let h : P[f]!.B[bthen.b]! = _ := wf.c!.ite_bthen.bsig!
          simpa only [StackFrame.ret!, getters, h] using wf.K.tail

    · case ite_false f K ρ X cond b bthen belse cond_0 wf =>
        apply (· ⬝wf ·)
        · apply goto!h wf.K.current wf.c!.ite_belse
        · let h : P[f]!.B[belse.b]! = _ := wf.c!.ite_belse.bsig!
          simpa only [StackFrame.ret!, getters, h] using wf.K.tail

    · case call f g K ρ b X x bret wf =>
        apply (· ⬝wf · ⬝wf ·)
        · apply StackFrame.WF.entry Pwf (by simpa using wf.c.call_flt)
          · rw[getElem!_pos X x wf.c.call_args,
               X.getElem_length wf.c.call_args]
            simpa [← List.getElem_map Func.fsig] using wf.c.call_arity
        · let p := wf.K.tail
          let s := congrArg BlockSig.r wf.c!.call_bret.bsig!
          simp only [StackFrame.ret!, getters, CallStack.bsig!, StackFrame.bsig!] at p s ⊢
          rw[s]
          exact p
        · apply goto_rets!h wf.K.current
          · let glt : g < P.size := by simpa using wf.c.call_flt
            let zlt : 0 < P[g].B.length := Pwf⁅g⁆.head.zero_lt_map
            let gsig : P[g].B[0].r = P[g].fsig.ret :=
              congrArg BlockSig.r Pwf⁅g⁆.head.get0eq_map
            simpa only [getters,
                       CallStack.bsig!,
                       getElem!_pos P g glt,
                       getElem!_pos P[g].B 0 zlt,
                       Option.getD_some,
                       StackFrame.ret!,
                       Program.fsigs,
                       List.getElem_map Func.fsig,
                       gsig]
            using wf.c!.call_bret

    · case retn f g K ρ X Y y b bret wf =>
        let ypf : (Y[y]'wf.c.retn_args).length = P[g]!.B[b]!.r :=
          Y.getElem_length wf.c.retn_args ▸
          wf.c.retn_length ▸
          getElem!_pos P g wf.K.current.flt ▸
          getElem!_pos (P[g]'wf.K.current.flt).B b wf.K.current.blt ▸
          rfl
        apply (· ⬝wf ·)
        · apply StackFrame.WF.mk
          · exact ⟨getElem!_pos Y y wf.c.retn_args ▸
                   List.length_append ▸
                   ypf ▸
                   wf.K.tail.head.bsig.1,
                   wf.K.tail.head.bsig.2⟩
          · exact wf.K.tail.head.ρwf
        · exact wf.K.tail.tail

    · case spork f K ρ X b bbody bspwn wf =>
        apply (· ⬝wf ·)
        · apply StackFrame.WF.mk
          · apply And.intro
            · let apf := congrArg BlockSig.Γ wf.c.spork_bbody.bsig
              simp only [getters] at apf
              rw[getElem!_pos X bbody.args wf.c.spork_bbody.args,
                 X.getElem_length wf.c.spork_bbody.args,
                 ← apf, Option.getD_none, Nat.add_zero]
              exact Nat.le_refl ((P[f]'wf.K.current.flt).B[bbody.b]'wf.c.spork_bbody.blt).Γ
            · let bpf := congrArg BlockSig.σ wf.c.spork_bbody.bsig
              simp only [getters, CallStack.bsig, StackFrame.bsig] at bpf
              rw[SpawnDeque.pushsig, bpf]
              simp only [getters]
          · apply wf.K.current.ρwf.push
            · apply SpawnBlock.WF.mk <;> simp only [getters]
              · rw[getElem!_pos X bspwn.args wf.c.spork_bspwn.args,
                   X.getElem_length wf.c.spork_bspwn.args]
                exact congrArg BlockSig.Γ wf.c.spork_bspwn.2
              · exact congrArg BlockSig.σ wf.c.spork_bspwn.2
              · exact wf.c.spork_bspwn.1
        · let h : P[f]!.B[bbody.b]! = _ := wf.c!.spork_bbody.bsig!
          simpa only [StackFrame.ret!, getters, h] using wf.K.tail

    · case promote f unpr bspwn prom X K b K' c u p wf =>
        exact node
          (thread (wf.promote (by simp[u])))
          (thread (Thread.WF.spawn! Pwf wf.K.peep.flt wf.K.peep.ρwf.unpr.head'))
          (by simp[CallStack.prom_promsig_nil.mp p])
          rfl
    
    · case spoin_unpr f K bspwn ρ X b bunpr bprom wf =>
        apply (· ⬝wf ·)
        · apply StackFrame.WF.mk
          · apply And.intro
            · let apf := congrArg BlockSig.Γ wf.c.spoin_bunpr.bsig
              simp only [getters] at apf
              rw[getElem!_pos X bunpr.args wf.c.spoin_bunpr.args,
                 X.getElem_length wf.c.spoin_bunpr.args,
                 ← apf, Option.getD_none, Nat.add_zero]
              exact Nat.le_refl ((P[f]'wf.K.current.flt).B[bunpr.b]'wf.c.spoin_bunpr.blt).Γ
            · let bpf := congrArg BlockSig.σ wf.c.spoin_bunpr.bsig
              simp only [getters, CallStack.bsig, StackFrame.bsig,
                         SpawnDeque.pushsig, List.tail_cons] at bpf
              rw[bpf]
          · exact wf.K.current.ρwf.unpush
        · let h : P[f]!.B[bunpr.b]! = _ := wf.c!.spoin_bunpr.bsig!
          simpa only [StackFrame.ret!, getters, h] using wf.K.tail

    · case spoin_prom f g K ρ X b b' bunpr bprom Y y bspwn K_unpr_nil Rpwf Rcwf ret_prom_nil heq =>
        let flt : f < P.size := Rpwf.get.K.current.flt
        let glt : g < P.size := Rcwf.get.K.current.flt
        apply (· ⬝wf ·)
        · apply StackFrame.WF.mk
          · apply And.intro
            · let apf := congrArg BlockSig.Γ Rpwf.get.c.spoin_bprom.bsig
              simp only [getters, CallStack.bsig, StackFrame.bsig] at apf
              simp only [getters, ThreadTree.promsig,
                         Thread.promsig, CallStack.promsig, SpawnDeque.promsig,
                         ThreadTree.retjoin, Thread.retjoin, CallStack.retjoin] at heq
              rw[List.map_cons, List.cons_append, List.head?_cons, Option.some_inj,
                 getElem!_pos P f flt, getElem!_pos P g glt,
                 getElem!_pos P[g].B b'] at heq
              rw[getElem!_pos X bprom.args Rpwf.get.c.spoin_bprom.args,
                 getElem!_pos Y y Rcwf.get.c.retn_args,
                 List.length_append,
                 X.getElem_length Rpwf.get.c.spoin_bprom.args,
                 Y.getElem_length Rcwf.get.c.retn_args,
                 Option.getD_none, Nat.add_zero, apf]
              simp only [SpawnDeque.sig, getters, SpawnDeque.out, List.reverseAux, List.map, List.head]
              let bpf := Rcwf.get.c.retn_length
              simp only [getters, CallStack.head, CallStack.bsig, StackFrame.bsig] at bpf
              rw[← bpf, ← heq]
              exact Nat.le_refl _
            · let bpf := congrArg BlockSig.σ Rpwf.get.c.spoin_bprom.bsig
              simp only [getters, CallStack.bsig, StackFrame.bsig,
                         SpawnDeque.pushsig, List.tail_cons] at bpf
              rw[bpf]
              simp[Rpwf.get.K.current.bsig.2]
          · let a : P[f].B; K.allPromoted ⊢ ⟨[], bspwn :: ρ⟩ WF-deque :=
              Rpwf.get.K.current.ρwf
            exact ⟨a.1, by simp[K_unpr_nil]; exact rfl⟩
        · let h : P[f]!.B[bprom.b]! = _ := Rpwf.get.c!.spoin_bprom.bsig!
          simpa only [StackFrame.ret!, getters, h] using Rpwf.get.K.tail
end Step
