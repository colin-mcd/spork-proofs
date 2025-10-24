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

  
  open ThreadTree.WF (thread node) in
  theorem preservation {P : Program} (Pwf : P WF-program) :
                       {R R' : ThreadTree} ->
                       P ⊢ R WF-tree -> P ⊢ R ↦ R' -> P ⊢ R' WF-tree := by
    intro R R' wf R_R'; cases R_R' <;> cases wf

    · case congr_parent Rp Rp' Rc Rp_Rp' Rpwf Rcwf Rcp Rpp =>
        exact node (preservation Pwf Rpwf Rp_Rp') Rcwf (preserve_promsig Rp_Rp' Rpwf ▸ Rpp) Rcp

    · case congr_child Rp Rc Rc' Rc_Rc' Rpwf Rcwf Rcp Rpp =>
        exact node Rpwf (preservation Pwf Rcwf Rc_Rc')
                        (preserve_retjoin Rc_Rc' Rcwf ▸ Rpp)
                        (preserve_prom Rc_Rc' Rcwf ▸ Rcp)

    · case stmt f K ρ X b e v c a wf =>
        apply thread
        exact match wf with
           | .mk (Kwf ⬝wf (.mk flt blt bsig ρwf)) (.stmt ewf cwf) =>
             let flt : f < P.size := wf.K.current.flt
             .mk (Kwf ⬝wf (.mk (X := X.concat v) flt blt
                    ⟨by simp; simp at bsig;
                        exact Nat.le_trans bsig.1 (Nat.le_add_right X.length 1), bsig.2⟩
                    ρwf))
             --(.mk bwf.blt bwf.bsig (bwf.args.map (λ x xwf => by simp; exact xwf.weaken)))
                 (by simp[BlockSig.bind] at cwf; simp; exact cwf)

    · case goto f K ρ X b bnext wf =>
        apply thread
        exact match wf with
          | .mk (Kwf ⬝wf (.mk flt blt bsig ρwf)) (.goto bnext_wf) =>
              by simp only [getters] at bnext_wf; exact
              .mk ((by simp only[StackFrame.ret, getters, CallStack.bsig] at Kwf bsig bnext_wf
                       simp only[StackFrame.ret, getters]
                       rw[bnext_wf.bsig]
                       exact Kwf) ⬝wf
                   (.mk flt bnext_wf.blt ⟨bnext_wf.bsig ▸
                                          by simp;
                                             let x := argsOfGetElem bnext_wf.args
                                             simp at x
                                             rw[x, X.getElem_length bnext_wf.args]
                                             exact Nat.le_refl bnext.args.length,
                                          bsig.2 ▸ congrArg (·.σ) bnext_wf.bsig ▸
                                          by simp only [getters, CallStack.bsig, bsig.2]⟩ ρwf))
                  (by simp only [CallStack.bsig, getters]
                      let p := wf.c.goto_bnext.bsig
                      simp only [Thread.K, CallStack.head, StackFrame.f] at p
                      let bnextlt : bnext.b < P[f].B.length :=
                        by simp; rw[← List.length_map Block.bsig]; exact bnext_wf.blt
                      let bnextlt_wf : bnext.b < P[f].size :=
                        by simpa using wf.c.goto_bnext.blt
                      let cwf := Pwf⁅f⁆⁅bnext.b⁆.code
                      simp only [getters] at cwf
                      simp only [← getElem!_pos P[f].B bnext.b bnextlt] at p cwf ⊢
                      simp only [← getElem!_pos P f flt] at p cwf ⊢
                      simp at cwf
                      rw[p]
                      simp only [getElem!_pos P f flt] at p cwf ⊢
                      simp only [getElem!_pos P[f].B bnext.b bnextlt] at p cwf ⊢
                      simp only [getters, CallStack.bsig, ← bsig.2]
                      simp only [getElem!_pos P[f] bnext.b bnextlt_wf]
                      let cwf₂ : P.fsigs; P[f].B; P[f].B[bnext.b] ⊢ P[f][bnext.b].code WF-code :=
                        by simp; exact cwf
                      let xpf : X[bnext.args]!.length = P[f].B[bnext.b].Γ :=
                        argsOfGetElem bnext_wf.args ▸
                        ValMap.getElem_length bnext_wf.args ▸
                        (congrArg BlockSig.Γ bnext_wf.bsig).symm
                      rw[xpf]
                      rw[← @BlockSig.get_fix P[f].B[bnext.b]] at cwf₂
                      let rpf := congrArg BlockSig.r wf.c.goto_bnext.bsig
                      let σpf := congrArg BlockSig.σ wf.c.goto_bnext.bsig
                      let σpf' : P[f].B[b].σ = SpawnDeque.sig P[f].B ρ :=
                        wf.K.current.bsig.2
                      simp only [getters, CallStack.bsig] at rpf σpf
                      rw[← rpf, σpf']
                      rw[σpf] at cwf₂
                      exact cwf₂)

    · case ite_true f K ρ X cond bthen belse n cond_n neq0 wf =>
        apply thread
        exact match wf with
          | .mk (Kwf ⬝wf (.mk flt blt bsig ρwf)) (.ite cond_wf bthen_wf belse_wf) =>
            .mk (Kwf ⬝wf (.mk sorry sorry sorry sorry))
                (.goto Pwf p ρwf bthen_wf)

    · case ite_false f K ρ X cond bthen belse cond_0 wf =>
        apply thread
        exact match wf with
          | Kwf ⬝wf (.mk p ρwf _ (.code (.ite cond_wf bthen_wf belse_wf))) =>
            Kwf ⬝wf (.goto Pwf p ρwf belse_wf)

    · case call f g K ρ X x bret wf =>
        apply thread
        exact match wf with
          | Kwf ⬝wf kwf@(.mk fwf ρwf _ (.code (.call flt sigwf x_wf
                bret_wf@(.mk bret_lt bret_sig_wf argswf)))) =>
              let bret_wf' : Cont.WFRets P[f].bsigs ⟨X.length, ρ.sig⟩
                               P.fsigs[g].ret bret :=
                P.funs.getElem_map (·.fsig) ▸ bret_wf
              let gframe_wf :=
                StackFrame.WF.goto_entry
                  (f := g) Pwf (P.size_eq_fsigs_length ▸ flt)
                  x_wf (P.funs.getElem_map (·.fsig) ▸ sigwf)
              let glt := gframe_wf.flt
              let bret_wf'' : Cont.WFRets P[f].bsigs ⟨X.length, ρ.sig⟩
                                P[g].fsig.ret bret :=
                P.funs.getElem_map (·.fsig) ▸ bret_wf'
              Kwf ⬝wf ⟨fwf, ρwf, rfl, .cont bret_wf''⟩ ⬝wf gframe_wf

    · case retn f g K ρ X Y y bret wf =>
        apply thread
        exact match wf with
          | Kwf ⬝wf (.mk flt ρwf _ (.cont bret_wf))
                ⬝wf (.mk glt ⟨.nil, _⟩ _ (.code (.retn _ ylen y_wf))) =>
            Kwf ⬝wf (.goto_rets Pwf flt ρwf (ylen ▸ bret_wf) y_wf)

    · case spork f K ρ X g g_args bbody wf =>
       apply thread
       exact match wf with
         | Kwf ⬝wf ⟨flt, ⟨unpr_wf, prom_wf⟩, _, .code
               (.spork glt gsig g_args_wf bbody_wf)⟩ =>
           let glt' : g < P.funs.length := List.length_map (α := Func) (·.fsig) ▸ glt
           let h : FuncSig.mk X[g_args]!.length P[g]!.fsig.ret = P.fsigs[g] :=
             argsOfGetElem g_args_wf ▸
             getElem!_pos P g glt' ▸
             g_args_wf.map_length (λ x xwf => X[x]) ▸
             gsig ▸
             List.getElem_map (·.fsig) (l := P.funs) (h := glt) ▸
             rfl
           Kwf ⬝wf (.goto Pwf flt ⟨unpr_wf.concat ⟨glt, h⟩, prom_wf⟩
                     (by rw[ρ.pushsig, getElem!_pos P g glt']
                         simp at bbody_wf; simp
                         exact bbody_wf))

    · case promote f unpr g prom X K c K' u p wf =>
        let kProm := CallStack.allPromoted_iff_nil.mpr u
        let rec hp : {K' : CallStack} -> {gets : Option Nat} -> K'.prom = [] ->
                     P; gets ⊢ (K ⬝ ⟨f, ⟨g :: unpr, prom⟩, X, c⟩ ++ K') WF-stack ->
                     P; gets ⊢ (K ⬝ ⟨f, ⟨unpr, g.ret :: prom⟩, X, c⟩ ++ K') WF-stack ∧
                     P; none ⊢ {⟨g.f, ∅, g.args, .codeEntry P g.f⟩} WF-stack ∧
                     g.ret = P[g.f]!.fsig.ret
          | .nil, gets, _, wf => by
            rw[CallStack.append_nil] at *
            apply And.intro <;> try (apply And.intro)
            · exact wf.tail ⬝wf
                (let kwf := wf.head
                 ⟨wf.head.flt,
                  (let x := wf.head.ρwf
                   by rw[kProm] at *; exact x.promote),
                  wf.head.cb,
                  wf.head.cwf⟩)
            · apply (.nil ⬝wf ·)
              let glt : g.f < P.funs.length := by
                rw[← List.length_map (·.fsig)]
                exact wf.head.ρwf.unpr.head'.flt
              let Psize : P.funs.length = P.fsigs.length :=
                (List.length_map (as := P.funs) (·.fsig)).symm
              let glt' := Psize ▸ glt
              exact StackFrame.WF.mk glt SpawnDeque.WF.empty rfl
                (StackFrame.WF.entry (canProm := true) Pwf glt
                  (List.getElem_map Func.fsig (l := P.funs) ▸
                   (congrArg (·.arity) wf.head.ρwf.unpr.head'.sig).symm)
                ).cwf
            · let gflt := wf.head.ρwf.unpr.head'.flt
              let gflt' : g.f < P.funs.length :=
                List.length_map (as := P.funs) (·.fsig) ▸ gflt
              let x : g.ret = P.fsigs[g.f].ret :=
                congrArg (·.ret) wf.head.ρwf.unpr.head'.sig
              rw[getElem!_pos P g.f gflt',
                 x,
                 List.getElem_map (·.fsig) (l := P.funs)]
          | K' ⬝ k', gets, p, wf =>
            let ⟨kp', Kp'⟩ := List.append_eq_nil_iff.mp p
            let k'wf := wf.head
            let ⟨K'wf', gwf, glt⟩ := hp Kp' wf.tail
            let l := K'wf'
            let k'wf' := k'wf.castCanProm
              (K ⬝ ⟨f, ⟨unpr, g.ret :: prom⟩, X, c⟩ ++ K').allPromoted
              (λ (x : (K ⬝ ⟨f, ⟨g :: unpr, prom⟩, X, c⟩ ++ K').allPromoted) =>
                 let x' : (K ⬝ ⟨f, ⟨g :: unpr, prom⟩, X, c⟩ ++ K').unpr = [] :=
                   by simp_all[x]
                 let x'' : g :: unpr = [] :=
                   (List.append_eq_nil_iff.mp
                     (List.append_eq_nil_iff.mp
                       (CallStack.append_unpr ▸ x')).left).right
                 nomatch x'')
            ⟨K'wf' ⬝wf k'wf', gwf, glt⟩
        let ⟨Kwf, gwf, glt⟩ := hp p wf
        exact node (thread Kwf) (thread gwf) (by simp_all) (by simp)

    · case spoin_unpr f K ρ sc X bunpr bprom wf =>
        apply thread
        exact match wf with
          | Kwf ⬝wf ⟨flt, ⟨unpr_wf, prom_wf⟩, _,
              .code (.spoin nn bunpr_wf bprom_wf)⟩ =>
            let h : (ρ.push sc).sig.tail = ρ.sig := by simp
            Kwf ⬝wf (.goto Pwf flt ⟨unpr_wf.unconcat.1, prom_wf⟩ (h ▸ bunpr_wf))

    · case spoin_prom f K ρ' X bunpr bprom Y y g K_unpr_nil wf retwf Rp R'p =>
        let g_ret_eq : g.ret = P[g.f]!.fsig.ret :=
          congrArg (λ | some x => x | _ => g.ret) R'p
        apply thread
        let wf'' : (ThreadTree.thread (K ⬝ ⟨f, ⟨[], g.ret :: ρ'⟩, X,
                      .code (.spoin bunpr bprom)⟩)).WF P :=
          g_ret_eq ▸ wf
        let flt := wf''.get.head.flt
        let sd_wf : (SpawnDeque.mk [] ρ').WF P.fsigs K.allPromoted :=
          ⟨IVec.nil, by simp[K_unpr_nil]; rfl⟩
        let y_wf : IVec (·.WF Y.length) y := retwf.get.head.cwf.c.retn_args
        let y_len_eq_g_ret : y.length = g.ret := g_ret_eq ▸ retwf.get.head.cwf'.c.retn_length.symm
        let cont_wf : bprom.WFRets P[f].bsigs ⟨X.length, ρ'⟩ y.length :=
          y_len_eq_g_ret ▸ wf''.get.head.cwf.c.spoin_bprom
        exact wf''.get.tail ⬝wf
          (.goto_rets Pwf flt sd_wf cont_wf y_wf)
end Step
