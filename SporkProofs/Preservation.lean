import SporkProofs.Syntax
import SporkProofs.Semantics

namespace Step
  theorem preserve_retjoin_stack_cons
    {Pr K f ρ ρ' X X' c c'} :
      CallStack.retjoin Pr (K ⬝ ⟨f, ρ, X, c⟩) =
        CallStack.retjoin Pr (K ⬝ ⟨f, ρ', X', c'⟩)
    := by cases K <;> rfl

  theorem preserve_retjoin_stack_cons_cons {Pr K k k'} :
      (K ⬝ k ⬝ k').retjoin Pr = (K ⬝ k).retjoin Pr :=
    by cases K <;> rfl

  theorem preserve_retjoin_stack_cons_nonnil {Pr K k} :
      K ≠ ∅ → (K ⬝ k).retjoin Pr = K.retjoin Pr := by
    cases K <;> intro nn
    · case nil => contradiction
    · case cons => rfl

  -- List.append_ne_nil_of_left_ne_nil
  theorem stack_append_left_nonnil : (s t : CallStack) -> (h : s ≠ ∅) -> s ++ t ≠ ∅
    | s, .nil, h => h
    | s, K ⬝ k, h => by simp

  theorem preserve_retjoin_stack_append {Pr K k} : {K' : CallStack} ->
      CallStack.retjoin Pr (K ⬝ k ++ K') = CallStack.retjoin Pr (K ⬝ k)
    | .nil => rfl
    | K' ⬝ k' => preserve_retjoin_stack_cons_nonnil
                   (stack_append_left_nonnil (K ⬝ k) K' (by simp)) ▸
                 preserve_retjoin_stack_append (K' := K')

  theorem preserve_retjoin {Pr : Program} : {P P' : ThreadPool} ->
                         Pr ⊢ P ↦ P' -> {ρ : SporkSig} -> P.Okay Pr ρ ->
                         P.retjoin Pr = P'.retjoin Pr
  | P, P', s => by
    cases s <;> intro Pₒₖ <;>
    try (exact preserve_retjoin_stack_cons)
    · case stepₗ P P' P₂ s =>
        simp_all!; match Pₒₖ with
          | .cat Pok P2ok => exact preserve_retjoin s Pok
    · case stepᵣ P₁ P P' s =>
        rfl
    · case retn f g K ρ' X Y y bret =>
        exact preserve_retjoin_stack_cons (K := K)
    · case promote f unpr g prom X K c K' u p =>
        simp[ThreadPool.retjoin];
        rw[preserve_retjoin_stack_append,
           preserve_retjoin_stack_append,
           preserve_retjoin_stack_cons]

  theorem goto_okay_rets
      {Pr} (Prok : Pr.Okay) {f canProm ρ} {X Y : ValMap} {bnext} {y : List Var}
      (p : f < Pr.size)
      (ρok : ρ.Okay Pr.fsigs canProm)
      (bnext_ok : bnext.OkayRets Pr.funs[f].bsigs ⟨X.length, ρ.sig⟩ y.length)
      (y_ok : IVec (·.Okay Y.length) y) :
      StackFrame.Okay Pr none canProm
        ⟨f, ρ, X[bnext.args]! ++ Y[y]!, codeOf Pr f bnext⟩ :=
    let ⟨bok, sigok, x_ok⟩ := bnext_ok
    let bok' : bnext.b < Pr.funs[f].blocks.length :=
      List.length_map Block.bsig ▸ bok
    let xlen : bnext.args.length = X[bnext.args].length :=
      x_ok.map_length (λ x xₒₖ => X[x])
    let ylen : y.length = Y[y].length :=
      y_ok.map_length (λ y yₒₖ => Y[y])
    let code_ok : Pr.funs[f]!.blocks[bnext.b]!.code.Okay
                    Pr.fsigs Pr.funs[f].bsigs Pr.funs[f].fsig.ret
                    ⟨(X[bnext.args]! ++ Y[y]!).length, ρ.sig⟩ := by
      rw[codeOfGetElem p bok',
         argsOfGetElem x_ok,
         argsOfGetElem y_ok,
         List.length_append,
         ← xlen, ← ylen, ← sigok]
      simp; exact ((Prok.1.get ⟨f, p⟩).1.get ⟨bnext.b, bok'⟩).1
    ⟨p, ρok, rfl, .code code_ok⟩

  theorem goto_okay
      {Pr} (Prok : Pr.Okay) {f canProm ρ} {X : ValMap} {bnext}
      (p : f < Pr.size)
      (ρok : ρ.Okay Pr.fsigs canProm)
      (bnext_ok : bnext.Okay Pr.funs[f].bsigs ⟨X.length, ρ.sig⟩) :
      StackFrame.Okay Pr none canProm ⟨f, ρ, X[bnext.args]!, codeOf Pr f bnext⟩ :=
    List.append_nil X[bnext.args]! ▸
    goto_okay_rets Prok (Y := []) (y := []) p ρok bnext_ok.cast0 .nil

  theorem entry_okay
      {Pr} (Prok : Pr.Okay) {f canProm} {X : List Val}
      (p : f < Pr.size)
      (sigok : Pr.funs[f].fsig.arity = X.length) :
      StackFrame.Okay Pr none canProm ⟨f, ∅, X, codeEntry Pr f⟩ :=
    let fok := Prok.1.get ⟨f, p⟩
    let c' : Code.Okay Pr.fsigs Pr.funs[f].bsigs Pr.funs[f].fsig.ret
              ⟨X.length, []⟩
              Pr.funs[f]!.blocks.head!.code :=
      sigok ▸
      Eq.symm (getElem!_pos Pr.funs f p) ▸
      fok.2.headeq ▸
      fok.2.head!eq ▸
      (fok.1.head fok.2.nonnil).1
    ⟨p, SpawnDeque.empty_okay, rfl, .code c'⟩

  theorem goto_entry_okay
      {Pr} (Prok : Pr.Okay) {f canProm} {X : ValMap} {x : List Var}
      (p : f < Pr.size)
      (xok : IVec (·.Okay X.length) x)
      (sigok : Pr.funs[f].fsig.arity = x.length) :
      StackFrame.Okay Pr none canProm ⟨f, ∅, X[x]!, codeEntry Pr f⟩ :=
    entry_okay Prok p (argsOfGetElem xok ▸
                       xok.map_length (λ x xₒₖ => X[x]) ▸
                       sigok)
  
  open ThreadPool.Okay (leaf cat) in
  theorem preservation {Pr : Program} (Prok : Pr.Okay) :
                       {P P' : ThreadPool} -> {ρ : SporkSig} ->
                       P.Okay Pr ρ -> Pr ⊢ P ↦ P' -> P'.Okay Pr ρ := by
    intro P P' ρ ok P_P'; cases P_P' <;> cases ok

    · case stepₗ P P' P₂ P_P' P2ok Pok =>
        exact cat (preservation Prok Pok P_P') P2ok

    · case stepᵣ P₁ P P' P_P' Pok P1ok =>
        exact cat (preserve_retjoin P_P' Pok ▸ P1ok) (preservation Prok Pok P_P')

    · case stmt f K ρ X e v c a ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X.concat v, .code c⟩)
        exact match ok with
           | Kok ⬝ₒₖ (.mk p ρok _ (.code (.stmt eok cok))) =>
             Kok ⬝ₒₖ (.mk p ρok rfl (.code
                 (by simp[BlockSig.bind] at cok; simp; exact cok)))

    · case goto f K ρ X bnext ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X[bnext.args]!, codeOf Pr f bnext⟩)
        exact match ok with
          | Kok ⬝ₒₖ (.mk p ρok _ (.code (.trfr (.goto bnext_ok))))=>
            Kok ⬝ₒₖ (goto_okay Prok p ρok bnext_ok)

    · case ite_true f K ρ X cond bthen belse n cond_n neq0 ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X[bthen.args]!, codeOf Pr f bthen⟩)
        exact match ok with
          | Kok ⬝ₒₖ (.mk p ρok _ (.code (.trfr (.ite cond_ok bthen_ok belse_ok)))) =>
            Kok ⬝ₒₖ (goto_okay Prok p ρok bthen_ok)

    · case ite_false f K ρ X cond bthen belse cond_0 ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X[belse.args]!, codeOf Pr f belse⟩)
        exact match ok with
          | Kok ⬝ₒₖ (.mk p ρok _ (.code (.trfr (.ite cond_ok bthen_ok belse_ok)))) =>
            Kok ⬝ₒₖ (goto_okay Prok p ρok belse_ok)

    · case call f g K ρ X x bret ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X, .cont bret⟩ ⬝ ⟨g, ∅, X[x]!, codeEntry Pr g⟩)
        exact match ok with
          | Kok ⬝ₒₖ kok@(.mk fok ρok _ (.code (.trfr (.call flt sigok x_ok
                bret_ok@(.mk bret_lt bret_sig_okay argsok))))) =>
              let bret_ok' : Cont.OkayRets Pr.funs[f].bsigs ⟨X.length, ρ.sig⟩
                               Pr.fsigs[g].ret bret :=
                Pr.funs.getElem_map (·.fsig) ▸ bret_ok
              let gframe_ok :=
                goto_entry_okay (f := g) Prok (Pr.size_eq_fsigs_length ▸ flt) x_ok
                  (Pr.funs.getElem_map (·.fsig) ▸ sigok)
              let glt := gframe_ok.flt
              let bret_ok'' : Cont.OkayRets Pr.funs[f].bsigs ⟨X.length, ρ.sig⟩
                                Pr.funs[g].fsig.ret bret :=
                Pr.funs.getElem_map (·.fsig) ▸ bret_ok'
              Kok ⬝ₒₖ ⟨fok, ρok, rfl, .cont bret_ok''⟩ ⬝ₒₖ gframe_ok

    · case retn f g K ρ X Y y bret ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X[bret.args]! ++ Y[y]!, codeOf Pr f bret⟩)
        exact match ok with
          | Kok ⬝ₒₖ (.mk flt ρok _ (.cont bret_ok))
                ⬝ₒₖ (.mk glt ⟨.nil, _⟩ _ (.code (.trfr (.retn _ ylen y_ok)))) =>
            Kok ⬝ₒₖ (goto_okay_rets Prok flt ρok (ylen ▸ bret_ok) y_ok)

    · case spork f K ρ X g g_args bbody ok =>
       apply @leaf Pr (K ⬝ ⟨f, ρ.push ⟨g, X[g_args]!, Pr.funs[g]!.fsig.ret⟩,
                            X[bbody.args]!, codeOf Pr f bbody⟩)
       exact match ok with
         | Kok ⬝ₒₖ ⟨flt, ⟨unpr_ok, prom_ok⟩, _, .code
               (.trfr (.spork glt gsig g_args_ok bbody_ok))⟩ =>
           let glt' : g < Pr.funs.length := List.length_map (α := Func) (·.fsig) ▸ glt
           let h : FuncSig.mk X[g_args]!.length Pr.funs[g]!.fsig.ret = Pr.fsigs[g] :=
             argsOfGetElem g_args_ok ▸
             getElem!_pos Pr.funs g glt' ▸
             congrArg₂ FuncSig.mk
               (g_args_ok.map_length (λ x xₒₖ => X[x]) ▸ Eq.symm gsig) (by simp)
           Kok ⬝ₒₖ (goto_okay Prok flt ⟨unpr_ok.concat ⟨glt, h⟩, prom_ok⟩
                     (by rw[ρ.pushsig, getElem!_pos Pr.funs g glt']
                         simp[BlockSig.spork] at bbody_ok; simp
                         exact bbody_ok))

    · case promote f unpr g prom X K c K' u p ok =>
        let kProm : K.allPromoted = true := by simp_all
        let rec hp : {K' : CallStack} -> {gets : Option Nat} -> K'.prom = [] ->
                     CallStack.Okay Pr gets (K ⬝ ⟨f, ⟨g :: unpr, prom⟩, X, c⟩ ++ K') ->
                     CallStack.Okay Pr gets (K ⬝ ⟨f, ⟨unpr, g.ret :: prom⟩, X, c⟩ ++ K') ∧
                     CallStack.Okay Pr none {⟨g.f, ∅, g.args, codeEntry Pr g.f⟩} ∧
                     g.ret = Pr.funs[g.f]!.fsig.ret
          | .nil, gets, _, ok => by
            rw[CallStack.append_nil] at *
            apply And.intro <;> try (apply And.intro)
            · exact ok.tail ⬝ₒₖ
                (let kok := ok.head
                 ⟨ok.head.flt,
                  (let x := ok.head.ρₒₖ
                   by rw[kProm] at *; exact x.promote),
                  ok.head.cb,
                  ok.head.cₒₖ⟩)
            · apply (.nil ⬝ₒₖ ·)
              let glt : g.f < Pr.funs.length := by
                rw[← List.length_map (·.fsig)]
                exact ok.head.ρₒₖ.unpr.head'.flt
              let Prsize : Pr.funs.length = Pr.fsigs.length :=
                (List.length_map (as := Pr.funs) (·.fsig)).symm
              let glt' := Prsize ▸ glt
              exact StackFrame.Okay.mk glt SpawnDeque.empty_okay rfl
                (entry_okay (canProm := true) Prok glt
                  (List.getElem_map Func.fsig (l := Pr.funs) ▸
                   (congrArg (·.arity) ok.head.ρₒₖ.unpr.head'.sig).symm)
                ).cₒₖ
            · let gflt := ok.head.ρₒₖ.unpr.head'.flt
              let gflt' : g.f < Pr.funs.length :=
                List.length_map (as := Pr.funs) (·.fsig) ▸ gflt
              let x : g.ret = Pr.fsigs[g.f].ret :=
                congrArg (·.ret) ok.head.ρₒₖ.unpr.head'.sig
              rw[getElem!_pos Pr.funs g.f gflt',
                 x,
                 List.getElem_map (·.fsig) (l := Pr.funs)]
          | K' ⬝ k', gets, p, ok =>
            let ⟨kp', Kp'⟩ := List.append_eq_nil_iff.mp p
            let k'ok := ok.head
            let ⟨K'ok', gok, glt⟩ := hp Kp' ok.tail
            let l := K'ok'
            let k'ok' := k'ok.castCanProm
              (K ⬝ ⟨f, ⟨unpr, g.ret :: prom⟩, X, c⟩ ++ K').allPromoted
              (λ (x : (K ⬝ ⟨f, ⟨g :: unpr, prom⟩, X, c⟩ ++ K').allPromoted) =>
                 let x' : (K ⬝ ⟨f, ⟨g :: unpr, prom⟩, X, c⟩ ++ K').unpr = [] :=
                   by simp_all[x]
                 let x'' : g :: unpr = [] :=
                   (List.append_eq_nil_iff.mp
                     (List.append_eq_nil_iff.mp
                       (CallStack.append_unpr ▸ x')).left).right
                 by contradiction)
            ⟨K'ok' ⬝ₒₖ k'ok', gok, glt⟩
        let ⟨Kok, gok, glt⟩ := hp p ok
        let prom_p : Pr.funs[g.f]!.fsig.ret ::
                       (K ⬝ ⟨f, ⟨g :: unpr, prom⟩, X, c⟩ ++ K').prom =
                     (K ⬝ ⟨f, ⟨unpr, g.ret :: prom⟩, X, c⟩ ++ K').prom := by
          simp_all[CallStack.append_prom, p, glt]
        exact cat (prom_p ▸ leaf Kok) (leaf gok)

    · case spoin_unpr f K ρ sc X bunpr bprom ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X[bunpr.args]!, codeOf Pr f bunpr⟩)
        exact match ok with
          | Kok ⬝ₒₖ ⟨flt, ⟨unpr_ok, prom_ok⟩, _,
              .code (.trfr (.spoin nn bunpr_ok bprom_ok))⟩ =>
            let h : (ρ.push sc).sig.tail = ρ.sig := by simp
            Kok ⬝ₒₖ (goto_okay Prok flt ⟨unpr_ok.unconcat.1, prom_ok⟩ (h ▸ bunpr_ok))

    · case spoin_prom f K ρ' X bunpr bprom Y y g K_unpr_nil retok ok =>
        let g_ret_eq : g.ret = Pr.funs[g.f]!.fsig.ret :=
          congrArg (λ | some x => x | _ => g.ret) (congrArg List.head? ok.same_prom)
        let ρ_eq_ρ'_Kprom : ρ = ρ' ++ K.prom :=
          Eq.symm (congrArg List.tail ok.same_prom)
        rw[ρ_eq_ρ'_Kprom] at ok ⊢
        apply @leaf Pr (K ⬝ ⟨f, ⟨[], ρ'⟩, X[bprom.args]! ++ Y[y]!, codeOf Pr f bprom⟩)
        let ok'' : (ThreadPool.leaf (K ⬝ ⟨f, ⟨[], g.ret :: ρ'⟩, X,
                      .code (.trfr (.spoin bunpr bprom))⟩)).Okay Pr (g.ret :: ρ' ++ K.prom) :=
          g_ret_eq ▸ ok
        let flt := ok''.get.head.flt
        let sd_ok : (SpawnDeque.mk [] ρ').Okay Pr.fsigs K.allPromoted :=
          ⟨IVec.nil, by simp[CallStack.allPromoted]; rw[K_unpr_nil]; rfl⟩
        let y_ok : IVec (·.Okay Y.length) y :=
          match retok.get.head.cₒₖ.c.t with
            | .retn _ _ y_ok => y_ok
        let y_len_eq_g_ret : y.length = g.ret :=
          match retok.get.head.cₒₖ'.c.t with
            | .retn _ l _ => g_ret_eq ▸ Eq.symm l
        let cont_ok : bprom.OkayRets Pr.funs[f].bsigs ⟨X.length, ρ'⟩ y.length :=
          match ok''.get.head.cₒₖ.c.t with
            | .spoin nn unpr_ok prom_ok => y_len_eq_g_ret ▸ prom_ok
        exact ok''.get.tail ⬝ₒₖ
          (goto_okay_rets Prok flt sd_ok cont_ok y_ok)
end Step
