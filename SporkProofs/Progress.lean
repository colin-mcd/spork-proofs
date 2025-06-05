import SporkProofs.Syntax
import SporkProofs.Semantics
import SporkProofs.Preservation

namespace Step

  inductive Next (Pr : Program) : ThreadPool -> Type where
    | result (g X x) :
        Next Pr {{⟨g, ∅, X, .code (.trfr (.retn x))⟩}}
    | blocked (K f gret ρ X bunpr bprom) :
        Next Pr {K ⬝ ⟨f, ⟨[], gret :: ρ⟩, X, .code (.trfr (.spoin bunpr bprom))⟩}
    | step {P} (P') (s : Pr ⊢ P ↦ P') :
        Next Pr P

  theorem prom_imp_allPromoted
      {Pr K get f gret ρ X c}
      (ok : (K ⬝ ⟨f, ⟨[], gret :: ρ⟩, X, c⟩).Okay Pr get) :
      K.unpr = [] :=
    K.allPromoted_imp_nil
      (ok.head.ρₒₖ.prom.prom_canProm_true K.allPromoted)
  
  def progress {Pr : Program} : -- (Prok : Pr.Okay) :
               (P : ThreadPool) -> P.Okay' Pr ->
               Next Pr P
    | .cat P₁ P₂, ok =>
      let P₁ok : P₁.Okay' Pr := ok.to_okay.left.to_okay'
      let P₂ok := ok.to_okay.right.to_okay'
      match progress P₁ P₁ok with
        | .result g X x =>
          let y := ok.to_okay.left.same_prom;
          by contradiction
        | .step P₁' s =>
          .step _ (.stepₗ s)
        | .blocked K f gret ρ X bunpr bprom =>
          let P₁b : ThreadPool :=
            {K ⬝ ⟨f, ⟨[], gret :: ρ⟩, X, .code (.trfr (.spoin bunpr bprom))⟩}
          let P₁bok : P₁b.Okay' Pr := ok.to_okay.left.to_okay'
          match progress P₂ P₂ok with
            | .result g Y y =>
              .step _ (.spoin_prom (g := ⟨g, default /- doesn't matter -/, gret⟩)
                         (prom_imp_allPromoted ok.to_okay.left.get))
            | .blocked K' f' gret' ρ' X' bunpr' bprom' =>
              let z := ok.to_okay.right.same_prom
              by contradiction
            | .step P₂' s =>
              .step _ (.stepᵣ s)
    | .leaf (K ⬝ ⟨f, ρ, X, .code (.stmt e c)⟩), ok =>
      let eₒₖ := ok.to_okay.get.head.cₒₖ.c.e
      .step _ (.stmt (Expr.Eval.mk eₒₖ))
    | .leaf (K ⬝ ⟨f, ρ, X, .code (.trfr (.goto bnext))⟩), ok =>
      .step _ .goto
    | .leaf (K ⬝ ⟨f, ρ, X, .code (.trfr (.ite cond bthen belse))⟩), ok =>
      let condₒₖ := match ok.to_okay.get.head.cₒₖ.c.t with
        | .ite condₒₖ bthenₒₖ belseₒₖ => condₒₖ
      let c? := cond.eval X condₒₖ
      if p : c? = 0 then
        .step _ (.ite_false (p ▸ .mk condₒₖ))
      else
        .step _ (.ite_true (.mk condₒₖ) p)
    | .leaf (K ⬝ ⟨f, ρ, X, .code (.trfr (.call g args bret))⟩), ok =>
      .step _ .call
    | .leaf (K ⬝ ⟨f, ρ, X, .cont bnext⟩ ⬝ ⟨g, ρempty, Y, .code (.trfr (.retn y))⟩), ok =>
      let p : ρempty = ∅ :=
        by cases ρempty; cases ok.to_okay.get.head.cₒₖ.c.t; simp_all; rfl
      p ▸ .step _ .retn
    | .leaf (K ⬝ ⟨f, ρ, X, .code c⟩ ⬝ ⟨g, ρempty, Y, .code (.trfr (.retn y))⟩), ok =>
      let x := ok.to_okay.get.tail.head.isCont
      by contradiction
    | .leaf (.nil ⬝ ⟨g, ρempty, Y, .code (.trfr (.retn y))⟩), ok =>
      let p : ρempty = ∅ :=
        by cases ρempty; cases ok.to_okay.get.head.cₒₖ.c.t; simp_all; rfl
      p ▸ .result g Y y
    | .leaf (K ⬝ ⟨f, ρ, X, .code (.trfr (.spork bbody g args))⟩), ok =>
      sorry
    | .leaf (K ⬝ ⟨f, ρ, X, .code (.trfr (.spoin bunpr bprom))⟩), ok =>
      -- either spoin_unpr or spoin_prom->blocked
      sorry
end Step
