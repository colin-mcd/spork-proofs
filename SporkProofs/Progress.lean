import SporkProofs.Syntax
import SporkProofs.Semantics

namespace Step

  inductive Next (P : Program) : ThreadTree -> Type where
    | result (g X x) :
        Next P {{⟨g, ∅, X, .code (.retn x)⟩}}
    | blocked (K f gret π X bunpr bprom) :
        Next P {K ⬝ ⟨f, ⟨[], gret :: π⟩, X, .code (.spoin bunpr bprom)⟩}
    | step {R} (R') (s : P ⊢ R ↦ R') :
        Next P R
  
  def progress {P : Program} :
               (R : ThreadTree) -> R.WF P ->
               Next P R
    | .node Rp Rc, wf =>
      let Rpwf : Rp.WF P := wf.parent
      let Rcwf := wf.child
      match progress Rp Rpwf with
        | .result g X x =>
          nomatch wf.parent_prom
        | .step Rp' s =>
          .step _ (congr_parent s)
        | .blocked K f gret π X bunpr bprom =>
          let Rpb : ThreadTree :=
            {K ⬝ ⟨f, ⟨[], gret :: π⟩, X, .code (.spoin bunpr bprom)⟩}
          let Rpbwf : Rpb.WF P := wf.parent
          match progress Rc Rcwf with
            | .result g Y y =>
              .step _ (.spoin_prom (g := ⟨g, default /- doesn't matter -/, gret⟩)
                         (K.allPromoted_iff_nil.mp
                           (wf.parent.get.head.ρwf.prom.prom_canProm_true
                             K.allPromoted)))
            | .blocked K' f' gret' π' X' bunpr' bprom' =>
              nomatch wf.child_prom
            | .step Rc' s =>
              .step _ (congr_child s)
    | .thread (K ⬝ ⟨f, ρ, X, .code (.stmt e c)⟩), wf =>
      .step _ (.stmt (.mk wf.get.head.cwf.c.stmt_expr))
    | .thread (K ⬝ ⟨f, ρ, X, .code (.goto bnext)⟩), wf =>
      .step _ .goto
    | .thread (K ⬝ ⟨f, ρ, X, .code (.ite cond bthen belse)⟩), wf =>
      if p : cond.eval X wf.get.head.cwf.c.ite_cond = 0 then
        .step _ (.ite_false (p ▸ .mk wf.get.head.cwf.c.ite_cond))
      else
        .step _ (.ite_true (.mk wf.get.head.cwf.c.ite_cond) p)
    | .thread (K ⬝ ⟨f, ρ, X, .code (.call g args bret)⟩), wf =>
      .step _ .call
    | .thread (K ⬝ ⟨f, ρ, X, .cont bnext⟩ ⬝ ⟨g, ρempty, Y, .code (.retn y)⟩), wf =>
      let p : ρempty = ∅ :=
        by cases ρempty <;> cases wf.get.head.cwf.c <;> simp_all; rfl
      p ▸ .step _ .retn
    | .thread (K ⬝ ⟨f, ρ, X, .code c⟩ ⬝ ⟨g, ρempty, Y, .code (.retn y)⟩), wf =>
      nomatch wf.get.tail.head.isCont
    | .thread (.nil ⬝ ⟨g, ρempty, Y, .code (.retn y)⟩), wf =>
      let p : ρempty = ∅ :=
        by cases ρempty <;> cases wf.get.head.cwf.c <;> simp_all; rfl
      p ▸ .result g Y y
    | .thread (K ⬝ ⟨f, ρ, X, .code (.spork bbody g args)⟩), wf =>
      .step _ .spork
    | .thread (K ⬝ ⟨f, ρ, X, .code (.spoin bunpr bprom)⟩), wf =>
      match ρ with
        | ⟨[], []⟩ =>
          nomatch wf.get.head.cwf.c.spoin_sn_nonnil
        | ⟨u :: us, ps⟩ =>
          let sc := (u :: us).getLast (by simp)
          let us' := (u :: us).dropLast
          let pf : SpawnDeque.mk (u :: us) ps = (SpawnDeque.mk us' ps).push sc :=
            by simp; symm; exact (u :: us).dropLast_concat_getLast (by simp)
          pf ▸ .step _ .spoin_unpr
        | ⟨[], p :: ps⟩ =>
          .blocked _ _ _ _ _ _ _
end Step
