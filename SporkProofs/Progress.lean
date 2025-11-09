import SporkProofs.SyntaxDefs
import SporkProofs.SemanticsDefs
import SporkProofs.SyntaxWF
import SporkProofs.SemanticsWF
import SporkProofs.Semantics

namespace Step

  inductive Next (P : Program) : ThreadTree -> Type where
    | result (f X b x) :
        Next P {{⟨f, ∅, X, b⟩} ⋄ (.retn x)}
    | blocked (K f bspwn π X b bunpr bprom) :
        Next P {K ⬝ ⟨f, ⟨[], bspwn :: π⟩, X, b⟩ ⋄ (.spoin bunpr bprom)}
    | step {R} (R') (s : P ⊢ R ↦ R') :
        Next P R
  
  def progress {P : Program} :
               (R : ThreadTree) -> P ⊢ R WF-tree ->
               Next P R
    | .node Rp Rc, wf =>
      let Rpwf : P ⊢ Rp WF-tree := wf.parent
      let Rcwf := wf.child
      match progress Rp Rpwf with
        | .result g X b x =>
          nomatch wf.parent_prom
        | .step Rp' s =>
          .step _ (congr_parent s)
        | .blocked K f bspwn π X b bunpr bprom =>
          let Rpb : ThreadTree :=
            {K ⬝ ⟨f, ⟨[], bspwn :: π⟩, X, b⟩ ⋄ (.spoin bunpr bprom)}
          let Rpbwf : P ⊢ Rpb WF-tree := wf.parent
          match progress Rc Rcwf with
            | .result g Y b' y =>
              .step _ (.spoin_prom (K.allPromoted_iff_nil.mp
                  (wf.parent.get.K.head.ρwf.prom.prom_canProm_true K.allPromoted)))
            | .blocked K' f' gret' π' X' b' bunpr' bprom' =>
              nomatch wf.child_prom
            | .step Rc' s =>
              .step _ (congr_child s)
    | .thread (K ⬝ ⟨f, ρ, X, b⟩ ⋄ (.stmt e c)), wf =>
      .step _ (.stmt (.mk wf.get.c.stmt_expr))
    | .thread (K ⬝ ⟨f, ρ, X, b⟩ ⋄ (.goto bnext)), wf =>
      .step _ .goto
    | .thread (K ⬝ ⟨f, ρ, X, b⟩ ⋄ (.ite cond bthen belse)), wf =>
      if p : cond.eval X wf.get.c.ite_cond = 0 then
        .step _ (.ite_false (p ▸ .mk wf.get.c.ite_cond))
      else
        .step _ (.ite_true (.mk wf.get.c.ite_cond) p)
    | .thread (K ⬝ ⟨f, ρ, X, b⟩ ⋄ (.call g args bret)), wf =>
      .step _ .call
    | .thread (K ⬝ ⟨f, ρ, X, bret⟩ ⬝ ⟨g, ρempty, Y, b⟩ ⋄ (.retn y)), wf =>
      let p : ρempty = ∅ :=
        by cases ρempty <;> cases wf.get.c <;> simp_all; rfl
      p ▸ .step _ .retn
    | .thread (.nil ⬝ ⟨g, ρempty, Y, b⟩ ⋄ (.retn y)), wf =>
      let p : ρempty = ∅ :=
        by cases ρempty <;> cases wf.get.c <;> simp_all; rfl
      p ▸ .result g Y b y
    | .thread (K ⬝ ⟨f, ρ, X, b⟩ ⋄ (.spork bbody bspwn)), wf =>
      .step _ .spork
    | .thread (K ⬝ ⟨f, ρ, X, b⟩ ⋄ (.spoin bunpr bprom)), wf =>
      match ρ with
        | ⟨[], []⟩ =>
          nomatch wf.get.c.spoin_oblg
        | ⟨u :: us, ps⟩ =>
          let sc := (u :: us).getLast (by simp)
          let us' := (u :: us).dropLast
          let pf : SpawnDeque.mk (u :: us) ps = (SpawnDeque.mk us' ps).push sc :=
            by simp; symm; exact (u :: us).dropLast_concat_getLast (by simp)
          pf ▸ .step _ .spoin_unpr
        | ⟨[], p :: ps⟩ =>
          .blocked _ _ _ _ _ _ _ _
end Step
