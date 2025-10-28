import SporkProofs.Syntax
import SporkProofs.Semantics
import SporkProofs.Progress
import SporkProofs.Preservation

namespace Steps

  theorem preservation {P : Program} (Pwf : P WF-program) :
                        {R R' : ThreadTree} ->
                        P ⊢ R WF-tree -> P ⊢ R ↦* R' -> P ⊢ R' WF-tree
    | R, .(R), Rwf, .nil => Rwf
    | R, R'', Rwf, @Steps.cons .(P) .(R) R' .(R'') R_sR' R'_R'' =>
      Step.preservation Pwf (preservation Pwf Rwf R_sR') R'_R''

  theorem preserves_prom {P : Program} (Pwf : P WF-program) : {R R' : ThreadTree} ->
                         P ⊢ R ↦* R' -> P ⊢ R WF-tree -> R.prom = R'.prom
  | R, .(R), .nil, _Rwf  => rfl
  | R, R'', @Steps.cons .(P) .(R) R' .(R'') R_R' R'_R'', Rwf =>
    let p_R_R' : R.prom = R'.prom := preserves_prom Pwf R_R' Rwf
    let p_R'_R'' : R'.prom = R''.prom := Step.preserve_prom R'_R'' (preservation Pwf Rwf R_R')
    Eq.trans p_R_R' p_R'_R''

  def soundness {P : Program} (Pwf : P WF-program) {R R' : ThreadTree}
                (Rwf : P ⊢ R WF-tree) (R_R' : P ⊢ R ↦* R') : Step.Next P R' :=
    Step.progress R' (preservation Pwf Rwf R_R')

  inductive NextRoot (P : Program) : ThreadTree -> Type where
    | result (g X b x) :
        NextRoot P {{⟨g, ∅, X, b⟩} ⋄ .retn x}
    | step {R} (R') (s : P ⊢ R ↦ R') :
        NextRoot P R

  def program_soundness {P : Program} (Pwf : P WF-program) {R : ThreadTree}
                        (ss : P ⊢ (ThreadTree.init P Pwf) ↦* R) : NextRoot P R :=
    let Piwf := ThreadTree.WF.init Pwf
    let Rwf := preservation Pwf Piwf ss
    match Step.progress R Rwf with
      | .result g X b x => .result g X b x
      | .blocked K f bspwn π X b bunpr bprom =>
        let c := preserves_prom Pwf ss Piwf
        by contradiction
      | .step R' s => .step R' s

end Steps
