import SporkProofs.Syntax
import SporkProofs.Semantics
import SporkProofs.Progress
import SporkProofs.Preservation

namespace Steps

  theorem preservation {P : Program} (Pwf : P.WF) :
                        {R R' : ThreadTree} ->
                        R.WF P -> P ⊢ R ↦* R' -> R'.WF P
    | R, .(R), Rwf, .nil => Rwf
    | R, R'', Rwf, @Steps.cons .(P) .(R) R' .(R'') R_sR' R'_R'' =>
      Step.preservation Pwf (preservation Pwf Rwf R_sR') R'_R''

  theorem preserves_prom {P : Program} (Pwf : P.WF) : {R R' : ThreadTree} ->
                         P ⊢ R ↦* R' -> R.WF P -> R.prom = R'.prom
  | R, .(R), .nil, _Rwf  => rfl
  | R, R'', @Steps.cons .(P) .(R) R' .(R'') R_R' R'_R'', Rwf =>
    let p_R_R' : R.prom = R'.prom := preserves_prom Pwf R_R' Rwf
    let p_R'_R'' : R'.prom = R''.prom := Step.preserve_prom R'_R'' (preservation Pwf Rwf R_R')
    Eq.trans p_R_R' p_R'_R''

  def soundness {P : Program} (Pwf : P.WF) {R R' : ThreadTree}
                (Rwf : R.WF P) (R_R' : P ⊢ R ↦* R') : Step.Next P R' :=
    Step.progress R' (preservation Pwf Rwf R_R')

  inductive NextRoot (P : Program) : ThreadTree -> Type where
    | result (g X x) :
        NextRoot P {{⟨g, ∅, X, .code (.retn x)⟩}}
    | step {R} (R') (s : P ⊢ R ↦ R') :
        NextRoot P R

  def program_soundness {P : Program} (Pwf : P.WF) {R : ThreadTree}
                        (ss : P ⊢ (ThreadTree.init P) ↦* R) : NextRoot P R :=
    let Piwf := ThreadTree.WF.init Pwf
    let Rwf := preservation Pwf Piwf ss
    match Step.progress R Rwf with
      | .result g X x => .result g X x
      | .blocked K f gret π X bunpr bprom =>
        let c := preserves_prom Pwf ss Piwf
        by contradiction
      | .step R' s => .step R' s

end Steps
