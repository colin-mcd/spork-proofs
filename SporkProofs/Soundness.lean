import SporkProofs.SyntaxDefs
import SporkProofs.SemanticsDefs
import SporkProofs.SyntaxWF
import SporkProofs.SemanticsWF
import SporkProofs.Progress
import SporkProofs.Preservation

namespace Steps

  theorem preservation {P : Program} (Pwf : P WF-program) : {R R' : ThreadTree} ->
                        P ⊢ R WF-tree -> P ⊢ R ↦* R' -> P ⊢ R' WF-tree
    | R, .(R), Rwf, .nil => Rwf
    | R, R'', Rwf, @Steps.cons .(P) .(R) R' .(R'') R_sR' R'_R'' =>
      Step.preservation Pwf (preservation Pwf Rwf R_sR') R'_R''

  theorem preserve_prom {P : Program} : {R R' : ThreadTree} ->
                         P ⊢ R ↦* R' -> R.prom = R'.prom
  | R, .(R), .nil  => rfl
  | R, R'', @Steps.cons .(P) .(R) R' .(R'') R_R' R'_R'' =>
    Eq.trans R_R'.preserve_prom R'_R''.preserve_prom

  theorem preserve_last_f {P} : {R R' : ThreadTree} ->
                          P ⊢ R ↦* R' -> R.split.fst.K.last!.f = R'.split.fst.K.last!.f
    | R, .(R), .nil => rfl
    | R, R'', @Steps.cons .(P) .(R) R' .(R'') ss s  =>
      Eq.trans ss.preserve_last_f s.preserve_last_f

  def soundness {P : Program} (Pwf : P WF-program) {R R' : ThreadTree}
                (Rwf : P ⊢ R WF-tree) (R_R' : P ⊢ R ↦* R') : Step.Next P R' :=
    Step.progress R' (preservation Pwf Rwf R_R')

  inductive Next (P : Program) : ThreadTree -> Type where
    | result (X b x) : Next P {{⟨0, ∅, X, b⟩} ⋄ .retn x}
    | step {R} (R') (s : P ⊢ R ↦ R') : Next P R

  def program_soundness {P : Program} (Pwf : P WF-program) {R : ThreadTree}
                        (ss : P ⊢ (ThreadTree.init P Pwf) ↦* R) : Next P R:=
    have Rwf := ss.preservation Pwf (ThreadTree.WF.init Pwf)
    have feq := ss.preserve_last_f
    match Step.progress R Rwf with
      | .result g X b x => by
        simp at feq
        rw[← feq]
        exact .result X b x
      | .blocked K f bspwn π X b bunpr bprom => by
        have c := ss.preserve_prom
        contradiction
      | .step R' s => .step R' s

end Steps
