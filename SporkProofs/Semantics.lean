import SporkProofs.SemanticsDefs

inductive Step (P : Program) : (R R' : ThreadTree) -> Type where
  | congr_parent {Rp Rp' Rc} :
    Step P Rp Rp' ->
    Step P (Rp ⋏ Rc) (Rp' ⋏ Rc)

  | congr_child {Rp Rc Rc'} :
    Step P Rc Rc' ->
    Step P (Rp ⋏ Rc) (Rp ⋏ Rc')
  
  | stmt {f K ρ X b e v c} :
    X ⊢ₑₓₚᵣ e ⇓ v ->
    Step P {K ⬝ ⟨f, ρ, X, b⟩ ⋄ .stmt e c}
           {K ⬝ ⟨f, ρ, X.concat v, b⟩ ⋄ c}

  | goto {f K ρ X b bnext} :
    Step P {K ⬝ ⟨f, ρ, X, b⟩ ⋄ .goto bnext}
           {K ⬝ ⟨f, ρ, X[bnext.args]!, bnext.b⟩ ⋄ P[f]![bnext.b]!.code}

  | ite_true {f K ρ X b cond bthen belse n} :
    X ⊢ₐₜₒₘ cond ⇓ n ->
    n ≠ 0 ->
    Step P {K ⬝ ⟨f, ρ, X, b⟩ ⋄ .ite cond bthen belse}
           {K ⬝ ⟨f, ρ, X[bthen.args]!, bthen.b⟩ ⋄ P[f]![bthen.b]!.code}

  | ite_false {f K ρ X b cond bthen belse} :
    X ⊢ₐₜₒₘ cond ⇓ 0 ->
    Step P {K ⬝ ⟨f, ρ, X, b⟩ ⋄ .ite cond bthen belse}
           {K ⬝ ⟨f, ρ, X[belse.args]!, belse.b⟩ ⋄ P[f]![belse.b]!.code}

  | call {f g K ρ b X x bret} :
    Step P {K ⬝ ⟨f, ρ, X, b⟩ ⋄ .call g x bret}
           {K ⬝ ⟨f, ρ, X[bret.args]!, bret.b⟩ ⬝ ⟨g, ∅, X[x]!, 0⟩ ⋄ P[g]![0]!.code}

  | retn {f g K ρ X Y y b bret} :
    Step P {K ⬝ ⟨f, ρ, X, bret⟩ ⬝ ⟨g, ∅, Y, b⟩ ⋄ .retn y}
           {K ⬝ ⟨f, ρ, X ++ Y[y]!, bret⟩ ⋄ P[f]![bret]!.code}

  | spork {f K ρ X b bbody bspwn} :
    Step P {K ⬝ ⟨f, ρ, X, b⟩ ⋄ .spork bbody bspwn}
           {K ⬝ ⟨f, ρ.push ⟨bspwn.b, X[bspwn.args]!⟩,
                 X[bbody.args]!, bbody.b⟩ ⋄ P[f]![bbody.b]!.code}

  | promote {f unpr bspwn prom X K b K' C} :
    K.unpr = [] ->
    K'.prom = [] ->
    Step P {(K ⬝ ⟨f, ⟨bspwn :: unpr, prom⟩, X, b⟩ ++ K') ⋄ C}
           ({(K ⬝ ⟨f, ⟨unpr, bspwn :: prom⟩, X, b⟩ ++ K') ⋄ C} ⋏
            {{⟨f, ∅, bspwn.args, bspwn.b⟩} ⋄ P[f]![bspwn.b]!.code})

  | spoin_unpr {f K ρ bspwn X b bunpr bprom} :
    Step P {K ⬝ ⟨f, ρ.push bspwn, X, b⟩ ⋄ .spoin bunpr bprom}
           {K ⬝ ⟨f, ρ, X[bunpr.args]!, bunpr.b⟩ ⋄ P[f]![bunpr.b]!.code}

  | spoin_prom {f g K ρ X b b' bunpr bprom Y y} {bspwn : SpawnBlock} :
    K.unpr = [] ->
    Step P ({(K ⬝ ⟨f, ⟨[], bspwn :: ρ⟩, X, b⟩ ⋄ .spoin bunpr bprom)} ⋏
             {{⟨g, ∅, Y, b'⟩} ⋄ .retn y})
           {K ⬝ ⟨f, ⟨∅, ρ⟩, X[bprom.args]! ++ Y[y]!, bprom.b⟩ ⋄ P[f]![bprom.b]!.code}

inductive Steps (P : Program) : (R R' : ThreadTree) -> Type where
  | nil {R : ThreadTree} : Steps P R R
  | cons {R R' R'' : ThreadTree} : Steps P R R' -> Step P R' R'' -> Steps P R R''

namespace Step
  notation (name := poolstep) P:arg " ⊢ " R:arg " ↦ " R':arg => Step P R R'
end Step

namespace Steps
  notation (name := stepsstep) P:arg " ⊢ " R:arg " ↦* " R':arg => Steps P R R'

  @[simp] def append {P : Program} : {R R' R'' : ThreadTree} ->
                (P ⊢ R ↦* R') -> (P ⊢ R' ↦* R'') -> (P ⊢ R ↦* R'')
    | _R, _R', .(_R'), ss', nil => ss'
    | _R, _R', _R'', ss', cons ss s => cons (append ss' ss) s
  instance {P : Program} {R R' R'' : ThreadTree} :
           HAppend (P ⊢ R ↦* R') (P ⊢ R' ↦* R'') (P ⊢ R ↦* R'') where
    hAppend := append
  instance {P : Program} {R R' : ThreadTree} : Singleton (P ⊢ R ↦ R') (P ⊢ R ↦* R') where
    singleton := cons nil

  @[simp] def concat {P : Program} : {R R' R'' : ThreadTree} ->
                (P ⊢ R ↦ R') -> (P ⊢ R' ↦* R'') -> (P ⊢ R ↦* R'')
    | _R, _R', .(_R'), ss', nil => {ss'}
    | _R, _R', _R'', ss', cons ss s => cons (concat ss' ss) s

  universe u
  def byInd {Q : ThreadTree -> Sort u}
            {P : Program} :
            {Rₛ Rₑ : ThreadTree} ->
            Q Rₛ ->
            ((Rᵢ Rᵢ₁ : ThreadTree) -> Q Rᵢ -> P ⊢ Rᵢ ↦ Rᵢ₁ -> Q Rᵢ₁) ->
            P ⊢ Rₛ ↦* Rₑ ->
            Q Rₑ
    | Rₛ, .(Rₛ), n, _c, nil => n
    | Rₛ, Rₑ, n, c, @Steps.cons .(P) .(Rₛ) R₁ₑ .(Rₑ) ss s =>
      c R₁ₑ Rₑ (byInd n c ss) s

  def byIndR {Q : ThreadTree -> Sort u}
            {P : Program} :
            {Rₛ Rₑ : ThreadTree} ->
            Q Rₑ ->
            ((Rᵢ Rᵢ₁ : ThreadTree) -> P ⊢ Rᵢ ↦ Rᵢ₁ -> Q Rᵢ₁ -> Q Rᵢ) ->
            P ⊢ Rₛ ↦* Rₑ ->
            Q Rₛ
    | Rₛ, .(Rₛ), n, _c, nil => n
    | Rₛ, Rₑ, n, c, @Steps.cons .(P) .(Rₛ) R₁ₑ .(Rₑ) ss s =>
      byIndR (c R₁ₑ Rₑ s n) c ss

  def congr_parent {P} {Rp Rp' Rc : ThreadTree} :
                   P ⊢ Rp ↦* Rp' -> P ⊢ (Rp ⋏ Rc) ↦* (Rp' ⋏ Rc)
    | .nil => .nil
    | .cons ss s => .cons ss.congr_parent s.congr_parent

  def congr_child {P} {Rp Rc Rc' : ThreadTree} :
                  P ⊢ Rc ↦* Rc' -> P ⊢ (Rp ⋏ Rc) ↦* (Rp ⋏ Rc')
    | .nil => .nil
    | .cons ss s => .cons ss.congr_child s.congr_child

end Steps
