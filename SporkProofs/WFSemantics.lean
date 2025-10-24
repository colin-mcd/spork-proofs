import SporkProofs.Syntax
import SporkProofs.WFSyntax
import SporkProofs.Semantics
import SporkProofs.IVec
import SporkProofs.HeadIs
import SporkProofs.SimpSet

theorem argswf (Γ : Scope) : IVec (Γ ⊢ · WF-var) ((List.range Γ).map Var.mk) :=
  let rec h : (Γ : Scope) -> (n : Nat) ->
              IVec ((Γ + n) ⊢ · WF-var) ((List.range' n Γ).map Var.mk)
    | 0, n => .nil
    | Γ + 1, n => .cons ⟨by simp⟩ (Nat.add_assoc Γ 1 n ▸
                                   Nat.add_comm 1 n ▸
                                   h Γ (n + 1))
  List.range_eq_range' ▸ h Γ 0

-- namespace StackFrameCode
--   inductive WF (fsigs B bsig ret) : StackFrameCode -> Prop
--     | code {c} : c.WF fsigs B bsig -> (code c).WF fsigs B bsig ret
--     | cont {b} : b.WFRets B bsig ret -> (cont b).WF fsigs B bsig ret

--   namespace WF
--     notation (name := notationwf) fsigs:arg "; " B:arg "; " bsig:arg "; " ret:arg " ⊢ " c:arg " WF-sfc" => WF fsigs B bsig ret c

--     instance {fsigs B bsig ret} : (c : StackFrameCode) ->
--              Decidable (fsigs; B; bsig; ret ⊢ c WF-sfc)
--       | .code c =>
--         decidable_of_iff (fsigs; B; bsig ⊢ c WF-code)
--           ⟨code, λ (code p) => p⟩
--       | .cont b =>
--         decidable_of_iff (B; bsig ⊢ b(ret) WF-cont)
--           ⟨cont, λ (cont p) => p⟩

--     theorem c {fsigs B bsig ret c} :
--              fsigs; B; bsig; ret ⊢ (.code c) WF-sfc ->
--              fsigs; B; bsig ⊢ c WF-code
--       | code c => c

--     theorem b {fsigs B bsig b ret} :
--              fsigs; B; bsig; ret ⊢ (.cont b) WF-sfc ->
--              B; bsig ⊢ b(ret) WF-cont
--       | cont b => b
--   end WF
-- end StackFrameCode

/-
  inductive WF (B : BlockSigs) (bsig : BlockSig) (b : Cont) : Prop where
    | mk (_ : b.b < B.length)
         (_ : B[b.b] = ⟨b.args.length, bsig.σ⟩)
         (_ : IVec (bsig.Γ ⊢ · WF-var) b.args)
-/

namespace SpawnBlock
  inductive WF (B : BlockSigs) (bspwn : SpawnBlock) : Prop where
    | mk (_ : bspwn.b < B.length)
         (_ : B[bspwn.b].Γ = bspwn.args.length)
         (_ : B[bspwn.b].σ = [])

  namespace WF
    notation (name := notationwf) B:arg " ⊢ " bspwn " WF-spawn" => WF B bspwn
    
    instance {B: BlockSigs} (bspwn: SpawnBlock): Decidable (B ⊢ bspwn WF-spawn) :=
      decidable_of_iff (∃ _ : bspwn.b < B.length,
                        B[bspwn.b].Γ = bspwn.args.length ∧
                        B[bspwn.b].σ = [])
        ⟨λ ⟨a, b, c⟩ => .mk a b c, λ | .mk a b c => ⟨a, b, c⟩⟩

    theorem b {B bspwn}: B ⊢ bspwn WF-spawn -> bspwn.b < B.length
      | mk b _args _σ => b
    theorem b' {F : Func} {bspwn} (wf : F.B ⊢ bspwn WF-spawn) : bspwn.b < F.size :=
      F.size_eq_B_length ▸ wf.b
    theorem args {B bspwn}: (wf : B ⊢ bspwn WF-spawn) -> (B[bspwn.b]'(b wf)).Γ = bspwn.args.length
      | mk _b args _σ => args
    theorem σ {B bspwn}: (wf : B ⊢ bspwn WF-spawn) -> (B[bspwn.b]'(b wf)).σ = []
      | mk _b _args σ => σ

    theorem init {P} (Pwf : P WF-program) : (P[0]'Pwf.main.zero_lt).B ⊢ .init WF-spawn :=
      by let zlt := Pwf.main.zero_lt
         let mainΓ := congrArg FuncSig.arity Pwf.main.get0eq
         let entryΓ := congrArg BlockSig.Γ Pwf⁅0⁆.head.get0eq
         simp only [getters] at mainΓ entryΓ
         apply SpawnBlock.WF.mk <;> try (simp only [getters])
         · let mainΓ : P[0].fsig.arity = 0 := mainΓ
           simpa[mainΓ] using entryΓ
         · simpa using congrArg BlockSig.σ Pwf⁅0⁆.head.get0eq
         · exact Pwf⁅0⁆.head.zero_lt_map
  end WF
end SpawnBlock


namespace SpawnDeque
  abbrev SpawnOrder (canProm : Bool) (prom : List SpawnBlock) : Prop :=
    prom = if canProm then prom else []

  namespace SpawnOrder
    theorem of_nil {canProm : Bool} : SpawnOrder canProm [] :=
      by cases canProm <;> rfl
    theorem prom_canProm_true : (canProm : Bool) -> {bspwn : SpawnBlock} -> {prom : List SpawnBlock} ->
                                SpawnOrder canProm (bspwn :: prom) -> canProm = true
      | true, _gret, _prom, _so => rfl
  end SpawnOrder

  inductive WF (B: BlockSigs) (canProm: Bool) (ρ: SpawnDeque) : Prop
    | mk (_ : IVec (B ⊢ · WF-spawn) ρ.unpr) (_: SpawnOrder canProm ρ.prom)

  namespace WF
    notation (name := notationwf) B:arg "; " canProm:arg " ⊢ " ρ:arg " WF-deque" => WF B canProm ρ
  
    instance {B canProm} : (ρ : SpawnDeque) -> Decidable (B; canProm ⊢ ρ WF-deque)
      | .mk u p => decidable_of_iff
          (IVec (B ⊢ · WF-spawn) u ∧ SpawnOrder canProm p)
          ⟨λ ⟨a, b⟩ => ⟨a, b⟩, λ ⟨a, b⟩ => ⟨a, b⟩⟩
    
    theorem unpr {fsigs canProm} {ρ : SpawnDeque} : fsigs; canProm ⊢ ρ WF-deque -> IVec (fsigs ⊢ · WF-spawn) ρ.unpr | mk u _p => u
    theorem prom {fsigs canProm} {ρ : SpawnDeque} : fsigs; canProm ⊢ ρ WF-deque -> SpawnOrder canProm ρ.prom | mk _u p => p

    theorem castCanProm {fsigs ρ} : {canProm : Bool} -> (canProm' : Bool) -> canProm ≤ canProm' -> fsigs; canProm ⊢ ρ WF-deque -> fsigs; canProm' ⊢ ρ WF-deque
      | false, false, _, .mk MatchesOblg p => .mk MatchesOblg p
      | true, true, _, .mk u p => .mk u p
      | false, true, _, .mk u _p => .mk u rfl

    theorem promote {fsigs u p bspwn} (wf : fsigs; true ⊢ ⟨bspwn :: u, p⟩ WF-deque) :
                    fsigs; true ⊢ ⟨u, bspwn :: p⟩ WF-deque :=
      ⟨wf.unpr.tail, rfl⟩

    theorem empty {fsigs canProm} : fsigs; canProm ⊢ ∅ WF-deque :=
      ⟨.nil, .of_nil⟩
  end WF

  -- abbrev oblg : (ex: Nat) -> SpawnDeque -> Oblg
  --   | ex,
  -- inductive MatchesOblg (B : List BlockSig) : SpawnDeque -> Oblg -> Prop where
  --   | join_π (bspwn : SpawnBlock) (π : List SpawnBlock) (σ : Oblg) :
  --            MatchesOblg B ⟨[], π⟩ σ ->
  --            MatchesOblg B ⟨[], bspwn :: π⟩ (σ.join B[bspwn.b]!.σ.last)
  --   | spoin_π (bspwn : SpawnBlock) (π : List SpawnBlock) (σ : Oblg) :
  --             MatchesOblg B ⟨[], π⟩ σ ->
  --             MatchesOblg B ⟨[], bspwn :: π⟩ (σ.spoin B[bspwn.b]!.σ.last)
  --   | spoin_υ (bspwn : SpawnBlock) (υ π : List SpawnBlock) (σ : Oblg) :
  --             MatchesOblg B ⟨υ, π⟩ σ ->
  --             MatchesOblg B ⟨υ.concat bspwn, π⟩ (σ.spoin B[bspwn.b]!.σ.last)
  --   | retn (n : Nat) : MatchesOblg B ⟨[], []⟩ (.retn n)
  --   | exit (n : Nat) : MatchesOblg B ⟨[], []⟩ (.exit n)

  -- namespace MatchesOblg
  --   instance decide_matches_oblg {B: List BlockSig} :
  --                                (ρ : SpawnDeque) -> (σ : Oblg) ->
  --                                Decidable (MatchesOblg B ρ σ)
  --     | ⟨[], bspwn :: π⟩, .join σ n => sorry
  --     | ⟨[], bspwn :: π⟩, .spoin σ n => sorry
  --     | ⟨b_end :: υ, π⟩, .spoin σ n => sorry
  --     | ⟨[], []⟩, .retn n => isTrue sorry
  --     | ⟨[], []⟩, .exit n => isTrue sorry
  --     | ⟨_ :: _, _⟩, .retn n => isFalse sorry
  --     | ⟨_, _ :: _⟩, .retn n => isFalse sorry
  --     | ⟨_ :: _, _⟩, .exit n => isFalse sorry
  --     | ⟨_, _ :: _⟩, .exit n => isFalse sorry
  --     | ⟨_ :: _, _⟩, .join σ n => isFalse sorry
  --     | ⟨[], []⟩, .join σ n => isFalse sorry
  --     | ⟨[], []⟩, .spoin σ n => isFalse
  -- end MatchesOblg
end SpawnDeque

namespace StackFrame
  inductive WF (P : Program) (K : CallStack) (gets : Nat) : StackFrame -> Prop where
    | mk {f ρ X b} :
         (flt : f < P.size) ->
         (blt : b < P[f].B.length) ->
         (P[f].B[b].Γ ≤ X.length + gets ∧ P[f].B[b].σ = ρ.sig P[f].B) ->
         --P[f].B[b] = ⟨X.length + gets, P[f].B[b].r, ρ.sig P[f].B⟩ ->
         P[f].B; K.allPromoted ⊢ ρ WF-deque ->
         (mk f ρ X b).WF P K gets

  namespace WF
    notation (name := notationwf) P:arg "; " K:arg "; " gets:arg " ⊢ " k " WF-frame" => WF P K gets k
    notation (name := notationwf') P:arg "; " K:arg " ⊢ " k " WF-frame" => WF P K 0 k
    instance {P K gets} : (k : StackFrame) -> Decidable (P; K; gets ⊢ k WF-frame)
      | .mk f ρ X b =>
        decidable_of_iff (∃ flt : f < P.size,
                          ∃ blt : b < P[f].B.length,
                          --P[f].B[b] = ⟨X.length + gets, P[f].B[b].r, ρ.sig P[f].B⟩ ∧
                          (P[f].B[b].Γ ≤ X.length + gets ∧ P[f].B[b].σ = ρ.sig P[f].B) ∧
                          P[f].B; K.allPromoted ⊢ ρ WF-deque)
          ⟨λ ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, λ ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

    theorem flt {P K gets} : {k : StackFrame} ->
                P; K; gets ⊢ k WF-frame -> k.f < P.size
      | .mk _f _ρ _X _b, mk flt _blt _bsig _ρwf => flt

    theorem blt {P K gets} : {k : StackFrame} ->
                (wf : P; K; gets ⊢ k WF-frame) -> k.b < (P[k.f]'wf.flt).B.length
      | .mk _f _ρ _X _b, mk _flt blt _bsig _ρwf => blt

    theorem blt' {P K gets k} (wf : P; K; gets ⊢ k WF-frame) :
                 k.b < (P[k.f]'wf.flt).size :=
      (P[k.f]'wf.flt).size_eq_B_length ▸ wf.blt

    theorem ρwf {P K gets} : {k : StackFrame} ->
                (wf : P; K; gets ⊢ k WF-frame) -> (P[k.f]'wf.flt).B; K.allPromoted ⊢ k.ρ WF-deque
      | .mk _f _ρ _X _b, mk _flt _blt _bsig ρwf => ρwf

    theorem bsig {P K gets} : {k : StackFrame} ->
                 (wf : P; K; gets ⊢ k WF-frame) ->
                 (((P[k.f]'wf.flt).B[k.b]'wf.blt).Γ ≤ k.X.length + gets ∧
                  ((P[k.f]'wf.flt).B[k.b]'wf.blt).σ = k.ρ.sig (P[k.f]'wf.flt).B)
                 -- ((P[k.f]'wf.flt).B[k.b]'wf.blt) = ⟨k.X.length + gets, ((P[k.f]'wf.flt).B[k.b]'wf.blt).r, k.ρ.sig (P[k.f]'wf.flt).B⟩
      | .mk _f _ρ _X _b, mk _flt _blt bsig _ρwf => bsig

    theorem bsig! {P K gets} : {k : StackFrame} ->
                 (wf : P; K; gets ⊢ k WF-frame) ->
                 (P[k.f]!.B[k.b]!.Γ ≤ k.X.length + gets ∧
                  P[k.f]!.B[k.b]!.σ = k.ρ.sig P[k.f]!.B)
--                 P[k.f]!.B[k.b]! = ⟨k.X.length + gets, P[k.f]!.B[k.b]!.r, k.ρ.sig P[k.f]!.B⟩
      | .mk f _ρ _X b, mk flt blt bsig _ρwf =>
        getElem!_pos P f flt ▸
        getElem!_pos P[f].B b blt ▸
        bsig

    theorem changeStack {P K K' gets k} :
                        P; K; gets ⊢ k WF-frame ->
                        (K.allPromoted ≤ K'.allPromoted) ->
                        P; K'; gets ⊢ k WF-frame
      | .mk flt blt bsig ρwf, klt =>
        .mk flt blt bsig (ρwf.castCanProm K'.allPromoted klt)

    theorem spawn {P f bspwn} (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                  P; .nil ⊢ .spawn f bspwn WF-frame :=
      let blt := bwf.b
      -- let sigeq : P[f].B[bspwn.b] = ⟨bspwn.args.length, P[f].B[bspwn.b].r, []⟩ :=
      --   bwf.args ▸ bwf.σ ▸ rfl
      ⟨flt, blt, ⟨bwf.args ▸ Nat.le_refl P[f].B[bspwn.b].Γ, bwf.σ⟩, .empty⟩

    theorem entry {P} (Pwf : P WF-program) {f K X} (flt : f < P.size)
                  (sigwf : P[f].fsig.arity = X.length) : P; K ⊢ ⟨f, ∅, X, 0⟩ WF-frame :=
      let blt : 0 < P[f].B.length :=
        Pwf⁅f⁆.head.zero_lt_map
--      let sigeq := sigwf ▸ Pwf⁅f⁆.head.get0eq_map ▸ rfl
      ⟨flt, blt, ⟨sigwf ▸ Pwf⁅f⁆.head.get0eq_map ▸ by simp,
                  List.getElem_map Block.bsig ▸
                  congrArg (·.σ) Pwf⁅f⁆.head.get0eq⟩, .empty⟩

    theorem goto_rets
        {P} {f K ρ} {X : ValMap} {bnext : Cont} {r : Nat}
        (flt : f < P.size)
        (ρwf : P[f].B; K.allPromoted ⊢ ρ WF-deque)
        (bnext_wf : P[f].B; ⟨X.length, P[f].B[bnext.b]!.r, ρ.sig P[f].B⟩ ⊢ bnext(r) WF-cont) :
        P; K; r ⊢ ⟨f, ρ, X[bnext.args]'bnext_wf.args, bnext.b⟩ WF-frame :=
      ⟨flt,
       bnext_wf.blt,
       bnext_wf.bsig ▸ by simp; rw[ValMap.getElem_length bnext_wf.args]; simp,
       --bnext_wf.bsig ▸ by simp; symm; exact ValMap.getElem_length bnext_wf.args,
       ρwf⟩

    theorem goto
        {P} {f K ρ} {X : ValMap} {bnext : Cont}
        (p : f < P.size)
        (ρwf : P[f].B; K.allPromoted ⊢ ρ WF-deque)
        (bnext_wf : P[f].B; ⟨X.length, P[f].B[bnext.b]!.r, ρ.sig P[f].B⟩ ⊢ bnext WF-cont) :
        P; K ⊢ ⟨f, ρ, X[bnext.args]'bnext_wf.args, bnext.b⟩ WF-frame :=
      goto_rets p ρwf bnext_wf
  
    theorem goto_entry
        {P} (Pwf : P WF-program) {f K} {X : ValMap} {x : List Var}
        (p : f < P.size)
        (xwf : IVec (·.WF X.length) x)
        (sigwf : P[f].fsig.arity = x.length) :
        P; K ⊢ ⟨f, ∅, X[x]'xwf, 0⟩ WF-frame :=
      entry Pwf p (xwf.map_length (λ x xwf => X[x]) ▸ sigwf)
  end WF

  @[simp] def ret {P K gets} (k : StackFrame) (kwf : P; K; gets ⊢ k WF-frame) : Nat :=
    ((P[k.f]'kwf.flt).B[k.b]'kwf.blt).r

  @[simp] def ret! (P : Program) (k : StackFrame) : Nat :=
    P[k.f]!.B[k.b]!.r

  @[simp] def code {P K gets} (k : StackFrame) (kwf : P; K; gets ⊢ k WF-frame) : Code :=
    ((P[k.f]'kwf.flt)[k.b]'kwf.blt').code

  namespace WF
    @[simp] theorem ret!_eq_ret {P K k gets} (kwf : P; K; gets ⊢ k WF-frame) : k.ret! P = k.ret kwf :=
      by rw[ret, ret!,
            getElem!_pos P k.f kwf.flt,
            getElem!_pos (P[k.f]'kwf.flt).B k.b kwf.blt]

    @[simp] theorem code!_eq_code {P K k gets} (kwf : P; K; gets ⊢ k WF-frame) : k.code! P = k.code kwf :=
      by rw[code, code!,
            getElem!_pos P k.f kwf.flt,
            getElem!_pos (P[k.f]'kwf.flt) k.b kwf.blt']
  end WF
end StackFrame


namespace CallStack

  /--
  (Potentially partial) call stack, awaiting a return of `gets` args.
  When `gets` is `none`, this must be a full call stack,
  where the current frame is at the surface of the stack.
  When `gets` is `some n`, it is a partial call stack awaiting
  a return of `n` args from the following stack frame
  -/
  inductive WF (P : Program) : (gets : Option Nat) -> CallStack -> Prop where
    | nil {gets : Nat} : nil.WF P (some gets)
    | cons {K k} {gets : Option Nat} :
           P; K; (gets.getD 0) ⊢ k WF-frame ->
           K.WF P (some (k.ret! P)) ->
           (K ⬝ k).WF P gets

  namespace WF
    notation (name := callstackwfcons) t " ⬝wf " h:arg => WF.cons h t
    notation (name := notationwf) P:arg "; " gets:arg " ⊢ " K:arg " WF-stack" => WF P gets K
    notation (name := notationwf') P:arg " ⊢ " K " WF-stack" => WF P none K

    instance instDecidable {P} : {gets : Option Nat} -> (K : CallStack) ->
                           Decidable (P; gets ⊢ K WF-stack)
      | some gets, .nil => isTrue .nil
      | none, .nil => isFalse (λ _ => by contradiction)
      | gets, K ⬝ k =>
        let _ : Decidable (P; (k.ret! P) ⊢ K WF-stack) := instDecidable K
        decidable_of_iff (P; K; (gets.getD 0) ⊢ k WF-frame ∧ K.WF P (some (k.ret! P)))
          ⟨λ ⟨a, b⟩ => .cons a b, λ | .cons a b => ⟨a, b⟩⟩
        -- dite (P; K; (gets.getD 0) ⊢ k WF-frame)
        --   (λ kwf => let _ : Decidable (P; (k.ret kwf) ⊢ K WF-stack) :=
        --               instDecidable K
        --             decidable_of_iff (P; (k.ret kwf) ⊢ K WF-stack)
        --               ⟨cons kwf, λ | cons _kwf' Kwf => Kwf⟩)
        --   (isFalse ∘ λ | kₙwf, cons kwf _Kwf => kₙwf kwf)

    theorem nonnil {P} {K : CallStack} (Kwf : P ⊢ K WF-stack) : K ≠ CallStack.nil :=
      by cases Kwf <;> simp
    theorem head' {P gets} :
                  {K : CallStack} ->
                  (nn : K ≠ CallStack.nil) ->
                  P; gets ⊢ K WF-stack ->
                  P; K.tail; (gets.getD 0) ⊢ (K.head nn) WF-frame
      | _K ⬝ _k, _nn, _Kwf ⬝wf kwf => kwf
    theorem tail' {P gets} :
                  {K : CallStack} ->
                  (nn : K ≠ CallStack.nil) ->
                  (Kwf : P; gets ⊢ K WF-stack) ->
                  P; (some ((K.head nn).ret! P)) ⊢ K.tail WF-stack
      | _K ⬝ _k, _nn, Kwf ⬝wf _kwf => Kwf
    theorem head! {P gets} :
                  {K : CallStack} ->
                  (nn : K ≠ CallStack.nil) ->
                  P; gets ⊢ K WF-stack ->
                  P; K.tail; (gets.getD 0) ⊢ K.head! WF-frame
      | _K ⬝ _k, _nn, _Kwf ⬝wf kwf => kwf

    theorem head {P gets K k} (Kwf : P; gets ⊢ (K ⬝ k) WF-stack) :
                 P; K; (gets.getD 0) ⊢ k WF-frame :=
      head' (by simp) Kwf

    theorem tail {P gets K k} (Kwf : P; gets ⊢ (K ⬝ k) WF-stack) :
                 P; (some (k.ret! P)) ⊢ K WF-stack :=
      tail' (by simp) Kwf

    theorem current! {P K} (Kwf : P ⊢ K WF-stack) :
                     P; K.tail ⊢ K.head! WF-frame :=
      head! Kwf.nonnil Kwf

    theorem current {P K} (Kwf : P ⊢ K WF-stack) :
                    P; K.tail ⊢ (K.head Kwf.nonnil) WF-frame :=
      head' Kwf.nonnil Kwf
  end WF

  @[simp] def retjoin?! (P : Program) : (K : CallStack) -> Option Nat
    | .nil => none
    | .nil ⬝ k => some (k.ret! P)
    | K ⬝ _k => K.retjoin?! P
  
  theorem retjoin_eq_retjoin?! {P get} : {K : CallStack} -> (wf : P; get ⊢ K WF-stack) ->
          (if K = .nil then none else some (K.retjoin P)) = K.retjoin?! P
    | .nil, _wf =>
      rfl
    | .nil ⬝ k, (_ ⬝wf kwf) => by
      simp only [reduceCtorEq, if_false, retjoin?!, retjoin, StackFrame.ret!]
    | K ⬝ k ⬝ _k', wf =>
      retjoin_eq_retjoin?! (K := K ⬝ k) wf.tail

  @[simp] def bsig! (P : Program) (K : CallStack) : BlockSig :=
    ⟨K.head!.X.length,
     (P[K.head!.f]!.B[K.head!.b]!).r,
     K.head!.ρ.sig P[K.head!.f]!.B⟩
  @[simp] def bsig {P : Program} (K : CallStack) (wf : P ⊢ K WF-stack) : BlockSig :=
    let flt := wf.current.flt
    let blt := wf.current.blt
    ⟨(K.head wf.nonnil).X.length,
     (P[(K.head wf.nonnil).f].B[(K.head wf.nonnil).b]).r,
     (K.head wf.nonnil).ρ.sig P[(K.head wf.nonnil).f].B⟩
  @[simp] def bsig' {P : Program} : (K : CallStack) -> (wf : P ⊢ K WF-stack) -> BlockSig
    | K ⬝ ⟨f, ρ, X, b⟩, wf =>
      let flt := wf.current.flt
      let blt := wf.current.blt
      ⟨X.length, P[f].B[b].r, ρ.sig P[f].B⟩
  theorem bsig_eq_bsig' {P : Program} : {K : CallStack} -> (wf : P ⊢ K WF-stack) -> K.bsig wf = K.bsig' wf
    | _K ⬝ ⟨_f, _ρ, _X, _b⟩, _wf => rfl
  theorem bsig!_eq_bsig {P : Program} : {K : CallStack} -> (wf : P ⊢ K WF-stack) -> K.bsig wf = K.bsig! P
    | _K ⬝ ⟨f, _ρ, _X, b⟩, wf =>
      by simp only [bsig, getters, bsig!]
         rw[getElem!_pos P f wf.current.flt,
            getElem!_pos (P[f]'wf.current.flt).B b wf.current.blt]

  -- @[simp] def code! (P : Program) (K : CallStack) : Code :=
  --   K.head!.code! P
  @[simp] def code {P : Program} (K : CallStack) (wf : P ⊢ K WF-stack) : Code :=
    (K.head wf.nonnil).code wf.current

  namespace WF
    theorem append {P} : {K K' : CallStack} -> {gets : Option Nat} ->
                   P; (some (K'.retjoin P)) ⊢ K WF-stack -> P; gets ⊢ K' WF-stack ->
                   K' ≠ .nil -> K.allPromoted -> P; gets ⊢ (K ++ K') WF-stack
      | K, .nil ⬝ k, gets, Kwf, K'wf@(.nil ⬝wf kwf), _knn, kprom =>
        by simp; exact
          (Option.some_inj.mp (retjoin_eq_retjoin?! K'wf) ▸ Kwf) ⬝wf
          (kwf.changeStack (λ _ => kprom))
      | K, K' ⬝ k' ⬝ k, gets, Kwf, K'wf ⬝wf kwf, p, kprom =>
        (append Kwf K'wf (λ x => by contradiction) kprom) ⬝wf
          (kwf.changeStack (by simp[← ·, allPromoted_iff_nil.mp kprom]))

    theorem unappend {P} : {get : Option Nat} -> {K K' : CallStack} ->
                     P; get ⊢ (K ++ K') WF-stack -> (K' ≠ .nil) -> K.allPromoted ->
                     P; (some (K'.retjoin P)) ⊢ K WF-stack ∧ P; get ⊢ K' WF-stack
      | get, K, .nil ⬝ k, wf, _, kprom =>
        let wf' : P; get ⊢ (K ⬝ k) WF-stack :=
          by rw[@append_cons K .nil k] at wf; exact wf
        let k_wf : P; K; (get.getD 0) ⊢ k WF-frame :=
          wf'.head -- ⟨wf'.head.flt, wf'.head.blt, wf'.head.bsig, wf'.head.ρwf⟩
          --⟨wf'.head.flt, kprom ▸ wf'.head.ρwf, wf'.head.cwf⟩
        let nil_k_wf := .nil ⬝wf (k_wf.changeStack (K' := .nil) (λ _ => rfl))
        let rr : some ((.nil ⬝ k).retjoin P) = (.nil ⬝ k).retjoin?! P :=
          retjoin_eq_retjoin?! nil_k_wf
        ⟨rr ▸ wf'.tail, nil_k_wf⟩
      | get, K, (K' ⬝ k') ⬝ k, wf, _, kprom =>
        let ⟨Kwf, K'wf⟩ := unappend wf.tail (by simp) kprom
        let kprom' := allPromoted_iff_nil.mp kprom
        let kp : [] ++ (K' ⬝ k').unpr = K.unpr ++ (K' ⬝ k').unpr :=
          kprom'.symm ▸ rfl
        let k'wf : P; (K' ⬝ k'); (get.getD 0) ⊢ k WF-frame :=
          wf.head.changeStack (λ kap => by simp at kap; simp[kap])
        ⟨Kwf, K'wf ⬝wf k'wf⟩

    theorem code!_eq_code {P : Program} {K : CallStack} (Kwf : P ⊢ K WF-stack) : K.code! P = K.code Kwf :=
      by rw[CallStack.code!,
            CallStack.code,
            CallStack.head!_eq_head,
            Kwf.current.code!_eq_code]

    theorem code {P : Program} (Pwf : P WF-program) :
                 {K : CallStack} -> (Kwf : P ⊢ K WF-stack) ->
                 P.fsigs; (P[(K.head Kwf.nonnil).f]'Kwf.current.flt).B; (K.bsig Kwf) ⊢
                   (K.code Kwf) WF-code
      | K ⬝ k, Kwf ⬝wf kwf =>
        let flt := kwf.flt
        let blt : k.b < P[k.f].size :=
          by simpa using kwf.blt
        let Xlen : (P[k.f].B[k.b]'kwf.blt).Γ ≤ k.X.length :=
          by simpa only [Option.getD_none, Nat.add_zero] using kwf.bsig.1
        by simp only [getters, CallStack.code, StackFrame.code, CallStack.bsig]
           rw[← kwf.bsig.2,
              ← Nat.add_sub_of_le Xlen]
           simpa using Pwf⁅k.f⁆⁅k.b⁆.code.weaken_Γ

    theorem code! {P : Program} (Pwf : P WF-program) {K : CallStack} (Kwf : P ⊢ K WF-stack) :
                  P.fsigs; P[K.head!.f]!.B; (K.bsig! P) ⊢ (K.code! P) WF-code :=
      K.head!_eq_head Kwf.nonnil ▸
      getElem!_pos P (K.head Kwf.nonnil).f Kwf.current.flt ▸
      code!_eq_code Kwf ▸
      bsig!_eq_bsig Kwf ▸
      code Pwf Kwf

    theorem spawn {P : Program} {f : FuncIdx} {bspwn : SpawnBlock}
                  (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                  P ⊢ spawn f bspwn WF-stack :=
      .nil ⬝wf (.spawn flt bwf)
  end WF
end CallStack

namespace Thread
  inductive WF (P : Program) : Thread -> Prop where
    | mk {K c} :
         P ⊢ K WF-stack ->
         P.fsigs; P[K.head!.f]!.B; (K.bsig! P) ⊢ c WF-code ->
         WF P (K ⋄ c)

  namespace WF
    notation (name := notationwf) P:arg " ⊢ " T " WF-thread" => WF P T

    theorem K {P} {T : Thread} : (wf : P ⊢ T WF-thread) -> P ⊢ T.K WF-stack
      | .mk K _c => K
    theorem c! {P} {T : Thread} : P ⊢ T WF-thread ->
              P.fsigs; (P[T.K.head!.f]!).B; (T.K.bsig! P) ⊢ T.c WF-code
      | .mk _K c => c
    theorem c {P} {T : Thread} (wf : P ⊢ T WF-thread) :
              P.fsigs; (P[(T.K.head wf.K.nonnil).f]'wf.K.current.flt).B; (T.K.bsig wf.K) ⊢ T.c WF-code :=
      getElem!_pos P (T.K.head wf.K.nonnil).f wf.K.current.flt ▸
      T.K.head!_eq_head wf.K.nonnil ▸
      T.K.bsig!_eq_bsig wf.K ▸
      wf.c!

    theorem nonnil {P} {T : Thread} (wf : P ⊢ T WF-thread) : T.K ≠ .nil := wf.K.nonnil

    instance {P} : {T : Thread} -> Decidable (P ⊢ T WF-thread)
      | .nil ⋄ c => isFalse (λ p => by contradiction)
      | K ⬝ k ⋄ c =>
        decidable_of_iff (P ⊢ (K ⬝ k) WF-stack ∧
                          P.fsigs; P[k.f]!.B; ((K ⬝ k).bsig! P) ⊢ c WF-code)
          ⟨λ ⟨a, b⟩ => ⟨a, b⟩, λ ⟨a, b⟩ => ⟨a, b⟩⟩
  end WF

  @[simp] def fromStack {P : Program} (K : CallStack) (Kwf : P ⊢ K WF-stack) : Thread :=
    K ⋄ K.code Kwf

  @[simp] def spawn (P : Program) (f : FuncIdx) (bspwn : SpawnBlock)
                    (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) : Thread :=
    @fromStack P (.spawn f bspwn) (.spawn flt bwf)

  namespace WF
    theorem fromStack!_eq_fromStack {P K} (Kwf : P ⊢ K WF-stack) :
                                    fromStack! P K = fromStack K Kwf := by
      simp
      rw[K.head!_eq_head Kwf.nonnil,
         getElem!_pos P (K.head Kwf.nonnil).f Kwf.current.flt,
         getElem!_pos (P[(K.head Kwf.nonnil).f]'Kwf.current.flt) (K.head Kwf.nonnil).b Kwf.current.blt']

    theorem fromStack! {P K} (Pwf : P WF-program) (Kwf : P ⊢ K WF-stack) : P ⊢ fromStack! P K WF-thread :=
      .mk Kwf (Kwf.code! Pwf)

    theorem fromStack {P K} (Pwf : P WF-program) (Kwf : P ⊢ K WF-stack) : P ⊢ fromStack K Kwf WF-thread :=
      fromStack!_eq_fromStack Kwf ▸
      fromStack! Pwf Kwf

    theorem spawn!_eq_spawn {P f bspwn} (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                            spawn! P f bspwn = spawn P f bspwn flt bwf :=
      by simp; rw[codeOfGetElem flt bwf.b']

    theorem spawn! {P f bspwn} (Pwf : P WF-program) (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                   P ⊢ spawn! P f bspwn WF-thread :=
      fromStack! Pwf (.spawn flt bwf)
    
    theorem spawn {P f bspwn} (Pwf : P WF-program) (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                  P ⊢ spawn P f bspwn flt bwf WF-thread :=
      fromStack Pwf (.spawn flt bwf)
  end WF
end Thread

namespace ThreadTree
  inductive WF (P : Program) : ThreadTree -> Prop where
    | thread {T} :
           (Twf : P ⊢ T WF-thread) ->
           (thread T).WF P
    | node {Rp Rc} :
          (Rpwf : Rp.WF P) ->
          (Rcwf : Rc.WF P) ->
          ((Rp.promsig P).head? = some (Rc.retjoin P)) ->
          (Rc.prom = []) ->
          (Rp ⋏ Rc).WF P

  namespace WF
    notation (name := notationwf) P:arg " ⊢ " R " WF-tree" => WF P R

    theorem get {P T} : P ⊢ .thread T WF-tree -> P ⊢ T WF-thread
      | thread Twf => Twf
    theorem child {P Rp Rc} : P ⊢ Rp ⋏ Rc WF-tree -> Rc.WF P
      | node _Rpwf Rcwf _Rpprom _Rcprom => Rcwf
    theorem parent {P Rp Rc} : (Rp ⋏ Rc).WF P -> Rp.WF P
      | node Rpwf _Rcwf _Rprom _Rcprom => Rpwf
    theorem parent_prom {P Rp Rc} : (Rp ⋏ Rc).WF P ->
                                 (Rp.promsig P).head? = some (Rc.retjoin P)
      | node _Rpwf _Rcwf Rpprom _Rcprom => Rpprom
    theorem child_prom {P Rp Rc} : (Rp ⋏ Rc).WF P -> Rc.prom = []
      | node _Rpwf _Rcwf _Rpprom Rcprom => Rcprom

    instance instDecidable {P} : (R : ThreadTree) -> Decidable (R.WF P)
      | .thread T => decidable_of_iff (P ⊢ T WF-thread)
          ⟨thread, λ | thread Kwf => Kwf⟩
      | Rp ⋏ Rc =>
        let _ : Decidable (Rp.WF P) := instDecidable Rp
        let _ : Decidable (Rc.WF P) := instDecidable Rc
        decidable_of_iff (Rp.WF P ∧
                          Rc.WF P ∧
                          (Rp.promsig P).head? = some (Rc.retjoin P) ∧
                          Rc.prom = [])
          ⟨λ ⟨Rwf, Rcwf, Rp, Rcp⟩ => node Rwf Rcwf Rp Rcp,
           λ | node Rwf Rcwf Rp Rcp => ⟨Rwf, Rcwf, Rp, Rcp⟩⟩
  end WF

  @[simp] def spawn (P : Program) (f : FuncIdx) (bspwn : SpawnBlock)
                    (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) : ThreadTree :=
    thread (.spawn P f bspwn flt bwf)

  @[simp] def init (P : Program) (Pwf : P WF-program) : ThreadTree :=
    let main := 0 -- first function in program is main()
    let entry := SpawnBlock.mk 0 [] -- entry block with no args (since main takes none)
    let zlt := Pwf.main.zero_lt
    spawn P main entry zlt (.init Pwf)

  namespace WF
    theorem spawn!_eq_spawn {P f bspwn} (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                            spawn! P f bspwn = spawn P f bspwn flt bwf := by
      simp only [spawn!, spawn]
      rw[Thread.WF.spawn!_eq_spawn flt bwf]
    
    theorem spawn! {P f bspwn} (Pwf : P WF-program) (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                   P ⊢ spawn! P f bspwn WF-tree :=
      .thread (.spawn! Pwf flt bwf)

    theorem spawn {P f bspwn} (Pwf : P WF-program) (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                  P ⊢ spawn P f bspwn flt bwf WF-tree :=
      .thread (.spawn Pwf flt bwf)

    theorem init!_eq_init {P} (Pwf : P WF-program) : init! P = init P Pwf :=
      by simp only [init!, init]
         rw[spawn!_eq_spawn Pwf.main.zero_lt (by simpa using .init Pwf)]
    
    theorem init! {P} (Pwf : P WF-program) : P ⊢ init! P WF-tree :=
      spawn! Pwf Pwf.main.zero_lt (.init Pwf)

    theorem init {P} (Pwf : P WF-program) : P ⊢ init P Pwf WF-tree :=
      spawn Pwf Pwf.main.zero_lt (.init Pwf)
  end WF
end ThreadTree
