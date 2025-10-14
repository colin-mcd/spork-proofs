abbrev Val := Int

abbrev Scope := Nat
abbrev Params := Nat

inductive Var where
  | mk (v : Nat)

abbrev BlockIdx := Nat
abbrev FuncIdx := Nat

inductive Atom
  | val (v : Val)
  | var (v : Var)

inductive Uop where
  | INEG | LNOT

inductive Bop where
  | IADD | ISUB | IMUL | IDIV  | IMOD
  | ILT | ILE | IGT | IGE | IEQ | INE
  | LAND | LOR | LXOR

inductive Expr where
  | nop (a : Atom)
  | uop (o : Uop) (a : Atom)
  | bop (o : Bop) (a b : Atom)

inductive Cont where
  | mk (b : BlockIdx) (args : List Var)

inductive Code where
  | stmt (e : Expr) (c : Code)
  | goto (bnext : Cont)
  | ite (cond : Atom) (bthen : Cont) (belse : Cont)
  | call (f : FuncIdx) (args : List Var) (bret : Cont)
  | retn (args : List Var)
  | spork (bbody : Cont) (bspwn : Cont)
  | spoin (bunpr : Cont) (bprom : Cont)
  -- | join (bsync : Cont)
  -- | exit (args : List Var)

-- Obligation to return, exit, spoin, or join
-- inductive Oblg where
--   | retn (n : Nat)
--   | exit (n : Nat)
--   | spoin (σ : Oblg) (n : Nat)
--   | join (σ : Oblg) (n : Nat)

-- block with a local scope Γ which must return r values and obligated to spoin σ
inductive BlockSig where
  | mk (Γ : Nat) (r : Nat) (σ : List Nat)

inductive Block where
  | mk (bsig : BlockSig) (code : Code)

inductive FuncSig where
  | mk (params : Params) (ret : Nat)

inductive Func where
  | mk (fsig : FuncSig) (blocks : List Block)

inductive Program where
  | mk (funs : List Func)


abbrev FuncSigs := List FuncSig
abbrev BlockSigs := List BlockSig

/-
namespace Oblg
--  @[simp] abbrev spoin
  deriving instance DecidableEq for Oblg

  inductive isRetn : Oblg -> Prop where
    | mk (n : Nat) : (retn n).isRetn
  inductive isExit : Oblg -> Prop where
    | mk (n : Nat) : (exit n).isExit
  inductive isSpoin : Oblg -> Prop where
    | mk (σ : Oblg) (n : Nat) : (σ.spoin n).isSpoin
  inductive isJoin : Oblg -> Prop where
    | mk (σ : Oblg) (n : Nat) : (σ.join n).isJoin
  -- inductive isRetnN : Oblg -> Nat -> Prop where
  --   | mk (n : Nat) : (retn n).isRetnN n
  -- inductive isExitN : Oblg -> Nat -> Prop where
  --   | mk (n : Nat) : (exit n).isExitN n

  instance : {σ : Oblg} -> Decidable σ.isRetn := by
    intro σ; cases σ <;> try exact .isFalse (by intro; contradiction)
    · case retn n => exact .isTrue (.mk n)
  instance : {σ : Oblg} -> Decidable σ.isExit := by
    intro σ; cases σ <;> try exact .isFalse (by intro; contradiction)
    · case exit n => exact .isTrue (.mk n)
  instance : {σ : Oblg} -> Decidable σ.isSpoin := by
    intro σ; cases σ <;> try exact .isFalse (by intro; contradiction)
    · case spoin σ n => exact .isTrue (.mk σ n)
  instance : {σ : Oblg} -> Decidable σ.isJoin := by
    intro σ; cases σ <;> try exact .isFalse (by intro; contradiction)
    · case join σ n => exact .isTrue (.mk σ n)
  -- instance : {σ : Oblg} -> {n : Nat} -> Decidable (σ.isRetnN n) := by
  --   intro σ n; cases σ <;> try exact .isFalse (by intro; contradiction)
  --   · case retn n' => exact decidable_of_iff (n = n')
  --                       ⟨λ h => by rw[h]; exact .mk n', λ | .mk n'' => rfl⟩
  -- instance : {σ : Oblg} -> {n : Nat} -> Decidable (σ.isExitN n) := by
  --   intro σ n; cases σ <;> try exact .isFalse (by intro; contradiction)
  --   · case exit n' => exact decidable_of_iff (n = n')
  --                       ⟨λ h => by rw[h]; exact .mk n', λ | .mk n'' => rfl⟩

  @[simp] abbrev getRetn : (σ : Oblg) -> σ.isRetn -> Nat
    | retn n, _ => n
  @[simp] abbrev getExit : (σ : Oblg) -> σ.isExit -> Nat
    | exit n, _ => n
  @[simp] abbrev getSpoin : (σ : Oblg) -> σ.isSpoin -> Oblg × Nat
    | spoin σ n, _ => ⟨σ, n⟩
  @[simp] abbrev getJoin : (σ : Oblg) -> σ.isJoin -> Oblg × Nat
    | join σ n, _ => ⟨σ, n⟩

  @[simp] abbrev head : Oblg -> Nat
    | retn n => n
    | exit n => n
    | spoin _σ n => n
    | join _σ n => n
  @[simp] abbrev tail : Oblg -> Oblg
    | retn n => retn n
    | exit n => exit n
    | spoin σ _n => σ
    | join σ _n => σ
  @[simp] abbrev last : Oblg -> Nat
    | retn n => n
    | exit n => n
    | spoin σ _n => σ.last
    | join σ _n => σ.last
  @[simp] abbrev sig : Oblg -> List Nat
    | retn _n => []
    | exit _n => []
    | spoin σ n => n :: σ.sig
    | join σ n => n :: σ.sig


  inductive RetnExit | Retn | Exit
  inductive SpoinJoin | Spoin | Join
  deriving instance DecidableEq for RetnExit
  deriving instance DecidableEq for SpoinJoin

  abbrev POblg : Type := (RetnExit × Nat) × List (SpoinJoin × Nat)
  def POblg_Oblg : POblg -> Oblg
    | ((.Retn, n), []) => .retn n
    | ((.Exit, n), []) => .exit n
    | (ren, (.Spoin, n) :: ρ) => (POblg_Oblg (ren, ρ)).spoin n
    | (ren, (.Join, n) :: ρ) => (POblg_Oblg (ren, ρ)).join n
  @[simp] theorem POblg_Oblg_Retn (n : Nat) : POblg_Oblg ((.Retn, n), []) = .retn n := by simp[POblg_Oblg]
  @[simp] theorem POblg_Oblg_Exit (n : Nat) : POblg_Oblg ((.Exit, n), []) = .exit n := by simp[POblg_Oblg]
  @[simp] theorem POblg_Oblg_Spoin (ren : RetnExit × Nat) (n : Nat) (ρ : List (SpoinJoin × Nat)) : POblg_Oblg (ren, (.Spoin, n) :: ρ) = (POblg_Oblg (ren, ρ)).spoin n := by simp[POblg_Oblg]
  @[simp] theorem POblg_Oblg_Join (ren : RetnExit × Nat) (n : Nat) (ρ : List (SpoinJoin × Nat)) : POblg_Oblg (ren, (.Join, n) :: ρ) = (POblg_Oblg (ren, ρ)).join n := by simp[POblg_Oblg]

  @[simp] abbrev Oblg_POblg : Oblg -> POblg
    | .retn n => ((.Retn, n), [])
    | .exit n => ((.Exit, n), [])
    | .spoin σ n => let (ren, ρ) := Oblg_POblg σ
                    (ren, (.Spoin, n) :: ρ)
    | .join σ n => let (ren, ρ) := Oblg_POblg σ
                   (ren, (.Join, n) :: ρ)

  @[simp] theorem POblg_Oblg_POblg : (ρ : POblg) -> Oblg_POblg (POblg_Oblg ρ) = ρ
    | ((.Retn, n), []) => by simp
    | ((.Exit, n), []) => by simp
    | (ren, (.Spoin, n) :: ρ) => by simp[POblg_Oblg_POblg (ren, ρ)]
    | (ren, (.Join, n) :: ρ) => by simp[POblg_Oblg_POblg (ren, ρ)]

  @[simp] theorem Oblg_POblg_Oblg : (σ : Oblg) -> POblg_Oblg (Oblg_POblg σ) = σ
    | .retn n => by simp
    | .exit n => by simp
    | .spoin σ n => by simp[Oblg_POblg_Oblg σ]
    | .join σ n => by simp[Oblg_POblg_Oblg σ]
end Oblg
-/

namespace BlockSig
  @[simp] abbrev Γ | mk Γ _r _σ => Γ
  @[simp] abbrev r | mk _Γ r _σ => r
  @[simp] abbrev σ | mk _Γ _r σ => σ
  @[simp] abbrev bind | mk Γ r σ => mk Γ.succ r σ
  -- @[simp] abbrev retn | mk Γ _σ, n => mk Γ (Oblg.retn n)
  -- @[simp] abbrev exit | mk Γ _σ, n => mk Γ (Oblg.exit n)
  -- @[simp] abbrev spoin | mk Γ σ, n => mk Γ (σ.spoin n)
  -- @[simp] abbrev join | mk Γ σ, n => mk Γ (σ.join n)
  -- @[simp] abbrev head | mk _Γ σ => σ.head
  -- @[simp] abbrev tail | mk Γ σ => mk Γ σ.tail
  @[simp] abbrev binds | mk Γ r σ, Γ' => mk (Γ + Γ') r σ
--  @[simp] abbrev join

  @[simp] abbrev spork | mk Γ r σ, s => mk Γ r (s :: σ)
  @[simp] abbrev spoin | mk Γ r σ => mk Γ r σ.tail
  @[simp] abbrev spwn | mk Γ _r _σ, n => mk Γ n []
  -- @[simp] abbrev spoin_unpr | mk Γ r σ => mk Γ r σ.tail
  -- @[simp] abbrev spoin_prom : (bsig : BlockSig) -> bsig.σ ≠ [] -> BlockSig
  --   | mk Γ r (s :: σ),

  deriving instance DecidableEq for BlockSig
  -- instance : Inhabited BlockSig := ⟨0, .exit 1⟩
  instance : Inhabited BlockSig := ⟨0, 1, []⟩

  -- @[simp] def add (a b : BlockSig) :=
  --   mk (a.arity + b.arity) (a.sporkNest ++ b.sporkNest)

  -- instance : Add BlockSig where
  --   add := add

  -- @[simp] theorem add_arity (a b : BlockSig) : (a + b).arity = a.arity + b.arity :=
  --   by simp
  -- @[simp] theorem add_sporkNest (a b : BlockSig) : (a + b).sporkNest = a.sporkNest ++ b.sporkNest :=
  --   by simp
  -- @[simp] theorem add_unfolded (a a' sn sn') : (mk a sn) + (mk a' sn') = mk (a + a') (sn ++ sn') :=
  --   rfl
  -- @[simp] theorem add_zero : (a : BlockSig) -> (a + .mk 0 []) = a
  --   | .mk arity sn => by simp
end BlockSig

namespace FuncSig
  @[simp] abbrev arity | mk a _r => a
  @[simp] abbrev ret | mk _a r => r

  deriving instance DecidableEq, Inhabited for FuncSig
end FuncSig

namespace Var
  @[simp] abbrev idx | mk v => v

  @[simp] abbrev inc | mk v, n => mk (v + n)

  deriving instance DecidableEq for Var

  instance {n} : OfNat Var n where
    ofNat := Var.mk n
  instance : Coe Nat Var where
    coe := mk
  instance : Coe Var Nat where
    coe := idx
end Var

namespace Atom
  deriving instance DecidableEq for Atom
end Atom

namespace Uop
  deriving instance DecidableEq for Uop
end Uop

namespace Bop
  deriving instance DecidableEq for Bop
end Bop

namespace Expr
  deriving instance DecidableEq for Expr
end Expr

namespace Cont
  deriving instance DecidableEq for Cont

  @[simp] abbrev b | mk b _args => b
  @[simp] abbrev args | mk _b args => args
end Cont

namespace Code
  deriving instance DecidableEq for Code

  @[simp] def split : Code -> List Expr × (c : Code) ×' (∀ e, ∀ c', c ≠ .stmt e c')
    | stmt e c => let (es, cp) := c.split
                  (e :: es, cp)
    | goto bnext => ([], ⟨goto bnext, by intros e c; simp⟩)
    | ite e bthen belse => ([], ⟨ite e bthen belse, by intros e c; simp⟩)
    | call g args bret => ([], ⟨call g args bret, by intros e c; simp⟩)
    | retn args => ([], ⟨retn args, by intros e c; simp⟩)
    | spork bbody bspwn => ([], ⟨spork bbody bspwn, by intros e c; simp⟩)
    | spoin bunpr bprom => ([], ⟨spoin bunpr bprom, by intros e c; simp⟩)
    -- | join bsync => ([], ⟨join bsync, by intros e c; simp⟩)
    -- | exit args => ([], ⟨exit args, by intros e c; simp⟩)

  @[simp] def merge : List Expr -> Code -> Code
    | [], c => c
    | e :: es, c => stmt e (merge es c)

  @[simp] theorem merge_split {c e c' p} (q : split c = (e, ⟨c', p⟩)) : merge e c' = c := by
    cases c <;> try (cases e <;> simp_all)
    · case stmt e' es' e'' es'' =>
      exact merge_split (Prod.ext q.1.2 q.2)
end Code

namespace Block
  @[simp] abbrev bsig | mk bsig _code => bsig
  @[simp] abbrev code | mk _bsig code => code

  deriving instance DecidableEq for Block

  instance : Inhabited Block where
    default := mk ⟨0, 0, []⟩ (.retn [])
             --mk ⟨0, .retn 0⟩ (.retn [])
end Block


namespace Func
  @[simp] abbrev fsig | mk fsig _blocks => fsig
  @[simp] abbrev blocks | mk _fsig blocks => blocks
  @[simp] abbrev B : Func -> BlockSigs | mk _fsig blocks => blocks.map (·.bsig)
  @[simp] abbrev size | mk _fsig blocks => blocks.length

  @[simp] theorem size_eq_B_length (f : Func) : f.B.length = f.size :=
    by simp

  deriving instance DecidableEq for Func

  instance : Inhabited Func where
    default := mk ⟨0, 0⟩ default

  instance : GetElem Func BlockIdx Block (λ f b => b < f.blocks.length) where
    getElem f b p := f.blocks[b]
end Func

namespace Program
  @[simp] abbrev funs | mk funs => funs
  @[simp] abbrev fsigs : Program -> FuncSigs
    | mk funs => funs.map (·.fsig)
  @[simp] abbrev size : Program -> Nat
    | mk funs => funs.length

  @[simp] theorem size_eq_fsigs_length (P : Program) : P.fsigs.length = P.size :=
    by simp

  deriving instance DecidableEq for Program

  instance : GetElem Program FuncIdx Func (λ P f => f < P.size) where
    getElem P f p := P.funs[f]
end Program
