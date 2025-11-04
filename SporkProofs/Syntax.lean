import SporkProofs.SimpSet

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

inductive ResultSig where
  | retn (r : Nat)
  | exit (e : Nat)
deriving Repr, DecidableEq

-- block with a local scope Γ which must return r values and obligated to spoin σ
inductive BlockSig where
  | mk (Γ : Scope) (r : ResultSig) (σ : List Nat)

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

namespace ResultSig
  def n
    | retn n => n
    | exit n => n

  universe u
  def elimD {α : ResultSig -> Type u} (r : (n : Nat) -> α (retn n)) (e : (n : Nat) -> α (exit n)) : (r : ResultSig) -> α r
    | retn n => r n
    | exit n => e n
  def elim {α : Type u} (r : Nat -> α) (e : Nat -> α) : ResultSig -> α
    | retn n => r n
    | exit n => e n

  @[simp] def isRetn
    | retn _n => true
    | exit _n => false
  @[simp] def isExit
    | retn _n => false
    | exit _n => true

  @[simp] theorem isRetn_neq_isExit {r} : isRetn r ≠ isExit r :=
    by cases r <;> simp

  def getRetn : (r : ResultSig) -> r.isRetn -> Nat
    | .retn n, _ => n

  def getExit : (r : ResultSig) -> r.isExit -> Nat
    | .exit n, _ => n

  theorem isRetn_eq : {r : ResultSig} -> r.isRetn -> r = .retn r.n
    | .retn _n, _ => rfl
  theorem isExit_eq : {r : ResultSig} -> r.isExit -> r = .exit r.n
    | .exit _n, _ => rfl
  theorem not_isRetn_isExit : {r : ResultSig} -> ¬ r.isRetn -> r.isExit
    |.exit _n, _nr => rfl
  theorem not_isExit_isRetn : {r : ResultSig} -> ¬ r.isExit -> r.isRetn
    |.retn _n, _ne => rfl
  
  @[simp, getters] theorem get_retn_n {n} : (retn n).n = n := rfl
  @[simp, getters] theorem get_exit_n {n} : (exit n).n = n := rfl
  @[simp, getters] theorem get_getRetn_n {n} : (retn n).getRetn rfl = n := rfl
  @[simp, getters] theorem get_getExit_n {n} : (exit n).getExit rfl = n := rfl
  @[simp, getters] theorem get_isRetn {n} : (retn n).isRetn = true := rfl
  @[simp, getters] theorem get_isExit {n} : (exit n).isExit = true := rfl
  @[simp, getters] theorem get_elim_r {α n} {r e : Nat -> α} : (retn n).elim r e = r n := rfl
  @[simp, getters] theorem get_elim_e {α n} {r e : Nat -> α} : (exit n).elim r e = e n := rfl
  @[simp, getters] theorem get_elim_fix {r} : elim retn exit r = r := by cases r <;> simp
  
  instance : Inhabited ResultSig where
    default := retn 0
end ResultSig

namespace BlockSig
  def Γ | mk Γ _r _σ => Γ
  def r | mk _Γ r _σ => r
  def σ | mk _Γ _r σ => σ
  def bind | mk Γ r σ => mk Γ.succ r σ
  def binds | mk Γ r σ, Γ' => mk (Γ + Γ') r σ
  def spork | mk Γ r σ, s => mk Γ r (s :: σ)
  def spoin | mk Γ r σ => mk Γ r σ.tail
  def spwn | mk Γ _r _σ, n => mk Γ (.exit n) []

  @[simp, getters] theorem get_fix {b} : mk b.Γ b.r b.σ = b := rfl
  @[simp, getters] theorem get_1 {b : BlockSig} : b.1 = b.Γ := rfl
  @[simp, getters] theorem get_2 {b : BlockSig} : b.2 = b.r := rfl
  @[simp, getters] theorem get_3 {b : BlockSig} : b.3 = b.σ := rfl
  @[simp, getters] theorem get_Γ {Γ r σ} : (mk Γ r σ).Γ = Γ := rfl
  @[simp, getters] theorem get_r {Γ r σ} : (mk Γ r σ).r = r := rfl
  @[simp, getters] theorem get_σ {Γ r σ} : (mk Γ r σ).σ = σ := rfl
  @[simp, getters] theorem get_bind {Γ r σ} : (mk Γ r σ).bind = mk Γ.succ r σ := rfl
  @[simp, getters] theorem get_binds {Γ r σ Γ'} : (mk Γ r σ).binds Γ' = mk (Γ + Γ') r σ := rfl
  @[simp, getters] theorem get_spork {Γ r σ s} : (mk Γ r σ).spork s = mk Γ r (s :: σ) := rfl
  @[simp, getters] theorem get_spoin {Γ r σ} : (mk Γ r σ).spoin = mk Γ r σ.tail := rfl
  @[simp, getters] theorem get_spwn {Γ r σ n} : (mk Γ r σ).spwn n = mk Γ (.exit n) [] := rfl

  deriving instance Repr, DecidableEq, Inhabited for BlockSig
end BlockSig

namespace FuncSig
  def arity | mk a _r => a
  def ret | mk _a r => r
  
  @[simp, getters] theorem get_fix {f : FuncSig} : mk f.arity f.ret = f := rfl
  @[simp, getters] theorem get_1 {f : FuncSig} : f.1 = f.arity := rfl
  @[simp, getters] theorem get_2 {f : FuncSig} : f.2 = f.ret := rfl
  @[simp, getters] theorem get_arity {a r} : (mk a r).arity = a := rfl
  @[simp, getters] theorem get_ret {a r} : (mk a r).ret = r := rfl

  deriving instance Repr, DecidableEq, Inhabited for FuncSig
end FuncSig

namespace Var
  def idx | mk v => v
  def inc (v : Var) (n : Nat) := mk (v.idx + n)

  @[simp, getters] theorem get_fix {v : Var} : mk v.idx = v := rfl
  @[simp, getters] theorem get_1 {v : Var} : v.1 = v.idx := rfl
  @[simp, getters] theorem get_idx {i} : (mk i).idx = i := rfl
  @[simp, getters] theorem get_inc {i n} : (mk i).inc n = mk (i + n) := rfl

  deriving instance Repr, DecidableEq for Var

  instance {n} : OfNat Var n where
    ofNat := Var.mk n
  instance : Coe Nat Var where
    coe := mk
  instance : Coe Var Nat where
    coe := idx
end Var

namespace Atom
  deriving instance Repr, DecidableEq for Atom
end Atom

namespace Uop
  deriving instance Repr, DecidableEq for Uop
end Uop

namespace Bop
  deriving instance Repr, DecidableEq for Bop
end Bop

namespace Expr
  deriving instance Repr, DecidableEq for Expr
end Expr

namespace Cont
  deriving instance Repr, DecidableEq for Cont

  def b | mk b _args => b
  def args | mk _b args => args

  @[simp, getters] theorem get_fix {c : Cont} : mk c.b c.args = c := rfl
  @[simp, getters] theorem get_1 {c : Cont} : c.1 = c.b := rfl
  @[simp, getters] theorem get_2 {c : Cont} : c.2 = c.args := rfl
  @[simp, getters] theorem get_b {b args} : (mk b args).b = b := rfl
  @[simp, getters] theorem get_args {b args} : (mk b args).args = args := rfl

  def offset_B (B : Nat) (c : Cont) := mk (c.b + B) c.args
  
  @[simp, getters] theorem offset_B_b {B c} : (offset_B B c).b = c.b + B := rfl
  @[simp, getters] theorem offset_B_args {B c} : (offset_B B c).args = c.args := rfl
end Cont

namespace Code
  deriving instance Repr, DecidableEq for Code
  instance : Inhabited Code where
    default := retn []

  @[simp] def split : Code -> List Expr × (c : Code) ×' (∀ e, ∀ c', c ≠ .stmt e c')
    | stmt e c => let (es, cp) := c.split
                  (e :: es, cp)
    | goto bnext => ([], ⟨goto bnext, by intros e c; simp⟩)
    | ite e bthen belse => ([], ⟨ite e bthen belse, by intros e c; simp⟩)
    | call g args bret => ([], ⟨call g args bret, by intros e c; simp⟩)
    | retn args => ([], ⟨retn args, by intros e c; simp⟩)
    | spork bbody bspwn => ([], ⟨spork bbody bspwn, by intros e c; simp⟩)
    | spoin bunpr bprom => ([], ⟨spoin bunpr bprom, by intros e c; simp⟩)

  @[simp] def merge : List Expr -> Code -> Code
    | [], c => c
    | e :: es, c => stmt e (merge es c)

  @[simp] theorem merge_split {c e c' p} (q : split c = (e, ⟨c', p⟩)) : merge e c' = c := by
    cases c <;> try (cases e <;> simp_all)
    · case stmt e' es' e'' es'' =>
      exact merge_split (Prod.ext q.1.2 q.2)

  def offset_B (B : Nat) : Code -> Code
    | stmt e c => stmt e (c.offset_B B)
    | goto bnext => goto (bnext.offset_B B)
    | ite cond bthen belse => ite cond (bthen.offset_B B) (belse.offset_B B)
    | call g args bret => call g args (bret.offset_B B)
    | retn args => retn args
    | spork bbody bspwn => spork (bbody.offset_B B) (bspwn.offset_B B)
    | spoin bunpr bprom => spoin (bunpr.offset_B B) (bprom.offset_B B)
end Code

namespace Block
  deriving instance Repr, DecidableEq, Inhabited for Block

  def bsig | mk bsig _code => bsig
  def code | mk _bsig code => code

  @[simp, getters] theorem get_fix {b : Block} : mk b.bsig b.code = b := rfl
  @[simp, getters] theorem get_1 {b : Block} : b.1 = b.bsig := rfl
  @[simp, getters] theorem get_2 {b : Block} : b.2 = b.code := rfl
  @[simp, getters] theorem get_bsig {bsig c} : (mk bsig c).bsig = bsig := rfl
  @[simp, getters] theorem get_code {bsig c} : (mk bsig c).code = c := rfl

  @[simp] def offset_B (B : Nat) (b : Block) := mk b.bsig (b.code.offset_B B)
end Block


namespace Func
  def fsig | mk fsig _blocks => fsig
  def blocks | mk _fsig blocks => blocks

  @[simp, getters] theorem get_fix {f : Func} : mk f.fsig f.blocks = f := rfl
  @[simp, getters] theorem get_1 {f : Func} : f.1 = f.fsig := rfl
  @[simp, getters] theorem get_2 {f : Func} : f.2 = f.blocks := rfl
  @[simp, getters] theorem get_fsig {fsig blocks} : (mk fsig blocks).fsig = fsig := rfl
  @[simp, getters] theorem get_blocks {fsig blocks} : (mk fsig blocks).blocks = blocks := rfl

  @[simp] abbrev B (f : Func) : BlockSigs :=
    f.blocks.map (·.bsig)
  @[simp] abbrev size (f : Func) :=
    f.blocks.length
  @[simp] abbrev entry (f : Func) :=
    f.blocks[0]!.code

  @[simp] theorem size_eq_B_length (f : Func) : f.B.length = f.size :=
    by simp

  @[simp] def offset_B (B : Nat) (f : Func) := mk f.fsig (f.blocks.map (Block.offset_B B))

  deriving instance Repr, DecidableEq for Func

  instance : Inhabited Func where
    default := mk ⟨0, 0⟩ default

  instance : GetElem Func BlockIdx Block (λ f b => b < f.size) where
    getElem f b p := f.blocks[b]
end Func

namespace Program
  def funs | mk funs => funs

  @[simp, getters] theorem get_fix {P : Program} : mk P.funs = P := rfl
  @[simp, getters] theorem get_1 {P : Program} : P.1 = P.funs := rfl
  @[simp, getters] theorem get_funs {funs} : (mk funs).funs = funs := rfl

  @[simp] abbrev fsigs (P : Program) : FuncSigs :=
    P.funs.map (·.fsig)
  @[simp] abbrev size (P : Program) : Nat :=
    P.funs.length

  @[simp] theorem size_eq_fsigs_length (P : Program) : P.fsigs.length = P.size :=
    by simp

  deriving instance Repr, DecidableEq for Program

  instance : GetElem Program FuncIdx Func (λ P f => f < P.size) where
    getElem P f p := P.funs[f]
end Program
