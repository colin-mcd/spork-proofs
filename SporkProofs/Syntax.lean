import SporkProofs.IVec
import SporkProofs.HeadIs

abbrev Val := Int

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
  | spork (n : Nat) (bbody : Cont) (bspwn : Cont)
  | spoin (bunpr : Cont) (bprom : Cont)
  | join (bsync : Cont)
  | exit (args : List Var)

--abbrev SporkSig := List Nat
-- Obligation to return, exit, spoin, or join
inductive Oblg where
  | retn (n : Nat)
  | exit (n : Nat)
  | spoin (σ : Oblg) (n : Nat)
  | join (σ : Oblg) (n : Nat)

-- block with `arity` args and nested under `sporks`
inductive BlockSig where
  | mk (arity : Nat) (oblg : Oblg)

inductive Block where
  | mk (bsig : BlockSig) (code : Code)

inductive FuncSig where
  | mk (arity : Nat) (ret : Nat)

inductive Func where
  | mk (fsig : FuncSig) (blocks : List Block)

inductive Program where
  | mk (funs : List Func) (main: List Block)

abbrev Scope := Nat
abbrev FuncSigs := List FuncSig
abbrev BlockSigs := List BlockSig

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
  
end Oblg

namespace BlockSig
  @[simp] abbrev arity | mk a _σ => a
  @[simp] abbrev oblg | mk _a σ => σ
  @[simp] abbrev bind | mk a σ => mk a.succ σ
  @[simp] abbrev retn | mk a _σ, n => mk a (Oblg.retn n)
  @[simp] abbrev exit | mk a _σ, n => mk a (Oblg.exit n)
  @[simp] abbrev spoin | mk a σ, n => mk a (σ.spoin n)
  @[simp] abbrev join | mk a σ, n => mk a (σ.join n)
  @[simp] abbrev head | mk _a σ => σ.head
  @[simp] abbrev tail | mk a σ => mk a σ.tail
  @[simp] abbrev binds | mk a σ, b => mk (a + b) σ
--  @[simp] abbrev join

  -- @[simp] abbrev spork | mk a σ, s => mk a (SporkSig.spwn σ s)
  -- @[simp] abbrev spoin | mk a σ => mk a σ.tail

  deriving instance DecidableEq for BlockSig

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

namespace Var
  inductive WF (Γ : Scope) (v : Var) : Prop where
    | mk : v.idx < Γ -> v.WF Γ

  namespace WF
    notation (name := wfnotation) Γ:arg " ⊢ " v:arg " WF-var" => WF Γ v

    theorem idx {Γ : Scope} {v : Var} : Γ ⊢ v WF-var -> v.idx < Γ | .mk idx => idx

    instance {Γ : Scope} {v : Var} : Decidable (Γ ⊢ v WF-var) :=
      decidable_of_iff (v.idx < Γ) ⟨(⟨·⟩), (·.1)⟩

    theorem weakening {Γ Γ'} {v : Var} (wf : Γ ⊢ v WF-var) : (Γ + Γ') ⊢ v WF-var :=
      .mk (Nat.lt_add_right Γ' wf.idx)
  end WF
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
    | spork n bbody bspwn => ([], ⟨spork n bbody bspwn, by intros e c; simp⟩)
    | spoin bunpr bprom => ([], ⟨spoin bunpr bprom, by intros e c; simp⟩)
    | join bsync => ([], ⟨join bsync, by intros e c; simp⟩)
    | exit args => ([], ⟨exit args, by intros e c; simp⟩)

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
    default := mk ⟨0, .retn 0⟩ (.retn [])
end Block


namespace Func
  @[simp] abbrev fsig | mk fsig _blocks => fsig
  @[simp] abbrev blocks | mk _fsig blocks => blocks
  @[simp] abbrev bsigs : Func -> BlockSigs | mk _fsig blocks => blocks.map (·.bsig)
  @[simp] abbrev size | mk _fsig blocks => blocks.length

  @[simp] theorem size_eq_bsigs_length (f : Func) : f.bsigs.length = f.size :=
    by simp

  deriving instance DecidableEq for Func

  instance : Inhabited Func where
    default := mk ⟨0, 0⟩ default

  instance : GetElem Func BlockIdx Block (λ f b => b < f.blocks.length) where
    getElem f b p := f.blocks[b]
end Func

namespace Program
  @[simp] abbrev funs | mk funs _main => funs
  @[simp] abbrev main | mk _funs main => main
  @[simp] abbrev fsigs : Program -> FuncSigs
    | mk funs _main => funs.map (·.fsig)
  @[simp] abbrev size : Program -> Nat
    | mk funs _main => funs.length

  @[simp] theorem size_eq_fsigs_length (P : Program) : P.fsigs.length = P.size :=
    by simp

  deriving instance DecidableEq for Program

  instance : GetElem Program FuncIdx Func (λ P f => f < P.size) where
    getElem P f p := P.funs[f]
end Program

/- ==================== Well-Formedness Rules ==================== -/

namespace Atom
  inductive WF (Γ : Scope) : Atom -> Prop where
    | val {v : Val} : (val v).WF Γ
    | var {v : Var} : Γ ⊢ v WF-var -> (var v).WF Γ

  namespace WF
    notation (name := wfnotation) Γ:arg " ⊢ " a:arg " WF-atom" => WF Γ a

    instance {Γ : Scope} : (a : Atom) -> Decidable (Γ ⊢ a WF-atom)
      | .val _v => isTrue val
      | .var v => decidable_of_iff (Γ ⊢ v WF-var) ⟨var, λ (var v) => v⟩

    theorem vwf {Γ : Scope} {v : Var} : Γ ⊢ (Atom.var v) WF-atom -> Γ ⊢ v WF-var
      | .var wf => wf

    theorem weakening {Γ Γ'} {a : Atom} : Γ ⊢ a WF-atom -> (Γ + Γ') ⊢ a WF-atom
      | .val => .val
      | .var wf => .var wf.weakening
  end WF
end Atom

namespace Expr  
  inductive WF (Γ : Scope) : Expr -> Prop where
    | nop {a : Atom} : Γ ⊢ a WF-atom -> (nop a).WF Γ
    | uop {o : Uop} {a : Atom} : Γ ⊢ a WF-atom -> (uop o a).WF Γ
    | bop {o : Bop} {a b : Atom} : Γ ⊢ a WF-atom -> Γ ⊢ b WF-atom -> (bop o a b).WF Γ

  namespace WF
    notation (name := wfnotation) Γ:arg " ⊢ " e:arg " WF-expr" => WF Γ e

    instance {Γ : Scope} : (e : Expr) -> Decidable (Γ ⊢ e WF-expr)
      | .nop a => decidable_of_iff (Γ ⊢ a WF-atom)
          ⟨nop, λ (nop a) => a⟩
      | .uop _o a => decidable_of_iff (Γ ⊢ a WF-atom)
          ⟨uop, λ (uop wf) => wf⟩
      | .bop _o a b => decidable_of_iff (Γ ⊢ a WF-atom ∧ Γ ⊢ b WF-atom)
          ⟨And.elim bop, λ (bop a b) => ⟨a, b⟩⟩

    theorem weakening {Γ Γ'} {e : Expr} : Γ ⊢ e WF-expr -> (Γ + Γ') ⊢ e WF-expr
      | .nop a => .nop a.weakening
      | .uop a => .uop a.weakening
      | .bop a b => .bop a.weakening b.weakening
  end WF
end Expr

namespace Cont
  -- a continuation that takes `bsig.arity + rets` args
  inductive WFRets (bsigs : BlockSigs) (bsig : BlockSig) (rets : Nat) (b : Cont) : Prop where
    | mk (_ : b.b < bsigs.length)
         (_ : bsigs[b.b] = ⟨b.args.length + rets, bsig.oblg⟩)
         (_ : IVec (bsig.arity ⊢ · WF-var) b.args)

  inductive WF (bsigs : BlockSigs) (bsig : BlockSig) (b : Cont) : Prop where
    | mk (_ : b.b < bsigs.length)
         (_ : bsigs[b.b] = ⟨b.args.length, bsig.oblg⟩)
         (_ : IVec (bsig.arity ⊢ · WF-var) b.args)

  namespace WFRets
    notation (name := notationwf) bsigs:arg " ; " bsig:arg " ⊢ " b:arg " ( " rets:arg " )" " WF-cont" => WFRets bsigs bsig rets b
  end WFRets
  namespace WF
    notation (name := notationwf) bsigs:arg " ; " bsig:arg " ⊢ " b:arg " WF-cont" => WF bsigs bsig b
  end WF

  namespace WFRets
    instance {bsigs : BlockSigs} {bsig : BlockSig} {b : Cont} :
             Coe (bsigs; bsig ⊢ b(0) WF-cont) (bsigs; bsig ⊢ b WF-cont) where
      coe := λ ⟨bwf, blen, argswf⟩ => ⟨bwf, blen, argswf⟩

    instance wf {bsigs : BlockSigs} {bsig : BlockSig} {rets : Nat} {b : Cont} :
                Decidable (bsigs; bsig ⊢ b(rets) WF-cont) :=
      dite (b.b < bsigs.length)
        (λ t => decidable_of_iff
                  ((bsigs[b.b] = ⟨b.args.length + rets, bsig.oblg⟩) ∧
                   IVec (bsig.arity ⊢ · WF-var) b.args)
                  ⟨λ ⟨p1, p2⟩ => ⟨t, p1, p2⟩,
                   λ ⟨_, p1, p2⟩ => ⟨p1, p2⟩⟩)
        (λ f => isFalse (f ∘ (λ ⟨p, _, _⟩ => p)))

    abbrev cast0 {bsigs bsig b} : bsigs; bsig ⊢ b(0) WF-cont -> bsigs; bsig ⊢ b WF-cont
      | ⟨a, b, c⟩ => ⟨a, b, c⟩
    theorem blt {bsigs bsig rets b} (wf : bsigs; bsig ⊢ b(rets) WF-cont) :
                b.b < bsigs.length := wf.1
    theorem bsig {bsigs bsig rets b} (wf : bsigs; bsig ⊢ b(rets) WF-cont) :
                 bsigs[b.b]'wf.blt = ⟨b.args.length + rets, bsig.oblg⟩ := wf.2
    theorem args {bsigs bsig rets b} (wf : bsigs; bsig ⊢ b(rets) WF-cont) :
                 IVec (bsig.arity ⊢ · WF-var) b.args := wf.3

    theorem weakening_bsigs
            {bsigs bsigs' bsig ret b} :
            bsigs; bsig ⊢ b(ret) WF-cont ->
            (bsigs ++ bsigs'); bsig ⊢ b(ret) WF-cont
      | mk blt bsigb args =>
        mk (List.length_append ▸ Nat.lt_add_right bsigs'.length blt)
           (List.getElem_append_left' blt bsigs' ▸ bsigb)
           args
  end WFRets

  namespace WF
    instance {bsigs : BlockSigs} {bsig : BlockSig} {b : Cont} :
             Coe (bsigs; bsig ⊢ b WF-cont) (bsigs; bsig ⊢ b(0) WF-cont) where
      coe := λ ⟨bwf, blen, argswf⟩ => ⟨bwf, blen, argswf⟩

    instance wf {bsigs : BlockSigs} {bsig : BlockSig} {b : Cont} :
                Decidable (bsigs; bsig ⊢ b WF-cont) :=
      decidable_of_iff (b.WFRets bsigs bsig 0) ⟨Coe.coe, Coe.coe⟩

    abbrev cast0 {bsigs bsig b} : bsigs; bsig ⊢ b WF-cont -> bsigs; bsig ⊢ b(0) WF-cont
      | ⟨a, b, c⟩ => ⟨a, b, c⟩
    theorem blt {bsigs bsig b} (wf : bsigs; bsig ⊢ b WF-cont) :
                b.b < bsigs.length := wf.1
    theorem bsig {bsigs bsig b} (wf : bsigs; bsig ⊢ b WF-cont) :
                 bsigs[b.b]'wf.blt = ⟨b.args.length, bsig.oblg⟩ := wf.2
    theorem args {bsigs bsig b} (wf : bsigs; bsig ⊢ b WF-cont) :
                 IVec (bsig.arity ⊢ · WF-var) b.args := wf.3

    theorem weakening_bsigs
            {bsigs bsigs' bsig b}
            (wf : bsigs; bsig ⊢ b WF-cont) :
            (bsigs ++ bsigs'); bsig ⊢ b WF-cont :=
      wf.cast0.weakening_bsigs.cast0
  end WF

  theorem WFRets0_iff_WF {bsigs : BlockSigs} {bsig : BlockSig} {b : Cont} :
                         bsigs; bsig ⊢ b(0) WF-cont ↔ bsigs; bsig ⊢ b WF-cont :=
    ⟨Coe.coe, Coe.coe⟩
end Cont

namespace Code
  --notation e:arg " ;; " c => stmt e c

  inductive WF (fsigs : FuncSigs) (bsigs: BlockSigs) : BlockSig -> Code -> Prop where
    | stmt
        {bsig : BlockSig}
        {e : Expr}
        {c : Code} :
        bsig.arity ⊢ e WF-expr ->
        c.WF fsigs bsigs bsig.bind ->
        (stmt e c).WF fsigs bsigs bsig

    | goto
        {bsig : BlockSig}
        {bnext : Cont} :
        bsigs; bsig ⊢ bnext WF-cont ->
        (goto bnext).WF fsigs bsigs bsig

    | ite
        {bsig : BlockSig}
        {cond : Atom}
        {bthen : Cont}
        {belse : Cont} :
        bsig.arity ⊢ cond WF-atom ->
        bsigs; bsig ⊢ bthen WF-cont ->
        bsigs; bsig ⊢ belse WF-cont ->
        (ite cond bthen belse).WF fsigs bsigs bsig

    | call
        {bsig : BlockSig}
        {f : FuncIdx}
        {args : List Var}
        {bret : Cont} :
        (_ : f < fsigs.length) ->
        fsigs[f].arity = args.length ->
        IVec (bsig.arity ⊢ · WF-var) args ->
        bsigs; bsig ⊢ bret(fsigs[f].ret) WF-cont ->
        (call f args bret).WF fsigs bsigs bsig
        
    | retn
        {bsig : BlockSig}
        {args : List Var} :
        bsig.oblg = .retn args.length ->
        IVec (bsig.arity ⊢ · WF-var) args ->
        (retn args).WF fsigs bsigs bsig

    | spork
        {bsig : BlockSig}
        {bbody : Cont}
        {bspwn : Cont}
        {n : Nat} :
        bsigs; (bsig.spoin n) ⊢ bbody WF-cont ->
        bsigs; (bsig.exit n) ⊢ bspwn WF-cont ->
        (spork n bbody bspwn).WF fsigs bsigs bsig

    | spoin
        {bsig : BlockSig}
        {bunpr : Cont}
        {bprom : Cont} :
        bsig.oblg.isSpoin ->
        bsigs; bsig.tail ⊢ bunpr WF-cont ->
        bsigs; (bsig.tail.join bsig.head) ⊢ bprom WF-cont ->
        (spoin bunpr bprom).WF fsigs bsigs bsig
    
    | join
        {bsig : BlockSig}
        {bsync : Cont} :
        bsig.oblg.isJoin ->
        bsync.WFRets bsigs bsig.tail bsig.head ->
        (join bsync).WF fsigs bsigs bsig
    
    | exit
        {bsig : BlockSig}
        {args : List Var}:
        bsig.oblg = .exit args.length ->
        IVec (bsig.arity ⊢ · WF-var) args ->
        (exit args).WF fsigs bsigs bsig

  namespace WF
    
    notation (name := notationwf) fsigs:arg " ; " bsigs:arg " ; " bsig:arg " ⊢ " c:arg " WF-code" => WF fsigs bsigs bsig c
--    notation:min (name := notationwf') fsigs:arg bsigs:arg bsig:arg " ⊢ " c " WF-code" => WF fsigs bsigs bsig c

    instance instDecidable {fsigs bsigs bsig} : (c : Code) ->
                           Decidable (fsigs; bsigs; bsig ⊢ c WF-code)
      | .stmt e c =>
          let _ : Decidable (fsigs; bsigs; bsig.bind ⊢ c WF-code) := instDecidable c;
          decidable_of_iff (bsig.arity ⊢ e WF-expr ∧
                            fsigs; bsigs; bsig.bind ⊢ c WF-code)
            ⟨λ ⟨e, c⟩ => stmt e c, λ | stmt e c => ⟨e, c⟩⟩
      | .goto bnext =>
          decidable_of_iff (bsigs; bsig ⊢ bnext WF-cont)
            ⟨goto, λ | goto wf => wf⟩
      | .ite cond bthen belse =>
          decidable_of_iff (bsig.arity ⊢ cond WF-atom ∧
                            bsigs; bsig ⊢ bthen WF-cont ∧
                            bsigs; bsig ⊢ belse WF-cont)
            ⟨λ ⟨a, b, c⟩ => ite a b c, λ | ite a b c => ⟨a, b, c⟩⟩
      | .call f args bret =>
          decidable_of_iff (∃ _ : f < fsigs.length,
                            fsigs[f].arity = args.length ∧
                            IVec (bsig.arity ⊢ · WF-var) args ∧
                            bsigs; bsig ⊢ bret(fsigs[f].ret) WF-cont)
            ⟨λ ⟨a, b, c, d⟩ => call a b c d,
             λ | call a b c d => ⟨a, b, c, d⟩⟩
      | .retn args =>
          decidable_of_iff (bsig.oblg = Oblg.retn args.length ∧
                            IVec (bsig.arity ⊢ · WF-var) args)
            ⟨λ ⟨a, b⟩ => retn a b, λ | retn a b => ⟨a, b⟩⟩
      | .spork n bbody bspwn =>
          decidable_of_iff (bsigs; (bsig.spoin n) ⊢ bbody WF-cont ∧
                            bsigs; (bsig.exit n) ⊢ bspwn WF-cont)
            ⟨λ ⟨a, b⟩ => spork a b, λ | spork a b => ⟨a, b⟩⟩
      | .spoin bunpr bprom =>
          decidable_of_iff (bsig.oblg.isSpoin ∧
                            bsigs; bsig.tail ⊢ bunpr WF-cont ∧
                            bsigs; (bsig.tail.join bsig.head) ⊢ bprom WF-cont)
            ⟨λ ⟨a, b, c⟩ => spoin a b c, λ | spoin a b c => ⟨a, b, c⟩⟩
      | .join bsync =>
          decidable_of_iff (bsig.oblg.isJoin ∧
                            bsync.WFRets bsigs bsig.tail bsig.head)
            ⟨λ ⟨a, b⟩ => join a b, λ | join a b => ⟨a, b⟩⟩
      | .exit args =>
          decidable_of_iff (bsig.oblg = .exit args.length ∧
                            IVec (bsig.arity ⊢ · WF-var) args)
            ⟨λ ⟨a, b⟩ => exit a b, λ | exit a b => ⟨a, b⟩⟩

    -- Accessor methods
    theorem stmt_expr {fsigs bsigs bsig e c} : fsigs; bsigs; bsig ⊢ (.stmt e c) WF-code -> bsig.arity ⊢ e WF-expr
      | stmt ewf _cwf => ewf
    theorem stmt_code {fsigs bsigs bsig e c} : fsigs; bsigs; bsig ⊢ (.stmt e c) WF-code -> fsigs; bsigs; bsig.bind ⊢ c WF-code
      | stmt _ewf cwf => cwf

    theorem goto_bnext {fsigs bsigs bsig bnext} :
                       fsigs; bsigs; bsig ⊢ (.goto bnext) WF-code ->
                       bsigs; bsig ⊢ bnext WF-cont
      | goto bnextwf => bnextwf

    theorem ite_cond {fsigs bsigs bsig cond bthen belse} :
                     fsigs; bsigs; bsig ⊢ (.ite cond bthen belse) WF-code ->
                     bsig.arity ⊢ cond WF-atom
      | ite condwf _ _ => condwf
    theorem ite_bthen {fsigs bsigs bsig cond bthen belse} :
                      fsigs; bsigs; bsig ⊢ (.ite cond bthen belse) WF-code ->
                      bsigs; bsig ⊢ bthen WF-cont
      | ite _ bthenwf _ => bthenwf
    theorem ite_belse {fsigs bsigs bsig cond bthen belse} :
                      fsigs; bsigs; bsig ⊢ (.ite cond bthen belse) WF-code ->
                      bsigs; bsig ⊢ belse WF-cont
      | ite _ _ belsewf => belsewf

    theorem call_flt {fsigs bsigs bsig f args bret} :
                     fsigs; bsigs; bsig ⊢ (.call f args bret) WF-code ->
                     f < fsigs.length
      | call flt _ _ _ => flt
    theorem call_arity {fsigs bsigs bsig f args bret} :
                       (wf : fsigs; bsigs; bsig ⊢ (.call f args bret) WF-code) ->
                       (fsigs[f]'wf.call_flt).arity = args.length
      | call _ aritywf _ _ => aritywf
    theorem call_args {fsigs bsigs bsig f args bret} :
                      fsigs; bsigs; bsig ⊢ (.call f args bret) WF-code ->
                      IVec (bsig.arity ⊢ · WF-var) args
      | call _ _ argswf _ => argswf
    theorem call_bret {fsigs bsigs bsig f args bret} :
                      (wf : fsigs; bsigs; bsig ⊢ (.call f args bret) WF-code) ->
                      bsigs; bsig ⊢ bret((fsigs[f]'wf.call_flt).ret) WF-cont
      | call _ _ _ bretwf => bretwf

    theorem retn_oblg {fsigs bsigs bsig args} :
                      fsigs; bsigs; bsig ⊢ (.retn args) WF-code ->
                      bsig.oblg = .retn args.length
      | retn n _ => n
    theorem retn_args {fsigs bsigs bsig args} :
                      fsigs; bsigs; bsig ⊢ (.retn args) WF-code ->
                      IVec (bsig.arity ⊢ · WF-var) args
      | retn _ a => a

    theorem spork_bbody {fsigs bsigs bsig n bbody bspwn} :
                        (wf : fsigs; bsigs; bsig ⊢ (.spork n bbody bspwn) WF-code) ->
                        bsigs; (bsig.spoin n) ⊢ bbody WF-cont
      | spork bbodywf _ => bbodywf

    theorem spork_bspwn {fsigs bsigs bsig n bbody bspwn} :
                        (wf : fsigs; bsigs; bsig ⊢ (.spork n bbody bspwn) WF-code) ->
                        bsigs; (bsig.exit n) ⊢ bspwn WF-cont
      | spork _ bspwnwf => bspwnwf

    theorem spoin_oblg {fsigs bsigs bsig bunpr bprom} :
                       fsigs; bsigs; bsig ⊢ (.spoin bunpr bprom) WF-code ->
                       bsig.oblg.isSpoin
      | spoin issp _ _ => issp
    theorem spoin_bunpr {fsigs bsigs bsig bunpr bprom} :
                        fsigs; bsigs; bsig ⊢ (.spoin bunpr bprom) WF-code ->
                        bsigs; bsig.tail ⊢ bunpr WF-cont
      | spoin _ bunprwf _ => bunprwf
    theorem spoin_bprom {fsigs bsigs bsig bunpr bprom} :
                        (wf : fsigs; bsigs; bsig ⊢ (.spoin bunpr bprom) WF-code) ->
                        bsigs; (bsig.tail.join bsig.head) ⊢ bprom WF-cont
      | spoin _ _ bpromwf => bpromwf

    theorem weakening_bsigs
            {fsigs bsigs bsigs' bsig c} :
            fsigs; bsigs; bsig ⊢ c WF-code ->
            fsigs; (bsigs ++ bsigs'); bsig ⊢ c WF-code
      | stmt ewf cwf =>
        stmt ewf cwf.weakening_bsigs
      | goto bnextwf =>
        goto bnextwf.weakening_bsigs
      | ite ewf bthenwf belsewf =>
        ite ewf bthenwf.weakening_bsigs belsewf.weakening_bsigs
      | call flt aritywf argswf bretwf =>
        call flt aritywf argswf bretwf.weakening_bsigs
      | retn oblg argswf =>
        retn oblg argswf
      | spork bbodywf bspwnwf =>
        spork bbodywf.weakening_bsigs bspwnwf.weakening_bsigs
      | spoin snwf bunprwf bpromwf =>
        spoin snwf bunprwf.weakening_bsigs bpromwf.weakening_bsigs
      | join oblg bsyncwf =>
        join oblg bsyncwf.weakening_bsigs
      | exit oblg argswf =>
        exit oblg argswf

    theorem merge_wf {fsigs bsigs bsig} :
            {e : List Expr} -> {c : Code} ->
            (∀ i : Fin e.length, (bsig.arity + i) ⊢ e[i] WF-expr) ->
            fsigs; bsigs; (bsig.binds e.length) ⊢ c WF-code ->
            fsigs; bsigs; bsig ⊢ (c.merge e) WF-code
      | [], c, ewf, cwf => by simpa using cwf
      | e :: es, c, ewf, cwf =>
        .stmt (ewf ⟨0, by simp⟩)
          (merge_wf (bsig := bsig.bind) (e := es)
            (λ i => let ewf' := ewf ⟨i.1 + 1, by simp⟩
                    by simp[← Nat.add_assoc bsig.1 1 i.1] at ewf'
                       simp
                       rw[Nat.add_assoc, Nat.add_comm 1 i.1]
                       exact ewf')
            (match bsig with
              | .mk arity sn => by
                simp
                simp at cwf
                rw[Nat.add_comm es.length 1,
                   ← Nat.add_assoc] at cwf
                exact cwf))

    theorem split_wf {fsigs bsigs bsig} {c : Code} (cwf : fsigs; bsigs; bsig ⊢ c WF-code) :
            (∀ i : Fin c.split.1.length, (bsig.arity + i) ⊢ c.split.1[i] WF-expr)
              ∧ fsigs; bsigs; (bsig.binds c.split.1.length) ⊢ c.split.2.1 WF-code := by
      cases c <;> try (exact And.intro (λ i => nomatch i) (by simpa using cwf))
      · case stmt e c =>
        let p := @split_wf fsigs bsigs bsig.bind c cwf.stmt_code
        apply And.intro
        · exact (λ | ⟨0, l⟩ => cwf.stmt_expr
                   | ⟨i + 1, l⟩ =>
                     by simpa[Nat.add_assoc, Nat.add_comm 1 i]
                        using p.1 ⟨i, by simpa using l⟩)
        · (match h : bsig with
             | .mk arity sn =>
               simpa[h, Nat.add_assoc, Nat.add_comm 1]
               using p.2)
  end WF
end Code

namespace Block
  inductive WF (fsigs bsigs) (b : Block) : Prop where
    | mk (c : b.code.WF fsigs bsigs b.bsig)

  namespace WF
    notation (name := notationwf) fsigs:arg " ; " bsigs:arg " ⊢ " b:arg " WF-block" => WF fsigs bsigs b

    instance (fsigs bsigs) : {b : Block} -> Decidable (fsigs; bsigs ⊢ b WF-block)
      | .mk bsig code =>
        decidable_of_iff (fsigs; bsigs; bsig ⊢ code WF-code)
          ⟨λ a => mk a, λ | mk a => a⟩

    theorem code {fsigs bsigs b} : fsigs; bsigs ⊢ b WF-block ->
                 fsigs; bsigs; b.bsig ⊢ b.code WF-code
      | .mk c => c

    theorem weakening_bsigs
            {fsigs bsigs bsigs' b} :
            fsigs; bsigs ⊢ b WF-block ->
            fsigs; (bsigs ++ bsigs') ⊢ b WF-block
      | mk cwf => mk cwf.weakening_bsigs
  end WF
end Block

namespace Blocks
  inductive WF (fsigs : FuncSigs) (bs: List Block) (bsig: BlockSig) : Prop where
    | mk (blocks : IVec (fsigs; (bs.map (·.bsig)) ⊢ · WF-block) bs)
         (head : HeadIs bs (·.bsig) bsig)

  namespace WF
    notation (name := notationwf) fsigs:arg " ; " bsig:arg " ⊢ " bs:arg " WF-blocks" => WF fsigs bs bsig

    instance wf {fsigs: FuncSigs} {bs: List Block} {bsig: BlockSig}:
                      Decidable (fsigs; bsig ⊢ bs WF-blocks) :=
      decidable_of_iff (IVec (fsigs; (bs.map (·.bsig)) ⊢ · WF-block) bs ∧
                        HeadIs bs (·.bsig) bsig)
        ⟨λ ⟨a, b⟩ => mk a b, λ | mk a b => ⟨a, b⟩⟩

    theorem blocks {fsigs bs bsig} : fsigs; bsig ⊢ bs WF-blocks -> IVec (fsigs; (bs.map (·.bsig)) ⊢ · WF-block) bs
      | .mk blocks _head => blocks
    theorem head {fsigs bs bsig} : fsigs; bsig ⊢ bs WF-blocks -> HeadIs bs (·.bsig) bsig
      | .mk _blocks head => head

    theorem add_blocks
            {fsigs bs bs' bsig} :
            fsigs; bsig ⊢ bs WF-blocks ->
            IVec (fsigs; ((bs ++ bs').map (·.bsig)) ⊢ · WF-block) bs' ->
            fsigs; bsig ⊢ (bs ++ bs') WF-blocks
      | .mk blocks head, bs'wf =>
        .mk (IVec.append (blocks.map
              (λ b bwf => by simpa using bwf.weakening_bsigs)) bs'wf)
            ⟨by rw[List.head?_eq_some_head,
                   List.head_append_left head.nonnil,
                   ← head.head?eq,
                   List.head?_eq_head head.nonnil]⟩
  end WF
end Blocks

namespace Func
  -- inductive WF (fsigs : FuncSigs) (f : Func) : Prop where
  --   | mk (blocks : IVec (·.WF fsigs (f.blocks.map (·.bsig))) f.blocks)
  --        (head : HeadIs f.blocks (·.bsig) ⟨f.fsig.arity, .retn f.fsig.ret⟩)
  abbrev WF (fsigs: FuncSigs) (f: Func): Prop :=
    fsigs; ⟨f.fsig.arity, .retn f.fsig.ret⟩ ⊢ f.blocks WF-blocks

  namespace WF
    notation (name := notationwf) fsigs:arg " ⊢ " f:arg " WF-func" => WF fsigs f
    notation (name := notationwf') P:arg " ⊢ " f:arg " WF-func'" => WF (Program.fsigs P) f
    
    instance {fsigs : FuncSigs} {f : Func}: Decidable (fsigs ⊢ f WF-func) := Blocks.WF.wf

    theorem blocks {fsigs f} : fsigs ⊢ f WF-func ->
                   IVec (fsigs; (f.blocks.map (·.bsig)) ⊢ · WF-block) f.blocks
      := Blocks.WF.blocks
    theorem head {fsigs f} : fsigs ⊢ f WF-func ->
                 HeadIs f.blocks (·.bsig) ⟨f.fsig.arity, .retn f.fsig.ret⟩
      := Blocks.WF.head

    theorem add_blocks
            {fsigs fsig bs bs'} :
            fsigs ⊢ (.mk fsig bs) WF-func ->
            IVec (fsigs; ((bs ++ bs').map (·.bsig)) ⊢ · WF-block) bs' ->
            fsigs ⊢ (.mk fsig (bs ++ bs')) WF-func :=
      Blocks.WF.add_blocks
  end WF
end Func

namespace Program
  inductive WF (P : Program): Prop where
    | mk (funcs : IVec (P ⊢ · WF-func') P.funs)
         (main: P.fsigs; ⟨0, .exit 1⟩ ⊢ P.main WF-blocks)

  namespace WF
    notation (name := notationwf) P:arg " WF-program" => WF P
    
    instance {P : Program}: Decidable (P WF-program) :=
      decidable_of_iff (IVec (P.fsigs ⊢ · WF-func) P.funs ∧
                        P.fsigs; ⟨0, .exit 1⟩ ⊢ P.main WF-blocks)
          ⟨λ ⟨a, b⟩ => mk a b, λ | mk a b => ⟨a, b⟩⟩

    theorem funcs {P} : P WF-program -> IVec (P.fsigs ⊢ · WF-func) P.funs
      | .mk funcs _main => funcs
    theorem main {P} : P WF-program -> P.fsigs; ⟨0, .exit 1⟩ ⊢ P.main WF-blocks
      | mk _funcs main => main
  end WF  
end Program

