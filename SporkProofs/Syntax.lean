--import Mathlib.Tactic.Linarith
import SporkProofs.IVec

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

inductive Transfer where
  | goto (bnext : Cont)
  | ite (cond : Atom) (bthen : Cont) (belse : Cont)
  | call (f : FuncIdx) (args : List Var) (bret : Cont)
  | retn (args : List Var)
  | spork (bbody : Cont) (fspwn : FuncIdx) (args : List Var)
  | spoin (bunpr : Cont) (bprom : Cont)

inductive Code where
  | stmt (e : Expr) (c : Code)
  | trfr (t : Transfer)

abbrev SporkSig := List Nat

-- block with `arity` args and nested under `sporks`
inductive BlockSig where
  | mk (arity : Nat) (sporkNest : SporkSig)

inductive Block where
  | mk (bsig : BlockSig) (code : Code)

inductive FuncSig where
  | mk (arity : Nat) (ret : Nat)

inductive Func where
  | mk (fsig : FuncSig) (blocks : List Block)

inductive Program where
  | mk (funs : List Func)

abbrev Scope := Nat
abbrev FuncSigs := List FuncSig
abbrev BlockSigs := List BlockSig

namespace BlockSig
  abbrev arity | mk a _ss => a
  abbrev sporkNest | mk _a ss => ss
  abbrev bind | mk a ss => mk a.succ ss
  abbrev spork | mk a ss, s => mk a (s :: ss)
  abbrev spoin | mk a ss => mk a ss.tail

  -- instance instDecidableEq : DecidableEq BlockSig
  --   | ⟨ar, sn⟩, ⟨ar', sn'⟩ =>
  --       decidable_of_iff ((ar, sn) = (ar', sn'))
  --         ⟨congrArg (λ (areq, sneq) => mk areq sneq),
  --          congrArg (λ | mk areq sneq => (areq, sneq))⟩
  deriving instance DecidableEq for BlockSig
end BlockSig

namespace FuncSig
  abbrev arity | mk a _r => a
  abbrev ret | mk _a r => r

  -- instance instDecidableEq : DecidableEq FuncSig
  --   | ⟨arity, ret⟩, ⟨arity', ret'⟩ =>
  --     decidable_of_iff ((arity, ret) = (arity', ret'))
  --       ⟨congrArg (λ (areq, sneq) => mk areq sneq),
  --        congrArg (λ | mk areq sneq => (areq, sneq))⟩
  deriving instance DecidableEq, Inhabited for FuncSig
end FuncSig

namespace Var
  variable (Γ : Scope)

  abbrev idx | mk v => v

  inductive Okay (v : Var) : Prop where
    | mk : v.idx < Γ -> v.Okay

  instance instDecidable (v : Var) : Decidable (v.Okay Γ) :=
    decidable_of_iff (v.idx < Γ) ⟨(⟨·⟩), (·.1)⟩
  
  -- instance instDecidableEq : DecidableEq Var
  --   | ⟨v⟩, ⟨v'⟩ => decidable_of_iff (v = v') ⟨congrArg mk, λ eq => congrArg (·.1) eq⟩
  deriving instance DecidableEq for Var

  instance instOfNat {n} : OfNat Var n where
    ofNat := Var.mk n
  instance instCoeVarToNat : Coe Nat Var where
    coe := mk
  instance instCoeNatToVar : Coe Var Nat where
    coe := idx
end Var

namespace Atom
  variable (Γ : Scope)

  inductive Okay : Atom -> Prop where
    | val {v : Val} : (val v).Okay
    | var {v : Var} : v.Okay Γ -> (var v).Okay

  instance instDecidable : (a : Atom) -> Decidable (a.Okay Γ)
    | val _v => isTrue Okay.val
    | var v => decidable_of_iff (v.Okay Γ) ⟨Okay.var, λ (.var v) => v⟩

  -- instance instDecidableEq : DecidableEq Atom
  --   | val v, val v' => decidable_of_iff (v = v')
  --       ⟨congrArg val, λ eq => congrArg (λ | (val v) => v | _ => v) eq⟩
  --   | var v, var v' => decidable_of_iff (v = v')
  --       ⟨congrArg var, λ eq => congrArg (λ | (var v) => v | _ => v) eq⟩
  --   | val v, var v' => isFalse (by simp)
  --   | var v, val v' => isFalse (by simp)
  deriving instance DecidableEq for Atom
end Atom

namespace Uop
  -- instance instDecidableEq : DecidableEq Uop
  --   | a, b => by cases a <;> cases b <;>
  --                first | exact isTrue rfl | exact isFalse (by simp)
  deriving instance DecidableEq for Uop
end Uop

namespace Bop
  -- instance instDecidableEq : DecidableEq Bop
  --   | a, b => by cases a <;> cases b <;>
  --                first | exact isTrue rfl | exact isFalse (by simp)
  deriving instance DecidableEq for Bop
end Bop

namespace Expr
  variable (Γ : Scope)
  
  inductive Okay : Expr -> Prop where
    | nop {a : Atom} : a.Okay Γ -> (nop a).Okay
    | uop {o : Uop} {a : Atom} : a.Okay Γ -> (uop o a).Okay
    | bop {o : Bop} {a b : Atom} : a.Okay Γ -> b.Okay Γ -> (bop o a b).Okay

  instance instDecidable : (e : Expr) -> Decidable (e.Okay Γ)
    | nop a => decidable_of_iff (a.Okay Γ)
        ⟨Okay.nop, λ (.nop a) => a⟩
    | uop _o a => decidable_of_iff (a.Okay Γ)
        ⟨Okay.uop, λ (.uop ok) => ok⟩
    | bop _o a b => decidable_of_iff (a.Okay Γ ∧ b.Okay Γ)
        ⟨And.elim Okay.bop, λ (.bop a b) => ⟨a, b⟩⟩

  -- instance instDecidableEq : DecidableEq Expr
  --   | nop v, nop v' =>
  --     decidable_of_iff (v = v')
  --       ⟨congrArg nop,
  --        congrArg (λ | nop v => v | _ => v)⟩
  --   | uop o a, uop o' a' =>
  --     decidable_of_iff ((o, a) = (o', a'))
  --       ⟨congrArg (λ (o, a) => uop o a),
  --        congrArg (λ | uop o a => (o, a) | _ => (o, a))⟩
  --   | bop o a b, bop o' a' b' =>
  --     decidable_of_iff ((o, a, b) = (o', a', b'))
  --       ⟨congrArg (λ (o, a, b) => bop o a b),
  --        congrArg (λ | bop o a b => (o, a, b) | _ => (o, a, b))⟩
  --   | nop _, uop _ _ => isFalse (by simp)
  --   | nop _, bop _ _ _ => isFalse (by simp)
  --   | uop _ _, nop _ => isFalse (by simp)
  --   | uop _ _, bop _ _ _ => isFalse (by simp)
  --   | bop _ _ _, nop _ => isFalse (by simp)
  --   | bop _ _ _, uop _ _ => isFalse (by simp)
  deriving instance DecidableEq for Expr
end Expr

namespace Cont
  variable
    (bsigs : BlockSigs)
    (bsig : BlockSig)

  abbrev b | mk b _args => b
  abbrev args | mk _b args => args

  -- a continuation that takes `bsig.arity + rets` args
  inductive OkayRets (rets : Nat) (b : Cont) :Prop where
    | mk (_ : b.b < bsigs.length)
         (_ : bsigs[b.b] = ⟨b.args.length + rets, bsig.sporkNest⟩)
         (_ : IVec (·.Okay bsig.arity) b.args)

  inductive Okay (b : Cont) : Prop where
    | mk (_ : b.b < bsigs.length)
         (_ : bsigs[b.b] = ⟨b.args.length, bsig.sporkNest⟩)
         (_ : IVec (·.Okay bsig.arity) b.args)

  instance instOkayRetsOkayCoe {bsigs : BlockSigs} {bsig : BlockSig} {b : Cont} :
                               Coe (OkayRets bsigs bsig 0 b) (Okay bsigs bsig b) where
    coe := λ  ⟨bok, blen, argsok⟩ => ⟨bok, blen, argsok⟩
  instance instOkayOkayRetsCoe {bsigs : BlockSigs} {bsig : BlockSig} {b : Cont} :
                               Coe (Okay bsigs bsig b) (OkayRets bsigs bsig 0 b) where
    coe := λ ⟨bok, blen, argsok⟩ => ⟨bok, blen, argsok⟩

  namespace OkayRets
    abbrev cast0 {bsigs bsig b} : OkayRets bsigs bsig 0 b -> Okay bsigs bsig b
      | ⟨a, b, c⟩ => ⟨a, b, c⟩
  end OkayRets

  namespace Okay
    abbrev cast0 {bsigs bsig b} : Okay bsigs bsig b -> OkayRets bsigs bsig 0 b
      | ⟨a, b, c⟩ => ⟨a, b, c⟩
  end Okay

  def OkayRets0_iff_Okay {bsigs : BlockSigs} {bsig : BlockSig} {b : Cont} :
                         OkayRets bsigs bsig 0 b ↔ Okay bsigs bsig b :=
    ⟨Coe.coe, Coe.coe⟩

  instance instDecidableRets (rets : Nat) (b : Cont) : Decidable (b.OkayRets bsigs bsig rets) :=
    dite (b.b < bsigs.length)
      (λ t => decidable_of_iff
                ((bsigs[b.b] = ⟨b.args.length + rets, bsig.sporkNest⟩) ∧
                 IVec (·.Okay bsig.arity) b.args)
                ⟨λ ⟨p1, p2⟩ => ⟨t, p1, p2⟩,
                 λ ⟨_, p1, p2⟩ => ⟨p1, p2⟩⟩)
      (λ f => isFalse (f ∘ (λ ⟨p, _, _⟩ => p)))

  instance instDecidable (b : Cont) : Decidable (b.Okay bsigs bsig) :=
    decidable_of_iff (b.OkayRets bsigs bsig 0) OkayRets0_iff_Okay

  -- instance instDecidableEq : DecidableEq Cont
  --   | ⟨b, args⟩, ⟨b', args'⟩ => decidable_of_iff
  --       ((b, args) = (b', args'))
  --       ⟨congrArg (λ (b, args) => mk b args),
  --        congrArg (λ | mk b args => (b, args))⟩
  deriving instance DecidableEq for Cont
end Cont

namespace Transfer
  variable
    (fsigs : FuncSigs)
    (bsigs : BlockSigs)
    (ret : Nat)
    (bsig : BlockSig)

  inductive Okay : Transfer -> Prop where
    | goto
        {bnext : Cont} :
        bnext.Okay bsigs bsig ->
        (goto bnext).Okay

    | ite
        {cond : Atom}
        {bthen : Cont}
        {belse : Cont} :
        cond.Okay bsig.arity ->
        bthen.Okay bsigs bsig ->
        belse.Okay bsigs bsig ->
        (ite cond bthen belse).Okay

    | call
        {f : FuncIdx}
        {args : List Var}
        {bret : Cont} :
        (_ : f < fsigs.length) ->
        fsigs[f].arity = args.length ->
        IVec (·.Okay bsig.arity) args ->
        bret.OkayRets bsigs bsig fsigs[f].ret ->
        (call f args bret).Okay
        
    | retn
        {args : List Var} :
        bsig.sporkNest = [] ->
        ret = args.length ->
        IVec (·.Okay bsig.arity) args ->
        (retn args).Okay

    | spork
        {bbody : Cont}
        {fspwn : FuncIdx}
        {args : List Var} :
        (_ : fspwn < fsigs.length) ->
        fsigs[fspwn].arity = args.length ->
        IVec (·.Okay bsig.arity) args ->
        bbody.Okay bsigs (bsig.spork fsigs[fspwn].ret) ->
        (spork bbody fspwn args).Okay

    | spoin
        {bunpr : Cont}
        {bprom : Cont} :
        -- Note: not sure if introducing s, ss here
        -- will cause lean to think pattern matching this
        -- is noncomputable?
        (bsig_sn_nonnil : bsig.sporkNest ≠ []) ->
        bunpr.Okay bsigs bsig.spoin ->
        bprom.OkayRets bsigs bsig.spoin (bsig.sporkNest.head bsig_sn_nonnil) ->
        (spoin bunpr bprom).Okay

  instance instDecidable : (t : Transfer) -> Decidable (t.Okay fsigs bsigs ret bsig)
    | goto bnext =>
        decidable_of_iff (bnext.Okay bsigs bsig)
          ⟨Okay.goto, λ | .goto ok => ok⟩
    | ite cond bthen belse =>
        decidable_of_iff (cond.Okay bsig.arity ∧ bthen.Okay bsigs bsig ∧ belse.Okay bsigs bsig)
          ⟨λ ⟨a, b, c⟩ => Okay.ite a b c, λ | .ite a b c => ⟨a, b, c⟩⟩
    | call f args bret =>
        decidable_of_iff (∃ _ : f < fsigs.length,
                          fsigs[f].arity = args.length ∧
                          IVec (·.Okay bsig.arity) args ∧
                          bret.OkayRets bsigs bsig fsigs[f].ret)
          ⟨λ ⟨a, b, c, d⟩ => Okay.call a b c d,
           λ | .call a b c d => ⟨a, b, c, d⟩⟩
    | retn args =>
        decidable_of_iff (bsig.sporkNest = [] ∧ ret = args.length ∧ IVec (·.Okay bsig.arity) args)
          ⟨λ ⟨a, b, c⟩ => Okay.retn a b c, λ | .retn a b c => ⟨a, b, c⟩⟩
    | spork bbody fspwn args =>
        decidable_of_iff (∃ _ : fspwn < fsigs.length,
                          fsigs[fspwn].arity = args.length ∧
                          IVec (·.Okay bsig.arity) args ∧
                          bbody.Okay bsigs (bsig.spork fsigs[fspwn].ret))
          ⟨λ ⟨a, b, c, d⟩ => Okay.spork a b c d, λ | .spork a b c d => ⟨a, b, c, d⟩⟩
    | spoin bunpr bprom =>
        match (generalizing := true) h : bsig with
          | ⟨arity, []⟩ => isFalse (λ x => by cases x; contradiction)
          | ⟨arity, s :: ss⟩ =>
              decidable_of_iff (bunpr.Okay bsigs ⟨arity, ss⟩ ∧
                                bprom.OkayRets bsigs ⟨arity, ss⟩ s)
              ⟨λ ⟨a, b⟩ => Okay.spoin (by simp) a b,
               λ | .spoin h' a b => ⟨a, b⟩⟩

  -- instance instDecidableEq : DecidableEq Transfer
  --   | t, t' => by
  --     cases t <;> cases t' <;>

  --     -- for mismatched constructors, automatically
  --     -- derive isFalse by contradiction:
  --     try (apply isFalse; intro; contradiction)

  --     -- remaining cases, potentially isTrue:
  --     · case goto.goto bnext bnext' =>
  --         exact decidable_of_iff (bnext = bnext')
  --           ⟨congrArg goto,
  --            congrArg (λ | goto bnext => bnext | _ => bnext)⟩

  --     · case ite.ite cond bthen belse cond' bthen' belse' =>
  --         exact decidable_of_iff ((cond, bthen, belse) = (cond', bthen', belse'))
  --           ⟨congrArg (λ (a, b, c) => ite a b c),
  --            congrArg (λ | ite a b c => (a, b, c) | _ => (cond, bthen, belse))⟩

  --     · case call.call f args bret f' args' bret' =>
  --         exact decidable_of_iff ((f, args, bret) = (f', args', bret'))
  --           ⟨congrArg (λ (a, b, c) => call a b c),
  --            congrArg (λ | call f args bret => (f, args, bret) | _ => (f, args, bret))⟩

  --     · case retn.retn args args' =>
  --         exact decidable_of_iff (args = args')
  --           ⟨congrArg retn,
  --            congrArg (λ | retn args => args | _ => args)⟩

  --     · case spork.spork bbody fspwn args bbody' fspwn' args' =>
  --         exact decidable_of_iff ((bbody, fspwn, args) = (bbody', fspwn', args'))
  --           ⟨congrArg (λ (a, b, c) => spork a b c),
  --            congrArg (λ | spork a b c => (a, b, c) | _ => (bbody, fspwn, args))⟩

  --     · case spoin.spoin bunpr bprom bunpr' bprom' =>
  --         exact decidable_of_iff ((bunpr, bprom) = (bunpr', bprom'))
  --           ⟨congrArg (λ (a, b) => spoin a b),
  --            congrArg (λ | spoin a b => (a, b) | _ => (bunpr, bprom))⟩
  deriving instance DecidableEq for Transfer
end Transfer

namespace Code
  variable
    (fsigs : FuncSigs)
    (bsigs : BlockSigs)
    (ret : Nat)

  abbrev view : Code -> List Expr × Transfer
    | stmt e c => let (es, t) := view c; (e :: es, t)
    | trfr t => ([], t)

  inductive Okay : (bsig : BlockSig) -> Code -> Prop where
    | stmt
        {bsig : BlockSig}
        {e : Expr}
        {c : Code} :
        e.Okay bsig.arity ->
        c.Okay bsig.bind ->
        (stmt e c).Okay bsig

    | trfr
        {bsig : BlockSig}
        {t : Transfer} :
        t.Okay fsigs bsigs ret bsig ->
        (trfr t).Okay bsig

  namespace Okay
    abbrev t {fsigs bsigs ret bsig t} : (Code.trfr t).Okay fsigs bsigs ret bsig -> t.Okay fsigs bsigs ret bsig
      | trfr ok => ok
    abbrev e {fsigs bsigs ret bsig e c} : (Code.stmt e c).Okay fsigs bsigs ret bsig -> e.Okay bsig.arity
      | stmt eok _cok => eok
    abbrev c {fsigs bsigs ret bsig e c} : (Code.stmt e c).Okay fsigs bsigs ret bsig -> c.Okay fsigs bsigs ret bsig.bind
      | stmt _eok cok => cok
  end Okay

  instance instDecidable : {bsig : BlockSig} -> (c : Code) -> Decidable (c.Okay fsigs bsigs ret bsig)
    | bsig, stmt e c =>
      let _ : Decidable (c.Okay fsigs bsigs ret bsig.bind) := instDecidable c
      decidable_of_iff (e.Okay bsig.arity ∧ c.Okay fsigs bsigs ret bsig.bind)
        ⟨λ ⟨a, b⟩ => Okay.stmt a b,
         λ | (.stmt a b) => ⟨a, b⟩⟩
    | bsig, trfr t => decidable_of_iff (t.Okay fsigs bsigs ret bsig)
        ⟨Okay.trfr,
         λ | Okay.trfr a => a⟩

  -- instance instDecidableEq : DecidableEq Code
  --   | stmt e c, stmt e' c' =>
  --     let _ : Decidable (c = c') := instDecidableEq c c'
  --     decidable_of_iff (e = e' ∧ c = c')
  --     ⟨λ ⟨a, b⟩ => a ▸ b ▸ rfl,
  --      λ p => ⟨congrArg (λ | stmt e c => e | _ => e) p,
  --              congrArg (λ | stmt e c => c | _ => c) p⟩⟩
  --   | trfr t, trfr t' => decidable_of_iff (t = t')
  --       ⟨congrArg trfr,
  --        congrArg (λ | trfr t => t | _ => t)⟩
  --   | stmt _ _, trfr _ => isFalse (by simp)
  --   | trfr _, stmt _ _ => isFalse (by simp)
  deriving instance DecidableEq for Code
end Code

namespace Block
  variable
    (fsigs : FuncSigs)
    (bsigs : BlockSigs)
    (ret : Nat)

  abbrev bsig | mk bsig _code => bsig
  abbrev code | mk _bsig code => code

  inductive Okay (b : Block) : Prop where
    | mk (c : b.code.Okay fsigs bsigs ret b.bsig)

  instance instDecidable : {b : Block} -> Decidable (b.Okay fsigs bsigs ret)
    | mk bsig code =>
      decidable_of_iff (code.Okay fsigs bsigs ret bsig)
        ⟨λ a => .mk a, λ | .mk a => a⟩

  -- instance instDecidableEq : DecidableEq Block
  --   | mk bsig code, mk bsig' code' =>
  --     decidable_of_iff ((bsig, code) = (bsig', code'))
  --       ⟨congrArg (λ (a, b) => mk a b),
  --        λ x => congrArg (λ | .mk a b => (a, b)) x⟩

  deriving instance DecidableEq for Block

  instance instInhabited : Inhabited Block where
    default := mk ⟨0, []⟩ (Code.trfr (Transfer.retn []))
end Block

inductive HeadIs {α β : Type} (l : List α) (m : α -> β) (b : β) : Prop where
  | mk (h : m <$> l.head? = some b)

namespace HeadIs
  abbrev head?eq {α β : Type} {l : List α} {m : α -> β} {b : β} : HeadIs l m b -> m <$> l.head? = some b
    | mk h => h

  theorem nonnil {α β : Type} {l : List α} {m : α -> β} {b : β} (h : HeadIs l m b) : l ≠ [] :=
    match (generalizing := true) l, h with
      | a :: as, mk p => by simp

  theorem headeq {α β : Type} {l : List α} {m : α -> β} {b : β} (h : HeadIs l m b) : m (l.head h.nonnil) = b :=
    match (generalizing := true) l, h with
      | _a :: _as, mk p => Option.some_inj.mp p

  theorem head!eq {α β : Type} [Inhabited α] {l : List α}
                  {m : α -> β} {b : β} (h : HeadIs l m b) :
                  l.head h.nonnil = l.head! := by
    cases l
    · case nil => cases h; contradiction
    · case cons => rfl

  instance instDecidable {α β : Type} {m : α -> β} {b : β} [DecidableEq β] : {l : List α} -> Decidable (HeadIs l m b)
    | l => decidable_of_iff (m <$> l.head? = some b) ⟨mk, λ | mk h => h⟩
end HeadIs

namespace Func
  variable (fsigs : FuncSigs)
  abbrev fsig | mk fsig _blocks => fsig
  abbrev blocks | mk _fsig blocks => blocks
  abbrev bsigs : Func -> BlockSigs | mk _fsig blocks => blocks.map (·.bsig)

  inductive Okay (f : Func) : Prop where
    | mk (blocks : IVec (·.Okay fsigs (f.blocks.map (·.bsig)) f.fsig.ret) f.blocks)
         (head : HeadIs f.blocks (·.bsig) ⟨f.fsig.arity, []⟩)

  instance instDecidable : {f : Func} -> Decidable (f.Okay fsigs)
    | mk fsig blocks => decidable_of_iff
        (IVec (·.Okay fsigs (blocks.map (·.bsig)) fsig.ret) blocks ∧
         HeadIs blocks (·.bsig) ⟨fsig.arity, []⟩)
        ⟨λ ⟨a, b⟩ => Okay.mk a b, λ | .mk a b => ⟨a, b⟩⟩

  -- instance instDecidableEq : DecidableEq Func
  --   | mk fsig blocks, mk fsig' blocks' =>
  --     decidable_of_iff ((fsig, blocks) = (fsig', blocks'))
  --       ⟨congrArg (λ (a, b) => mk a b),
  --        λ x => congrArg (λ | .mk a b => (a, b)) x⟩
  deriving instance DecidableEq for Func

  instance instInhabited : Inhabited Func where
    default := mk ⟨0, 0⟩ default
end Func

namespace Program
  abbrev funs | mk funs => funs
  abbrev fsigs : Program -> FuncSigs | mk funs => funs.map (·.fsig)
  abbrev size | mk funs => funs.length

  theorem size_eq_fsigs_length (Pr : Program) : Pr.size = Pr.fsigs.length :=
    by simp

  inductive Okay (Pr : Program): Prop where
    | mk (funcs : IVec (·.Okay Pr.fsigs) Pr.funs)
         (head : HeadIs Pr.funs (·.fsig) ⟨0, 1⟩)

  instance instDecidable : {p : Program} -> Decidable p.Okay
    | mk funs => decidable_of_iff
        (IVec (·.Okay (funs.map (·.fsig))) funs ∧
         HeadIs funs (·.fsig) ⟨0, 1⟩)
        ⟨λ ⟨a, b⟩ => Okay.mk a b, λ | .mk a b => ⟨a, b⟩⟩

  -- instance instDecidableEq : DecidableEq Program
  --   | mk funs, mk funs' =>
  --     decidable_of_iff (funs = funs')
  --       ⟨congrArg mk, λ x => congrArg (λ | .mk a => a) x⟩
  deriving instance DecidableEq for Program
end Program

