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
  | spork (bbody : Cont) (fspwn : FuncIdx) (args : List Var)
  | spoin (bunpr : Cont) (bprom : Cont)

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
  @[simp] abbrev arity | mk a _ss => a
  @[simp] abbrev sporkNest | mk _a ss => ss
  @[simp] abbrev bind | mk a ss => mk a.succ ss
  @[simp] abbrev spork | mk a ss, s => mk a (s :: ss)
  @[simp] abbrev spoin | mk a ss => mk a ss.tail

  deriving instance DecidableEq for BlockSig

  @[simp] def add (a b : BlockSig) :=
    mk (a.arity + b.arity) (a.sporkNest ++ b.sporkNest)

  instance : Add BlockSig where
    add := add

  @[simp] theorem add_arity (a b : BlockSig) : (a + b).arity = a.arity + b.arity :=
    by simp
  @[simp] theorem add_sporkNest (a b : BlockSig) : (a + b).sporkNest = a.sporkNest ++ b.sporkNest :=
    by simp
  @[simp] theorem add_unfolded (a a' sn sn') : (mk a sn) + (mk a' sn') = mk (a + a') (sn ++ sn') :=
    rfl
  @[simp] theorem add_zero : (a : BlockSig) -> (a + .mk 0 []) = a
    | .mk arity sn => by simp
end BlockSig

namespace FuncSig
  @[simp] abbrev arity | mk a _r => a
  @[simp] abbrev ret | mk _a r => r

  deriving instance DecidableEq, Inhabited for FuncSig
end FuncSig

namespace Var
  @[simp] abbrev idx | mk v => v

  @[simp] abbrev inc | mk v, n => mk (v + n)

  inductive WF (Γ : Scope) (v : Var) : Prop where
    | mk : v.idx < Γ -> v.WF Γ

  namespace WF
    theorem idx {Γ : Scope} {v : Var} : v.WF Γ -> v.idx < Γ | .mk idx => idx

    instance {Γ : Scope} {v : Var} : Decidable (v.WF Γ) :=
      decidable_of_iff (v.idx < Γ) ⟨(⟨·⟩), (·.1)⟩

    theorem weakening {Γ Γ'} {v : Var} (wf : v.WF Γ) : v.WF (Γ + Γ') :=
      .mk (Nat.lt_add_right Γ' wf.idx)
  end WF
  
  deriving instance DecidableEq for Var

  instance {n} : OfNat Var n where
    ofNat := Var.mk n
  instance : Coe Nat Var where
    coe := mk
  instance : Coe Var Nat where
    coe := idx
end Var

namespace Atom
  inductive WF (Γ : Scope) : Atom -> Prop where
    | val {v : Val} : (val v).WF Γ
    | var {v : Var} : v.WF Γ -> (var v).WF Γ

  namespace WF
    instance {Γ : Scope} : (a : Atom) -> Decidable (a.WF Γ)
      | .val _v => isTrue val
      | .var v => decidable_of_iff (v.WF Γ) ⟨var, λ (var v) => v⟩

    theorem vwf {Γ : Scope} {v : Var} : (Atom.var v).WF Γ -> v.WF Γ | .var wf => wf

    theorem weakening {Γ Γ'} {a : Atom} : a.WF Γ -> a.WF (Γ + Γ')
      | .val => .val
      | .var wf => .var wf.weakening
  end WF
  deriving instance DecidableEq for Atom
end Atom

namespace Uop
  deriving instance DecidableEq for Uop
end Uop

namespace Bop
  deriving instance DecidableEq for Bop
end Bop

namespace Expr  
  inductive WF (Γ : Scope) : Expr -> Prop where
    | nop {a : Atom} : a.WF Γ -> (nop a).WF Γ
    | uop {o : Uop} {a : Atom} : a.WF Γ -> (uop o a).WF Γ
    | bop {o : Bop} {a b : Atom} : a.WF Γ -> b.WF Γ -> (bop o a b).WF Γ

  namespace WF
    instance {Γ : Scope} : (e : Expr) -> Decidable (e.WF Γ)
      | .nop a => decidable_of_iff (a.WF Γ)
          ⟨nop, λ (nop a) => a⟩
      | .uop _o a => decidable_of_iff (a.WF Γ)
          ⟨uop, λ (uop wf) => wf⟩
      | .bop _o a b => decidable_of_iff (a.WF Γ ∧ b.WF Γ)
          ⟨And.elim bop, λ (bop a b) => ⟨a, b⟩⟩

    theorem weakening {Γ Γ'} {e : Expr} : e.WF Γ -> e.WF (Γ + Γ')
      | .nop a => .nop a.weakening
      | .uop a => .uop a.weakening
      | .bop a b => .bop a.weakening b.weakening
  end WF

  deriving instance DecidableEq for Expr
end Expr

namespace Cont
  @[simp] abbrev b | mk b _args => b
  @[simp] abbrev args | mk _b args => args

  -- a continuation that takes `bsig.arity + rets` args
  inductive WFRets (bsigs : BlockSigs) (bsig : BlockSig) (rets : Nat) (b : Cont) : Prop where
    | mk (_ : b.b < bsigs.length)
         (_ : bsigs[b.b] = ⟨b.args.length + rets, bsig.sporkNest⟩)
         (_ : IVec (·.WF bsig.arity) b.args)

  inductive WF (bsigs : BlockSigs) (bsig : BlockSig) (b : Cont) : Prop where
    | mk (_ : b.b < bsigs.length)
         (_ : bsigs[b.b] = ⟨b.args.length, bsig.sporkNest⟩)
         (_ : IVec (·.WF bsig.arity) b.args)

  namespace WFRets
    instance {bsigs : BlockSigs} {bsig : BlockSig} {b : Cont} :
             Coe (WFRets bsigs bsig 0 b) (WF bsigs bsig b) where
      coe := λ ⟨bwf, blen, argswf⟩ => ⟨bwf, blen, argswf⟩

    instance {bsigs : BlockSigs} {bsig : BlockSig} {rets : Nat} {b : Cont} : Decidable (b.WFRets bsigs bsig rets) :=
      dite (b.b < bsigs.length)
        (λ t => decidable_of_iff
                  ((bsigs[b.b] = ⟨b.args.length + rets, bsig.sporkNest⟩) ∧
                   IVec (·.WF bsig.arity) b.args)
                  ⟨λ ⟨p1, p2⟩ => ⟨t, p1, p2⟩,
                   λ ⟨_, p1, p2⟩ => ⟨p1, p2⟩⟩)
        (λ f => isFalse (f ∘ (λ ⟨p, _, _⟩ => p)))

    abbrev cast0 {bsigs bsig b} : WFRets bsigs bsig 0 b -> WF bsigs bsig b
      | ⟨a, b, c⟩ => ⟨a, b, c⟩
    theorem blt {bsigs bsig rets b} (wf : WFRets bsigs bsig rets b) :
                b.b < bsigs.length := wf.1
    theorem bsig {bsigs bsig rets b} (wf : WFRets bsigs bsig rets b) :
                 bsigs[b.b]'wf.blt = ⟨b.args.length + rets, bsig.sporkNest⟩ := wf.2
    theorem args {bsigs bsig rets b} (wf : WFRets bsigs bsig rets b) :
                 IVec (·.WF bsig.arity) b.args := wf.3

    theorem weakening_bsigs
            {bsigs bsigs' bsig ret b} :
            WFRets bsigs bsig ret b ->
            WFRets (bsigs ++ bsigs') bsig ret b
      | mk blt bsigb args =>
        mk (List.length_append ▸ Nat.lt_add_right bsigs'.length blt)
           (List.getElem_append_left' blt bsigs' ▸ bsigb)
           args
  end WFRets

  namespace WF
    instance {bsigs : BlockSigs} {bsig : BlockSig} {b : Cont} :
             Coe (WF bsigs bsig b) (WFRets bsigs bsig 0 b) where
      coe := λ ⟨bwf, blen, argswf⟩ => ⟨bwf, blen, argswf⟩

    instance {bsigs : BlockSigs} {bsig : BlockSig} {b : Cont} : Decidable (b.WF bsigs bsig) :=
      decidable_of_iff (b.WFRets bsigs bsig 0) ⟨Coe.coe, Coe.coe⟩

    abbrev cast0 {bsigs bsig b} : WF bsigs bsig b -> WFRets bsigs bsig 0 b
      | ⟨a, b, c⟩ => ⟨a, b, c⟩
    theorem blt {bsigs bsig b} (wf : WF bsigs bsig b) :
                b.b < bsigs.length := wf.1
    theorem bsig {bsigs bsig b} (wf : WF bsigs bsig b) :
                 bsigs[b.b]'wf.blt = ⟨b.args.length, bsig.sporkNest⟩ := wf.2
    theorem args {bsigs bsig b} (wf : WF bsigs bsig b) :
                 IVec (·.WF bsig.arity) b.args := wf.3

    theorem weakening_bsigs
            {bsigs bsigs' bsig b}
            (wf : WF bsigs bsig b) :
            WF (bsigs ++ bsigs') bsig b :=
      wf.cast0.weakening_bsigs.cast0
  end WF

  theorem WFRets0_iff_WF {bsigs : BlockSigs} {bsig : BlockSig} {b : Cont} :
                         WFRets bsigs bsig 0 b ↔ WF bsigs bsig b :=
    ⟨Coe.coe, Coe.coe⟩

  deriving instance DecidableEq for Cont
end Cont

namespace Code
  --notation e:arg " ;; " c => stmt e c

  inductive WF (fsigs : FuncSigs) (bsigs ret) : BlockSig -> Code -> Prop where
    | stmt
        {bsig : BlockSig}
        {e : Expr}
        {c : Code} :
        e.WF bsig.arity ->
        c.WF fsigs bsigs ret bsig.bind ->
        (stmt e c).WF fsigs bsigs ret bsig

    | goto
        {bsig : BlockSig}
        {bnext : Cont} :
        bnext.WF bsigs bsig ->
        (goto bnext).WF fsigs bsigs ret bsig

    | ite
        {bsig : BlockSig}
        {cond : Atom}
        {bthen : Cont}
        {belse : Cont} :
        cond.WF bsig.arity ->
        bthen.WF bsigs bsig ->
        belse.WF bsigs bsig ->
        (ite cond bthen belse).WF fsigs bsigs ret bsig

    | call
        {bsig : BlockSig}
        {f : FuncIdx}
        {args : List Var}
        {bret : Cont} :
        (_ : f < fsigs.length) ->
        fsigs[f].arity = args.length ->
        IVec (·.WF bsig.arity) args ->
        bret.WFRets bsigs bsig fsigs[f].ret ->
        (call f args bret).WF fsigs bsigs ret bsig
        
    | retn
        {bsig : BlockSig}
        {args : List Var} :
        bsig.sporkNest = [] ->
        ret = args.length ->
        IVec (·.WF bsig.arity) args ->
        (retn args).WF fsigs bsigs ret bsig

    | spork
        {bsig : BlockSig}
        {bbody : Cont}
        {fspwn : FuncIdx}
        {args : List Var} :
        (_ : fspwn < fsigs.length) ->
        fsigs[fspwn].arity = args.length ->
        IVec (·.WF bsig.arity) args ->
        bbody.WF bsigs (bsig.spork fsigs[fspwn].ret) ->
        (spork bbody fspwn args).WF fsigs bsigs ret bsig

    | spoin
        {bsig : BlockSig}
        {bunpr : Cont}
        {bprom : Cont} :
        (bsig_sn_nonnil : bsig.sporkNest ≠ []) ->
        bunpr.WF bsigs bsig.spoin ->
        bprom.WFRets bsigs bsig.spoin (bsig.sporkNest.head bsig_sn_nonnil) ->
        (spoin bunpr bprom).WF fsigs bsigs ret bsig


  @[simp] def split : Code -> List Expr × (c : Code) ×' (∀ e, ∀ c', c ≠ .stmt e c')
    | stmt e c => let (es, cp) := c.split; (e :: es, cp)
    | goto bnext => ([], ⟨goto bnext, by intros e c; simp⟩)
    | ite e bthen belse => ([], ⟨ite e bthen belse, by intros e c; simp⟩)
    | call g args bret => ([], ⟨call g args bret, by intros e c; simp⟩)
    | retn args => ([], ⟨retn args, by intros e c; simp⟩)
    | spork bbody gspwn gargs => ([], ⟨spork bbody gspwn gargs, by intros e c; simp⟩)
    | spoin bunpr bprom => ([], ⟨spoin bunpr bprom, by intros e c; simp⟩)

  @[simp] def join : List Expr -> Code -> Code
    | [], c => c
    | e :: es, c => stmt e (join es c)

  @[simp] theorem join_split {c e c' p} (q : split c = (e, ⟨c', p⟩)) : join e c' = c := by
    cases c <;> try (cases e <;> simp_all)
    · case stmt e' es' e'' es'' =>
      exact join_split (Prod.ext q.1.2 q.2)

  namespace WF
    instance instDecidable {fsigs bsigs ret bsig} : (c : Code) ->
                           Decidable (c.WF fsigs bsigs ret bsig)
      | .stmt e c =>
          let _ : Decidable (c.WF fsigs bsigs ret bsig.bind) := instDecidable c
          decidable_of_iff (e.WF bsig.arity ∧ c.WF fsigs bsigs ret bsig.bind)
            ⟨λ ⟨e, c⟩ => stmt e c, λ | stmt e c => ⟨e, c⟩⟩
      | .goto bnext =>
          decidable_of_iff (bnext.WF bsigs bsig)
            ⟨goto, λ | goto wf => wf⟩
      | .ite cond bthen belse =>
          decidable_of_iff (cond.WF bsig.arity ∧ bthen.WF bsigs bsig ∧ belse.WF bsigs bsig)
            ⟨λ ⟨a, b, c⟩ => ite a b c, λ | ite a b c => ⟨a, b, c⟩⟩
      | .call f args bret =>
          decidable_of_iff (∃ _ : f < fsigs.length,
                            fsigs[f].arity = args.length ∧
                            IVec (·.WF bsig.arity) args ∧
                            bret.WFRets bsigs bsig fsigs[f].ret)
            ⟨λ ⟨a, b, c, d⟩ => call a b c d,
             λ | call a b c d => ⟨a, b, c, d⟩⟩
      | .retn args =>
          decidable_of_iff (bsig.sporkNest = [] ∧ ret = args.length ∧ IVec (·.WF bsig.arity) args)
            ⟨λ ⟨a, b, c⟩ => retn a b c, λ | retn a b c => ⟨a, b, c⟩⟩
      | .spork bbody fspwn args =>
          decidable_of_iff (∃ _ : fspwn < fsigs.length,
                            fsigs[fspwn].arity = args.length ∧
                            IVec (·.WF bsig.arity) args ∧
                            bbody.WF bsigs (bsig.spork fsigs[fspwn].ret))
            ⟨λ ⟨a, b, c, d⟩ => spork a b c d, λ | spork a b c d => ⟨a, b, c, d⟩⟩
      | .spoin bunpr bprom =>
          match (generalizing := true) h : bsig with
            | ⟨arity, []⟩ =>
                isFalse (λ x => by cases x <;> contradiction)
            | ⟨arity, s :: ss⟩ =>
                decidable_of_iff (bunpr.WF bsigs ⟨arity, ss⟩ ∧
                                  bprom.WFRets bsigs ⟨arity, ss⟩ s)
                ⟨λ ⟨a, b⟩ => spoin (by simp) a b,
                 λ | spoin h' a b => ⟨a, b⟩⟩

    -- Accessor methods
    theorem stmt_expr {fsigs bsigs ret bsig e c} : (Code.stmt e c).WF fsigs bsigs ret bsig -> e.WF bsig.arity
      | stmt ewf _cwf => ewf
    theorem stmt_code {fsigs bsigs ret bsig e c} : (Code.stmt e c).WF fsigs bsigs ret bsig -> c.WF fsigs bsigs ret bsig.bind
      | stmt _ewf cwf => cwf

    theorem goto_bnext {fsigs bsigs ret bsig bnext} :
                       WF fsigs bsigs ret bsig (.goto bnext) ->
                       bnext.WF bsigs bsig
      | goto bnextwf => bnextwf

    theorem ite_cond {fsigs bsigs ret bsig cond bthen belse} :
                     WF fsigs bsigs ret bsig (.ite cond bthen belse) ->
                     cond.WF bsig.arity
      | ite condwf _ _ => condwf
    theorem ite_bthen {fsigs bsigs ret bsig cond bthen belse} :
                      WF fsigs bsigs ret bsig (.ite cond bthen belse) ->
                      bthen.WF bsigs bsig
      | ite _ bthenwf _ => bthenwf
    theorem ite_belse {fsigs bsigs ret bsig cond bthen belse} :
                      WF fsigs bsigs ret bsig (.ite cond bthen belse) ->
                      belse.WF bsigs bsig
      | ite _ _ belsewf => belsewf

    theorem call_flt {fsigs bsigs ret bsig f args bret} :
                     WF fsigs bsigs ret bsig (.call f args bret) ->
                     f < fsigs.length
      | call flt _ _ _ => flt
    theorem call_arity {fsigs bsigs ret bsig f args bret} :
                       (wf : WF fsigs bsigs ret bsig (.call f args bret)) ->
                       (fsigs[f]'wf.call_flt).arity = args.length
      | call _ aritywf _ _ => aritywf
    theorem call_args {fsigs bsigs ret bsig f args bret} :
                      WF fsigs bsigs ret bsig (.call f args bret) ->
                      IVec (·.WF bsig.arity) args
      | call _ _ argswf _ => argswf
    theorem call_bret {fsigs bsigs ret bsig f args bret} :
                      (wf : WF fsigs bsigs ret bsig (.call f args bret)) ->
                      bret.WFRets bsigs bsig (fsigs[f]'wf.call_flt).ret
      | call _ _ _ bretwf => bretwf

    theorem retn_sn_nil {fsigs bsigs ret bsig args} :
                          WF fsigs bsigs ret bsig (.retn args) ->
                          bsig.sporkNest = []
      | retn n _ _ => n
    theorem retn_length {fsigs bsigs ret bsig args} :
                        WF fsigs bsigs ret bsig (.retn args) ->
                        ret = args.length
      | retn _ l _ => l
    theorem retn_args {fsigs bsigs ret bsig args} :
                      WF fsigs bsigs ret bsig (.retn args) ->
                      IVec (·.WF bsig.arity) args
      | retn _ _ a => a

    theorem spork_flt {fsigs bsigs ret bsig bbody f args} :
                      WF fsigs bsigs ret bsig (.spork bbody f args) ->
                      f < fsigs.length
      | spork flt _ _ _ => flt
    theorem spork_arity {fsigs bsigs ret bsig bbody f args} :
                        (wf : WF fsigs bsigs ret bsig (.spork bbody f args)) ->
                        (fsigs[f]'wf.spork_flt).arity = args.length
      | spork _ aritywf _ _ => aritywf
    theorem spork_args {fsigs bsigs ret bsig bbody f args} :
                      WF fsigs bsigs ret bsig (.spork bbody f args) ->
                      IVec (·.WF bsig.arity) args
      | spork _ _ argswf _ => argswf
    theorem spork_bbody {fsigs bsigs ret bsig bbody f args} :
                        (wf : WF fsigs bsigs ret bsig (.spork bbody f args)) ->
                        bbody.WF bsigs (bsig.spork (fsigs[f]'wf.spork_flt).ret)
      | spork _ _ _ bbodywf => bbodywf

    theorem spoin_sn_nonnil {fsigs bsigs ret bsig bunpr bprom} :
                            WF fsigs bsigs ret bsig (.spoin bunpr bprom) ->
                            bsig.sporkNest ≠ []
      | spoin nn _ _ => nn
    theorem spoin_bunpr {fsigs bsigs ret bsig bunpr bprom} :
                        WF fsigs bsigs ret bsig (.spoin bunpr bprom) ->
                        bunpr.WF bsigs bsig.spoin
      | spoin _ bunprwf _ => bunprwf
    theorem spoin_bprom {fsigs bsigs ret bsig bunpr bprom} :
                        (wf : WF fsigs bsigs ret bsig (.spoin bunpr bprom)) ->
                        bprom.WFRets bsigs bsig.spoin
                          (bsig.sporkNest.head wf.spoin_sn_nonnil)
      | spoin _ _ bpromwf => bpromwf

    theorem weakening_bsigs
            {fsigs bsigs bsigs' ret bsig c} :
            WF fsigs bsigs ret bsig c ->
            WF fsigs (bsigs ++ bsigs') ret bsig c
      | stmt ewf cwf =>
        stmt ewf cwf.weakening_bsigs
      | goto bnextwf =>
        goto bnextwf.weakening_bsigs
      | ite ewf bthenwf belsewf =>
        ite ewf bthenwf.weakening_bsigs belsewf.weakening_bsigs
      | call flt aritywf argswf bretwf =>
        call flt aritywf argswf bretwf.weakening_bsigs
      | retn snwf retwf argswf =>
        retn snwf retwf argswf
      | spork flt aritywf argswf bbodywf =>
        spork flt aritywf argswf bbodywf.weakening_bsigs
      | spoin snwf bunprwf bpromwf =>
        spoin snwf bunprwf.weakening_bsigs bpromwf.weakening_bsigs

    theorem join_wf {fsigs bsigs ret bsig} :
            {e : List Expr} -> {c : Code} ->
            (∀ i : Fin e.length, e[i].WF (bsig.arity + i)) ->
            c.WF fsigs bsigs ret (bsig + .mk e.length []) ->
            (c.join e).WF fsigs bsigs ret bsig
      | [], c, ewf, cwf => by simpa using cwf
      | e :: es, c, ewf, cwf =>
        .stmt (ewf ⟨0, by simp⟩)
          (join_wf (bsig := bsig.bind) (e := es)
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

    theorem split_wf {fsigs bsigs ret bsig} {c : Code} (cwf : c.WF fsigs bsigs ret bsig) :
            (∀ i : Fin c.split.1.length, c.split.1[i].WF (bsig.arity + i))
              ∧ c.split.2.1.WF fsigs bsigs ret (bsig + .mk c.split.1.length []) := by
      cases c <;> try (exact And.intro (λ i => nomatch i) (by simpa using cwf))
      · case stmt e c =>
        let p := @split_wf fsigs bsigs ret bsig.bind c cwf.stmt_code
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

  deriving instance DecidableEq for Code
end Code

namespace Block
  @[simp] abbrev bsig | mk bsig _code => bsig
  @[simp] abbrev code | mk _bsig code => code

  inductive WF (fsigs bsigs ret) (b : Block) : Prop where
    | mk (c : b.code.WF fsigs bsigs ret b.bsig)

  namespace WF
    instance (fsigs bsigs ret) : {b : Block} -> Decidable (b.WF fsigs bsigs ret)
      | .mk bsig code =>
        decidable_of_iff (code.WF fsigs bsigs ret bsig)
          ⟨λ a => mk a, λ | mk a => a⟩

    theorem code {fsigs bsigs ret b} : WF fsigs bsigs ret b ->
                 b.code.WF fsigs bsigs ret b.bsig
      | .mk c => c

    theorem weakening_bsigs
            {fsigs bsigs bsigs' ret b} :
            WF fsigs bsigs ret b ->
            WF fsigs (bsigs ++ bsigs') ret b
      | mk cwf => mk cwf.weakening_bsigs
  end WF

  deriving instance DecidableEq for Block

  instance : Inhabited Block where
    default := mk ⟨0, []⟩ (.retn [])
end Block

namespace Func
  @[simp] abbrev fsig | mk fsig _blocks => fsig
  @[simp] abbrev blocks | mk _fsig blocks => blocks
  @[simp] abbrev bsigs : Func -> BlockSigs | mk _fsig blocks => blocks.map (·.bsig)
  @[simp] abbrev size | mk _fsig blocks => blocks.length
  
  @[simp] theorem size_eq_bsigs_length (f : Func) : f.bsigs.length = f.size :=
    by simp

  inductive WF (fsigs : FuncSigs) (f : Func) : Prop where
    | mk (blocks : IVec (·.WF fsigs (f.blocks.map (·.bsig)) f.fsig.ret) f.blocks)
         (head : HeadIs f.blocks (·.bsig) ⟨f.fsig.arity, []⟩)

  namespace WF
    instance {fsigs : FuncSigs} : {f : Func} -> Decidable (f.WF fsigs)
      | .mk fsig blocks => decidable_of_iff
          (IVec (·.WF fsigs (blocks.map (·.bsig)) fsig.ret) blocks ∧
           HeadIs blocks (·.bsig) ⟨fsig.arity, []⟩)
          ⟨λ ⟨a, b⟩ => mk a b, λ | mk a b => ⟨a, b⟩⟩

    theorem blocks {fsigs f} : WF fsigs f -> IVec (·.WF fsigs (f.blocks.map (·.bsig)) f.fsig.ret) f.blocks
      | mk blocks _head => blocks
    theorem head {fsigs f} : WF fsigs f -> HeadIs f.blocks (·.bsig) ⟨f.fsig.arity, []⟩
      | mk _blocks head => head

    theorem add_blocks
            {fsigs fsig bs bs'} :
            WF fsigs (.mk fsig bs) ->
            IVec (·.WF fsigs ((bs ++ bs').map (·.bsig)) fsig.ret) bs' ->
            WF fsigs (.mk fsig (bs ++ bs'))
      | mk blocks head, bs'wf =>
        mk (IVec.append (blocks.map
             (λ b bwf => by simpa using bwf.weakening_bsigs)) bs'wf)
           ⟨by rw[List.head?_eq_some_head,
                  List.head_append_left head.nonnil,
                  ← head.head?eq,
                  List.head?_eq_head head.nonnil]⟩
  end WF

  deriving instance DecidableEq for Func

  instance : Inhabited Func where
    default := mk ⟨0, 0⟩ default

  instance : GetElem Func BlockIdx Block (λ f b => b < f.blocks.length) where
    getElem f b p := f.blocks[b]
end Func

namespace Program
  @[simp] abbrev funs | mk funs => funs
  @[simp] abbrev fsigs : Program -> FuncSigs | mk funs => funs.map (·.fsig)
  @[simp] abbrev size | mk funs => funs.length

  @[simp] theorem size_eq_fsigs_length (P : Program) : P.fsigs.length = P.size :=
    by simp

  inductive WF (P : Program): Prop where
    | mk (funcs : IVec (·.WF P.fsigs) P.funs)
         (head : HeadIs P.funs (·.fsig) ⟨0, 1⟩)

  namespace WF
    instance : {p : Program} -> Decidable p.WF
      | .mk funs => decidable_of_iff
          (IVec (·.WF (funs.map (·.fsig))) funs ∧
           HeadIs funs (·.fsig) ⟨0, 1⟩)
          ⟨λ ⟨a, b⟩ => mk a b, λ | mk a b => ⟨a, b⟩⟩

    theorem funcs {P} : WF P -> IVec (·.WF P.fsigs) P.funs | .mk funcs _head => funcs
    theorem head {P} : WF P -> HeadIs P.funs (·.fsig) ⟨0, 1⟩ | .mk _funcs head => head
    theorem main_lt : {P : Program} -> WF P -> 0 < P.fsigs.length
      | .mk (main :: funs), .mk funcs head => by simp
    theorem main_lt' : {P : Program} -> WF P -> 0 < P.size
      | .mk (main :: funs), .mk funcs head => by simp
  end WF

  deriving instance DecidableEq for Program

  instance : GetElem Program FuncIdx Func (λ P f => f < P.size) where
    getElem P f p := P.funs[f]
  
end Program

