import SporkProofs.Syntax
import SporkProofs.IVec
import SporkProofs.HeadIs

namespace Var
  inductive WF (Γ : Scope) (v : Var) : Prop where
    | mk : v.idx < Γ -> v.WF Γ

  namespace WF
    notation (name := wfnotation) Γ:arg " ⊢ " v " WF-var" => WF Γ v

    theorem idx {Γ : Scope} {v : Var} : Γ ⊢ v WF-var -> v.idx < Γ | .mk idx => idx

    instance {Γ : Scope} {v : Var} : Decidable (Γ ⊢ v WF-var) :=
      decidable_of_iff (v.idx < Γ) ⟨(⟨·⟩), (·.1)⟩

    theorem weaken {Γ Γ'} {v : Var} (wf : Γ ⊢ v WF-var) : (Γ + Γ') ⊢ v WF-var :=
      .mk (Nat.lt_add_right Γ' wf.idx)
  end WF
end Var

namespace IVec
  theorem weaken {Γ Γ'} {xs : List Var} {xswf : IVec (Γ ⊢ · WF-var) xs} : IVec ((Γ + Γ') ⊢ · WF-var) xs :=
    xswf.map (λ _v vwf => vwf.weaken)
end IVec

namespace Atom
  inductive WF (Γ : Scope) : Atom -> Prop where
    | val {v : Val} : (val v).WF Γ
    | var {v : Var} : Γ ⊢ v WF-var -> (var v).WF Γ

  namespace WF
    notation (name := wfnotation) Γ:arg " ⊢ " a " WF-atom" => WF Γ a

    instance {Γ : Scope} : (a : Atom) -> Decidable (Γ ⊢ a WF-atom)
      | .val _v => isTrue val
      | .var v => decidable_of_iff (Γ ⊢ v WF-var) ⟨var, λ (var v) => v⟩

    theorem vwf {Γ : Scope} {v : Var} : Γ ⊢ (Atom.var v) WF-atom -> Γ ⊢ v WF-var
      | .var wf => wf

    theorem weaken {Γ Γ'} {a : Atom} : Γ ⊢ a WF-atom -> (Γ + Γ') ⊢ a WF-atom
      | .val => .val
      | .var wf => .var wf.weaken
  end WF
end Atom

namespace Expr  
  inductive WF (Γ : Scope) : Expr -> Prop where
    | nop {a : Atom} : Γ ⊢ a WF-atom -> (nop a).WF Γ
    | uop {o : Uop} {a : Atom} : Γ ⊢ a WF-atom -> (uop o a).WF Γ
    | bop {o : Bop} {a b : Atom} : Γ ⊢ a WF-atom -> Γ ⊢ b WF-atom -> (bop o a b).WF Γ

  namespace WF
    notation (name := wfnotation) Γ:arg " ⊢ " e " WF-expr" => WF Γ e

    instance {Γ : Scope} : (e : Expr) -> Decidable (Γ ⊢ e WF-expr)
      | .nop a => decidable_of_iff (Γ ⊢ a WF-atom)
          ⟨nop, λ (nop a) => a⟩
      | .uop _o a => decidable_of_iff (Γ ⊢ a WF-atom)
          ⟨uop, λ (uop wf) => wf⟩
      | .bop _o a b => decidable_of_iff (Γ ⊢ a WF-atom ∧ Γ ⊢ b WF-atom)
          ⟨And.elim bop, λ (bop a b) => ⟨a, b⟩⟩

    theorem weaken {Γ Γ'} {e : Expr} : Γ ⊢ e WF-expr -> (Γ + Γ') ⊢ e WF-expr
      | .nop a => .nop a.weaken
      | .uop a => .uop a.weaken
      | .bop a b => .bop a.weaken b.weaken
  end WF
end Expr

namespace Cont
  /-- a continuation that takes `b.args.length + rets` args -/
  inductive WFRets (B : BlockSigs) (bsig : BlockSig) (rets : Nat) (b : Cont) : Prop where
    | mk (_ : b.b < B.length)
         (_ : B[b.b] = ⟨b.args.length + rets, bsig.r, bsig.σ⟩)
         (_ : IVec (bsig.Γ ⊢ · WF-var) b.args)

  /-- a continuation that takes `b.args.length` args -/
  inductive WF (B : BlockSigs) (bsig : BlockSig) (b : Cont) : Prop where
    | mk (_ : b.b < B.length)
         (_ : B[b.b] = ⟨b.args.length, bsig.r, bsig.σ⟩)
         (_ : IVec (bsig.Γ ⊢ · WF-var) b.args)

  namespace WFRets
    notation (name := notationwf) B:arg "; " bsig:arg " ⊢ " b:arg " ( " rets " )" " WF-cont" => WFRets B bsig rets b
  end WFRets
  namespace WF
    notation (name := notationwf) B:arg "; " bsig:arg " ⊢ " b " WF-cont" => WF B bsig b
  end WF

  namespace WFRets
    instance {B : BlockSigs} {bsig : BlockSig} {b : Cont} :
             Coe (B; bsig ⊢ b(0) WF-cont) (B; bsig ⊢ b WF-cont) where
      coe := λ ⟨bwf, blen, argswf⟩ => ⟨bwf, blen, argswf⟩

    instance wf {B : BlockSigs} {bsig : BlockSig} {rets : Nat} {b : Cont} :
                Decidable (B; bsig ⊢ b(rets) WF-cont) :=
      dite (b.b < B.length)
        (λ t => decidable_of_iff
                  ((B[b.b] = ⟨b.args.length + rets, bsig.r, bsig.σ⟩) ∧
                   IVec (bsig.Γ ⊢ · WF-var) b.args)
                  ⟨λ ⟨p1, p2⟩ => ⟨t, p1, p2⟩,
                   λ ⟨_, p1, p2⟩ => ⟨p1, p2⟩⟩)
        (λ f => isFalse (f ∘ (λ ⟨p, _, _⟩ => p)))

    abbrev cast0 {B bsig b} : B; bsig ⊢ b(0) WF-cont -> B; bsig ⊢ b WF-cont
      | ⟨a, b, c⟩ => ⟨a, b, c⟩
    theorem blt {B bsig rets b} (wf : B; bsig ⊢ b(rets) WF-cont) :
                b.b < B.length := wf.1
    theorem bsig {B bsig rets b} (wf : B; bsig ⊢ b(rets) WF-cont) :
                 B[b.b]'wf.blt = ⟨b.args.length + rets, bsig.r, bsig.σ⟩ := wf.2
    theorem bsig! {B bsig rets b} (wf : B; bsig ⊢ b(rets) WF-cont) :
                  B[b.b]! = ⟨b.args.length + rets, bsig.r, bsig.σ⟩ :=
      getElem!_pos B b.b wf.blt ▸ wf.bsig
    theorem args {B bsig rets b} (wf : B; bsig ⊢ b(rets) WF-cont) :
                 IVec (bsig.Γ ⊢ · WF-var) b.args := wf.3

    theorem weaken_Bₗ {B B' bsig ret b} : B; bsig ⊢ b(ret) WF-cont ->
                      (B ++ B'); bsig ⊢ b(ret) WF-cont
      | mk blt bsigb args =>
        mk (List.length_append ▸ Nat.lt_add_right B'.length blt)
           (List.getElem_append_left' blt B' ▸
            getElem!_pos B b.b blt ▸
            bsigb)
           args

    theorem weaken_Bᵣ {B B' bsig ret b} : B'; bsig ⊢ b(ret) WF-cont ->
                      (B ++ B'); bsig ⊢ (b.offset_B B.length)(ret) WF-cont
      | mk blt bsigb args =>
        mk (b.offset_B_b ▸
            List.length_append ▸
            Nat.add_comm B.length B'.length ▸
            Nat.add_lt_add_iff_right.mpr blt)
           (by simp; exact bsigb)
           args

    theorem weaken_Γ {B Γ bsig ret b} : B; bsig ⊢ b(ret) WF-cont ->
                     B; (bsig.binds Γ) ⊢ b(ret) WF-cont
      | mk blt bsigb args =>
        mk blt bsigb args.weaken
  end WFRets

  namespace WF
    instance {B : BlockSigs} {bsig : BlockSig} {b : Cont} :
             Coe (B; bsig ⊢ b WF-cont) (B; bsig ⊢ b(0) WF-cont) where
      coe := λ ⟨bwf, blen, argswf⟩ => ⟨bwf, blen, argswf⟩

    instance wf {B : BlockSigs} {bsig : BlockSig} {b : Cont} :
                Decidable (B; bsig ⊢ b WF-cont) :=
      decidable_of_iff (b.WFRets B bsig 0) ⟨Coe.coe, Coe.coe⟩

    abbrev cast0 {B bsig b} : B; bsig ⊢ b WF-cont -> B; bsig ⊢ b(0) WF-cont
      | ⟨a, b, c⟩ => ⟨a, b, c⟩
    theorem blt {B bsig b} (wf : B; bsig ⊢ b WF-cont) :
                b.b < B.length := wf.1
    theorem bsig {B bsig b} (wf : B; bsig ⊢ b WF-cont) :
                 B[b.b]'wf.blt = ⟨b.args.length, bsig.r, bsig.σ⟩ := wf.2
    theorem bsig! {B bsig b} (wf : B; bsig ⊢ b WF-cont) :
                  B[b.b]! = ⟨b.args.length, bsig.r, bsig.σ⟩ :=
      getElem!_pos B b.b wf.blt ▸ wf.bsig
    theorem args {B bsig b} (wf : B; bsig ⊢ b WF-cont) :
                 IVec (bsig.Γ ⊢ · WF-var) b.args := wf.3

    theorem weaken_Bₗ {B B' bsig b} (wf : B; bsig ⊢ b WF-cont) :
                      (B ++ B'); bsig ⊢ b WF-cont :=
      wf.cast0.weaken_Bₗ.cast0
    theorem weaken_Bᵣ {B B' bsig b} (wf : B'; bsig ⊢ b WF-cont) :
                      (B ++ B'); bsig ⊢ (b.offset_B B.length) WF-cont :=
      wf.cast0.weaken_Bᵣ.cast0
    theorem weaken_Γ {B Γ bsig b} (wf : B; bsig ⊢ b WF-cont) :
                     B; (bsig.binds Γ) ⊢ b WF-cont :=
      wf.cast0.weaken_Γ.cast0
  end WF

  theorem WFRets0_iff_WF {B : BlockSigs} {bsig : BlockSig} {b : Cont} :
                         B; bsig ⊢ b(0) WF-cont ↔ B; bsig ⊢ b WF-cont :=
    ⟨Coe.coe, Coe.coe⟩
end Cont

namespace Code

  inductive WF (P: List FuncSig) (B: BlockSigs) : BlockSig -> Code -> Prop where
    | stmt
        {bsig : BlockSig}
        {e : Expr}
        {c : Code} :
        bsig.Γ ⊢ e WF-expr ->
        c.WF P B bsig.bind ->
        (stmt e c).WF P B bsig

    | goto
        {bsig : BlockSig}
        {bnext : Cont} :
        B; bsig ⊢ bnext WF-cont ->
        (goto bnext).WF P B bsig

    | ite
        {bsig : BlockSig}
        {cond : Atom}
        {bthen : Cont}
        {belse : Cont} :
        bsig.Γ ⊢ cond WF-atom ->
        B; bsig ⊢ bthen WF-cont ->
        B; bsig ⊢ belse WF-cont ->
        (ite cond bthen belse).WF P B bsig

    | call
        {bsig : BlockSig}
        {f : FuncIdx}
        {args : List Var}
        {bret : Cont} :
        (_ : f < P.length) ->
        P[f].arity = args.length ->
        IVec (bsig.Γ ⊢ · WF-var) args ->
        B; bsig ⊢ bret(P[f].ret) WF-cont ->
        (call f args bret).WF P B bsig
        
    | retn
        {bsig : BlockSig}
        {args : List Var} :
        bsig.r.n = args.length ->
        bsig.σ = [] ->
        IVec (bsig.Γ ⊢ · WF-var) args ->
        (retn args).WF P B bsig

    | spork
        {bsig : BlockSig}
        {bbody : Cont}
        {bspwn : Cont} :
        B[bspwn.b]!.r.isExit ->
        B; (bsig.spork B[bspwn.b]!.r.n) ⊢ bbody WF-cont ->
        B; (bsig.spwn B[bspwn.b]!.r.n) ⊢ bspwn WF-cont ->
        (spork bbody bspwn).WF P B bsig

    | spoin
        {bsig : BlockSig}
        {bunpr : Cont}
        {bprom : Cont} :
        (σnn : bsig.σ ≠ []) ->
        B; bsig.spoin ⊢ bunpr WF-cont ->
        B; bsig.spoin ⊢ bprom(bsig.σ.head σnn) WF-cont ->
        (spoin bunpr bprom).WF P B bsig

  namespace WF
    
    notation (name := notationwf) P:arg "; " B:arg "; " bsig:arg " ⊢ " c " WF-code" => WF P B bsig c

    instance instDecidable {P B bsig} : (c : Code) ->
                           Decidable (P; B; bsig ⊢ c WF-code)
      | .stmt e c =>
          let _ : Decidable (P; B; bsig.bind ⊢ c WF-code) := instDecidable c;
          decidable_of_iff (bsig.Γ ⊢ e WF-expr ∧
                            P; B; bsig.bind ⊢ c WF-code)
            ⟨λ ⟨e, c⟩ => stmt e c, λ | stmt e c => ⟨e, c⟩⟩
      | .goto bnext =>
          decidable_of_iff (B; bsig ⊢ bnext WF-cont)
            ⟨goto, λ | goto wf => wf⟩
      | .ite cond bthen belse =>
          decidable_of_iff (bsig.Γ ⊢ cond WF-atom ∧
                            B; bsig ⊢ bthen WF-cont ∧
                            B; bsig ⊢ belse WF-cont)
            ⟨λ ⟨a, b, c⟩ => ite a b c, λ | ite a b c => ⟨a, b, c⟩⟩
      | .call f args bret =>
          decidable_of_iff (∃ _ : f < P.length,
                            P[f].arity = args.length ∧
                            IVec (bsig.Γ ⊢ · WF-var) args ∧
                            B; bsig ⊢ bret(P[f].ret) WF-cont)
            ⟨λ ⟨a, b, c, d⟩ => call a b c d,
             λ | call a b c d => ⟨a, b, c, d⟩⟩
      | .retn args =>
          decidable_of_iff (bsig.r.n = args.length ∧
                            bsig.σ = [] ∧
                            IVec (bsig.Γ ⊢ · WF-var) args)
            ⟨λ ⟨a, b, c⟩ => retn a b c, λ | retn a b c => ⟨a, b, c⟩⟩
      | .spork bbody bspwn =>
          decidable_of_iff (B[bspwn.b]!.r.isExit ∧
                            B; (bsig.spork B[bspwn.b]!.r.n) ⊢ bbody WF-cont ∧
                            B; (bsig.spwn B[bspwn.b]!.r.n) ⊢ bspwn WF-cont)
            ⟨λ ⟨a, b, c⟩ => spork a b c, λ | spork a b c => ⟨a, b, c⟩⟩
      | .spoin bunpr bprom =>
          decidable_of_iff (∃ σnn : bsig.σ ≠ [],
                            B; bsig.spoin ⊢ bunpr WF-cont ∧
                            B; bsig.spoin ⊢ bprom(bsig.σ.head σnn) WF-cont)
            ⟨λ ⟨a, b, c⟩ => spoin a b c, λ | spoin a b c => ⟨a, b, c⟩⟩

    -- Accessor methods
    theorem stmt_expr {P B bsig e c} : P; B; bsig ⊢ (.stmt e c) WF-code -> bsig.Γ ⊢ e WF-expr
      | stmt ewf _cwf => ewf
    theorem stmt_code {P B bsig e c} : P; B; bsig ⊢ (.stmt e c) WF-code -> P; B; bsig.bind ⊢ c WF-code
      | stmt _ewf cwf => cwf

    theorem goto_bnext {P B bsig bnext} :
                       P; B; bsig ⊢ (.goto bnext) WF-code ->
                       B; bsig ⊢ bnext WF-cont
      | goto bnextwf => bnextwf

    theorem ite_cond {P B bsig cond bthen belse} :
                     P; B; bsig ⊢ (.ite cond bthen belse) WF-code ->
                     bsig.Γ ⊢ cond WF-atom
      | ite condwf _ _ => condwf
    theorem ite_bthen {P B bsig cond bthen belse} :
                      P; B; bsig ⊢ (.ite cond bthen belse) WF-code ->
                      B; bsig ⊢ bthen WF-cont
      | ite _ bthenwf _ => bthenwf
    theorem ite_belse {P B bsig cond bthen belse} :
                      P; B; bsig ⊢ (.ite cond bthen belse) WF-code ->
                      B; bsig ⊢ belse WF-cont
      | ite _ _ belsewf => belsewf

    theorem call_flt {P B bsig f args bret} :
                     P; B; bsig ⊢ (.call f args bret) WF-code ->
                     f < P.length
      | call flt _ _ _ => flt
    theorem call_arity {P B bsig f args bret} :
                       (wf : P; B; bsig ⊢ (.call f args bret) WF-code) ->
                       (P[f]'wf.call_flt).arity = args.length
      | call _ aritywf _ _ => aritywf
    theorem call_args {P B bsig f args bret} :
                      P; B; bsig ⊢ (.call f args bret) WF-code ->
                      IVec (bsig.Γ ⊢ · WF-var) args
      | call _ _ argswf _ => argswf
    theorem call_bret {P B bsig f args bret} :
                      (wf : P; B; bsig ⊢ (.call f args bret) WF-code) ->
                      B; bsig ⊢ bret((P[f]'wf.call_flt).ret) WF-cont
      | call _ _ _ bretwf => bretwf

    theorem retn_length {P B bsig args} :
                        P; B; bsig ⊢ (.retn args) WF-code ->
                        bsig.r.n = args.length
      | retn n _ _ => n
    theorem retn_oblg {P B bsig args} :
                      P; B; bsig ⊢ (.retn args) WF-code ->
                      bsig.σ = []
      | retn _ σ _ => σ
    theorem retn_args {P B bsig args} :
                      P; B; bsig ⊢ (.retn args) WF-code ->
                      IVec (bsig.Γ ⊢ · WF-var) args
      | retn _ _ a => a
    
    theorem spork_exit {P B bsig bbody bspwn} :
                       (wf : P; B; bsig ⊢ (.spork bbody bspwn) WF-code) ->
                       B[bspwn.b]!.r.isExit
      | spork isexit _ _ => isexit

    theorem spork_bbody {P B bsig bbody bspwn} :
                        (wf : P; B; bsig ⊢ (.spork bbody bspwn) WF-code) ->
                        B; (bsig.spork B[bspwn.b]!.r.n) ⊢ bbody WF-cont
      | spork _ bbodywf _ => bbodywf

    theorem spork_bspwn {P B bsig bbody bspwn} :
                        (wf : P; B; bsig ⊢ (.spork bbody bspwn) WF-code) ->
                        B; (bsig.spwn B[bspwn.b]!.r.n) ⊢ bspwn WF-cont
      | spork _ _ bspwnwf => bspwnwf

    theorem spoin_oblg {P B bsig bunpr bprom} :
                       P; B; bsig ⊢ (.spoin bunpr bprom) WF-code ->
                       bsig.σ ≠ []
      | spoin issp _ _ => issp
    theorem spoin_bunpr {P B bsig bunpr bprom} :
                        P; B; bsig ⊢ (.spoin bunpr bprom) WF-code ->
                        B; bsig.spoin ⊢ bunpr WF-cont
      | spoin _ bunprwf _ => bunprwf
    theorem spoin_bprom {P B bsig bunpr bprom} :
                        (wf : P; B; bsig ⊢ (.spoin bunpr bprom) WF-code) ->
                        B; bsig.spoin ⊢ bprom(bsig.σ.head wf.spoin_oblg) WF-cont
      | spoin _ _ bpromwf => bpromwf

    theorem weaken_Bₗ {P B B' bsig c} : P; B; bsig ⊢ c WF-code ->
                      P; (B ++ B'); bsig ⊢ c WF-code
      | stmt ewf cwf =>
        stmt ewf cwf.weaken_Bₗ
      | goto bnextwf =>
        goto bnextwf.weaken_Bₗ
      | ite ewf bthenwf belsewf =>
        ite ewf bthenwf.weaken_Bₗ belsewf.weaken_Bₗ
      | call flt aritywf argswf bretwf =>
        call flt aritywf argswf bretwf.weaken_Bₗ
      | retn r σ argswf =>
        retn r σ argswf
      | spork (bspwn := bspwn) isexit bbodywf bspwnwf =>
        let h := List.getElem?_append_left bspwnwf.blt (l₂ := B')
        spork (by simpa[h] using isexit)
              (by simpa[h] using bbodywf.weaken_Bₗ)
              (by simpa[h] using bspwnwf.weaken_Bₗ)
      | spoin snwf bunprwf bpromwf =>
        spoin snwf bunprwf.weaken_Bₗ bpromwf.weaken_Bₗ

    theorem weaken_Bᵣ {P B B' bsig c} : P; B'; bsig ⊢ c WF-code ->
                      P; (B ++ B'); bsig ⊢ c.offset_B B.length WF-code
      | stmt ewf cwf =>
        stmt ewf cwf.weaken_Bᵣ
      | goto bnextwf =>
        goto bnextwf.weaken_Bᵣ
      | ite ewf bthenwf belsewf =>
        ite ewf bthenwf.weaken_Bᵣ belsewf.weaken_Bᵣ
      | call flt aritywf argswf bretwf =>
        call flt aritywf argswf bretwf.weaken_Bᵣ
      | retn r σ argswf =>
        retn r σ argswf
      | spork (bspwn := bspwn) isexit bbodywf bspwnwf =>
        let blt : bspwn.b < B'.length := bspwnwf.blt
        let blt' : bspwn.b + B.length < (B ++ B').length :=
          by simpa[Nat.add_comm bspwn.b B.length] using blt
        let h? : (B ++ B')[bspwn.b + B.length]? = B'[bspwn.b]? :=
          by simp[List.getElem?_eq_getElem blt']
        spork (by simpa[h?] using isexit)
              (by simpa[h?] using bbodywf.weaken_Bᵣ)
              (by simpa[h?] using bspwnwf.weaken_Bᵣ)
      | spoin snwf bunprwf bpromwf =>
        spoin snwf bunprwf.weaken_Bᵣ bpromwf.weaken_Bᵣ

    theorem weaken_Γ {P B Γ bsig c} : P; B; bsig ⊢ c WF-code ->
                     P; B; (bsig.binds Γ) ⊢ c WF-code
      | stmt ewf cwf =>
        stmt ewf.weaken (by simp[BlockSig.bind, BlockSig.binds]
                            rw[  Nat.add_assoc bsig.Γ Γ 1,
                                 Nat.add_comm Γ 1,
                               ← Nat.add_assoc bsig.Γ 1 Γ]
                            exact cwf.weaken_Γ)
      | goto bnextwf =>
        goto bnextwf.weaken_Γ
      | ite ewf bthenwf belsewf =>
        ite ewf.weaken bthenwf.weaken_Γ belsewf.weaken_Γ
      | call flt aritywf argswf bretwf =>
        call flt aritywf argswf.weaken bretwf.weaken_Γ
      | retn r σ argswf =>
        retn r σ argswf.weaken
      | spork (bspwn := bspwn) isexit bbodywf bspwnwf =>
        spork isexit bbodywf.weaken_Γ bspwnwf.weaken_Γ
      | spoin snwf bunprwf bpromwf =>
        spoin snwf bunprwf.weaken_Γ bpromwf.weaken_Γ

    theorem merge_wf {P B bsig} :
            {e : List Expr} -> {c : Code} ->
            (∀ i : Fin e.length, (bsig.Γ + i) ⊢ e[i] WF-expr) ->
            P; B; (bsig.binds e.length) ⊢ c WF-code ->
            P; B; bsig ⊢ (c.merge e) WF-code
      | [], c, ewf, cwf => by simpa using cwf
      | e :: es, c, ewf, cwf =>
        .stmt (ewf ⟨0, by simp⟩)
          (merge_wf (bsig := bsig.bind) (e := es)
            (λ i => let ewf' := ewf ⟨i.1 + 1, by simp⟩
                    by simp[← Nat.add_assoc bsig.1 1 i.1] at ewf'
                       simp[BlockSig.bind]
                       rw[Nat.add_assoc, Nat.add_comm 1 i.1]
                       exact ewf')
            (match bsig with
              | .mk Γ r σ => by
                simp
                simp at cwf
                rw[Nat.add_comm es.length 1,
                   ← Nat.add_assoc] at cwf
                exact cwf))

    theorem split_wf {P B bsig} {c : Code} (cwf : P; B; bsig ⊢ c WF-code) :
            (∀ i : Fin c.split.1.length, (bsig.Γ + i) ⊢ c.split.1[i] WF-expr)
              ∧ P; B; (bsig.binds c.split.1.length) ⊢ c.split.2.1 WF-code := by
      cases c <;> try (exact And.intro (λ i => nomatch i) (by simpa using cwf))
      · case stmt e c =>
        let p := @split_wf P B bsig.bind c cwf.stmt_code
        apply And.intro
        · exact (λ | ⟨0, l⟩ => cwf.stmt_expr
                   | ⟨i + 1, l⟩ =>
                     by simpa[BlockSig.bind, Nat.add_assoc, Nat.add_comm 1 i]
                        using p.1 ⟨i, by simpa using l⟩)
        · (match h : bsig with
             | .mk Γ r σ =>
               simpa[h, Nat.add_assoc, Nat.add_comm 1]
               using p.2)
  end WF
end Code

namespace Block
  inductive WF (P B) (b : Block) : Prop where
    | mk (c : P; B; b.bsig ⊢ b.code WF-code)

  namespace WF
    notation (name := notationwf) P:arg "; " B:arg " ⊢ " b " WF-block" => WF P B b

    instance (P B) : {b : Block} -> Decidable (P; B ⊢ b WF-block)
      | .mk bsig code =>
        decidable_of_iff (P; B; bsig ⊢ code WF-code)
          ⟨λ a => mk a, λ | mk a => a⟩

    theorem code {P B b} : P; B ⊢ b WF-block ->
                 P; B; b.bsig ⊢ b.code WF-code
      | .mk c => c

    theorem weaken_Bₗ {P B B' b} : P; B ⊢ b WF-block ->
                      P; (B ++ B') ⊢ b WF-block
      | mk cwf => mk cwf.weaken_Bₗ
    theorem weaken_Bᵣ {P B B' b} : P; B' ⊢ b WF-block ->
                      P; (B ++ B') ⊢ b.offset_B B.length WF-block
      | mk cwf => mk cwf.weaken_Bᵣ
  end WF
end Block

namespace Blocks
  inductive WF (P : List FuncSig) (bs: List Block) (bsig: BlockSig) : Prop where
    | mk (blocks : IVec (P; (bs.map (·.bsig)) ⊢ · WF-block) bs)
         (retns : IVec (λ b => bsig.r.isRetn ∧ b.bsig.r.isRetn -> b.bsig.r = bsig.r) bs)
         (head : HeadIs bs (·.bsig) bsig)

  namespace WF
    notation (name := notationwf) P:arg "; " bsig:arg " ⊢ " bs " WF-blocks" => WF P bs bsig

    instance wf {P bs bsig}: Decidable (P; bsig ⊢ bs WF-blocks) :=
      decidable_of_iff (IVec (P; (bs.map (·.bsig)) ⊢ · WF-block) bs ∧
                        IVec (λ b => bsig.r.isRetn ∧ b.bsig.r.isRetn -> b.bsig.r = bsig.r) bs ∧
                        HeadIs bs (·.bsig) bsig)
        ⟨λ ⟨a, b, c⟩ => mk a b c, λ | mk a b c => ⟨a, b, c⟩⟩

    theorem blocks {P bs bsig} : P; bsig ⊢ bs WF-blocks -> IVec (P; (bs.map (·.bsig)) ⊢ · WF-block) bs
      | .mk blocks _retns _head => blocks
    theorem retns {P bs bsig} : P; bsig ⊢ bs WF-blocks -> IVec (λ b => bsig.r.isRetn ∧ b.bsig.r.isRetn -> b.bsig.r = bsig.r) bs
      | .mk _blocks retns _head => retns
    theorem head {P bs bsig} : P; bsig ⊢ bs WF-blocks -> HeadIs bs (·.bsig) bsig
      | .mk _blocks _retns head => head

    theorem add_blocks
            {P bs bs' bsig} :
            P; bsig ⊢ bs WF-blocks ->
            IVec (P; ((bs ++ bs').map (·.bsig)) ⊢ · WF-block) bs' ->
            IVec (λ b => bsig.r.isRetn ∧ b.bsig.r.isRetn -> b.bsig.r = bsig.r) bs' ->
            P; bsig ⊢ (bs ++ bs') WF-blocks
      | .mk blocks retns head, bs'wf, retns' =>
        .mk (IVec.append (blocks.map
              (λ b bwf => by simpa using bwf.weaken_Bₗ)) bs'wf)
            (IVec.append retns retns')
            ⟨by rw[List.head?_eq_some_head,
                   List.head_append_left head.nonnil,
                   ← head.head?eq,
                   List.head?_eq_head head.nonnil]⟩
  end WF
end Blocks

namespace Func
  abbrev WF (P: List FuncSig) (f: Func): Prop :=
    P; ⟨f.fsig.arity, .retn f.fsig.ret, []⟩ ⊢ f.blocks WF-blocks

  namespace WF
    notation (name := notationwf) P:arg " ⊢ " f " WF-func" => WF P f
    notation (name := notationwf') P:arg " ⊢ " f " WF-func'" => WF (Program.P P) f
    
    instance {P f}: Decidable (P ⊢ f WF-func) := Blocks.WF.wf

    theorem blocks {P f} : P ⊢ f WF-func ->
                   IVec (P; (f.blocks.map (·.bsig)) ⊢ · WF-block) f.blocks
      := Blocks.WF.blocks
    theorem retns {P f} (wf : P ⊢ f WF-func) :
                  IVec (λ b => b.bsig.r.isRetn -> b.bsig.r = .retn f.fsig.ret) f.blocks
      := (Blocks.WF.retns wf).map (λ _b br bretn => br ⟨rfl, bretn⟩)
    theorem head {P f} : P ⊢ f WF-func ->
                 HeadIs f.blocks (·.bsig) ⟨f.fsig.arity, .retn f.fsig.ret, []⟩
      := Blocks.WF.head

    theorem add_blocks
            {P fsig bs bs'}
            (wf : P ⊢ (.mk fsig bs) WF-func)
            (bswf : IVec (P; ((bs ++ bs').map (·.bsig)) ⊢ · WF-block) bs')
            (retns : IVec (λ b => b.bsig.r.isRetn -> b.bsig.r = .retn fsig.ret) bs') :
            P ⊢ (.mk fsig (bs ++ bs')) WF-func :=
      Blocks.WF.add_blocks wf bswf (retns.map λ _b br ⟨_, bretn⟩ => br bretn)

    theorem get {P f} (fwf : P ⊢ f WF-func) (j : Fin f.size) :
                P; (f.blocks.map (·.bsig)) ⊢ f[j] WF-block :=
      fwf.blocks⁅j⁆
  end WF
end Func

namespace Program
  inductive WF (P : Program): Prop where
    | mk (funcs : IVec (P.fsigs ⊢ · WF-func) P.funs)
         (main: HeadIs P.funs (·.fsig) ⟨0, 1⟩)

  namespace WF
    notation (name := notationwf) P:arg " WF-program" => WF P
    
    instance {P : Program}: Decidable (P WF-program) :=
      decidable_of_iff (IVec (P.fsigs ⊢ · WF-func) P.funs ∧
                        HeadIs P.funs (·.fsig) ⟨0, 1⟩)
          ⟨λ ⟨a, b⟩ => mk a b, λ | mk a b => ⟨a, b⟩⟩

    theorem funcs {P} : P WF-program -> IVec (P.fsigs ⊢ · WF-func) P.funs
      | .mk funcs _main => funcs
    theorem main {P} : P WF-program -> HeadIs P.funs (·.fsig) ⟨0, 1⟩
      | mk _funcs main => main

    theorem get {P} (Pwf : P WF-program) (j : Fin P.size) : P.fsigs ⊢ P[j] WF-func :=
      Pwf.funcs.get j
  end WF
end Program

