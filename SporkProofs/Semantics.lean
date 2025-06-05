import SporkProofs.Syntax

theorem congrArg₂ {α β γ} (f : α → β → γ) {x x' : α} {y y' : β}
    (hx : x = x') (hy : y = y') : f x y = f x' y' := by subst hx hy; rfl

-- TODO: inlining of nested parreduces!!

abbrev ValMap : Type := List Val

instance instValMapGetElem : GetElem ValMap Var Val (λ X x => x.Okay X.length) where
  getElem X x xₒₖ := X[x.idx]'xₒₖ.1

instance instValMapGetElems : GetElem ValMap (List Var) (List Val) (λ X => IVec (·.Okay X.length)) where
  getElem X _args argsₒₖ := argsₒₖ.map (λ x xₒₖ => X[x])

abbrev valOf (p : Prop) [d : Decidable p] : Val := if decide p then 1 else 0

namespace Atom
  abbrev eval : (X : ValMap) -> (a : Atom) -> (a.Okay X.length) -> Val
    | _X, .val v, _okᵥ => v
    | X, .var x, okₓ =>
      let _ := match okₓ with | .var p => p
      X[x]

  inductive Eval (X : ValMap) (a : Atom) : Val -> Prop where
    | mk (okₐ : a.Okay X.length) : Eval X a (eval X a okₐ)

  notation (name := atomeval) X:arg " ⊢ₐₜₒₘ " a:arg " ⇓ " v:arg => Eval X a v

  namespace Eval
    instance instDecidableEval : {X : ValMap} -> {a : Atom} -> {v : Val} -> Decidable (X ⊢ₐₜₒₘ a ⇓ v)
      | X, a, v => decidable_of_iff (∃ p : a.Okay X.length, eval X a p = v)
        ⟨λ ⟨okₐ, p⟩ => p ▸ Eval.mk okₐ,
         λ | (Eval.mk okₐ) => ⟨okₐ, rfl⟩⟩

    theorem okay {X : ValMap} {a : Atom} {v : Val} : Eval X a v -> a.Okay X.length
      | Eval.mk okₐ => okₐ
    theorem eq {X : ValMap} {a : Atom} {v : Val} : (s : Eval X a v) -> eval X a (okay s) = v
      | Eval.mk okₐ => rfl

    abbrev progress (X : ValMap) (a : Atom) (okₐ : a.Okay X.length) : Σ' v, Eval X a v :=
      ⟨eval X a okₐ, Eval.mk okₐ⟩
  end Eval
end Atom

namespace Bop
  abbrev eval : Bop -> Val -> Val -> Val
    | .IADD, u, v => u + v
    | .ISUB, u, v => u - v
    | .IMUL, u, v => u * v
    | .IDIV, u, v => u / v
    | .IMOD, u, v => u % v
    | .ILT,  u, v => valOf (u < v)
    | .ILE,  u, v => valOf (u ≤ v)
    | .IGT,  u, v => valOf (u > v)
    | .IGE,  u, v => valOf (u ≥ v)
    | .IEQ,  u, v => valOf (u = v)
    | .INE,  u, v => valOf (u ≠ v)
    | .LAND, u, v => valOf (u ≠ 0 && v ≠ 0)
    | .LOR,  u, v => valOf (u ≠ 0 || v ≠ 0)
    | .LXOR, u, v => valOf (u ≠ 0 ^^ v ≠ 0)

  inductive Eval (o : Bop) (u v : Val) : Val -> Prop where
    | mk : Eval o u v (eval o u v)

  namespace Eval
    instance instDecidable {o : Bop} {u v w : Val} : Decidable (Eval o u v w) :=
      decidable_of_iff (eval o u v = w)
        ⟨λ p => p ▸ Eval.mk,
         λ | Eval.mk => rfl⟩

    theorem eq {o : Bop} {u v w : Val} : Eval o u v w -> eval o u v = w
      | Eval.mk => rfl

    abbrev progress (o : Bop) (u v : Val) : Σ' w, Eval o u v w :=
      ⟨eval o u v, Eval.mk⟩
  end Eval
end Bop

namespace Uop
  abbrev eval : Uop -> Val -> Val
    | INEG, v => -v
    | LNOT, v => valOf (v = 0)

  inductive Eval (o : Uop) (v : Val) : Val -> Prop where
    | mk : Eval o v (eval o v)

  namespace Eval
    instance instDecidable {o : Uop} {u v : Val} : Decidable (Eval o u v) :=
      decidable_of_iff (eval o u = v)
        ⟨λ p => p ▸ Eval.mk,
         λ | Eval.mk => rfl⟩

    theorem eq {o : Uop} {u v : Val} : Eval o u v -> eval o u = v
      | Eval.mk => rfl

    abbrev progress (o : Uop) (u : Val) : Σ' v, Eval o u v :=
      ⟨eval o u, Eval.mk⟩
  end Eval
end Uop

namespace Expr
  abbrev eval (X : ValMap) : (e : Expr) -> (e.Okay X.length) -> Val
    | nop a, ok =>
      let aₒₖ := match ok with | .nop aₒₖ => aₒₖ
      a.eval X aₒₖ
    | uop o a, ok =>
      let aₒₖ := match ok with | .uop aₒₖ => aₒₖ
      o.eval (a.eval X aₒₖ)
    | bop o a b, ok =>
      let aₒₖ := match ok with | .bop aₒₖ _ => aₒₖ
      let bₒₖ := match ok with | .bop _ bₒₖ => bₒₖ
      o.eval (a.eval X aₒₖ) (b.eval X bₒₖ)

  inductive Eval (X : ValMap) (e : Expr) : Val -> Prop where
    | mk (eₒₖ : e.Okay X.length) : Eval X e (eval X e eₒₖ)

  notation (name := expreval) X:arg " ⊢ₑₓₚᵣ " e:arg " ⇓ " v:arg => Eval X e v

  namespace Eval
    instance instDecidable {X : ValMap} {e : Expr} {v : Val} : Decidable (X ⊢ₑₓₚᵣ e ⇓ v) :=
      decidable_of_iff (∃ (eₒₖ : e.Okay X.length), eval X e eₒₖ = v)
        ⟨λ ⟨eₒₖ, p⟩ => p ▸ mk eₒₖ,
         λ | mk eₒₖ => ⟨eₒₖ, rfl⟩⟩

    theorem okay {X : ValMap} {e : Expr} {v: Val} : X ⊢ₑₓₚᵣ e ⇓ v -> e.Okay X.length
      | mk eₒₖ => eₒₖ
    theorem eq  {X : ValMap} {e : Expr} {v: Val} : (s : X  ⊢ₑₓₚᵣ e ⇓ v) -> eval X e (okay s) = v
      | mk eₒₖ => rfl

    abbrev progress (X : ValMap) (e : Expr) (eₒₖ : e.Okay X.length) : Σ' v, X  ⊢ₑₓₚᵣ e ⇓ v :=
      ⟨eval X e eₒₖ, Eval.mk eₒₖ⟩
  end Eval
end Expr

inductive StackFrameCode : Type
  | code (c : Code)
  | cont (b : Cont)
-- open StackFrameCode code cont

inductive SpawnCall : Type where
  | mk (f : FuncIdx) (args : List Val) (ret : Nat)

inductive SpawnDeque : Type where
  -- unpromoted sporks, oldest first (queue)
  -- promoted sporks, oldest last (stack)
  | mk (unpr : List SpawnCall) (prom : SporkSig)

inductive StackFrame : Type
  | mk (f : FuncIdx)
       (ρ : SpawnDeque)
       (X : ValMap)
       (c : StackFrameCode)

inductive CallStack : Type where
  | nil
  | cons (K : CallStack) (k : StackFrame)

inductive ThreadPool : Type where
  | leaf : CallStack -> ThreadPool
  | cat : ThreadPool -> ThreadPool -> ThreadPool

namespace StackFrameCode
  -- instance instCoeToSum : Coe (Code ⊕ Cont) StackFrameCode where
  --   coe := Sum.elim code cont
  -- instance instCoeFmSum : Coe StackFrameCode (Code ⊕ Cont) where
  --   coe := fun | code c => Sum.inl c | cont k => Sum.inr k
  
  abbrev isCode | code _ => true | cont _ => false
  abbrev isCont | code _ => false | cont _ => true

  abbrev extractD : (c : StackFrameCode) -> if isCode c then Code else Cont
    | code c => c
    | cont b => b
  abbrev extractCode : (c : StackFrameCode) -> isCode c -> Code
    | code c, _ => c
  abbrev extractCont : (c : StackFrameCode) -> isCont c -> Cont
    | cont b, _ => b

  inductive Okay (fsigs bsigs bsig ret) : StackFrameCode -> Prop
    | code {c} : c.Okay fsigs bsigs ret bsig -> (code c).Okay fsigs bsigs bsig ret
    | cont {b} : b.OkayRets bsigs bsig ret -> (cont b).Okay fsigs bsigs bsig ret

  namespace Okay
    abbrev c {fsigs bsigs bsig ret c} :
             Okay fsigs bsigs bsig ret (.code c) ->
             c.Okay fsigs bsigs ret bsig
      | code c => c

    abbrev b {fsigs bsigs bsig b ret} :
             Okay fsigs bsigs bsig ret (.cont b) ->
             b.OkayRets bsigs bsig ret
      | cont b => b
  end Okay

  instance instDecidable {fsigs bsigs bsig ret} :
                         (c : StackFrameCode) ->
                         Decidable (c.Okay fsigs bsigs bsig ret)
    | code c =>
      decidable_of_iff (c.Okay fsigs bsigs ret bsig)
        ⟨Okay.code, λ | Okay.code p => p⟩
    | cont b =>
      decidable_of_iff (b.OkayRets bsigs bsig ret)
        ⟨Okay.cont, λ | Okay.cont p => p⟩

  -- instance instDecidableEq : DecidableEq StackFrameCode
  --   | code c, code c' =>
  --     decidable_of_iff (c = c')
  --       ⟨congrArg code, congrArg (λ | code c => c | _ => c)⟩
  --   | cont b, cont b' =>
  --     decidable_of_iff (b = b')
  --       ⟨congrArg cont, congrArg (λ | cont b => b | _ => b)⟩
  --   | code c, cont b => isFalse (by simp)
  --   | cont b, code c => isFalse (by simp)
  deriving instance DecidableEq for StackFrameCode
end StackFrameCode

namespace SpawnCall
  abbrev f | mk f _args _ret => f
  abbrev args | mk _f args _ret => args
  abbrev ret | mk _f _args ret => ret

  inductive Okay (fsigs : FuncSigs) (sc : SpawnCall) : Prop where
    | mk (_ : sc.f < fsigs.length)
         (_ : ⟨sc.args.length, sc.ret⟩ = fsigs[sc.f]) :
         sc.Okay fsigs

  namespace Okay
    abbrev flt {fsigs} {sc : SpawnCall} : sc.Okay fsigs -> sc.f < fsigs.length | mk flt _ => flt
    abbrev sig {fsigs} {sc : SpawnCall} : (ok : sc.Okay fsigs) -> ⟨sc.args.length, sc.ret⟩ = fsigs[sc.f]'ok.flt | mk _ sig => sig
  end Okay

  instance instDecidable {fsigs : FuncSigs} : (sc : SpawnCall) -> Decidable (sc.Okay fsigs)
    | mk f args ret =>
      decidable_of_iff (∃ _ : f < fsigs.length, ⟨args.length, ret⟩ = fsigs[f])
        ⟨λ ⟨p, q⟩ => Okay.mk p q,
         λ | Okay.mk p q => ⟨p, q⟩⟩
  
  -- instance instDecidableEq : DecidableEq SpawnCall
  --   | mk f args ret, mk f' args' ret' =>
  --     decidable_of_iff ((f, args, ret) = (f', args', ret'))
  --       ⟨congrArg (λ (f, args, ret) => mk f args ret),
  --        congrArg (λ | mk f args ret => (f, args, ret))⟩
  deriving instance DecidableEq for SpawnCall
end SpawnCall

namespace SpawnDeque
  abbrev unpr : SpawnDeque -> List SpawnCall
    | ⟨u, _p⟩ => u
  abbrev prom : SpawnDeque -> SporkSig
    | ⟨_u, p⟩ => p

  abbrev SpawnOrder (canProm : Bool) (prom : SporkSig) : Prop :=
    prom = (if canProm then prom else [])

  namespace SpawnOrder
    theorem of_nil {canProm : Bool} : SpawnOrder canProm [] :=
      by cases canProm <;> rfl
    theorem prom_canProm_true : (canProm : Bool) -> {gret : Nat} -> {prom : SporkSig} ->
                                SpawnOrder canProm (gret :: prom) -> canProm = true
      | true, _gret, _prom, _so => rfl
  end SpawnOrder

  inductive Okay (fsigs : FuncSigs) (canProm : Bool) : SpawnDeque -> Prop
    | mk {unpr : List SpawnCall} {prom : SporkSig} :
         IVec (·.Okay fsigs) unpr ->
         SpawnOrder canProm prom ->
         (mk unpr prom).Okay fsigs canProm

  namespace Okay
    abbrev unpr {fsigs canProm} {ρ : SpawnDeque} : ρ.Okay fsigs canProm -> IVec (·.Okay fsigs) ρ.unpr | mk u _p => u
    abbrev prom {fsigs canProm} {ρ : SpawnDeque} : ρ.Okay fsigs canProm -> SpawnOrder canProm ρ.prom | mk _u p => p

    theorem castCanProm {fsigs ρ} : {canProm : Bool} -> (canProm' : Bool) -> canProm ≤ canProm' -> Okay fsigs canProm ρ -> Okay fsigs canProm' ρ
      | false, false, _, .mk u p => .mk u p
      | true, true, _, .mk u p => .mk u p
      | false, true, _, .mk u _p => .mk u rfl

    theorem promote {fsigs u p g} (ok : Okay fsigs true ⟨g :: u, p⟩) :
                    Okay fsigs true ⟨u, g.ret :: p⟩ :=
      ⟨ok.unpr.tail, rfl⟩
  end Okay
  
  abbrev sig : SpawnDeque -> SporkSig
    | mk u p => List.reverseAux (u.map (·.ret)) p
  abbrev push : SpawnDeque -> SpawnCall -> SpawnDeque
    | ⟨u, p⟩, sc => ⟨u.concat sc, p⟩
  abbrev pop_prom : SpawnDeque -> SpawnDeque
    | ⟨sc :: u, p⟩ => ⟨u, sc.ret :: p⟩
    | ⟨[], p⟩ => ⟨[], p⟩
  theorem pushsig (ρ : SpawnDeque) (sc : SpawnCall)
                  : (ρ.push sc).sig = sc.ret :: ρ.sig :=
    by simp
  instance empty_collection : EmptyCollection SpawnDeque := ⟨⟨[], []⟩⟩

  instance instDecidable {fsigs canProm} : (ρ : SpawnDeque) -> Decidable (ρ.Okay fsigs canProm)
    | mk u p => decidable_of_iff
        (IVec (·.Okay fsigs) u ∧ SpawnOrder canProm p)
        ⟨λ ⟨a, b⟩ => Okay.mk a b, λ | Okay.mk a b => ⟨a, b⟩⟩

  -- instance instDecidableEq : DecidableEq SpawnDeque
  --   | mk u p, mk u' p' => decidable_of_iff ((u, p) = (u', p'))
  --     ⟨congrArg (λ (u, p) => mk u p),
  --      congrArg (λ | mk u p => (u, p))⟩
  deriving instance DecidableEq for SpawnDeque

  theorem empty_okay {fsigs canProm} : SpawnDeque.Okay fsigs canProm ∅ :=
    ⟨.nil, .of_nil⟩
end SpawnDeque

namespace StackFrame
  abbrev f | mk f _ρ _X _c => f
  abbrev ρ | mk _f ρ _X _c => ρ
  abbrev X | mk _f _ρ X _c => X
  abbrev c | mk _f _ρ _X c => c
  abbrev bsig | mk _f ρ X _c => BlockSig.mk X.length ρ.sig

  inductive Okay (Pr : Program) (curr : Option Nat) (canProm : Bool) : StackFrame -> Prop where
    | mk {f ρ X c} :
         (_ : f < Pr.size) ->
         ρ.Okay Pr.fsigs canProm ->
         (if curr.isNone then c.isCode else c.isCont) = true ->
         c.Okay Pr.fsigs Pr.funs[f].bsigs ⟨X.length, ρ.sig⟩
                (curr.elim Pr.funs[f].fsig.ret id) ->
         (mk f ρ X c).Okay Pr curr canProm

  namespace Okay
    theorem flt {Pr curr canProm} : {k : StackFrame} -> k.Okay Pr curr canProm -> k.f < Pr.size
      | .mk _f _ρ _X _c, mk flt _ρₒₖ _cₒₖ _cb => flt
  end Okay

  abbrev func {Pr curr canProm} (k : StackFrame) (kₒₖ : k.Okay Pr curr canProm) : Func :=
    Pr.funs[k.f]'kₒₖ.flt

  namespace Okay
    -- abbrev func {Pr curr canProm} {k : StackFrame} (kₒₖ : k.Okay Pr curr canProm) : Func :=
    --   k.func kₒₖ
    -- abbrev ret {Pr curr canProm} {k : StackFrame} (kₒₖ : k.Okay Pr curr canProm) : Nat :=
    --   kₒₖ.func.fsig.ret
    theorem ρₒₖ {Pr curr canProm} : {k : StackFrame} -> k.Okay Pr curr canProm -> k.ρ.Okay Pr.fsigs canProm
      | .mk _f _ρ _X _c, mk _flt ρₒₖ _cₒₖ _cb => ρₒₖ
    theorem cₒₖ {Pr curr canProm} : {k : StackFrame} -> (kₒₖ : k.Okay Pr curr canProm) ->
                k.c.Okay Pr.fsigs (k.func kₒₖ).bsigs k.bsig
                         (curr.elim (k.func kₒₖ).fsig.ret id)
      | .mk _f _ρ _X _c, mk _flt _ρₒₖ _cb cₒₖ => cₒₖ
    theorem cₒₖ' {Pr curr canProm} : {k : StackFrame} -> (kₒₖ : k.Okay Pr curr canProm) ->
                 k.c.Okay Pr.fsigs Pr.funs[k.f]!.bsigs k.bsig
                          (curr.elim Pr.funs[k.f]!.fsig.ret id)
      | .mk f _ρ _X _c, mk flt _ρₒₖ _cb cₒₖ =>
        getElem!_pos Pr.funs f flt ▸ cₒₖ
    theorem cₒₖ'' {Pr curr canProm} : {k : StackFrame} -> (kₒₖ : k.Okay Pr curr canProm) ->
                  let flt : k.f < Pr.size := kₒₖ.flt
                  k.c.Okay Pr.fsigs Pr.funs[k.f].bsigs k.bsig
                           (curr.elim Pr.funs[k.f].fsig.ret id)
      | .mk _f _ρ _X _c, mk _flt _ρₒₖ _cb cₒₖ => cₒₖ
    theorem cb {Pr curr canProm} : {k : StackFrame} -> (kₒₖ : k.Okay Pr curr canProm) ->
               (if curr.isNone then k.c.isCode else k.c.isCont) = true
      | .mk _f _ρ _X _c, mk _flt _ρₒₖ cb _cₒₖ => cb
    theorem isCode {Pr canProm} : {k : StackFrame} ->
                   (kₒₖ : k.Okay Pr none canProm) -> k.c.isCode := cb
    theorem isCont {Pr canProm ret} : {k : StackFrame} ->
                   (kₒₖ : k.Okay Pr (some ret) canProm) -> k.c.isCont := cb

    theorem castCanProm {Pr curr canProm} : {k : StackFrame} ->
                        (canProm' : Bool) -> canProm ≤ canProm' ->
                        (kₒₖ : k.Okay Pr curr canProm) -> k.Okay Pr curr canProm'
      | .mk _f _ρ _X _c, canProm', l, .mk flt ρₒₖ cₒₖ cb =>
        .mk flt (ρₒₖ.castCanProm canProm' l) cₒₖ cb
  end Okay

  instance instDecidable {Pr curr canProm} : (k : StackFrame) -> Decidable (k.Okay Pr curr canProm)
    | mk f ρ X c =>
      decidable_of_iff (∃ _ : f < Pr.size,
                        ρ.Okay Pr.fsigs canProm ∧
                        (if curr.isNone then c.isCode else c.isCont) = true ∧
                        c.Okay Pr.fsigs Pr.funs[f].bsigs ⟨X.length, ρ.sig⟩
                          (curr.elim Pr.funs[f].fsig.ret id))
        ⟨λ ⟨a, b, c, d⟩ => Okay.mk a b c d,
         λ | Okay.mk a b c d => ⟨a, b, c, d⟩⟩

  -- instance instDecidableEq : DecidableEq StackFrame
  --   | mk f ρ X c, mk f' ρ' X' c' =>
  --     decidable_of_iff ((f, ρ, X, c) = (f', ρ', X', c'))
  --       ⟨congrArg (λ (a, b, c, d) => mk a b c d),
  --        congrArg (λ | mk a b c d => (a, b, c, d))⟩
  deriving instance DecidableEq for StackFrame
end StackFrame

namespace CallStack
  notation (name := callstackcons) t " ⬝ " h:arg => cons t h

  abbrev appendh : CallStack -> CallStack -> CallStack
    | K, nil => K
    | K, K' ⬝ k => (appendh K K') ⬝ k

  instance instAppend : Append CallStack where
    append := appendh
  instance instSingleton : Singleton StackFrame CallStack where
    singleton k := nil ⬝ k
  instance instEmptyCollection : EmptyCollection CallStack where
    emptyCollection := nil

  abbrev prom : CallStack -> SporkSig
    | nil => []
    | K ⬝ k => k.ρ.prom ++ prom K
  abbrev unpr : CallStack -> List SpawnCall
    | nil => []
    | K ⬝ k => unpr K ++ k.ρ.unpr
  abbrev allPromoted (K : CallStack) : Bool := K.unpr = []
  abbrev allPromoted_imp_nil {K} (p : allPromoted K) : K.unpr = [] := by simp_all
  abbrev nil_imp_allPromoted {K} (p : unpr K = []) : K.allPromoted := by simp_all
  abbrev firstFrame : (K : CallStack) -> K ≠ nil -> StackFrame
    | nil ⬝ k, p => k
    | K  ⬝ k ⬝ _k', p => firstFrame (K ⬝ k) (by simp)

  @[simp] theorem append_cons : {K K' : CallStack} -> {k : StackFrame} -> K ++ (K' ⬝ k) = (K ++ K') ⬝ k
    | _K, nil, _k => rfl
    | _K, _K' ⬝ _k', k => congrArg (· ⬝ k) append_cons
  @[simp] theorem append_nil : {K : CallStack} -> K ++ nil = K := rfl
  @[simp] theorem nil_append : {K : CallStack} -> nil ++ K = K
    | .nil => rfl
    | _K ⬝ _k => append_cons ▸ nil_append ▸ rfl
  theorem append_assoc : {K K' K'' : CallStack} -> (K ++ K') ++ K'' = K ++ (K' ++ K'')
    | _K, _K', nil => rfl
    | _K, _K', _K'' ⬝ k =>
      append_cons ▸ append_cons ▸ congrArg (· ⬝ k) append_assoc
  theorem append_unpr : {K K' : CallStack} -> (K ++ K').unpr = K.unpr ++ K'.unpr
    | K, nil => by simp
    | K, K' ⬝ k => by simp[unpr]; rw[← List.append_assoc, ← append_unpr]; rfl
  theorem append_prom : {K K' : CallStack} -> (K ++ K').prom = K'.prom ++ K.prom
    | K, nil => by simp
    | K, K' ⬝ k => by simp; exact append_prom
  -- theorem prom_nil_of_cons {K k} : (K ⬝ k).prom = [] -> k.ρ.prom = [] ∧ K.prom = [] :=
  --   List.append_eq_nil_iff.mp

  abbrev head : (K : CallStack) -> K ≠ nil -> StackFrame
    | _K ⬝ k, _ => k
  abbrev tail : CallStack -> CallStack
    | K ⬝ _k => K
    | nil => nil

  abbrev retjoin (Pr : Program) : CallStack -> Nat
    | nil => default
    | nil ⬝ ⟨f, _, _, _⟩ => Pr.funs[f]!.fsig.ret
    | K ⬝ _k => K.retjoin Pr

  @[simp] theorem retjoin_first {Pr : Program} : {k : StackFrame} -> {K : CallStack} -> ({k} ++ K).retjoin Pr = Pr.funs[k.f]!.fsig.ret
    | k, .nil => rfl
    | k, .nil ⬝ k' => rfl
    | k, K ⬝ k' ⬝ k'' => by
        simp only[retjoin]
        exact retjoin_first (K := K ⬝ k')

  inductive Okay (Pr : Program) : (get : Option Nat) -> CallStack -> Prop where
    | nil {gets} : nil.Okay Pr (some gets)
    | cons {K k gets} :
           (kₒₖ : k.Okay Pr gets K.allPromoted) ->
           K.Okay Pr (k.func kₒₖ).fsig.ret ->
           (K ⬝ k).Okay Pr gets

  namespace Okay
    notation (name := callstackokaycons) t " ⬝ₒₖ " h:arg => Okay.cons h t
    theorem nonnil {Pr} {K : CallStack} (Kₒₖ : K.Okay Pr none) : K ≠ CallStack.nil :=
      by cases Kₒₖ; simp
    theorem head' {Pr gets} :
                  {K : CallStack} ->
                  (nn : K ≠ CallStack.nil) ->
                  K.Okay Pr gets ->
                  (K.head nn).Okay Pr gets K.tail.allPromoted
      | _K ⬝ _k, _nn, _Kₒₖ ⬝ₒₖ kₒₖ => kₒₖ
    theorem tail' {Pr gets} :
                  {K : CallStack} ->
                  (nn : K ≠ CallStack.nil) ->
                  (Kₒₖ : K.Okay Pr gets) ->
                  K.tail.Okay Pr (some (Pr.funs[(K.head nn).f]'(Kₒₖ.head' nn).flt).fsig.ret)
      | _K ⬝ _k, _nn, Kₒₖ ⬝ₒₖ _kₒₖ => Kₒₖ

    theorem head {Pr gets K k} (Kₒₖ : (K ⬝ k).Okay Pr gets) :
                 k.Okay Pr gets K.allPromoted :=
      head' (by simp) Kₒₖ

    theorem tail {Pr gets K k} (Kₒₖ : (K ⬝ k).Okay Pr gets) :
                  K.Okay Pr (some (Pr.funs[k.f]'Kₒₖ.head.flt).fsig.ret) :=
      tail' (by simp) Kₒₖ
  end Okay

  instance instDecidable {Pr} : {gets : Option Nat} -> (K : CallStack) -> Decidable (K.Okay Pr gets)
    | some gets, nil => isTrue Okay.nil
    | none, nil => isFalse (by cases ·)
    | gets, K ⬝ k =>
      dite (k.Okay Pr gets K.allPromoted)
        (λ kₒₖ => let Kₒₖdec : Decidable (K.Okay Pr (some (k.func kₒₖ).fsig.ret)) := instDecidable K
                  decidable_of_iff (K.Okay Pr (some (k.func kₒₖ).fsig.ret))
                    ⟨Okay.cons kₒₖ, λ | Okay.cons _kₒₖ' Kₒₖ => Kₒₖ⟩)
        (isFalse ∘ λ | kₙₒₖ, .cons kₒₖ _Kₒₖ => kₙₒₖ kₒₖ)

  deriving instance DecidableEq for CallStack

  abbrev retjoin?! {Pr get} : (K : CallStack) -> K.Okay Pr get -> Option Nat
    | .nil, _ok => none
    | .nil ⬝ k, ok => some (k.func ok.head).fsig.ret
    | K ⬝ _k, ok => K.retjoin?! ok.tail
  
  theorem retjoin_eq_retjoin?! {Pr get} : {K : CallStack} -> (ok : K.Okay Pr get) ->
          (if K = .nil then none else some (K.retjoin Pr)) = K.retjoin?! ok
    | .nil, ok =>
      rfl
    | .nil ⬝ k, (_ ⬝ₒₖ kok) =>
      by simp[retjoin, getElem!_pos Pr.funs k.f kok.flt]
    | K ⬝ k ⬝ k', ok =>
      retjoin_eq_retjoin?! (K := K ⬝ k) ok.tail

  namespace Okay

    theorem append {Pr} : {K K' : CallStack} -> {gets : Option Nat} -> K.Okay Pr (some (K'.retjoin Pr)) -> K'.Okay Pr gets -> (gets.isNone ∨ K' ≠ .nil) -> K.allPromoted -> (K ++ K').Okay Pr gets
      | K, .nil ⬝ k, gets, Kok, K'ok@(.nil ⬝ₒₖ kok), _, kprom =>
        by simp; exact
          (Option.some_inj.mp (retjoin_eq_retjoin?! K'ok) ▸ Kok) ⬝ₒₖ (kprom ▸ kok)
      | K, K' ⬝ k' ⬝ k, gets, Kok, K'ok ⬝ₒₖ kok, p, kprom =>
        let kprom' : K.unpr = [] := by simp_all[kprom]
        let kp : (K' ⬝ k').unpr = (K ++ (K' ⬝ k')).unpr :=
          by simp[append_unpr, kprom']
        (append Kok K'ok (Or.inr (by simp)) kprom) ⬝ₒₖ
          (by simp only[allPromoted, kp.symm]; exact kok)

    theorem unappend {Pr} : {get : Option Nat} -> {K K' : CallStack} -> (K ++ K').Okay Pr get -> (K' ≠ .nil) ->
                     K.allPromoted -> K.Okay Pr (some (K'.retjoin Pr)) ∧ K'.Okay Pr get
      | get, K, .nil ⬝ k, ok, _, kprom =>
        let ok' : (K ⬝ k).Okay Pr get :=
          by rw[@append_cons K .nil k] at ok; exact ok
        let k_ok : k.Okay Pr get true :=
          kprom ▸ ok'.head
        ⟨by simp[retjoin]
            rw[getElem?_pos Pr.funs k.f k_ok.flt]
            exact ok'.tail,
         .nil ⬝ₒₖ k_ok⟩
      | get, K, (K' ⬝ k') ⬝ k, ok, _, kprom =>
        let ⟨Kok, K'ok⟩ := unappend ok.tail (by simp) kprom
        let kprom' : K.unpr = [] := by simp_all[kprom]
        let kp : [] ++ (K' ⬝ k').unpr = K.unpr ++ (K' ⬝ k').unpr :=
          kprom'.symm ▸ rfl
        let k'ok : k.Okay Pr get (K' ⬝ k').allPromoted := by
          show k.Okay Pr get ((K' ⬝ k').unpr = [])
          rw[← List.nil_append (K' ⬝ k').unpr, kp, ← append_unpr]
          exact ok.head
        ⟨Kok, K'ok ⬝ₒₖ k'ok⟩
  end Okay
end CallStack

namespace ThreadPool
  instance instAppend : Append ThreadPool where
    append := cat
  instance instSingleton : Singleton CallStack ThreadPool where
    singleton := ThreadPool.leaf
  instance instInsert : Insert CallStack ThreadPool where
    insert s p := {s} ++ p

  abbrev retjoin (Pr : Program) : ThreadPool -> Nat
    | leaf K => K.retjoin Pr
    | cat P _P' => P.retjoin Pr

  abbrev prom : ThreadPool -> SporkSig
    | leaf K => K.prom
    | cat P _P' => P.prom.tail

  inductive Okay (Pr : Program) : (ρ : SporkSig) -> ThreadPool -> Prop where
    | leaf {K} :
           (Kₒₖ : K.Okay Pr none) ->
           (leaf K).Okay Pr K.prom
    | cat {P P' ρ} :
          (Pₒₖ : P.Okay Pr (P'.retjoin Pr :: ρ)) ->
          (P'ₒₖ : P'.Okay Pr []) ->
          (cat P P').Okay Pr ρ

  namespace Okay
    abbrev get {Pr K ρ} : (ThreadPool.leaf K).Okay Pr ρ -> K.Okay Pr none
      | leaf Kₒₖ => Kₒₖ
    abbrev right {Pr P P' ρ} : (ThreadPool.cat P P').Okay Pr ρ -> P'.Okay Pr []
      | cat _Pₒₖ P'ₒₖ => P'ₒₖ
    abbrev left {Pr P P' ρ} : (ok : (ThreadPool.cat P P').Okay Pr ρ) -> P.Okay Pr (P'.retjoin Pr :: ρ)
      | cat Pₒₖ _P'ₒₖ => Pₒₖ
    
    theorem same_prom {Pr} : {P : ThreadPool} -> {ρ : SporkSig} ->
                      P.Okay Pr ρ -> P.prom = ρ
      | .cat P₁ P₂, ρ, .cat P₁ₒₖ P₂ₒₖ =>
        by simp[ThreadPool.prom, same_prom (ρ := P₂.retjoin Pr :: ρ) P₁ₒₖ]
      | .leaf K, .(K.prom), .leaf Kₒₖ => rfl
  end Okay

  -- TODO: generalize for child threads not starting from main
  abbrev init : ThreadPool := {{StackFrame.mk 0 ∅ ∅ (.cont (Cont.mk 0 []))}}
  abbrev child (f : FuncIdx) (args : List Val) : ThreadPool :=
    let vs := (List.range args.length).map Var.mk
    {{StackFrame.mk f ∅ args (.cont (Cont.mk 0 vs))}}

  instance instDecidable {Pr} : {ρ : SporkSig} -> (P : ThreadPool) -> Decidable (P.Okay Pr ρ)
    | ρ, leaf K => decidable_of_iff (ρ = K.prom ∧ K.Okay Pr none)
        ⟨λ ⟨p, Kₒₖ⟩ => p ▸ Okay.leaf Kₒₖ,
         λ | Okay.leaf Kₒₖ => ⟨rfl, Kₒₖ⟩⟩
    | ρ, cat P P' =>
      let _ : Decidable (P.Okay Pr (P'.retjoin Pr :: ρ)) := instDecidable P
      let _ : Decidable (P'.Okay Pr []) := instDecidable P'
      decidable_of_iff (P.Okay Pr (P'.retjoin Pr :: ρ) ∧ P'.Okay Pr [])
        ⟨λ ⟨Pₒₖ, P'ₒₖ⟩ => Okay.cat Pₒₖ P'ₒₖ,
         λ | Okay.cat Pₒₖ P'ₒₖ => ⟨Pₒₖ, P'ₒₖ⟩⟩

  deriving instance DecidableEq for ThreadPool


  inductive Okay' (Pr : Program) : ThreadPool -> Prop where
    | leaf {K} :
           (Kₒₖ : K.Okay Pr none) ->
           (leaf K).Okay' Pr
    | cat {P P'} :
          (Pₒₖ : P.Okay' Pr) ->
          (P'ₒₖ : P'.Okay' Pr) ->
          (P.prom.head? = some (P'.retjoin Pr)) ->
          (P'.prom = []) ->
          (cat P P').Okay' Pr

  namespace Okay
    theorem to_okay' {Pr : Program} : {P : ThreadPool} -> {ρ : SporkSig} ->
                     P.Okay Pr ρ -> P.Okay' Pr
      | .leaf K, .(K.prom), .leaf Kₒₖ =>
        .leaf Kₒₖ
      | .cat _P _P', _ρ, .cat Pₒₖ P'ₒₖ =>
        .cat Pₒₖ.to_okay' P'ₒₖ.to_okay'
          (Pₒₖ.same_prom ▸ rfl) P'ₒₖ.same_prom
  end Okay

  namespace Okay'
    theorem to_okay {Pr : Program} : {P : ThreadPool} ->
                     P.Okay' Pr -> P.Okay Pr P.prom
      | .leaf K, .leaf Kₒₖ =>
        .leaf Kₒₖ
      | .cat P P', .cat Pₒₖ P'ₒₖ Pprom P'prom =>
        match x : P.prom with
          | Ppromh :: Ppromt =>
            let x'' : Ppromh = retjoin Pr P' :=
              congrArg (λ | some h => h | none => Ppromh) (x ▸ Pprom)
            by simp![x]
               exact .cat (ρ := Ppromt) (x'' ▸ x ▸ Pₒₖ.to_okay) (P'prom ▸ P'ₒₖ.to_okay)
          | [] => let y := x ▸ Pprom
                  by contradiction
  end Okay'

  theorem okay_iff_okay' {Pr : Program} {P : ThreadPool} : P.Okay Pr P.prom <-> P.Okay' Pr :=
    ⟨Okay.to_okay', Okay'.to_okay⟩

end ThreadPool


@[inline] abbrev codeOf (Pr : Program) (f : FuncIdx) (b : Cont) : StackFrameCode :=
  .code Pr.funs[f]!.blocks[b.b]!.code
@[inline] abbrev codeEntry (Pr : Program) (f : FuncIdx) : StackFrameCode :=
  .code Pr.funs[f]!.blocks.head!.code

inductive Step (Pr : Program) : (P P' : ThreadPool) -> Type where
  | stepₗ {P P' P₂} :
    Step Pr P P' ->
    Step Pr (.cat P P₂) (.cat P' P₂)

  | stepᵣ {P₁ P P'} :
    Step Pr P P' ->
    Step Pr (.cat P₁ P) (.cat P₁ P')
  
  | stmt {f K ρ X e v c} :
    X ⊢ₑₓₚᵣ e ⇓ v ->
    Step Pr {K ⬝ ⟨f, ρ, X, .code (.stmt e c)⟩}
            {K ⬝ ⟨f, ρ, X.concat v, .code c⟩}

  | goto {f K ρ X bnext} :
    Step Pr {K ⬝ ⟨f, ρ, X, .code (.trfr (.goto bnext))⟩}
            {K ⬝ ⟨f, ρ, X[bnext.args]!, codeOf Pr f bnext⟩}

  | ite_true {f K ρ X cond bthen belse n} :
    X ⊢ₐₜₒₘ cond ⇓ n ->
    n ≠ 0 ->
    Step Pr {K ⬝ ⟨f, ρ, X, .code (.trfr (.ite cond bthen belse))⟩}
            {K ⬝ ⟨f, ρ, X[bthen.args]!, codeOf Pr f bthen⟩}

  | ite_false {f K ρ X cond bthen belse} :
    X ⊢ₐₜₒₘ cond ⇓ 0 ->
    Step Pr {K ⬝ ⟨f, ρ, X, .code (.trfr (.ite cond bthen belse))⟩}
            {K ⬝ ⟨f, ρ, X[belse.args]!, codeOf Pr f belse⟩}

  | call {f g K ρ X x bret} :
    Step Pr {K ⬝ ⟨f, ρ, X, .code (.trfr (.call g x bret))⟩}
            {K ⬝ ⟨f, ρ, X, .cont bret⟩ ⬝ ⟨g, {}, X[x]!, codeEntry Pr g⟩}

  | retn {f g K ρ X Y y bret} :
    Step Pr {K ⬝ ⟨f, ρ, X, .cont bret⟩ ⬝ ⟨g, {}, Y, .code (.trfr (.retn y))⟩}
            {K ⬝ ⟨f, ρ, X[bret.args]! ++ Y[y]!, codeOf Pr f bret⟩}

  | spork {f K ρ X g g_args bbody} :
    Step Pr {K ⬝ ⟨f, ρ, X, .code (.trfr (.spork bbody g g_args))⟩}
            {K ⬝ ⟨f, ρ.push ⟨g, X[g_args]!, Pr.funs[g]!.fsig.ret⟩, X[bbody.args]!, codeOf Pr f bbody⟩}

  | promote {f unpr g prom X K c K'} :
    K.unpr = [] ->
    K'.prom = [] ->
    Step Pr {K ⬝ ⟨f, ⟨g :: unpr, prom⟩, X, c⟩ ++ K'}
            {K ⬝ ⟨f, ⟨unpr, g.ret :: prom⟩, X, c⟩ ++ K',
             {⟨g.f, {}, g.args, codeEntry Pr g.f⟩}}

  | spoin_unpr {f K ρ sc X bunpr bprom} :
    Step Pr {K ⬝ ⟨f, ρ.push sc, X, .code (.trfr (.spoin bunpr bprom))⟩}
            {K ⬝ ⟨f, ρ, X[bunpr.args]!, codeOf Pr f bunpr⟩}

  | spoin_prom {f K ρ X bunpr bprom Y y} {g : SpawnCall} :
    K.unpr = [] ->
    Step Pr {(K ⬝ ⟨f, ⟨[], g.ret :: ρ⟩, X, .code (.trfr (.spoin bunpr bprom))⟩),
             {⟨g.f, {}, Y, .code (.trfr (.retn y))⟩}}
            {K ⬝ ⟨f, ⟨[], ρ⟩, X[bprom.args]! ++ Y[y]!, codeOf Pr f bprom⟩}

inductive Steps (Pr : Program) : (P P' : ThreadPool) -> Type where
  | nil {P : ThreadPool} : Steps Pr P P
  | cons {P P' P'' : ThreadPool} : Steps Pr P P' -> Step Pr P' P'' -> Steps Pr P P''

namespace Step
  notation (name := poolstep) Pr:arg " ⊢ " P:arg " ↦ " P':arg => Step Pr P P'
end Step

namespace Steps
  notation (name := stepsstep) Pr:arg " ⊢ " P:arg " ↦* " P':arg => Steps Pr P P'

  abbrev append {Pr : Program} : {P P' P'' : ThreadPool} ->
                (Pr ⊢ P ↦* P') -> (Pr ⊢ P' ↦* P'') -> (Pr ⊢ P ↦* P'')
    | _P, _P', .(_P'), ss', nil => ss'
    | _P, _P', _P'', ss', cons ss s => cons (append ss' ss) s
  instance instHAppend {Pr : Program} {P P' P'' : ThreadPool} :
                       HAppend (Pr ⊢ P ↦* P') (Pr ⊢ P' ↦* P'') (Pr ⊢ P ↦* P'') where
    hAppend := append
  instance instSingleton {Pr : Program} {P P' : ThreadPool} : Singleton (Pr ⊢ P ↦ P') (Pr ⊢ P ↦* P') where
    singleton := cons nil
end Steps

theorem codeOfGetElem {Pr : Program} {f : FuncIdx} {b : Cont}
                    (pf : f < Pr.size) (pb : b.b < Pr.funs[f].blocks.length) :
                    Pr.funs[f]!.blocks[b.b]! = Pr.funs[f].blocks[b.b] :=
  by rw[getElem!_pos Pr.funs f pf, getElem!_pos Pr.funs[f].blocks b.b pb]

theorem argsOfGetElem {x : List Var} {X : ValMap} (ok : IVec (·.Okay X.length) x):
                    X[x]! = X[x] :=
  getElem!_pos X x ok
