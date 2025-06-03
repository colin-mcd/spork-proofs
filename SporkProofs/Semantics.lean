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
open StackFrameCode code cont

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

  instance instDecidableEq : DecidableEq StackFrameCode
    | code c, code c' =>
      decidable_of_iff (c = c')
        ⟨congrArg code, congrArg (λ | code c => c | _ => c)⟩
    | cont b, cont b' =>
      decidable_of_iff (b = b')
        ⟨congrArg cont, congrArg (λ | cont b => b | _ => b)⟩
    | code c, cont b => isFalse (by simp)
    | cont b, code c => isFalse (by simp)
end StackFrameCode

inductive SpawnCall : Type where
  | mk (f : FuncIdx) (args : List Val) (ret : Nat)

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
  
  instance instDecidableEq : DecidableEq SpawnCall
    | mk f args ret, mk f' args' ret' =>
      decidable_of_iff ((f, args, ret) = (f', args', ret'))
        ⟨congrArg (λ (f, args, ret) => mk f args ret),
         congrArg (λ | mk f args ret => (f, args, ret))⟩
end SpawnCall

inductive SpawnDeque : Type where
  -- unpromoted sporks, oldest first (queue)
  -- promoted sporks, oldest last (stack)
  | mk (unpr : List SpawnCall) (prom : SporkSig)

namespace SpawnDeque
  abbrev unpr : SpawnDeque -> List SpawnCall
    | ⟨u, _p⟩ => u
  abbrev prom : SpawnDeque -> SporkSig
    | ⟨_u, p⟩ => p

  abbrev SpawnOrder (canProm : Bool) (prom : SporkSig) : Prop :=
    prom = (if canProm then prom else [])
  
  theorem SpawnOrder_nil (canProm : Bool) : SpawnOrder canProm [] :=
    by cases canProm <;> rfl

  inductive Okay (fsigs : FuncSigs) (canProm : Bool) : SpawnDeque -> Prop
    | mk {unpr : List SpawnCall} {prom : SporkSig} :
         IVec (·.Okay fsigs) unpr ->
         SpawnOrder canProm prom ->
         (mk unpr prom).Okay fsigs canProm

  namespace Okay
    abbrev unpr {fsigs canProm} {ρ : SpawnDeque} : ρ.Okay fsigs canProm -> IVec (·.Okay fsigs) ρ.unpr | mk u _p => u
    abbrev prom {fsigs canProm} {ρ : SpawnDeque} : ρ.Okay fsigs canProm -> SpawnOrder canProm ρ.prom | mk _u p => p
  end Okay
  
  abbrev sig : SpawnDeque -> SporkSig
    | mk u p => List.reverseAux (u.map (·.ret)) p
  abbrev push : SpawnDeque -> SpawnCall -> SpawnDeque
    | ⟨u, p⟩, sc => ⟨u ++ [sc], p⟩
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

  instance instDecidableEq : DecidableEq SpawnDeque
    | mk u p, mk u' p' => decidable_of_iff ((u, p) = (u', p'))
      ⟨congrArg (λ (u, p) => mk u p),
       congrArg (λ | mk u p => (u, p))⟩

  theorem empty_okay {fsigs canProm} : SpawnDeque.Okay fsigs canProm ∅ :=
    ⟨.nil, SpawnDeque.SpawnOrder_nil canProm⟩
end SpawnDeque

inductive StackFrame : Type
  | mk (f : FuncIdx)
       (ρ : SpawnDeque)
       (X : ValMap)
       (c : StackFrameCode)

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
    theorem isCode {Pr canProm} : {k : StackFrame} -> (kₒₖ : k.Okay Pr none canProm) -> k.c.isCode
      | .mk _f _ρ _X _c, mk _flt _ρₒₖ cb _cₒₖ => cb
    theorem isCont {Pr canProm ret} : {k : StackFrame} -> (kₒₖ : k.Okay Pr (some ret) canProm) -> k.c.isCont
      | .mk _f _ρ _X _c, mk _flt _ρₒₖ cb _cₒₖ => cb
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

  instance instDecidableEq : DecidableEq StackFrame
    | mk f ρ X c, mk f' ρ' X' c' =>
      decidable_of_iff ((f, ρ, X, c) = (f', ρ', X', c'))
        ⟨congrArg (λ (a, b, c, d) => mk a b c d),
         congrArg (λ | mk a b c d => (a, b, c, d))⟩
end StackFrame

inductive CallStack : Type where
  | nil
  | cons (K : CallStack) (k : StackFrame)

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
  abbrev firstFrame : (K : CallStack) -> K ≠ nil -> StackFrame
    | nil ⬝ k, p => k
    | K  ⬝ k ⬝ _k', p => firstFrame (K ⬝ k) (by simp)

  theorem append_cons : {K K' : CallStack} -> {k : StackFrame} -> (K ++ K') ⬝ k = K ++ (K' ⬝ k)
    | _K, nil, _k => rfl
    | _K, _K' ⬝ _k', k => congrArg (· ⬝ k) append_cons
  theorem append_nil : {K : CallStack} -> K ++ nil = K := rfl
  theorem nil_append : {K : CallStack} -> nil ++ K = K
    | .nil => rfl
    | _K ⬝ _k => append_cons ▸ nil_append ▸ rfl
  theorem append_assoc : {K K' K'' : CallStack} -> (K ++ K') ++ K'' = K ++ (K' ++ K'')
    | _K, _K', nil => rfl
    | _K, _K', _K'' ⬝ k =>
      append_cons ▸ append_cons ▸ congrArg (· ⬝ k) append_assoc
  theorem append_unpr : {K K' : CallStack} -> (K ++ K').unpr = K.unpr ++ K'.unpr
    | K, nil => by simp[append_nil]
    | K, K' ⬝ k => by
        simp[unpr]
        rw[← List.append_assoc, ← @append_unpr K K']
        exact rfl

  abbrev head : (K : CallStack) -> K ≠ nil -> StackFrame
    | _K ⬝ k, _ => k
  abbrev tail : CallStack -> CallStack
    | K ⬝ _k => K
    | nil => nil

  abbrev retjoin (Pr : Program) : CallStack -> Nat
    | nil => default
    | nil ⬝ ⟨f, _, _, _⟩ => Pr.funs[f]!.fsig.ret
    | K ⬝ _k => K.retjoin Pr

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

  instance instDecidableEq : DecidableEq CallStack
    | nil, nil => isTrue rfl
    | K ⬝ k, K' ⬝ k' =>
      let KK'dec : Decidable (K = K') := instDecidableEq K K'
      decidable_of_iff ((K = K') ∧ (k = k'))
        ⟨λ ⟨Keq, keq⟩ => Keq ▸ keq ▸ rfl,
         λ p => ⟨congrArg (λ | K ⬝ k => K | _ => K) p,
                 congrArg (λ | K ⬝ k => k | _ => k) p⟩⟩
    | nil, K' ⬝ k' => isFalse (by simp)
    | K' ⬝ k', nil => isFalse (by simp)

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

    theorem unappend {Pr} : {get : Option Nat} -> {K K' : CallStack} -> (K ++ K').Okay Pr get -> (K' ≠ .nil) ->
                     K.allPromoted -> K.Okay Pr (some (K'.retjoin Pr)) ∧ K'.Okay Pr get
      | get, K, .nil ⬝ k, ok, _, kprom =>
        let ok' : (K ⬝ k).Okay Pr get :=
          by rw[← @append_cons K .nil k] at ok; exact ok
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

    /-theorem find_cons {Pr} : {K K' : CallStack} -> {k : StackFrame} -> (ok : (K ⬝ k ++ K').Okay Pr none) -> (kprom : K.allPromoted) -> (nn : K' ≠ .nil) -> k.Okay Pr (K'.retjoin?! (unappend ok nn kprom)) K.allPromoted
      | get, K, K', k, ok => sorry-/
  end Okay
end CallStack


inductive ThreadPool : Type where
  | leaf : CallStack -> ThreadPool
  | cat : ThreadPool -> ThreadPool -> ThreadPool

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
          P.Okay Pr (P'.retjoin Pr :: ρ) ->
          P'.Okay Pr [] ->
          -- P.prom.head? = some (P'.retjoin Pr) ->
          -- P'.prom = [] ->
          (cat P P').Okay Pr ρ

  namespace Okay
    abbrev get {Pr K ρ} : (ThreadPool.leaf K).Okay Pr ρ -> K.Okay Pr none
      | leaf Kₒₖ => Kₒₖ
    abbrev right {Pr P P' ρ} : (ThreadPool.cat P P').Okay Pr ρ -> P'.Okay Pr []
      | cat _Pₒₖ P'ₒₖ => P'ₒₖ
    abbrev left {Pr P P' ρ} : (ok : (ThreadPool.cat P P').Okay Pr ρ) -> P.Okay Pr (P'.retjoin Pr :: ρ)
      | cat Pₒₖ _P'ₒₖ => Pₒₖ
  end Okay

  -- TODO: generalize for child threads not starting from main
  abbrev init : ThreadPool := {{StackFrame.mk 0 ∅ ∅ (cont (Cont.mk 0 []))}}
  abbrev child (f : FuncIdx) (args : List Val) : ThreadPool :=
    let vs := (List.range args.length).map Var.mk
    {{StackFrame.mk f ∅ args (cont (Cont.mk 0 vs))}}

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

  instance instDecidableEq : DecidableEq ThreadPool
    | leaf K, leaf K' =>
      decidable_of_iff (K = K')
        ⟨congrArg leaf,
         congrArg (λ | leaf K => K | _ => K)⟩
    | cat Pₗ Pᵣ, cat Pₗ' Pᵣ' =>
      match instDecidableEq Pₗ Pₗ', instDecidableEq Pᵣ Pᵣ' with
        | isFalse f, _ => isFalse (f ∘ congrArg (λ | cat l r => l | _ => Pₗ))
        | _, isFalse f => isFalse (f ∘ congrArg (λ | cat l r => r | _ => Pᵣ))
        | isTrue tₗ, isTrue tᵣ => isTrue (tₗ ▸ tᵣ ▸ rfl)
    | leaf _, cat _ _ => isFalse (by simp)
    | cat _ _, leaf _ => isFalse (by simp)

  -- abbrev step (Pr : Program) : ThreadPool -> Option ThreadPool
  --   | leaf (K ⬝ ⟨f, ρ, X, code (.stmt e c)⟩) =>
  --     if ok : e.Okay X.length then
  --       some {K ⬝ e.eval X ok}

end ThreadPool


@[inline] abbrev codeOf (Pr : Program) (f : FuncIdx) (b : Cont) : StackFrameCode :=
  code Pr.funs[f]!.blocks[b.b]!.code
@[inline] abbrev codeEntry (Pr : Program) (f : FuncIdx) : StackFrameCode :=
  code Pr.funs[f]!.blocks.head!.code

theorem codeOfGetElem {Pr : Program} {f : FuncIdx} {b : Cont}
                    (pf : f < Pr.size) (pb : b.b < Pr.funs[f].blocks.length) :
                    Pr.funs[f]!.blocks[b.b]! = Pr.funs[f].blocks[b.b] :=
  by rw[getElem!_pos Pr.funs f pf, getElem!_pos Pr.funs[f].blocks b.b pb]

theorem argsOfGetElem {x : List Var} {X : ValMap} (ok : IVec (·.Okay X.length) x):
                    X[x]! = X[x] :=
  getElem!_pos X x ok

inductive Step (Pr : Program) : (P P' : ThreadPool) -> Type where
  | stepₗ {P P' P₂} :
    Step Pr P P' ->
    Step Pr (P ++ P₂) (P' ++ P₂)

  | stepᵣ {P₁ P P'} :
    Step Pr P P' ->
    Step Pr (P₁ ++ P) (P₁ ++ P')
  
  | stmt {f K ρ X e v c} :
    X ⊢ₑₓₚᵣ e ⇓ v ->
    Step Pr {K ⬝ ⟨f, ρ, X, code (Code.stmt e c)⟩}
            {K ⬝ ⟨f, ρ, X ++ [v], code c⟩}

  | goto {f K ρ X bnext} :
    Step Pr {K ⬝ ⟨f, ρ, X, code (Code.trfr (Transfer.goto bnext))⟩}
            {K ⬝ ⟨f, ρ, X[bnext.args]!, codeOf Pr f bnext⟩}

  | ite_true {f K ρ X cond bthen belse n} :
    X ⊢ₐₜₒₘ cond ⇓ n ->
    n ≠ 0 ->
    Step Pr {K ⬝ ⟨f, ρ, X, code (Code.trfr (Transfer.ite cond bthen belse))⟩}
            {K ⬝ ⟨f, ρ, X[bthen.args]!, codeOf Pr f bthen⟩}

  | ite_false {f K ρ X cond bthen belse} :
    X ⊢ₐₜₒₘ cond ⇓ 0 ->
    Step Pr {K ⬝ ⟨f, ρ, X, code (Code.trfr (Transfer.ite cond bthen belse))⟩}
            {K ⬝ ⟨f, ρ, X[belse.args]!, codeOf Pr f belse⟩}

  | call {f g K ρ X x bret} :
    Step Pr {K ⬝ ⟨f, ρ, X, code (Code.trfr (Transfer.call g x bret))⟩}
            {K ⬝ ⟨f, ρ, X, cont bret⟩ ⬝ ⟨g, {}, X[x]!, codeEntry Pr g⟩}

  | retn {f g K ρ X Y y bret} :
    Step Pr {K ⬝ ⟨f, ρ, X, cont bret⟩ ⬝ ⟨g, {}, Y, code (Code.trfr (Transfer.retn y))⟩}
            {K ⬝ ⟨f, ρ, X[bret.args]! ++ Y[y]!, codeOf Pr f bret⟩}

  | spork {f K ρ X g g_args bbody} :
    Step Pr {K ⬝ ⟨f, ρ, X, code (Code.trfr (Transfer.spork bbody g g_args))⟩}
            {K ⬝ ⟨f, ρ.push ⟨g, X[g_args]!, Pr.funs[g]!.fsig.ret⟩, X[bbody.args]!, codeOf Pr f bbody⟩}

  | promote {f unpr g prom X K c K'} :
    K.unpr = [] ->
    K'.prom = [] ->
    Step Pr {K ⬝ ⟨f, ⟨g :: unpr, prom⟩, X, c⟩ ++ K'}
            {K ⬝ ⟨f, ⟨unpr, g.ret :: prom⟩, X, c⟩ ++ K',
             {⟨g.f, {}, g.args, codeEntry Pr g.f⟩}}

  | spoin_unpr {f K ρ sc X bunpr bprom} :
    Step Pr {K ⬝ ⟨f, ρ.push sc, X, code (Code.trfr (Transfer.spoin bunpr bprom))⟩}
            {K ⬝ ⟨f, ρ, X[bunpr.args]!, codeOf Pr f bunpr⟩}

  | spoin_prom {f K ρ X bunpr bprom Y y} {g : SpawnCall} :
    K.unpr = [] ->
    Step Pr {(K ⬝ ⟨f, ⟨[], g.ret :: ρ⟩, X, code (Code.trfr (Transfer.spoin bunpr bprom))⟩),
             {⟨g.f, {}, Y, code (Code.trfr (Transfer.retn y))⟩}}
            {K ⬝ ⟨f, ⟨[], ρ⟩, X[bprom.args]! ++ Y[y]!, codeOf Pr f bprom⟩}

namespace Step
  notation (name := poolstep) Pr:arg " ⊢ " P:arg " ↦ " P':arg => Step Pr P P'

  theorem preserve_retjoin_stack_cons
    {Pr K f ρ ρ' X X' c c'} :
      CallStack.retjoin Pr (K ⬝ ⟨f, ρ, X, c⟩) =
        CallStack.retjoin Pr (K ⬝ ⟨f, ρ', X', c'⟩)
    := by cases K <;> rfl

  theorem preserve_retjoin_stack_cons_cons {Pr K k k'} :
      (K ⬝ k ⬝ k').retjoin Pr = (K ⬝ k).retjoin Pr :=
    by cases K <;> rfl

  theorem preserve_retjoin_stack_cons_nonnil {Pr K k} :
      K ≠ ∅ → (K ⬝ k).retjoin Pr = K.retjoin Pr := by
    cases K <;> intro nn
    · case nil => contradiction
    · case cons => rfl

  -- List.append_ne_nil_of_left_ne_nil
  theorem stack_append_left_nonnil : (s t : CallStack) -> (h : s ≠ ∅) -> s ++ t ≠ ∅
    | s, .nil, h => h
    | s, K ⬝ k, h => by simp

  theorem preserve_retjoin_stack_append {Pr K k} : {K' : CallStack} ->
      CallStack.retjoin Pr (K ⬝ k ++ K') = CallStack.retjoin Pr (K ⬝ k)
    | .nil => rfl
    | K' ⬝ k' => preserve_retjoin_stack_cons_nonnil
                   (stack_append_left_nonnil (K ⬝ k) K' (by simp)) ▸
                 preserve_retjoin_stack_append (K' := K')

  theorem preserve_retjoin {Pr : Program} : {P P' : ThreadPool} ->
                         Pr ⊢ P ↦ P' -> {ρ : SporkSig} -> P.Okay Pr ρ ->
                         P.retjoin Pr = P'.retjoin Pr
  | P, P', s => by
    cases s <;> intro Pₒₖ <;>
    try (exact preserve_retjoin_stack_cons)
    · case stepₗ P P' P₂ s =>
        simp_all!; match Pₒₖ with
          | .cat Pok P2ok => exact preserve_retjoin s Pok
    · case stepᵣ P₁ P P' s =>
        rfl
    · case retn f g K ρ' X Y y bret =>
        exact preserve_retjoin_stack_cons (K := K)
    · case promote f unpr g prom X K c K' u p =>
        simp[ThreadPool.retjoin];
        rw[preserve_retjoin_stack_append,
           preserve_retjoin_stack_append,
           preserve_retjoin_stack_cons]

  theorem goto_okay_rets
      {Pr} (Prok : Pr.Okay) {f canProm ρ} {X Y : ValMap} {bnext} {y : List Var}
      (p : f < Pr.size)
      (ρok : ρ.Okay Pr.fsigs canProm)
      (bnext_ok : bnext.OkayRets Pr.funs[f].bsigs ⟨X.length, ρ.sig⟩ y.length)
      (y_ok : IVec (·.Okay Y.length) y) :
      StackFrame.Okay Pr none canProm
        ⟨f, ρ, X[bnext.args]! ++ Y[y]!, codeOf Pr f bnext⟩ :=
    let ⟨bok, sigok, x_ok⟩ := bnext_ok
    let bok' : bnext.b < Pr.funs[f].blocks.length :=
      List.length_map Block.bsig ▸ bok
    let xlen : bnext.args.length = X[bnext.args].length :=
      x_ok.map_length (λ x xₒₖ => X[x])
    let ylen : y.length = Y[y].length :=
      y_ok.map_length (λ y yₒₖ => Y[y])
    let code_ok : Pr.funs[f]!.blocks[bnext.b]!.code.Okay
                    Pr.fsigs Pr.funs[f].bsigs Pr.funs[f].fsig.ret
                    ⟨(X[bnext.args]! ++ Y[y]!).length, ρ.sig⟩ := by
      rw[codeOfGetElem p bok',
         argsOfGetElem x_ok,
         argsOfGetElem y_ok,
         List.length_append,
         ← xlen, ← ylen, ← sigok]
      simp; exact ((Prok.1.get ⟨f, p⟩).1.get ⟨bnext.b, bok'⟩).1
    ⟨p, ρok, rfl, .code code_ok⟩

  theorem goto_okay
      {Pr} (Prok : Pr.Okay) {f canProm ρ} {X : ValMap} {bnext}
      (p : f < Pr.size)
      (ρok : ρ.Okay Pr.fsigs canProm)
      (bnext_ok : bnext.Okay Pr.funs[f].bsigs ⟨X.length, ρ.sig⟩) :
      StackFrame.Okay Pr none canProm ⟨f, ρ, X[bnext.args]!, codeOf Pr f bnext⟩ :=
    List.append_nil X[bnext.args]! ▸
    goto_okay_rets Prok (Y := []) (y := []) p ρok bnext_ok.cast0 .nil

  theorem entry_okay
      {Pr} (Prok : Pr.Okay) {f canProm} {X : ValMap} {x : List Var}
      (p : f < Pr.size)
      (xok : IVec (·.Okay X.length) x)
      (sigok : Pr.funs[f].fsig.arity = x.length) :
      StackFrame.Okay Pr none canProm ⟨f, ∅, X[x]!, codeEntry Pr f⟩ :=
    let fok := Prok.1.get ⟨f, p⟩
    let c' : Code.Okay Pr.fsigs Pr.funs[f].bsigs Pr.funs[f].fsig.ret
              ⟨X[x]!.length, []⟩
              Pr.funs[f]!.blocks.head!.code :=
      argsOfGetElem xok ▸
      xok.map_length (λ x xₒₖ => X[x]) ▸
      sigok ▸
      Eq.symm (getElem!_pos Pr.funs f p) ▸
      fok.2.headeq ▸
      fok.2.head!eq ▸
      (fok.1.head fok.2.nonnil).1
    ⟨p, SpawnDeque.empty_okay, rfl, .code c'⟩

  theorem P_same_prom {Pr} : {P : ThreadPool} -> {ρ : SporkSig} ->
                    P.Okay Pr ρ -> P.prom = ρ
    | .cat P₁ P₂, ρ, .cat P₁ₒₖ P₂ₒₖ =>
      by simp[ThreadPool.prom]
         rw[P_same_prom (ρ := P₂.retjoin Pr :: ρ) P₁ₒₖ]
         simp
    | .leaf K, .(K.prom), .leaf Kₒₖ =>
      rfl

  
  open ThreadPool.Okay (leaf cat) in
  theorem preservation {Pr : Program} (Prok : Pr.Okay) : {P P' : ThreadPool} -> {ρ : SporkSig} -> P.Okay Pr ρ -> Pr ⊢ P ↦ P' -> P'.Okay Pr ρ := by
    intro P P' ρ ok P_P'; cases P_P' <;> cases ok

    · case stepₗ P P' P₂ P_P' P2ok Pok =>
        exact cat (preservation Prok Pok P_P') P2ok

    · case stepᵣ P₁ P P' P_P' Pok P1ok =>
        exact cat (preserve_retjoin P_P' Pok ▸ P1ok) (preservation Prok Pok P_P')

    · case stmt f K ρ X e v c a ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X ++ [v], code c⟩)
        exact match ok with
           | Kok ⬝ₒₖ (.mk p ρok _ (.code (.stmt eok cok))) =>
             Kok ⬝ₒₖ (.mk p ρok rfl (.code
                 (by simp[BlockSig.bind] at cok; simp; exact cok)))

    · case goto f K ρ X bnext ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X[bnext.args]!, codeOf Pr f bnext⟩)
        exact match ok with
          | Kok ⬝ₒₖ (.mk p ρok _ (.code (.trfr (.goto bnext_ok))))=>
            Kok ⬝ₒₖ (goto_okay Prok p ρok bnext_ok)

    · case ite_true f K ρ X cond bthen belse n cond_n neq0 ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X[bthen.args]!, codeOf Pr f bthen⟩)
        exact match ok with
          | Kok ⬝ₒₖ (.mk p ρok _ (.code (.trfr (.ite cond_ok bthen_ok belse_ok)))) =>
            Kok ⬝ₒₖ (goto_okay Prok p ρok bthen_ok)

    · case ite_false f K ρ X cond bthen belse cond_0 ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X[belse.args]!, codeOf Pr f belse⟩)
        exact match ok with
          | Kok ⬝ₒₖ (.mk p ρok _ (.code (.trfr (.ite cond_ok bthen_ok belse_ok)))) =>
            Kok ⬝ₒₖ (goto_okay Prok p ρok belse_ok)

    · case call f g K ρ X x bret ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X, cont bret⟩ ⬝ ⟨g, ∅, X[x]!, codeEntry Pr g⟩)
        exact match ok with
          | Kok ⬝ₒₖ kok@(.mk fok ρok _ (.code (.trfr (.call flt sigok x_ok
                bret_ok@(.mk bret_lt bret_sig_okay argsok))))) =>
              let bret_ok' : Cont.OkayRets Pr.funs[f].bsigs ⟨X.length, ρ.sig⟩
                               Pr.fsigs[g].ret bret :=
                Pr.funs.getElem_map (·.fsig) ▸ bret_ok
              let gframe_ok :=
                entry_okay (f := g) Prok (Pr.size_eq_fsigs_length ▸ flt) x_ok
                  (Pr.funs.getElem_map (·.fsig) ▸ sigok)
              let glt := gframe_ok.flt
              let bret_ok'' : Cont.OkayRets Pr.funs[f].bsigs ⟨X.length, ρ.sig⟩
                                Pr.funs[g].fsig.ret bret :=
                Pr.funs.getElem_map (·.fsig) ▸ bret_ok'
              Kok ⬝ₒₖ ⟨fok, ρok, rfl, .cont bret_ok''⟩ ⬝ₒₖ gframe_ok

    · case retn f g K ρ X Y y bret ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X[bret.args]! ++ Y[y]!, codeOf Pr f bret⟩)
        exact match ok with
          | Kok ⬝ₒₖ (.mk flt ρok _ (.cont bret_ok))
                ⬝ₒₖ (.mk glt ⟨.nil, _⟩ _ (.code (.trfr (.retn _ ylen y_ok)))) =>
            Kok ⬝ₒₖ (goto_okay_rets Prok flt ρok (ylen ▸ bret_ok) y_ok)

    · case spork f K ρ X g g_args bbody ok =>
       apply @leaf Pr (K ⬝ ⟨f, ρ.push ⟨g, X[g_args]!, Pr.funs[g]!.fsig.ret⟩,
                            X[bbody.args]!, codeOf Pr f bbody⟩)
       exact match ok with
         | Kok ⬝ₒₖ ⟨flt, ⟨unpr_ok, prom_ok⟩, _, .code
               (.trfr (.spork glt gsig g_args_ok bbody_ok))⟩ =>
           let glt' : g < Pr.funs.length := List.length_map (α := Func) (·.fsig) ▸ glt
           let h : FuncSig.mk X[g_args]!.length Pr.funs[g]!.fsig.ret = Pr.fsigs[g] :=
             argsOfGetElem g_args_ok ▸
             getElem!_pos Pr.funs g glt' ▸
             congrArg₂ FuncSig.mk
               (g_args_ok.map_length (λ x xₒₖ => X[x]) ▸ Eq.symm gsig) (by simp)
           Kok ⬝ₒₖ (goto_okay Prok flt ⟨unpr_ok.append (IVec.singleton ⟨glt, h⟩), prom_ok⟩
                     (by rw[ρ.pushsig, getElem!_pos Pr.funs g glt']
                         simp[BlockSig.spork] at bbody_ok; simp
                         exact bbody_ok))

    · case promote f unpr g prom X K c K' u p ok =>
        apply cat
        · exact sorry
        · apply @leaf Pr {⟨g.f, ∅, g.args, codeEntry Pr g.f⟩}
          apply (.nil ⬝ₒₖ ·)
          let ok' : (K ++ ({⟨f, ⟨(g :: unpr), prom⟩, X, c⟩} ++ K')).Okay Pr none :=
            CallStack.append_assoc ▸ ok
          let ⟨Kok, K'ok⟩ := ok'.unappend (K := K)
                               (by cases K' <;> simp)
                               (by simp[u])
          let rec hp : {K' : CallStack} ->
                       ({⟨f, ⟨g :: unpr, prom⟩, X, c⟩} ++ K').Okay Pr none ->
                       K'.prom = [] ->
--                       (K ⬝ ⟨f, ⟨g :: unpr, prom⟩, X, c⟩ ++ K').Okay Pr none ->
                       StackFrame.Okay Pr none true ⟨g.f, ∅, g.args, codeEntry Pr g.f⟩
            | .nil, ok, _ => by
              rw[CallStack.append_nil] at ok
              let _ ⬝ₒₖ kok' := ok
              let glt : g.f < Pr.size := by
                simp[Program.size]
                rw[← List.length_map (as := Pr.funs) (·.fsig)]
                exact kok'.ρₒₖ.unpr.head'.flt
              let gsig : ⟨g.args.length, g.ret⟩ = Pr.funs[g.f].fsig :=
                Pr.funs.getElem_map (·.fsig) ▸ kok'.ρₒₖ.unpr.head'.sig
              let gsig_arity : g.args.length = Pr.funs[g.f].fsig.arity :=
                congrArg (·.arity) gsig
              let gsig_ret : g.ret = Pr.funs[g.f].fsig.ret :=
                congrArg (·.ret) gsig
              -- TODO: make version of entry_okay that works on already-getElem'd x
              let eok : Okay Pr.fsigs Pr.funs[g.f].bsigs ⟨g.args.length, ∅⟩ Pr.funs[g.f].fsig.ret (codeEntry Pr g.f) := (entry_okay (x := g.args) Prok glt sorry gsig_arity.symm).cₒₖ
              exact ⟨ glt, SpawnDeque.empty_okay, rfl, eok⟩
            | K' ⬝ k', ok, p => sorry
          exact hp K'ok p

    · case spoin_unpr f K ρ sc X bunpr bprom ok =>
        apply @leaf Pr (K ⬝ ⟨f, ρ, X[bunpr.args]!, codeOf Pr f bunpr⟩)
        exact match ok with
          | Kok ⬝ₒₖ ⟨flt, ⟨unpr_ok, prom_ok⟩, _, .code (.trfr (.spoin nn bunpr_ok bprom_ok))⟩ =>
            let h : (ρ.push sc).sig.tail = ρ.sig := by simp
            Kok ⬝ₒₖ (goto_okay Prok flt ⟨unpr_ok.unappend.1, prom_ok⟩ (h ▸ bunpr_ok))

    · case spoin_prom f K ρ' X bunpr bprom Y y g K_unpr_nil retok ok =>
        let p : g.ret :: ρ' ++ K.prom = Pr.funs[g.f]!.fsig.ret :: ρ :=
          P_same_prom ok
        let g_ret_eq : g.ret = Pr.funs[g.f]!.fsig.ret :=
          congrArg (λ | some x => x | _ => g.ret) (congrArg List.head? p)
        let ρ_eq_ρ'_Kprom : ρ = ρ' ++ K.prom :=
          Eq.symm (congrArg List.tail p)
        rw[ρ_eq_ρ'_Kprom] at ok ⊢
        apply @leaf Pr (K ⬝ ⟨f, ⟨[], ρ'⟩, X[bprom.args]! ++ Y[y]!, codeOf Pr f bprom⟩)
        let ok'' : (ThreadPool.leaf (K ⬝ ⟨f, ⟨[], g.ret :: ρ'⟩, X,
                      code (.trfr (.spoin bunpr bprom))⟩)).Okay Pr (g.ret :: ρ' ++ K.prom) :=
          g_ret_eq ▸ ok
        let flt := ok''.get.head.flt
        let sd_ok : (SpawnDeque.mk [] ρ').Okay Pr.fsigs K.allPromoted :=
          ⟨IVec.nil, by simp[CallStack.allPromoted]; rw[K_unpr_nil]; rfl⟩
        let y_ok : IVec (·.Okay Y.length) y :=
          match retok.get.head.cₒₖ.c.t with
            | .retn _ _ y_ok => y_ok
        let y_len_eq_g_ret : y.length = g.ret :=
          match retok.get.head.cₒₖ'.c.t with
            | .retn _ l _ => g_ret_eq ▸ Eq.symm l
        let cont_ok : bprom.OkayRets Pr.funs[f].bsigs ⟨X.length, ρ'⟩ y.length :=
          match ok''.get.head.cₒₖ.c.t with
            | .spoin nn unpr_ok prom_ok => y_len_eq_g_ret ▸ prom_ok
        exact ok''.get.tail ⬝ₒₖ
          (goto_okay_rets Prok flt sd_ok cont_ok y_ok)
end Step

inductive Steps (Pr : Program) : (P P' : ThreadPool) -> Type where
  | nil {P : ThreadPool} : Steps Pr P P
  | cons {P P' P'' : ThreadPool} : Steps Pr P P' -> Pr ⊢ P' ↦ P'' -> Steps Pr P P''

namespace Steps
  notation (name := stepsstep) Pr:arg " ⊢ " P:arg " ↦* " P':arg => Steps Pr P P'

  abbrev append {Pr : Program} : {P P' P'' : ThreadPool} ->
                (Pr ⊢ P ↦* P') -> (Pr ⊢ P' ↦* P'') -> (Pr ⊢ P ↦* P'')
    | _P, _P', .(_P'), ss', nil => ss'
    | _P, _P', _P'', ss', cons ss s => cons (append ss' ss) s
  instance instHAppend {Pr : Program} {P P' P'' : ThreadPool} :
                       HAppend (Pr ⊢ P ↦* P') (Pr ⊢ P' ↦* P'') (Pr ⊢ P ↦* P'') :=
    ⟨append⟩
  instance instSingleton {Pr : Program} {P P' : ThreadPool} : Singleton (Pr ⊢ P ↦ P') (Pr ⊢ P ↦* P') :=
    ⟨λ s => cons nil s⟩
end Steps
