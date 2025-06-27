import SporkProofs.Syntax

abbrev ValMap : Type := List Val

inductive StackFrameCode : Type
  | code (c : Code)
  | cont (b : Cont)

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

inductive ThreadTree : Type where
  | thread : CallStack -> ThreadTree
  | node : ThreadTree -> ThreadTree -> ThreadTree


namespace ValMap
  instance : GetElem ValMap Var Val (λ X x => x.WF X.length) where
    getElem X x xwf := X[x.idx]'xwf.1

  instance : GetElem ValMap (List Var) (List Val) (λ X => IVec (·.WF X.length)) where
    getElem X _args argswf := argswf.list_map (λ x xwf => X[x])
end ValMap

@[simp] def valOf (p : Prop) [d : Decidable p] : Val := if decide p then 1 else 0

namespace Atom
  @[simp] def eval : (X : ValMap) -> (a : Atom) -> a.WF X.length -> Val
    | _X, .val v, _wfᵥ => v
    | X, .var x, wfₓ =>
      let _ := match wfₓ with | .var p => p
      X[x]

  inductive Eval (X : ValMap) (a : Atom) : Val -> Prop where
    | mk (wfₐ : a.WF X.length) : Eval X a (eval X a wfₐ)

  notation (name := atomeval) X:arg " ⊢ₐₜₒₘ " a:arg " ⇓ " v:arg => Eval X a v

  namespace Eval
    instance : {X : ValMap} -> {a : Atom} -> {v : Val} -> Decidable (X ⊢ₐₜₒₘ a ⇓ v)
      | X, a, v => decidable_of_iff (∃ p : a.WF X.length, eval X a p = v)
        ⟨λ ⟨wfₐ, p⟩ => p ▸ Eval.mk wfₐ,
         λ | (Eval.mk wfₐ) => ⟨wfₐ, rfl⟩⟩

    theorem wf {X : ValMap} {a : Atom} {v : Val} : Eval X a v -> a.WF X.length
      | Eval.mk wfₐ => wfₐ
    theorem eq {X : ValMap} {a : Atom} {v : Val} : (s : Eval X a v) -> eval X a (wf s) = v
      | Eval.mk wfₐ => rfl
  end Eval
end Atom

namespace Bop
  @[simp] def eval : Bop -> Val -> Val -> Val
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
    instance {o : Bop} {u v w : Val} : Decidable (Eval o u v w) :=
      decidable_of_iff (eval o u v = w)
        ⟨λ p => p ▸ Eval.mk,
         λ | Eval.mk => rfl⟩

    theorem eq {o : Bop} {u v w : Val} : Eval o u v w -> eval o u v = w
      | Eval.mk => rfl
  end Eval
end Bop

namespace Uop
  @[simp] def eval : Uop -> Val -> Val
    | INEG, v => -v
    | LNOT, v => valOf (v = 0)

  inductive Eval (o : Uop) (v : Val) : Val -> Prop where
    | mk : Eval o v (eval o v)

  namespace Eval
    instance {o : Uop} {u v : Val} : Decidable (Eval o u v) :=
      decidable_of_iff (eval o u = v)
        ⟨λ p => p ▸ Eval.mk,
         λ | Eval.mk => rfl⟩

    theorem eq {o : Uop} {u v : Val} : Eval o u v -> eval o u = v
      | Eval.mk => rfl
  end Eval
end Uop

namespace Expr
  @[simp] def eval (X : ValMap) : (e : Expr) -> (e.WF X.length) -> Val
    | nop a, wf =>
      let awf := match wf with | .nop awf => awf
      a.eval X awf
    | uop o a, wf =>
      let awf := match wf with | .uop awf => awf
      o.eval (a.eval X awf)
    | bop o a b, wf =>
      let awf := match wf with | .bop awf _ => awf
      let bwf := match wf with | .bop _ bwf => bwf
      o.eval (a.eval X awf) (b.eval X bwf)

  inductive Eval (X : ValMap) (e : Expr) : Val -> Prop where
    | mk (ewf : e.WF X.length) : Eval X e (eval X e ewf)

  notation (name := expreval) X:arg " ⊢ₑₓₚᵣ " e:arg " ⇓ " v:arg => Eval X e v

  namespace Eval
    instance {X : ValMap} {e : Expr} {v : Val} : Decidable (X ⊢ₑₓₚᵣ e ⇓ v) :=
      decidable_of_iff (∃ (ewf : e.WF X.length), eval X e ewf = v)
        ⟨λ ⟨ewf, p⟩ => p ▸ mk ewf,
         λ | mk ewf => ⟨ewf, rfl⟩⟩

    theorem wf {X : ValMap} {e : Expr} {v: Val} : X ⊢ₑₓₚᵣ e ⇓ v -> e.WF X.length
      | mk ewf => ewf
    theorem eq  {X : ValMap} {e : Expr} {v: Val} : (s : X  ⊢ₑₓₚᵣ e ⇓ v) -> eval X e (wf s) = v
      | mk ewf => rfl
  end Eval
end Expr

theorem codeOfGetElem {P : Program} {f : FuncIdx} {b : Cont}
                    (pf : f < P.size) (pb : b.b < P[f].size) :
                    P[f]![b.b]! = P[f][b.b] :=
  by rw[getElem!_pos P f pf, getElem!_pos P[f] b.b pb]

theorem argsOfGetElem {x : List Var} {X : ValMap} (wf : IVec (·.WF X.length) x):
                    X[x]! = X[x] :=
  getElem!_pos X x wf

namespace StackFrameCode  
  abbrev isCode | code _ => true | cont _ => false
  abbrev isCont | code _ => false | cont _ => true

  @[simp] def extractD : (c : StackFrameCode) -> if isCode c then Code else Cont
    | code c => c
    | cont b => b
  abbrev extractCode : (c : StackFrameCode) -> isCode c -> Code
    | code c, _ => c
  abbrev extractCont : (c : StackFrameCode) -> isCont c -> Cont
    | cont b, _ => b

  @[simp] abbrev codeOf (P : Program) (f : FuncIdx) (b : Cont) : StackFrameCode :=
    code P[f]![b.b]!.code
  @[simp] abbrev codeEntry (P : Program) (f : FuncIdx) : StackFrameCode :=
    code P[f]!.blocks.head!.code

  inductive WF (fsigs bsigs bsig ret) : StackFrameCode -> Prop
    | code {c} : c.WF fsigs bsigs ret bsig -> (code c).WF fsigs bsigs bsig ret
    | cont {b} : b.WFRets bsigs bsig ret -> (cont b).WF fsigs bsigs bsig ret

  namespace WF
    instance {fsigs bsigs bsig ret} : (c : StackFrameCode) ->
             Decidable (c.WF fsigs bsigs bsig ret)
      | .code c =>
        decidable_of_iff (c.WF fsigs bsigs ret bsig)
          ⟨code, λ (code p) => p⟩
      | .cont b =>
        decidable_of_iff (b.WFRets bsigs bsig ret)
          ⟨cont, λ (cont p) => p⟩

    theorem c {fsigs bsigs bsig ret c} :
             WF fsigs bsigs bsig ret (.code c) ->
             c.WF fsigs bsigs ret bsig
      | code c => c

    theorem b {fsigs bsigs bsig b ret} :
             WF fsigs bsigs bsig ret (.cont b) ->
             b.WFRets bsigs bsig ret
      | cont b => b
  end WF

  deriving instance DecidableEq for StackFrameCode
end StackFrameCode

namespace SpawnCall
  @[simp] abbrev f | mk f _args _ret => f
  @[simp] abbrev args | mk _f args _ret => args
  @[simp] abbrev ret | mk _f _args ret => ret

  inductive WF (fsigs : FuncSigs) (sc : SpawnCall) : Prop where
    | mk (_ : sc.f < fsigs.length)
         (_ : ⟨sc.args.length, sc.ret⟩ = fsigs[sc.f]) :
         sc.WF fsigs

  namespace WF
    instance {fsigs : FuncSigs} : (sc : SpawnCall) -> Decidable (sc.WF fsigs)
      | .mk f args ret =>
        decidable_of_iff (∃ _ : f < fsigs.length, ⟨args.length, ret⟩ = fsigs[f])
          ⟨λ ⟨p, q⟩ => ⟨p, q⟩, λ ⟨p, q⟩ => ⟨p, q⟩⟩

    theorem flt {fsigs} {sc : SpawnCall} : sc.WF fsigs -> sc.f < fsigs.length | mk flt _ => flt
    theorem sig {fsigs} {sc : SpawnCall} : (wf : sc.WF fsigs) -> ⟨sc.args.length, sc.ret⟩ = fsigs[sc.f]'wf.flt | mk _ sig => sig
  end WF
  
  deriving instance DecidableEq for SpawnCall
end SpawnCall

namespace SpawnDeque
  @[simp] abbrev unpr : SpawnDeque -> List SpawnCall
    | ⟨u, _p⟩ => u
  @[simp] abbrev prom : SpawnDeque -> SporkSig
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

  instance : EmptyCollection SpawnDeque := ⟨⟨[], []⟩⟩

  inductive WF (fsigs : FuncSigs) (canProm : Bool) : SpawnDeque -> Prop
    | mk {unpr : List SpawnCall} {prom : SporkSig} :
         IVec (·.WF fsigs) unpr ->
         SpawnOrder canProm prom ->
         (mk unpr prom).WF fsigs canProm

  namespace WF
    instance {fsigs canProm} : (ρ : SpawnDeque) -> Decidable (ρ.WF fsigs canProm)
      | .mk u p => decidable_of_iff
          (IVec (·.WF fsigs) u ∧ SpawnOrder canProm p)
          ⟨λ ⟨a, b⟩ => ⟨a, b⟩, λ ⟨a, b⟩ => ⟨a, b⟩⟩
    
    theorem unpr {fsigs canProm} {ρ : SpawnDeque} : ρ.WF fsigs canProm -> IVec (·.WF fsigs) ρ.unpr | mk u _p => u
    theorem prom {fsigs canProm} {ρ : SpawnDeque} : ρ.WF fsigs canProm -> SpawnOrder canProm ρ.prom | mk _u p => p

    theorem castCanProm {fsigs ρ} : {canProm : Bool} -> (canProm' : Bool) -> canProm ≤ canProm' -> WF fsigs canProm ρ -> WF fsigs canProm' ρ
      | false, false, _, .mk u p => .mk u p
      | true, true, _, .mk u p => .mk u p
      | false, true, _, .mk u _p => .mk u rfl

    theorem promote {fsigs u p g} (wf : WF fsigs true ⟨g :: u, p⟩) :
                    WF fsigs true ⟨u, g.ret :: p⟩ :=
      ⟨wf.unpr.tail, rfl⟩

    theorem empty {fsigs canProm} : SpawnDeque.WF fsigs canProm ∅ :=
      ⟨.nil, .of_nil⟩
  end WF
  
  @[simp] def sig : SpawnDeque -> SporkSig
    | mk u p => List.reverseAux (u.map (·.ret)) p
  @[simp] def push : SpawnDeque -> SpawnCall -> SpawnDeque
    | ⟨u, p⟩, sc => ⟨u.concat sc, p⟩
  @[simp] def pop_prom : SpawnDeque -> SpawnDeque
    | ⟨sc :: u, p⟩ => ⟨u, sc.ret :: p⟩
    | ⟨[], p⟩ => ⟨[], p⟩
  theorem pushsig (ρ : SpawnDeque) (sc : SpawnCall)
                  : (ρ.push sc).sig = sc.ret :: ρ.sig :=
    by simp

  deriving instance DecidableEq for SpawnDeque
end SpawnDeque

namespace StackFrame
  @[simp] abbrev f | mk f _ρ _X _c => f
  @[simp] abbrev ρ | mk _f ρ _X _c => ρ
  @[simp] abbrev X | mk _f _ρ X _c => X
  @[simp] abbrev c | mk _f _ρ _X c => c
  @[simp] def bsig | mk _f ρ X _c => BlockSig.mk X.length ρ.sig

  inductive WF (P : Program) (curr : Option Nat) (canProm : Bool) :
               (K : StackFrame) -> Prop where
    | mk {f ρ X c} :
         (_ : f < P.size) ->
         ρ.WF P.fsigs canProm ->
         (if curr.isNone then c.isCode else c.isCont) = true ->
         c.WF P.fsigs P[f].bsigs ⟨X.length, ρ.sig⟩
                (curr.elim P[f].fsig.ret id) ->
         (mk f ρ X c).WF P curr canProm

  namespace WF
    instance {P curr canProm} : (k : StackFrame) -> Decidable (k.WF P curr canProm)
      | .mk f ρ X c =>
        decidable_of_iff (∃ _ : f < P.size,
                          ρ.WF P.fsigs canProm ∧
                          (if curr.isNone then c.isCode else c.isCont) = true ∧
                          c.WF P.fsigs P[f].bsigs ⟨X.length, ρ.sig⟩
                            (curr.elim P[f].fsig.ret id))
          ⟨λ ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, λ ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

    theorem flt {P curr canProm} : {k : StackFrame} ->
                k.WF P curr canProm -> k.f < P.size
      | .mk _f _ρ _X _c, mk flt _ρwf _cwf _cb => flt
  end WF

  @[simp] def func {P curr canProm} (k : StackFrame) (kwf : k.WF P curr canProm) : Func :=
    P[k.f]'kwf.flt

  namespace WF

    theorem ρwf {P curr canProm} : {k : StackFrame} ->
                k.WF P curr canProm -> k.ρ.WF P.fsigs canProm
      | .mk _f _ρ _X _c, mk _flt ρwf _cwf _cb => ρwf
    theorem cwf {P curr canProm} : {k : StackFrame} -> (kwf : k.WF P curr canProm) ->
                k.c.WF P.fsigs (k.func kwf).bsigs k.bsig
                         (curr.elim (k.func kwf).fsig.ret id)
      | .mk _f _ρ _X _c, mk _flt _ρwf _cb cwf => cwf
    theorem cwf' {P curr canProm} : {k : StackFrame} -> (kwf : k.WF P curr canProm) ->
                 k.c.WF P.fsigs P[k.f]!.bsigs k.bsig
                          (curr.elim P[k.f]!.fsig.ret id)
      | .mk f _ρ _X _c, mk flt _ρwf _cb cwf =>
        getElem!_pos P f flt ▸ cwf
    theorem cwf'' {P curr canProm} : {k : StackFrame} -> (kwf : k.WF P curr canProm) ->
                  let flt : k.f < P.size := kwf.flt
                  k.c.WF P.fsigs P[k.f].bsigs k.bsig
                           (curr.elim P[k.f].fsig.ret id)
      | .mk _f _ρ _X _c, mk _flt _ρwf _cb cwf => cwf
    theorem cb {P curr canProm} : {k : StackFrame} -> (kwf : k.WF P curr canProm) ->
               (if curr.isNone then k.c.isCode else k.c.isCont) = true
      | .mk _f _ρ _X _c, mk _flt _ρwf cb _cwf => cb
    theorem isCode {P canProm} : {k : StackFrame} ->
                   (kwf : k.WF P none canProm) -> k.c.isCode := cb
    theorem isCont {P canProm ret} : {k : StackFrame} ->
                   (kwf : k.WF P (some ret) canProm) -> k.c.isCont := cb

    theorem castCanProm {P curr canProm} : {k : StackFrame} ->
                        (canProm' : Bool) -> canProm ≤ canProm' ->
                        (kwf : k.WF P curr canProm) -> k.WF P curr canProm'
      | .mk _f _ρ _X _c, canProm', l, .mk flt ρwf cwf cb =>
        .mk flt (ρwf.castCanProm canProm' l) cwf cb

    theorem entry
        {P} (Pwf : P.WF) {f canProm} {X : List Val}
        (p : f < P.size)
        (sigwf : P[f].fsig.arity = X.length) :
        WF P none canProm ⟨f, ∅, X, .codeEntry P f⟩ :=
      let fwf := Pwf.1.get ⟨f, p⟩
      let c' : Code.WF P.fsigs P[f].bsigs P[f].fsig.ret
                ⟨X.length, []⟩ P[f]!.blocks.head!.code :=
        sigwf ▸
        Eq.symm (getElem!_pos P f p) ▸
        fwf.2.headeq ▸
        fwf.2.head!eq ▸
        (fwf.1.head fwf.2.nonnil).1
      ⟨p, SpawnDeque.WF.empty, rfl, .code c'⟩

    theorem goto_rets
        {P} (Pwf : P.WF) {f canProm ρ} {X Y : ValMap} {bnext} {y : List Var}
        (p : f < P.size)
        (ρwf : ρ.WF P.fsigs canProm)
        (bnext_wf : bnext.WFRets P[f].bsigs ⟨X.length, ρ.sig⟩ y.length)
        (y_wf : IVec (·.WF Y.length) y) :
        StackFrame.WF P none canProm
          ⟨f, ρ, X[bnext.args]! ++ Y[y]!, .codeOf P f bnext⟩ :=
      let ⟨bwf, sigwf, x_wf⟩ := bnext_wf
      let bwf' : bnext.b < P[f].size :=
        by simp; exact (List.length_map Block.bsig ▸ bwf)
      let xlen : bnext.args.length = X[bnext.args].length :=
        x_wf.map_length (λ x xwf => X[x])
      let ylen : y.length = Y[y].length :=
        y_wf.map_length (λ y ywf => Y[y])
      let code_wf : P[f]![bnext.b]!.code.WF
                      P.fsigs P[f].bsigs P[f].fsig.ret
                      ⟨(X[bnext.args]! ++ Y[y]!).length, ρ.sig⟩ := by
        rw[codeOfGetElem p bwf',
           argsOfGetElem x_wf,
           argsOfGetElem y_wf,
           List.length_append,
           ← xlen, ← ylen]
        simp at sigwf
        simp
        rw[← sigwf];
        exact ((Pwf.1.get ⟨f, p⟩).1.get ⟨bnext.b, bwf'⟩).1
      ⟨p, ρwf, rfl, .code code_wf⟩
  
    theorem goto
        {P} (Pwf : P.WF) {f canProm ρ} {X : ValMap} {bnext}
        (p : f < P.size)
        (ρwf : ρ.WF P.fsigs canProm)
        (bnext_wf : bnext.WF P[f].bsigs ⟨X.length, ρ.sig⟩) :
        StackFrame.WF P none canProm ⟨f, ρ, X[bnext.args]!, .codeOf P f bnext⟩ :=
      List.append_nil X[bnext.args]! ▸
      goto_rets Pwf (Y := []) (y := []) p ρwf bnext_wf.cast0 .nil
  
    theorem goto_entry
        {P} (Pwf : P.WF) {f canProm} {X : ValMap} {x : List Var}
        (p : f < P.size)
        (xwf : IVec (·.WF X.length) x)
        (sigwf : P[f].fsig.arity = x.length) :
        StackFrame.WF P none canProm ⟨f, ∅, X[x]!, .codeEntry P f⟩ :=
      entry Pwf p (argsOfGetElem xwf ▸
                    xwf.map_length (λ x xwf => X[x]) ▸
                    sigwf)
  
  end WF

  deriving instance DecidableEq for StackFrame
end StackFrame

namespace CallStack
  notation (name := callstackcons) t " ⬝ " h:arg => cons t h

  @[simp] def append : CallStack -> CallStack -> CallStack
    | K, nil => K
    | K, K' ⬝ k => (CallStack.append K K') ⬝ k

  instance : Append CallStack where
    append := CallStack.append
  instance : Singleton StackFrame CallStack where
    singleton k := nil ⬝ k
  instance : EmptyCollection CallStack where
    emptyCollection := nil
  instance : Inhabited CallStack where
    default := nil

  @[simp] def prom : CallStack -> SporkSig
    | nil => []
    | K ⬝ k => k.ρ.prom ++ prom K
  @[simp] def unpr : CallStack -> List SpawnCall
    | nil => []
    | K ⬝ k => unpr K ++ k.ρ.unpr
  @[simp] abbrev allPromoted (K : CallStack) : Bool := K.unpr = []
  @[simp] def firstFrame : (K : CallStack) -> K ≠ nil -> StackFrame
    | nil ⬝ k, p => k
    | K  ⬝ k ⬝ _k', p => firstFrame (K ⬝ k) (by simp)

  @[simp] theorem append_eq {as bs} : append as bs = as ++ bs := rfl
  @[simp] theorem append_cons : {K K' : CallStack} -> {k : StackFrame} ->
                                K ++ (K' ⬝ k) = (K ++ K') ⬝ k
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
  @[simp] theorem append_unpr : {K K' : CallStack} -> (K ++ K').unpr = K.unpr ++ K'.unpr
    | K, nil => by simp
    | K, K' ⬝ k =>
      append_cons ▸
      List.append_assoc K.unpr K'.unpr k.ρ.unpr ▸
      @append_unpr K K' ▸
      rfl
  --@[simp] theorem append_unpr_ : {K K' : CallStack} -> (K.append K').unpr = K.unpr ++ K'.unpr := append_unpr
  @[simp] theorem append_prom : {K K' : CallStack} -> (K ++ K').prom = K'.prom ++ K.prom
    | K, nil => by simp
    | K, K' ⬝ k => by simp; exact append_prom

  theorem allPromoted_iff_nil {K} : allPromoted K <-> K.unpr = [] :=
    by simp
  theorem allPromoted_cons {K k} : allPromoted (K ⬝ k) <->
                                   allPromoted K ∧ k.ρ.unpr = [] :=
    by simp
  theorem allPromoted_append {K K'} : allPromoted (K ++ K') <->
                                      K.allPromoted ∧ K'.allPromoted :=
    by simp

  @[simp] def head : (K : CallStack) -> K ≠ nil -> StackFrame
    | _K ⬝ k, _ => k
  @[simp] def tail : CallStack -> CallStack
    | K ⬝ _k => K
    | nil => nil

  @[simp] def retjoin (P : Program) : CallStack -> Nat
    | nil => default
    | nil ⬝ ⟨f, _, _, _⟩ => P[f]!.fsig.ret
    | K ⬝ _k => K.retjoin P

  @[simp] theorem retjoin_first {P : Program} : {k : StackFrame} -> {K : CallStack} ->
                                ({k} ++ K).retjoin P = P[k.f]!.fsig.ret
    | _k, .nil => rfl
    | _k, .nil ⬝ _k' => rfl
    | _k, K ⬝ k' ⬝ _k'' => retjoin_first (K := K ⬝ k')

  /--
  (Potentially partial) call stack.
  When `get` is omitted (`none`), this must be a full call
  stack, where the current frame has `code` rather than `cont`
  When `get` is `some n`, it is a partial call stack awaiting
  a return of `n` args from the following stack frame
  -/
  inductive WF (P : Program) : (get : Option Nat := none) -> CallStack -> Prop where
    | nil {gets} : nil.WF P (some gets)
    | cons {K k gets} :
           (kwf : k.WF P gets K.allPromoted) ->
           K.WF P (k.func kwf).fsig.ret ->
           (K ⬝ k).WF P gets

  namespace WF
    notation (name := callstackwfcons) t " ⬝wf " h:arg => WF.cons h t

    instance instDecidable {P} : {gets : Option Nat} -> (K : CallStack) ->
                           Decidable (K.WF P gets)
      | some gets, .nil => isTrue WF.nil
      | none, .nil => isFalse (by cases ·)
      | gets, K ⬝ k =>
        dite (k.WF P gets K.allPromoted)
          (λ kwf => let Kwfdec : Decidable (K.WF P (some (k.func kwf).fsig.ret)) :=
                      instDecidable K
                    decidable_of_iff (K.WF P (some (k.func kwf).fsig.ret))
                      ⟨cons kwf, λ | cons _kwf' Kwf => Kwf⟩)
          (isFalse ∘ λ | kₙwf, cons kwf _Kwf => kₙwf kwf)

    theorem nonnil {P} {K : CallStack} (Kwf : K.WF P none) : K ≠ CallStack.nil :=
      by cases Kwf <;> simp
    theorem head' {P gets} :
                  {K : CallStack} ->
                  (nn : K ≠ CallStack.nil) ->
                  K.WF P gets ->
                  (K.head nn).WF P gets K.tail.allPromoted
      | _K ⬝ _k, _nn, _Kwf ⬝wf kwf => kwf
    theorem tail' {P gets} :
                  {K : CallStack} ->
                  (nn : K ≠ CallStack.nil) ->
                  (Kwf : K.WF P gets) ->
                  K.tail.WF P (some (P[(K.head nn).f]'(Kwf.head' nn).flt).fsig.ret)
      | _K ⬝ _k, _nn, Kwf ⬝wf _kwf => Kwf

    theorem head {P gets K k} (Kwf : (K ⬝ k).WF P gets) :
                 k.WF P gets K.allPromoted :=
      head' (by simp) Kwf

    theorem tail {P gets K k} (Kwf : (K ⬝ k).WF P gets) :
                  K.WF P (some (P[k.f]'Kwf.head.flt).fsig.ret) :=
      tail' (by simp) Kwf
  end WF

  deriving instance DecidableEq for CallStack
  
  @[simp] def retjoin?! {P get} : (K : CallStack) -> K.WF P get -> Option Nat
    | .nil, _wf => none
    | .nil ⬝ k, wf => some (k.func wf.head).fsig.ret
    | K ⬝ _k, wf => K.retjoin?! wf.tail
  
  theorem retjoin_eq_retjoin?! {P get} : {K : CallStack} -> (wf : K.WF P get) ->
          (if K = .nil then none else some (K.retjoin P)) = K.retjoin?! wf
    | .nil, _wf =>
      rfl
    | .nil ⬝ k, (_ ⬝wf kwf) =>
      congrArg (α := Func) (λ x => some x.fsig.ret) (getElem!_pos P k.f kwf.flt)
    | K ⬝ k ⬝ _k', wf =>
      retjoin_eq_retjoin?! (K := K ⬝ k) wf.tail

  namespace WF
    theorem append {P} : {K K' : CallStack} -> {gets : Option Nat} ->
                   K.WF P (some (K'.retjoin P)) -> K'.WF P gets ->
                   (gets.isNone ∨ K' ≠ .nil) -> K.allPromoted -> (K ++ K').WF P gets
      | K, .nil ⬝ k, gets, Kwf, K'wf@(.nil ⬝wf kwf), _, kprom =>
        by simp; exact
          (Option.some_inj.mp (retjoin_eq_retjoin?! K'wf) ▸ Kwf) ⬝wf (kprom ▸ kwf)
      | K, K' ⬝ k' ⬝ k, gets, Kwf, K'wf ⬝wf kwf, p, kprom =>
        let kprom' := allPromoted_iff_nil.mp kprom
        let kp : (K' ⬝ k').unpr = (K ++ (K' ⬝ k')).unpr :=
          by simp; rw[kprom']
        (append Kwf K'wf (Or.inr (by simp)) kprom) ⬝wf
          (by simp at kwf; simp; rw[kprom']; exact kwf)

    theorem unappend {P} : {get : Option Nat} -> {K K' : CallStack} ->
                     (K ++ K').WF P get -> (K' ≠ .nil) -> K.allPromoted ->
                     K.WF P (some (K'.retjoin P)) ∧ K'.WF P get
      | get, K, .nil ⬝ k, wf, _, kprom =>
        let wf' : (K ⬝ k).WF P get :=
          by rw[@append_cons K .nil k] at wf; exact wf
        let k_wf : k.WF P get true :=
          kprom ▸ wf'.head
        ⟨by simp only[retjoin]
            rw[getElem!_pos P k.f k_wf.flt]
            exact wf'.tail,
         .nil ⬝wf k_wf⟩
      | get, K, (K' ⬝ k') ⬝ k, wf, _, kprom =>
        let ⟨Kwf, K'wf⟩ := unappend wf.tail (by simp) kprom
        let kprom' := allPromoted_iff_nil.mp kprom
        let kp : [] ++ (K' ⬝ k').unpr = K.unpr ++ (K' ⬝ k').unpr :=
          kprom'.symm ▸ rfl
        let k'wf : k.WF P get (K' ⬝ k').allPromoted := by
          show k.WF P get ((K' ⬝ k').unpr = [])
          rw[← List.nil_append (K' ⬝ k').unpr, kp, ← append_unpr]
          exact wf.head
        ⟨Kwf, K'wf ⬝wf k'wf⟩
  end WF
end CallStack

namespace ThreadTree
  instance : Append ThreadTree where
    append := node
  instance : Singleton CallStack ThreadTree where
    singleton := thread
  instance : Insert CallStack ThreadTree where
    insert s p := {s} ++ p
  instance : Inhabited ThreadTree where
    default := thread default

  @[simp] def retjoin (P : Program) : ThreadTree -> Nat
    | thread K => K.retjoin P
    | node Rp _Rc => Rp.retjoin P

  @[simp] def prom : ThreadTree -> SporkSig
    | thread K => K.prom
    | node Rp _Rc => Rp.prom.tail

  @[simp] def spawn (P : Program) (f : FuncIdx) (args : List Val) : ThreadTree :=
    thread (.nil ⬝ ⟨f, ∅, args, .codeEntry P f⟩)

  @[simp] def init (P : Program) : ThreadTree :=
    let main := 0 -- first function in program is main()
    spawn P main []

  deriving instance DecidableEq for ThreadTree

  inductive WF (P : Program) : ThreadTree -> Prop where
    | thread {K} :
           (Kwf : K.WF P none) ->
           (thread K).WF P
    | node {Rp Rc} :
          (Rpwf : Rp.WF P) ->
          (Rcwf : Rc.WF P) ->
          (Rp.prom.head? = some (Rc.retjoin P)) ->
          (Rc.prom = []) ->
          (node Rp Rc).WF P

  namespace WF
    theorem get {P K} : (ThreadTree.thread K).WF P -> K.WF P
      | thread Kwf => Kwf
    theorem child {P Rp Rc} : (ThreadTree.node Rp Rc).WF P -> Rc.WF P
      | node _Rpwf Rcwf _Rpprom _Rcprom => Rcwf
    theorem parent {P Rp Rc} : (ThreadTree.node Rp Rc).WF P -> Rp.WF P
      | node Rpwf _Rcwf _Rprom _Rcprom => Rpwf
    theorem parent_prom {P Rp Rc} : (ThreadTree.node Rp Rc).WF P ->
                                 Rp.prom.head? = some (Rc.retjoin P)
      | node _Rpwf _Rcwf Rpprom _Rcprom => Rpprom
    theorem child_prom {P Rp Rc} : (ThreadTree.node Rp Rc).WF P -> Rc.prom = []
      | node _Rpwf _Rcwf _Rpprom Rcprom => Rcprom
  end WF

  namespace WF
    instance instDecidable {P} : (R : ThreadTree) -> Decidable (R.WF P)
      | .thread K => decidable_of_iff (K.WF P none)
          ⟨thread, λ | thread Kwf => Kwf⟩
      | .node Rp Rc =>
        let _ : Decidable (Rp.WF P) := instDecidable Rp
        let _ : Decidable (Rc.WF P) := instDecidable Rc
        decidable_of_iff (Rp.WF P ∧
                          Rc.WF P ∧
                          Rp.prom.head? = some (Rc.retjoin P) ∧
                          Rc.prom = [])
          ⟨λ ⟨Rwf, Rcwf, Rp, Rcp⟩ => node Rwf Rcwf Rp Rcp,
           λ | node Rwf Rcwf Rp Rcp => ⟨Rwf, Rcwf, Rp, Rcp⟩⟩

    theorem spawn {P f args ret} (Pwf : P.WF) (fwf : SpawnCall.WF P.fsigs (.mk f args ret)) :
                  (spawn P f args).WF P := by
      apply thread
      apply (.nil ⬝wf ·)
      exact StackFrame.WF.entry Pwf
              (by simp; rw[← List.length_map]; exact fwf.flt)
              (List.getElem_map (α := Func) (·.fsig) ▸
               (congrArg (α := FuncSig) (·.arity) fwf.sig).symm)

    theorem init {P} (Pwf : P.WF) : (ThreadTree.init P).WF P :=
      spawn (ret := 1) Pwf
        (.mk Pwf.main_lt
             (Pwf.head.get0eq ▸ (List.getElem_map (l := P.funs) (·.fsig)).symm))
  end WF

end ThreadTree


inductive Step (P : Program) : (R R' : ThreadTree) -> Type where
  | congr_parent {Rp Rp' Rc} :
    Step P Rp Rp' ->
    Step P (Rp.node Rc) (Rp'.node Rc)

  | congr_child {Rp Rc Rc'} :
    Step P Rc Rc' ->
    Step P (.node Rp Rc) (.node Rp Rc')
  
  | stmt {f K ρ X e v c} :
    X ⊢ₑₓₚᵣ e ⇓ v ->
    Step P {K ⬝ ⟨f, ρ, X, .code (.stmt e c)⟩}
            {K ⬝ ⟨f, ρ, X.concat v, .code c⟩}

  | goto {f K ρ X bnext} :
    Step P {K ⬝ ⟨f, ρ, X, .code (.goto bnext)⟩}
            {K ⬝ ⟨f, ρ, X[bnext.args]!, .codeOf P f bnext⟩}

  | ite_true {f K ρ X cond bthen belse n} :
    X ⊢ₐₜₒₘ cond ⇓ n ->
    n ≠ 0 ->
    Step P {K ⬝ ⟨f, ρ, X, .code (.ite cond bthen belse)⟩}
            {K ⬝ ⟨f, ρ, X[bthen.args]!, .codeOf P f bthen⟩}

  | ite_false {f K ρ X cond bthen belse} :
    X ⊢ₐₜₒₘ cond ⇓ 0 ->
    Step P {K ⬝ ⟨f, ρ, X, .code (.ite cond bthen belse)⟩}
            {K ⬝ ⟨f, ρ, X[belse.args]!, .codeOf P f belse⟩}

  | call {f g K ρ X x bret} :
    Step P {K ⬝ ⟨f, ρ, X, .code (.call g x bret)⟩}
            {K ⬝ ⟨f, ρ, X, .cont bret⟩ ⬝ ⟨g, {}, X[x]!, .codeEntry P g⟩}

  | retn {f g K ρ X Y y bret} :
    Step P {K ⬝ ⟨f, ρ, X, .cont bret⟩ ⬝ ⟨g, {}, Y, .code (.retn y)⟩}
            {K ⬝ ⟨f, ρ, X[bret.args]! ++ Y[y]!, .codeOf P f bret⟩}

  | spork {f K ρ X g g_args bbody} :
    Step P {K ⬝ ⟨f, ρ, X, .code (.spork bbody g g_args)⟩}
            {K ⬝ ⟨f, ρ.push ⟨g, X[g_args]!, P[g]!.fsig.ret⟩,
                  X[bbody.args]!, .codeOf P f bbody⟩}

  | promote {f unpr g prom X K c K'} :
    K.unpr = [] ->
    K'.prom = [] ->
    Step P {K ⬝ ⟨f, ⟨g :: unpr, prom⟩, X, c⟩ ++ K'}
            {K ⬝ ⟨f, ⟨unpr, g.ret :: prom⟩, X, c⟩ ++ K',
             {⟨g.f, {}, g.args, .codeEntry P g.f⟩}}

  | spoin_unpr {f K ρ sc X bunpr bprom} :
    Step P {K ⬝ ⟨f, ρ.push sc, X, .code (.spoin bunpr bprom)⟩}
            {K ⬝ ⟨f, ρ, X[bunpr.args]!, .codeOf P f bunpr⟩}

  | spoin_prom {f K ρ X bunpr bprom Y y} {g : SpawnCall} :
    K.unpr = [] ->
    Step P {(K ⬝ ⟨f, ⟨[], g.ret :: ρ⟩, X, .code (.spoin bunpr bprom)⟩),
             {⟨g.f, {}, Y, .code (.retn y)⟩}}
            {K ⬝ ⟨f, ⟨[], ρ⟩, X[bprom.args]! ++ Y[y]!, .codeOf P f bprom⟩}

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
end Steps
