import SporkProofs.Syntax
import SporkProofs.WFSyntax

abbrev ValMap : Type := List Val

-- inductive StackFrameCode : Type
--   | code (b: BlockIdx) (c : Code)
--   | cont (b : Cont)

inductive SpawnBlock : Type where
  | mk (b: BlockIdx) (args: List Val)
-- abbrev SpawnBlock: Type := Cont

inductive SpawnDeque : Type where
  -- unpromoted sporks, oldest first (queue)
  -- promoted sporks, oldest last (stack)
  | mk (unpr : List SpawnBlock) (prom : List SpawnBlock)

inductive StackFrame : Type
  | mk (f : FuncIdx)
       (ρ : SpawnDeque)
       (X : ValMap)
       (b : BlockIdx)

inductive CallStack : Type where
  | nil
  | cons (K : CallStack) (k : StackFrame)

inductive Thread : Type where
  | mk : CallStack -> Code -> Thread

inductive ThreadTree : Type where
  | thread : Thread -> ThreadTree
  | node : ThreadTree -> ThreadTree -> ThreadTree

@[simp] def valOf (p : Prop) [d : Decidable p] : Val := if decide p then 1 else 0

namespace ValMap
  instance : GetElem ValMap Var Val (·.length ⊢ · WF-var) where
    getElem X x xwf := X[x.idx]'xwf.1

  instance : GetElem ValMap (List Var) (List Val) (λ X => IVec (X.length ⊢ · WF-var)) where
    getElem X _args argswf := argswf.list_map (λ x xwf => X[x])

  theorem getElem_length {X : ValMap} {args : List Var} (wf : IVec (X.length ⊢ · WF-var) args) : X[args].length = args.length :=
      by simp[instGetElemListVarValIVecWFLength,
              IVec.map_length (λ x xwf => X[x]) wf]

  -- theorem getElem!_length (X : ValMap) (args : List Var) : X[args]!.length = args.length := by
  --   simp[GetElem?.getElem!, decidableGetElem?]
  --   exact
  --   if x : decide (IVec (X.length ⊢ · WF-var) args) then
  --     by simp at x; simp[x, getElem_length X args x]
  --   else
  --     by simp at x; simp[x]
end ValMap

namespace Atom
  @[simp] def eval : (X : ValMap) -> (a : Atom) -> X.length ⊢ a WF-atom -> Val
    | _X, .val v, _wfᵥ => v
    | X, .var x, wfₓ =>
      let _ := match wfₓ with | .var p => p
      X[x]

  inductive Eval (X : ValMap) (a : Atom) : Val -> Prop where
    | mk (wfₐ : X.length ⊢ a WF-atom) : Eval X a (eval X a wfₐ)

  notation (name := atomeval) X:arg " ⊢ₐₜₒₘ " a:arg " ⇓ " v:arg => Eval X a v

  namespace Eval
    instance : {X : ValMap} -> {a : Atom} -> {v : Val} -> Decidable (X ⊢ₐₜₒₘ a ⇓ v)
      | X, a, v => decidable_of_iff (∃ p : X.length ⊢ a WF-atom, eval X a p = v)
        ⟨λ ⟨wfₐ, p⟩ => p ▸ Eval.mk wfₐ,
         λ | (Eval.mk wfₐ) => ⟨wfₐ, rfl⟩⟩

    theorem wf {X : ValMap} {a : Atom} {v : Val} : Eval X a v -> X.length ⊢ a WF-atom
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
  @[simp] def eval (X : ValMap) : (e : Expr) -> (X.length ⊢ e WF-expr) -> Val
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
    | mk (ewf : X.length ⊢ e WF-expr) : Eval X e (eval X e ewf)

  notation (name := expreval) X:arg " ⊢ₑₓₚᵣ " e:arg " ⇓ " v:arg => Eval X e v

  namespace Eval
    instance {X : ValMap} {e : Expr} {v : Val} : Decidable (X ⊢ₑₓₚᵣ e ⇓ v) :=
      decidable_of_iff (∃ (ewf : X.length ⊢ e WF-expr), eval X e ewf = v)
        ⟨λ ⟨ewf, p⟩ => p ▸ mk ewf,
         λ | mk ewf => ⟨ewf, rfl⟩⟩

    theorem wf {X : ValMap} {e : Expr} {v: Val} : X ⊢ₑₓₚᵣ e ⇓ v -> X.length ⊢ e WF-expr
      | mk ewf => ewf
    theorem eq  {X : ValMap} {e : Expr} {v: Val} : (s : X  ⊢ₑₓₚᵣ e ⇓ v) -> eval X e (wf s) = v
      | mk ewf => rfl
  end Eval
end Expr

theorem codeOfGetElem {P : Program} {f : FuncIdx} {b : BlockIdx}
                    (pf : f < P.size) (pb : b < P[f].size) :
                    P[f]![b]! = P[f][b] :=
  by rw[getElem!_pos P f pf, getElem!_pos P[f] b pb]

theorem argsOfGetElem {x : List Var} {X : ValMap} (wf : IVec (X.length ⊢ · WF-var) x):
                    X[x]! = X[x] :=
  getElem!_pos X x wf

-- namespace StackFrameCode  
--   abbrev isCode | code _ _ => true | cont _ => false
--   abbrev isCont | code _ _ => false | cont _ => true

--   @[simp] def extractD : (c : StackFrameCode) -> if isCode c then BlockIdx × Code else Cont
--     | code b c => (b, c)
--     | cont b => b
--   abbrev extractCode : (c : StackFrameCode) -> isCode c -> BlockIdx × Code
--     | code b c, _ => (b, c)
--   abbrev extractCont : (c : StackFrameCode) -> isCont c -> Cont
--     | cont b, _ => b

--   @[simp] abbrev codeOfBlockIdx (P : Program) (f : FuncIdx) (b : BlockIdx) : StackFrameCode :=
--     code b P[f]![b]!.code
--   @[simp] abbrev codeOf (P : Program) (f : FuncIdx) (b : Cont) : StackFrameCode :=
--     code b.b P[f]![b.b]!.code
--   @[simp] abbrev codeEntry (P : Program) (f : FuncIdx) : StackFrameCode :=
--     code P[f]!.blocks.head!.code

--   deriving instance DecidableEq for StackFrameCode
-- end StackFrameCode

namespace SpawnBlock
  def b | mk b _args => b
  def args | mk _b args => args

  @[simp, getters] theorem get_fix {bspwn : SpawnBlock} : mk bspwn.b bspwn.args = bspwn := rfl
  @[simp, getters] theorem get_1 {bspwn : SpawnBlock} : bspwn.1 = bspwn.b := rfl
  @[simp, getters] theorem get_2 {bspwn : SpawnBlock} : bspwn.2 = bspwn.args := rfl
  @[simp, getters] theorem get_b {b args} : (mk b args).b = b := rfl
  @[simp, getters] theorem get_args {b args} : (mk b args).args = args := rfl

  @[simp] def code (P : Program) (f : FuncIdx) (bspwn : SpawnBlock) : Code :=
    P[f]![bspwn.b]!.code

  @[simp] def init : SpawnBlock := mk 0 []
  
  deriving instance Repr, DecidableEq for SpawnBlock
end SpawnBlock

namespace SpawnDeque
  def unpr | mk u _p => u
  def prom | mk _u p => p

  @[simp, getters] theorem get_fix {ρ : SpawnDeque} : mk ρ.unpr ρ.prom = ρ := rfl
  @[simp, getters] theorem get_1 {ρ : SpawnDeque} : ρ.1 = ρ.unpr := rfl
  @[simp, getters] theorem get_2 {ρ : SpawnDeque} : ρ.2 = ρ.prom := rfl
  @[simp, getters] theorem get_unpr {u p} : (mk u p).unpr = u := rfl
  @[simp, getters] theorem get_prom {u p} : (mk u p).prom = p := rfl
  
  @[simp] def out : SpawnDeque -> List SpawnBlock
    | mk u p => List.reverseAux u p
  @[simp] def promsig (B : List BlockSig) (ρ : SpawnDeque) : List Nat :=
    ρ.prom.map (B[·.b]!.r)
  @[simp] def sig (B: List BlockSig) (ρ : SpawnDeque) : List Nat :=
    ρ.out.map (B[·.b]!.r)
  @[simp] def push : SpawnDeque -> SpawnBlock -> SpawnDeque
    | ⟨u, p⟩, bspwn => ⟨u.concat bspwn, p⟩
  @[simp] def pop_prom : SpawnDeque -> SpawnDeque
    | ⟨bspwn :: u, p⟩ => ⟨u, bspwn :: p⟩
    | ⟨[], p⟩ => ⟨[], p⟩
  theorem pushsig (B: List BlockSig) (ρ : SpawnDeque) (bspwn : SpawnBlock)
                  : (ρ.push bspwn).sig B = B[bspwn.b]!.r :: ρ.sig B :=
    by simp

  instance : EmptyCollection SpawnDeque := ⟨⟨[], []⟩⟩
  deriving instance Repr, DecidableEq, Inhabited for SpawnDeque

  theorem sig_nil {B} : sig B ∅ = [] := rfl
end SpawnDeque

namespace StackFrame
  def f | mk f _ρ _X _b => f
  def ρ | mk _f ρ _X _b => ρ
  def X | mk _f _ρ X _b => X
  def b | mk _f _ρ _X b => b
  
  @[simp, getters] theorem get_fix {k : StackFrame} : mk k.f k.ρ k.X k.b = k := rfl
  @[simp, getters] theorem get_1 {k : StackFrame} : k.1 = k.f := rfl
  @[simp, getters] theorem get_2 {k : StackFrame} : k.2 = k.ρ := rfl
  @[simp, getters] theorem get_3 {k : StackFrame} : k.3 = k.X := rfl
  @[simp, getters] theorem get_4 {k : StackFrame} : k.4 = k.b := rfl
  @[simp, getters] theorem get_f {f ρ X b} : (mk f ρ X b).f = f := rfl
  @[simp, getters] theorem get_ρ {f ρ X b} : (mk f ρ X b).ρ = ρ := rfl
  @[simp, getters] theorem get_X {f ρ X b} : (mk f ρ X b).X = X := rfl
  @[simp, getters] theorem get_b {f ρ X b} : (mk f ρ X b).b = b := rfl

  @[simp] def code! (P : Program) (k : StackFrame) : Code :=
    P[k.f]![k.b]!.code

  @[simp] def spawn (f : FuncIdx) (bspwn : SpawnBlock) : StackFrame :=
    ⟨f, {}, bspwn.args, bspwn.b⟩

  deriving instance Repr, DecidableEq, Inhabited for StackFrame
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

  @[simp] def promsig (P : Program): CallStack -> List Nat
    | nil => []
    | K ⬝ k => k.ρ.promsig P[k.f]!.B ++ K.promsig P
  @[simp] def prom : CallStack -> List SpawnBlock
    | nil => []
    | K ⬝ k => k.ρ.prom ++ prom K
  @[simp] def unpr : CallStack -> List SpawnBlock
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
  @[simp] theorem append_promsig (P : Program) : {K K' : CallStack} -> (K ++ K').promsig P = K'.promsig P ++ K.promsig P
    | K, nil => by simp
    | K, K' ⬝ k => by simp; exact append_promsig P
  theorem prom_promsig_nil {P : Program} : {K : CallStack} -> K.prom = [] ↔ K.promsig P = []
    | nil => by simp
    | K ⬝ ⟨f, ⟨υ, π⟩, X, b⟩ => by simp; intro πnil; exact prom_promsig_nil

  @[simp] theorem prom_nil : (∅ : CallStack).prom = [] := rfl
  @[simp] theorem unpr_nil : nil.unpr = [] := rfl
  @[simp] theorem promsig_nil {P} : nil.promsig P = [] := rfl

  theorem allPromoted_iff_nil {K} : allPromoted K <-> K.unpr = [] :=
    by simp
  theorem allPromoted_cons {K k} : allPromoted (K ⬝ k) <->
                                   allPromoted K ∧ k.ρ.unpr = [] :=
    by simp
  theorem allPromoted_append {K K'} : allPromoted (K ++ K') <->
                                      K.allPromoted ∧ K'.allPromoted :=
    by simp

  def head : (K : CallStack) -> K ≠ nil -> StackFrame
    | _K ⬝ k, _ => k
  def tail : CallStack -> CallStack
    | K ⬝ _k => K
    | nil => nil

  def head? : CallStack -> Option StackFrame
    | _K ⬝ k => some k
    | nil => none
  def head! (K : CallStack) : StackFrame := K.head?.getD default

  @[simp, getters] theorem get_fix : {K : CallStack} -> {nn : K ≠ nil} ->
                                     K.tail ⬝ (K.head nn) = K
    | _K ⬝ _k, _ => rfl
  @[simp, getters] theorem get_head {K k} : (K ⬝ k).head CallStack.noConfusion = k := rfl
  @[simp, getters] theorem get_head! {K k} : (K ⬝ k).head! = k := rfl
  @[simp, getters] theorem get_head? {K k} : (K ⬝ k).head? = some k := rfl
  @[simp, getters] theorem get_tail {K k} : (K ⬝ k).tail = K := rfl
  @[simp, getters] theorem get_head!_nil : nil.head! = default := rfl
  @[simp, getters] theorem get_tail_nil : nil.tail = nil := rfl

  theorem head!_eq_head : {K : CallStack} -> (nn : K ≠ nil) -> K.head! = K.head nn
    | _K ⬝ _k, _nn => rfl

  @[simp] def retjoin (P : Program) : CallStack -> Nat
    | nil => default
    | nil ⬝ k => P[k.f]!.B[k.b]!.r
    | K ⬝ _k => K.retjoin P

  @[simp] theorem retjoin_first {P : Program} : {k : StackFrame} -> {K : CallStack} ->
                                ({k} ++ K).retjoin P = P[k.f]!.B[k.b]!.r
    | _k, .nil => rfl
    | _k, .nil ⬝ _k' => rfl
    | _k, K ⬝ k' ⬝ _k'' => retjoin_first (K := K ⬝ k')

  deriving instance Repr, DecidableEq for CallStack

  @[simp] def spawn (f : FuncIdx) (bspwn : SpawnBlock) : CallStack :=
    .nil ⬝ (.spawn f bspwn)

  @[simp] def code! (P : Program) (K : CallStack) : Code :=
    K.head!.code! P
end CallStack

namespace Thread
  -- 51 because priority of (=) is 50
  notation (name := threadnotation) K:49 " ⋄ " c:51 => Thread.mk K c

  def K | K ⋄ _c => K
  def c | _K ⋄ c => c

  @[simp, getters] theorem get_fix {T : Thread} : T.K ⋄ T.c = T := rfl
  @[simp, getters] theorem get_1 {T : Thread} : T.1 = T.K := rfl
  @[simp, getters] theorem get_2 {T : Thread} : T.2 = T.c := rfl
  @[simp, getters] theorem get_K {K c} : (K ⋄ c).K = K := rfl
  @[simp, getters] theorem get_c {K c} : (K ⋄ c).c = c := rfl
  
  @[simp] def retjoin (P : Program) : Thread -> Nat
    | K ⋄ _c => K.retjoin P

  @[simp] def prom (T : Thread) := T.K.prom
  @[simp] def unpr (T : Thread) := T.K.unpr
  @[simp] def promsig (P : Program) (T : Thread) := T.K.promsig P

  instance : Inhabited Thread where
    default := default ⋄ .retn []

  deriving instance Repr, DecidableEq for Thread

  @[simp] def fromStack! (P : Program) (K : CallStack) : Thread :=
    K ⋄ K.code! P

  @[simp] def spawn! (P : Program) (f : FuncIdx) (bspwn : SpawnBlock) : Thread :=
    fromStack! P (.spawn f bspwn)
end Thread

namespace ThreadTree
  notation (name := notationnode) Rp " ⋏ " Rc => ThreadTree.node Rp Rc

  instance : Append ThreadTree where
    append := node
  instance : Singleton Thread ThreadTree where
    singleton := thread
  instance : Insert Thread ThreadTree where
    insert s p := {s} ++ p
  instance : Inhabited ThreadTree where
    default := thread default

  @[simp] def retjoin (P : Program) : ThreadTree -> Nat
    | thread T => T.retjoin P
    | Rp ⋏ _Rc => Rp.retjoin P

  @[simp] def prom : ThreadTree -> List SpawnBlock
    | thread T => T.prom
    | Rp ⋏ _Rc => Rp.prom.tail

  @[simp] def promsig (P : Program) : ThreadTree -> List Nat
    | thread T => T.promsig P
    | Rp ⋏ _Rc => (Rp.promsig P).tail

  @[simp] def split : ThreadTree -> Thread × List ThreadTree
    | thread T => ⟨T, []⟩
    | Rp ⋏ Rc => let ⟨K, Rs⟩ := split Rp; ⟨K, Rc :: Rs⟩

  @[simp] def merge : Thread × List ThreadTree -> ThreadTree
    | ⟨T, []⟩ => thread T
    | ⟨T, R :: Rs⟩ => merge ⟨T, Rs⟩ ⋏ R

  @[simp] theorem split_merge : {KRs : Thread × List ThreadTree} -> split (merge KRs) = KRs
    | ⟨K, []⟩ => by simp
    | ⟨K, R :: Rs⟩ => by simp[split_merge (KRs := ⟨K, Rs⟩)]

  @[simp] theorem merge_split : {R : ThreadTree} -> merge (split R) = R
    | thread K => by simp
    | Rp ⋏ Rc => by simp[merge_split (R := Rp)]

  @[simp] def spawn! (P : Program) (f : FuncIdx) (bspwn : SpawnBlock) : ThreadTree :=
    thread (.spawn! P f bspwn)

  @[simp] def init! (P : Program) : ThreadTree :=
    let main := 0 -- first function in program is main()
    let entry := SpawnBlock.mk 0 [] -- entry block with no args (since main takes none)
    spawn! P main entry

  deriving instance Repr, DecidableEq for ThreadTree
end ThreadTree

inductive Step (P : Program) : (R R' : ThreadTree) -> Type where
  | congr_parent {Rp Rp' Rc} :
    Step P Rp Rp' ->
    Step P (Rp ⋏ Rc) (Rp' ⋏ Rc)

  | congr_child {Rp Rc Rc'} :
    Step P Rc Rc' ->
    Step P (Rp ⋏ Rc) (Rp ⋏ Rc')
  
  | stmt {f K ρ X b e v c} :
    X ⊢ₑₓₚᵣ e ⇓ v ->
    Step P {K ⬝ ⟨f, ρ, X, b⟩ ⋄ .stmt e c}
           {K ⬝ ⟨f, ρ, X.concat v, b⟩ ⋄ c}

  | goto {f K ρ X b bnext} :
    Step P {K ⬝ ⟨f, ρ, X, b⟩ ⋄ .goto bnext}
           {K ⬝ ⟨f, ρ, X[bnext.args]!, bnext.b⟩ ⋄ P[f]![bnext.b]!.code}

  | ite_true {f K ρ X b cond bthen belse n} :
    X ⊢ₐₜₒₘ cond ⇓ n ->
    n ≠ 0 ->
    Step P {K ⬝ ⟨f, ρ, X, b⟩ ⋄ .ite cond bthen belse}
           {K ⬝ ⟨f, ρ, X[bthen.args]!, bthen.b⟩ ⋄ P[f]![bthen.b]!.code}

  | ite_false {f K ρ X b cond bthen belse} :
    X ⊢ₐₜₒₘ cond ⇓ 0 ->
    Step P {K ⬝ ⟨f, ρ, X, b⟩ ⋄ .ite cond bthen belse}
           {K ⬝ ⟨f, ρ, X[belse.args]!, belse.b⟩ ⋄ P[f]![belse.b]!.code}

  | call {f g K ρ b X x bret} :
    Step P {K ⬝ ⟨f, ρ, X, b⟩ ⋄ .call g x bret}
           {K ⬝ ⟨f, ρ, X[bret.args]!, bret.b⟩ ⬝ ⟨g, {}, X[x]!, 0⟩ ⋄ P[g]!.entry}

  | retn {f g K ρ X Y y b bret} :
    Step P {K ⬝ ⟨f, ρ, X, bret⟩ ⬝ ⟨g, {}, Y, b⟩ ⋄ .retn y}
           {K ⬝ ⟨f, ρ, X ++ Y[y]!, bret⟩ ⋄ P[f]![bret]!.code}

  | spork {f K ρ X b bbody bspwn} :
    Step P {K ⬝ ⟨f, ρ, X, b⟩ ⋄ .spork bbody bspwn}
           {K ⬝ ⟨f, ρ.push ⟨bspwn.b, X[bspwn.args]!⟩,
                 X[bbody.args]!, bbody.b⟩ ⋄ P[f]![bbody.b]!.code}

  | promote {f unpr bspwn prom X K b K' C} :
    K.unpr = [] ->
    K'.prom = [] ->
    Step P {(K ⬝ ⟨f, ⟨bspwn :: unpr, prom⟩, X, b⟩ ++ K') ⋄ C}
           {(K ⬝ ⟨f, ⟨unpr, bspwn :: prom⟩, X, b⟩ ++ K') ⋄ C,
            {⟨f, {}, bspwn.args, bspwn.b⟩} ⋄ P[f]![bspwn.b]!.code}

  | spoin_unpr {f K ρ bspwn X b bunpr bprom} :
    Step P {K ⬝ ⟨f, ρ.push bspwn, X, b⟩ ⋄ .spoin bunpr bprom}
           {K ⬝ ⟨f, ρ, X[bunpr.args]!, bunpr.b⟩ ⋄ P[f]![bunpr.b]!.code}

  | spoin_prom {f g K ρ X b b' bunpr bprom Y y} {bspwn : SpawnBlock} :
    K.unpr = [] ->
    Step P {(K ⬝ ⟨f, ⟨[], bspwn :: ρ⟩, X, b⟩ ⋄ .spoin bunpr bprom),
             {⟨g, {}, Y, b'⟩} ⋄ .retn y}
           {K ⬝ ⟨f, ⟨[], ρ⟩, X[bprom.args]! ++ Y[y]!, bprom.b⟩ ⋄ P[f]![bprom.b]!.code}

  -- | spoin_prom {f K π X bunpr bprom bspwn} :
  --   K.unpr = [] ->
  --   Step P {K ⬝ ⟨f, ⟨[], bspwn :: π⟩, X, .code (.spoin bunpr bprom)⟩}
  --          {K ⬝ ⟨f, ⟨[], π⟩, X[bprom.args]!, .codeOf P f bprom⟩}

  -- | sync {f K ρ X Y y bsync} :
  --     Step P {K ⬝ ⟨f, ρ, X, .code (.join bsync)⟩,
  --             {⟨f, {}, Y, .code (.exit y)⟩}}
  --            {K ⬝ ⟨f, ρ, X ++ Y[y]!, .codeOf P f bsync⟩}

  -- | spoin_prom {f K ρ X bunpr bprom Y y} {bspwn : SpawnBlock} :
  --   K.unpr = [] ->
  --   Step P {(K ⬝ ⟨f, ⟨[], bspwn :: ρ⟩, X, .code (.spoin bunpr bprom)⟩),
  --            {⟨f, {}, Y, .code (.exit y)⟩}}
  --           {K ⬝ ⟨f, ⟨[], ρ⟩, X[bprom.args]! ++ Y[y]!, .codeOf P f bprom⟩}

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

  @[simp] def concat {P : Program} : {R R' R'' : ThreadTree} ->
                (P ⊢ R ↦ R') -> (P ⊢ R' ↦* R'') -> (P ⊢ R ↦* R'')
    | _R, _R', .(_R'), ss', nil => {ss'}
    | _R, _R', _R'', ss', cons ss s => cons (concat ss' ss) s

  universe u
  def byInd {Q : ThreadTree -> Sort u}
            {P : Program} :
            {Rₛ Rₑ : ThreadTree} ->
            Q Rₛ ->
            ((Rᵢ Rᵢ₁ : ThreadTree) -> Q Rᵢ -> P ⊢ Rᵢ ↦ Rᵢ₁ -> Q Rᵢ₁) ->
            P ⊢ Rₛ ↦* Rₑ ->
            Q Rₑ
    | Rₛ, .(Rₛ), n, _c, nil => n
    | Rₛ, Rₑ, n, c, @Steps.cons .(P) .(Rₛ) R₁ₑ .(Rₑ) ss s =>
      c R₁ₑ Rₑ (byInd n c ss) s

  def byIndR {Q : ThreadTree -> Sort u}
            {P : Program} :
            {Rₛ Rₑ : ThreadTree} ->
            Q Rₑ ->
            ((Rᵢ Rᵢ₁ : ThreadTree) -> P ⊢ Rᵢ ↦ Rᵢ₁ -> Q Rᵢ₁ -> Q Rᵢ) ->
            P ⊢ Rₛ ↦* Rₑ ->
            Q Rₛ
    | Rₛ, .(Rₛ), n, _c, nil => n
    | Rₛ, Rₑ, n, c, @Steps.cons .(P) .(Rₛ) R₁ₑ .(Rₑ) ss s =>
      byIndR (c R₁ₑ Rₑ s n) c ss

  -- | congr_parent {Rp Rp' Rc} :
  --   Step P Rp Rp' ->
  --   Step P (Rp.node Rc) (Rp'.node Rc)

  -- | congr_child {Rp Rc Rc'} :
  --   Step P Rc Rc' ->
  --   Step P (.node Rp Rc) (.node Rp Rc')

  def congr_parent {P} {Rp Rp' Rc : ThreadTree} :
                   P ⊢ Rp ↦* Rp' -> P ⊢ (Rp ⋏ Rc) ↦* (Rp' ⋏ Rc)
    | .nil => .nil
    | .cons ss s => .cons ss.congr_parent s.congr_parent

  def congr_child {P} {Rp Rc Rc' : ThreadTree} :
                  P ⊢ Rc ↦* Rc' -> P ⊢ (Rp ⋏ Rc) ↦* (Rp ⋏ Rc')
    | .nil => .nil
    | .cons ss s => .cons ss.congr_child s.congr_child

end Steps
