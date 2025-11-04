import SporkProofs.Syntax
import SporkProofs.WFSyntax
import SporkProofs.Semantics
import SporkProofs.IVec
import SporkProofs.HeadIs
import SporkProofs.SimpSet

theorem argswf (Γ : Scope) : IVec (Γ ⊢ · WF-var) ((List.range Γ).map Var.mk) :=
  let rec h : (Γ : Scope) -> (n : Nat) ->
              IVec ((Γ + n) ⊢ · WF-var) ((List.range' n Γ).map Var.mk)
    | 0, n => .nil
    | Γ + 1, n => .cons ⟨by simp⟩ (Nat.add_assoc Γ 1 n ▸
                                   Nat.add_comm 1 n ▸
                                   h Γ (n + 1))
  List.range_eq_range' ▸ h Γ 0

namespace SpawnBlock
  inductive WF (B : BlockSigs) (bspwn : SpawnBlock) : Prop where
    | mk (_ : bspwn.b < B.length)
         (_ : B[bspwn.b].Γ = bspwn.args.length)
         (_ : B[bspwn.b].σ = [])

  namespace WF
    notation (name := notationwf) B:arg " ⊢ " bspwn " WF-spawn" => WF B bspwn
    
    instance {B: BlockSigs} (bspwn: SpawnBlock): Decidable (B ⊢ bspwn WF-spawn) :=
      decidable_of_iff (∃ _ : bspwn.b < B.length,
                        B[bspwn.b].Γ = bspwn.args.length ∧
                        B[bspwn.b].σ = [])
        ⟨λ ⟨a, b, c⟩ => .mk a b c, λ | .mk a b c => ⟨a, b, c⟩⟩

    theorem b {B bspwn}: B ⊢ bspwn WF-spawn -> bspwn.b < B.length
      | mk b _args _σ => b
    theorem b' {F : Func} {bspwn} (wf : F.B ⊢ bspwn WF-spawn) : bspwn.b < F.size :=
      F.size_eq_B_length ▸ wf.b
    theorem args {B bspwn}: (wf : B ⊢ bspwn WF-spawn) -> (B[bspwn.b]'(b wf)).Γ = bspwn.args.length
      | mk _b args _σ => args
    theorem σ {B bspwn}: (wf : B ⊢ bspwn WF-spawn) -> (B[bspwn.b]'(b wf)).σ = []
      | mk _b _args σ => σ

    theorem init {P} (Pwf : P WF-program) : (P[0]'Pwf.main.zero_lt).B ⊢ .init WF-spawn :=
      by let zlt := Pwf.main.zero_lt
         let mainΓ := congrArg FuncSig.arity Pwf.main.get0eq
         let entryΓ := congrArg BlockSig.Γ Pwf⁅0⁆.head.get0eq
         simp only [getters] at mainΓ entryΓ
         apply SpawnBlock.WF.mk <;> try (simp only [getters])
         · let mainΓ : P[0].fsig.arity = 0 := mainΓ
           simpa[mainΓ] using entryΓ
         · simpa using congrArg BlockSig.σ Pwf⁅0⁆.head.get0eq
         · exact Pwf⁅0⁆.head.zero_lt_map
  end WF
end SpawnBlock


namespace SpawnDeque
  abbrev SpawnOrder (canProm : Bool) (prom : List SpawnBlock) : Prop :=
    prom = if canProm then prom else []

  namespace SpawnOrder
    theorem of_nil {canProm : Bool} : SpawnOrder canProm [] :=
      by cases canProm <;> rfl
    theorem prom_canProm_true : (canProm : Bool) -> {bspwn : SpawnBlock} -> {prom : List SpawnBlock} ->
                                SpawnOrder canProm (bspwn :: prom) -> canProm = true
      | true, _gret, _prom, _so => rfl
  end SpawnOrder

  inductive WF (B: BlockSigs) (canProm: Bool) (ρ: SpawnDeque) : Prop
    | mk (_ : IVec (B ⊢ · WF-spawn) ρ.unpr) (_: SpawnOrder canProm ρ.prom)

  namespace WF
    notation (name := notationwf) B:arg "; " canProm:arg " ⊢ " ρ " WF-deque" => WF B canProm ρ
  
    instance {B canProm} : (ρ : SpawnDeque) -> Decidable (B; canProm ⊢ ρ WF-deque)
      | .mk u p => decidable_of_iff
          (IVec (B ⊢ · WF-spawn) u ∧ SpawnOrder canProm p)
          ⟨λ ⟨a, b⟩ => ⟨a, b⟩, λ ⟨a, b⟩ => ⟨a, b⟩⟩
    
    theorem unpr {B canProm ρ} : B; canProm ⊢ ρ WF-deque -> IVec (B ⊢ · WF-spawn) ρ.unpr | mk u _p => u
    theorem prom {B canProm ρ} : B; canProm ⊢ ρ WF-deque -> SpawnOrder canProm ρ.prom | mk _u p => p
    theorem push {B canProm ρ bspwn} (ρwf : B; canProm ⊢ ρ WF-deque) (bspwnwf : B ⊢ bspwn WF-spawn) : B; canProm ⊢ ρ.push bspwn WF-deque :=
      ⟨ρwf.1.concat bspwnwf, ρwf.2⟩
    theorem unpush {B canProm ρ bspwn} (ρwf : B; canProm ⊢ ρ.push bspwn WF-deque) : B; canProm ⊢ ρ WF-deque :=
      ⟨ρwf.1.unconcat.1, ρwf.2⟩

    theorem castCanProm {fsigs ρ} : {canProm : Bool} -> (canProm' : Bool) -> canProm ≤ canProm' -> fsigs; canProm ⊢ ρ WF-deque -> fsigs; canProm' ⊢ ρ WF-deque
      | false, false, _, .mk MatchesOblg p => .mk MatchesOblg p
      | true, true, _, .mk u p => .mk u p
      | false, true, _, .mk u _p => .mk u rfl

    theorem promote {fsigs u p bspwn} (wf : fsigs; true ⊢ ⟨bspwn :: u, p⟩ WF-deque) :
                    fsigs; true ⊢ ⟨u, bspwn :: p⟩ WF-deque :=
      ⟨wf.unpr.tail, rfl⟩

    theorem empty {fsigs canProm} : fsigs; canProm ⊢ ∅ WF-deque :=
      ⟨.nil, .of_nil⟩
  end WF
end SpawnDeque

namespace StackFrame
  inductive WF (P : Program) (K : CallStack) (get : Nat) : StackFrame -> Prop where
    | mk {f ρ X b} :
         (flt : f < P.size) ->
         (blt : b < P[f].B.length) ->
         (P[f].B[b].Γ ≤ X.length + get ∧ P[f].B[b].σ = ρ.sig P[f].B) ->
         P[f].B; K.allPromoted ⊢ ρ WF-deque ->
         (mk f ρ X b).WF P K get

  namespace WF
    notation (name := notationwf) P:arg "; " K:arg "; " get:arg " ⊢ " k " WF-frame" => WF P K get k
    notation (name := notationwf') P:arg "; " K:arg " ⊢ " k " WF-frame" => WF P K 0 k
    instance {P K get} : (k : StackFrame) -> Decidable (P; K; get ⊢ k WF-frame)
      | .mk f ρ X b =>
        decidable_of_iff (∃ flt : f < P.size,
                          ∃ blt : b < P[f].B.length,
                          (P[f].B[b].Γ ≤ X.length + get ∧ P[f].B[b].σ = ρ.sig P[f].B) ∧
                          P[f].B; K.allPromoted ⊢ ρ WF-deque)
          ⟨λ ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, λ ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

    theorem flt {P K get} : {k : StackFrame} ->
                P; K; get ⊢ k WF-frame -> k.f < P.size
      | .mk _f _ρ _X _b, mk flt _blt _bsig _ρwf => flt

    theorem blt {P K get} : {k : StackFrame} ->
                (wf : P; K; get ⊢ k WF-frame) -> k.b < (P[k.f]'wf.flt).B.length
      | .mk _f _ρ _X _b, mk _flt blt _bsig _ρwf => blt

    theorem blt' {P K get k} (wf : P; K; get ⊢ k WF-frame) :
                 k.b < (P[k.f]'wf.flt).size :=
      (P[k.f]'wf.flt).size_eq_B_length ▸ wf.blt

    theorem ρwf {P K get} : {k : StackFrame} ->
                (wf : P; K; get ⊢ k WF-frame) -> (P[k.f]'wf.flt).B; K.allPromoted ⊢ k.ρ WF-deque
      | .mk _f _ρ _X _b, mk _flt _blt _bsig ρwf => ρwf

    theorem bsig {P K get} : {k : StackFrame} ->
                 (wf : P; K; get ⊢ k WF-frame) ->
                 (((P[k.f]'wf.flt).B[k.b]'wf.blt).Γ ≤ k.X.length + get ∧
                  ((P[k.f]'wf.flt).B[k.b]'wf.blt).σ = k.ρ.sig (P[k.f]'wf.flt).B)
      | .mk _f _ρ _X _b, mk _flt _blt bsig _ρwf => bsig

    theorem bsig! {P K get} : {k : StackFrame} ->
                 (wf : P; K; get ⊢ k WF-frame) ->
                 (P[k.f]!.B[k.b]!.Γ ≤ k.X.length + get ∧
                  P[k.f]!.B[k.b]!.σ = k.ρ.sig P[k.f]!.B)
      | .mk f _ρ _X b, mk flt blt bsig _ρwf =>
        getElem!_pos P f flt ▸
        getElem!_pos P[f].B b blt ▸
        bsig

    theorem changeStack {P K K' get k} :
                        P; K; get ⊢ k WF-frame ->
                        (K.allPromoted ≤ K'.allPromoted) ->
                        P; K'; get ⊢ k WF-frame
      | .mk flt blt bsig ρwf, klt =>
        .mk flt blt bsig (ρwf.castCanProm K'.allPromoted klt)

    theorem promote {P K get f bspwn u p X b} (kprom : K.allPromoted) :
                    P; K; get ⊢ ⟨f, ⟨bspwn :: u, p⟩, X, b⟩ WF-frame ->
                    P; K; get ⊢ ⟨f, ⟨u, bspwn :: p⟩, X, b⟩ WF-frame
      | .mk flt blt bsig ρwf =>
        .mk flt blt bsig (kprom ▸ (kprom ▸ ρwf).promote)

    theorem spawn {P f bspwn} (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                  P; .nil ⊢ .spawn f bspwn WF-frame :=
      let blt := bwf.b
      ⟨flt, blt, ⟨bwf.args ▸ Nat.le_refl P[f].B[bspwn.b].Γ, bwf.σ⟩, .empty⟩

    theorem entry {P} (Pwf : P WF-program) {f K X} (flt : f < P.size)
                  (sigwf : P[f].fsig.arity = X.length) : P; K ⊢ ⟨f, ∅, X, 0⟩ WF-frame :=
      let blt : 0 < P[f].B.length :=
        Pwf⁅f⁆.head.zero_lt_map
      ⟨flt, blt, ⟨sigwf ▸ Pwf⁅f⁆.head.get0eq_map ▸ by simp,
                  List.getElem_map Block.bsig ▸
                  congrArg (·.σ) Pwf⁅f⁆.head.get0eq⟩, .empty⟩

    theorem goto_rets
        {P} {f K ρ} {X : ValMap} {bnext : Cont} {r : Nat}
        (flt : f < P.size)
        (ρwf : P[f].B; K.allPromoted ⊢ ρ WF-deque)
        (bnext_wf : P[f].B; ⟨X.length, P[f].B[bnext.b]!.r, ρ.sig P[f].B⟩ ⊢ bnext(r) WF-cont) :
        P; K; r ⊢ ⟨f, ρ, X[bnext.args]'bnext_wf.args, bnext.b⟩ WF-frame :=
      ⟨flt,
       bnext_wf.blt,
       bnext_wf.bsig ▸ by simp; rw[ValMap.getElem_length bnext_wf.args]; simp,
       ρwf⟩

    theorem goto
        {P} {f K ρ} {X : ValMap} {bnext : Cont}
        (p : f < P.size)
        (ρwf : P[f].B; K.allPromoted ⊢ ρ WF-deque)
        (bnext_wf : P[f].B; ⟨X.length, P[f].B[bnext.b]!.r, ρ.sig P[f].B⟩ ⊢ bnext WF-cont) :
        P; K ⊢ ⟨f, ρ, X[bnext.args]'bnext_wf.args, bnext.b⟩ WF-frame :=
      goto_rets p ρwf bnext_wf

    theorem goto_rets!
        {P} {f K ρ} {X : ValMap} {bnext : Cont} {r : Nat}
        (flt : f < P.size)
        (ρwf : P[f].B; K.allPromoted ⊢ ρ WF-deque)
        (bnext_wf : P[f].B; ⟨X.length, P[f].B[bnext.b]!.r, ρ.sig P[f].B⟩ ⊢ bnext(r) WF-cont) :
        P; K; r ⊢ ⟨f, ρ, X[bnext.args]!, bnext.b⟩ WF-frame :=
      getElem!_pos X bnext.args bnext_wf.args ▸
      goto_rets flt ρwf bnext_wf

    theorem goto!
        {P} {f K ρ} {X : ValMap} {bnext : Cont}
        (flt : f < P.size)
        (ρwf : P[f].B; K.allPromoted ⊢ ρ WF-deque)
        (bnext_wf : P[f].B; ⟨X.length, P[f].B[bnext.b]!.r, ρ.sig P[f].B⟩ ⊢ bnext WF-cont) :
        P; K ⊢ ⟨f, ρ, X[bnext.args]!, bnext.b⟩ WF-frame :=
      goto_rets! flt ρwf bnext_wf
  
    theorem goto_entry
        {P} (Pwf : P WF-program) {f K} {X : ValMap} {x : List Var}
        (p : f < P.size)
        (xwf : IVec (·.WF X.length) x)
        (sigwf : P[f].fsig.arity = x.length) :
        P; K ⊢ ⟨f, ∅, X[x]'xwf, 0⟩ WF-frame :=
      entry Pwf p (xwf.map_length (λ x xwf => X[x]) ▸ sigwf)
  end WF

  @[simp] def ret {P K get} (k : StackFrame) (kwf : P; K; get ⊢ k WF-frame) : Nat :=
    ((P[k.f]'kwf.flt).B[k.b]'kwf.blt).r.n

  @[simp] def ret! (P : Program) (k : StackFrame) : Nat :=
    P[k.f]!.B[k.b]!.r.n

  @[simp] def code {P K get} (k : StackFrame) (kwf : P; K; get ⊢ k WF-frame) : Code :=
    ((P[k.f]'kwf.flt)[k.b]'kwf.blt').code

  @[simp] def bsig! (P : Program) (k : StackFrame) : BlockSig :=
    ⟨k.X.length, P[k.f]!.B[k.b]!.r, k.ρ.sig P[k.f]!.B⟩
  @[simp] def bsig {P K get} (k : StackFrame) (wf : P; K; get ⊢ k WF-frame) : BlockSig :=
    let flt := wf.flt
    let blt := wf.blt
    ⟨k.X.length, (P[k.f].B[k.b]).r, k.ρ.sig P[k.f].B⟩

  namespace WF
    theorem ret!_eq_ret {P K k get} (kwf : P; K; get ⊢ k WF-frame) : k.ret! P = k.ret kwf :=
      by rw[ret, ret!,
            getElem!_pos P k.f kwf.flt,
            getElem!_pos (P[k.f]'kwf.flt).B k.b kwf.blt]

    theorem code!_eq_code {P K k get} (kwf : P; K; get ⊢ k WF-frame) : k.code! P = k.code kwf :=
      by rw[code, code!,
            getElem!_pos P k.f kwf.flt,
            getElem!_pos (P[k.f]'kwf.flt) k.b kwf.blt']

    theorem bsig!_eq_bsig {P K get} : {k : StackFrame} -> (wf : P; K; get ⊢ k WF-frame) -> k.bsig wf = k.bsig! P
      | ⟨f, _ρ, _X, b⟩, wf =>
        by simp only [StackFrame.bsig, getters, StackFrame.bsig!]
           rw[getElem!_pos P f wf.flt,
              getElem!_pos (P[f]'wf.flt).B b wf.blt]
  end WF
end StackFrame


namespace CallStack

  /--
  (Potentially partial) call stack, awaiting a return of `get` args.
  When `get` is `none`, this must be a full call stack,
  where the current frame is at the surface of the stack.
  When `get` is `some n`, it is a partial call stack awaiting
  a return of `n` args from the following stack frame
  -/
  inductive WF (P : Program) : (get : Option Nat) -> CallStack -> Prop where
    | nil {get : Nat} : nil.WF P (some get)
    | cons {K k} {get : Option Nat} :
           P; K; (get.getD 0) ⊢ k WF-frame ->
           K.WF P (some (k.ret! P)) ->
           (K ⬝ k).WF P get

  namespace WF
    notation (name := callstackwfcons) t " ⬝wf " h:arg => WF.cons h t
    notation (name := notationwf) P:arg "; " get:arg " ⊢ " K " WF-stack" => WF P get K
    notation (name := notationwf') P:arg " ⊢ " K " WF-stack" => WF P none K

    instance instDecidable {P} : {get : Option Nat} -> (K : CallStack) ->
                           Decidable (P; get ⊢ K WF-stack)
      | some get, .nil => isTrue .nil
      | none, .nil => isFalse (λ _ => by contradiction)
      | get, K ⬝ k =>
        let _ : Decidable (P; (k.ret! P) ⊢ K WF-stack) := instDecidable K
        decidable_of_iff (P; K; (get.getD 0) ⊢ k WF-frame ∧ K.WF P (some (k.ret! P)))
          ⟨λ ⟨a, b⟩ => .cons a b, λ | .cons a b => ⟨a, b⟩⟩

    theorem nonnil {P} {K : CallStack} (Kwf : P ⊢ K WF-stack) : K ≠ CallStack.nil :=
      by cases Kwf <;> simp
    theorem head' {P get} :
                  {K : CallStack} ->
                  (nn : K ≠ CallStack.nil) ->
                  P; get ⊢ K WF-stack ->
                  P; K.tail; (get.getD 0) ⊢ (K.head nn) WF-frame
      | _K ⬝ _k, _nn, _Kwf ⬝wf kwf => kwf
    theorem tail' {P get} :
                  {K : CallStack} ->
                  (nn : K ≠ CallStack.nil) ->
                  (Kwf : P; get ⊢ K WF-stack) ->
                  P; (some ((K.head nn).ret! P)) ⊢ K.tail WF-stack
      | _K ⬝ _k, _nn, Kwf ⬝wf _kwf => Kwf
    theorem head! {P get} :
                  {K : CallStack} ->
                  (nn : K ≠ CallStack.nil) ->
                  P; get ⊢ K WF-stack ->
                  P; K.tail; (get.getD 0) ⊢ K.head! WF-frame
      | _K ⬝ _k, _nn, _Kwf ⬝wf kwf => kwf

    theorem head {P get K k} (Kwf : P; get ⊢ (K ⬝ k) WF-stack) :
                 P; K; (get.getD 0) ⊢ k WF-frame :=
      head' (by simp) Kwf

    theorem tail {P get K k} (Kwf : P; get ⊢ (K ⬝ k) WF-stack) :
                 P; (some (k.ret! P)) ⊢ K WF-stack :=
      tail' (by simp) Kwf

    theorem current! {P K} (Kwf : P ⊢ K WF-stack) :
                     P; K.tail ⊢ K.head! WF-frame :=
      head! Kwf.nonnil Kwf

    theorem current {P K} (Kwf : P ⊢ K WF-stack) :
                    P; K.tail ⊢ (K.head Kwf.nonnil) WF-frame :=
      head' Kwf.nonnil Kwf
  end WF

  @[simp] def exitsig?! (P : Program) : (K : CallStack) -> Option Nat
    | .nil => none
    | .nil ⬝ k => some (k.ret! P)
    | K ⬝ _k => K.exitsig?! P
  
  theorem exitsig_eq_exitsig?! {P get} : {K : CallStack} -> (wf : P; get ⊢ K WF-stack) ->
          (if K = .nil then none else some (K.exitsig P)) = K.exitsig?! P
    | .nil, _wf =>
      rfl
    | .nil ⬝ k, (_ ⬝wf kwf) => by
      simp only [reduceCtorEq, if_false, exitsig?!, exitsig, StackFrame.ret!]
    | K ⬝ k ⬝ _k', wf =>
      exitsig_eq_exitsig?! (K := K ⬝ k) wf.tail

  @[simp] def bsig! (P : Program) (K : CallStack) : BlockSig :=
    K.head!.bsig! P
  @[simp] def bsig {P : Program} (K : CallStack) (wf : P ⊢ K WF-stack) : BlockSig :=
    (K.head wf.nonnil).bsig wf.current

  @[simp] def code {P : Program} (K : CallStack) (wf : P ⊢ K WF-stack) : Code :=
    (K.head wf.nonnil).code wf.current

  namespace WF
    theorem append {P} : {K K' : CallStack} -> {get : Option Nat} ->
                   P; (some (K'.exitsig P)) ⊢ K WF-stack -> P; get ⊢ K' WF-stack ->
                   K' ≠ .nil -> K.allPromoted -> P; get ⊢ (K ++ K') WF-stack
      | K, .nil ⬝ k, get, Kwf, K'wf@(.nil ⬝wf kwf), _knn, kprom =>
        by simp; exact
          (Option.some_inj.mp (exitsig_eq_exitsig?! K'wf) ▸ Kwf) ⬝wf
          (kwf.changeStack (λ _ => kprom))
      | K, K' ⬝ k' ⬝ k, get, Kwf, K'wf ⬝wf kwf, p, kprom =>
        (append Kwf K'wf (λ x => by contradiction) kprom) ⬝wf
          (kwf.changeStack (by simp[← ·, allPromoted_iff_nil.mp kprom]))

    theorem unappend {P} : {get : Option Nat} -> {K K' : CallStack} ->
                     P; get ⊢ (K ++ K') WF-stack -> (K' ≠ .nil) -> K.allPromoted ->
                     P; (some (K'.exitsig P)) ⊢ K WF-stack ∧ P; get ⊢ K' WF-stack
      | get, K, .nil ⬝ k, wf, _, kprom =>
        let wf' : P; get ⊢ (K ⬝ k) WF-stack :=
          by rw[@append_cons K .nil k] at wf; exact wf
        let k_wf : P; K; (get.getD 0) ⊢ k WF-frame :=
          wf'.head
        let nil_k_wf := .nil ⬝wf (k_wf.changeStack (K' := .nil) (λ _ => rfl))
        let rr : some ((.nil ⬝ k).exitsig P) = (.nil ⬝ k).exitsig?! P :=
          exitsig_eq_exitsig?! nil_k_wf
        ⟨rr ▸ wf'.tail, nil_k_wf⟩
      | get, K, (K' ⬝ k') ⬝ k, wf, _, kprom =>
        let ⟨Kwf, K'wf⟩ := unappend wf.tail (by simp) kprom
        let kprom' := allPromoted_iff_nil.mp kprom
        let kp : [] ++ (K' ⬝ k').unpr = K.unpr ++ (K' ⬝ k').unpr :=
          kprom'.symm ▸ rfl
        let k'wf : P; (K' ⬝ k'); (get.getD 0) ⊢ k WF-frame :=
          wf.head.changeStack (λ kap => by simp at kap; simp[kap])
        ⟨Kwf, K'wf ⬝wf k'wf⟩
        

    @[simp] def peeph_exitsig? (P : Program) : CallStack -> Option Nat
      | .nil => none
      | .nil ⬝ k => some P[k.f]!.B[k.b]!.r.n
      | K ⬝ _k => peeph_exitsig? P K
    @[simp] theorem peeph_exitsig?_eq {P : Program} {K : CallStack} : (peeph_exitsig? P K).getD 0 = K.exitsig P :=
      by induction K
         · case nil => rfl
         · case cons K k ih =>
           cases K
           · case nil => rfl
           · case cons K k' => simpa using ih
    @[simp] theorem peeph_cons_isSome {P K k} : (peeph_exitsig? P (K ⬝ k)).isSome = true :=
      by induction K generalizing k
         · case nil => rfl
         · case cons K' k' ih => exact ih

    theorem peep {P K k K'} (wf : P ⊢ (K ⬝ k ++ K') WF-stack) :
                 P; K; (K'.exitsig P) ⊢ k WF-frame := by
      rw[← append_one, append_assoc] at wf
      let rec h : (K' : CallStack) -> (get : Option Nat) ->
                  P; get ⊢ (K ++ ({k} ++ K')) WF-stack ->
                  P; K; (((peeph_exitsig? P K') <|> get).getD 0) ⊢ k WF-frame
        | .nil, a, wf => wf.head
        | .nil ⬝ k'', get, wf => by simpa using wf.tail.head
        | K'' ⬝ k'' ⬝ k''', get, wf =>
          let hk := h (K'' ⬝ k'') (some (StackFrame.ret! P k''')) (wf.tail)
          by rw[peeph_exitsig?,
                Option.orElse_eq_orElse,
                ← Option.or_eq_orElse,
                Option.or_of_isSome peeph_cons_isSome]
             · rw[Option.orElse_eq_orElse,
                  ← Option.or_eq_orElse,
                  Option.or_of_isSome peeph_cons_isSome] at hk
               exact hk
             · exact CallStack.noConfusion
      simpa using h K' none wf

    theorem bsig!_eq_bsig {P K} (wf : P ⊢ K WF-stack) : K.bsig wf = K.bsig! P := by
      simp only [bsig!, bsig]
      rw[wf.current.bsig!_eq_bsig,
         CallStack.head!_eq_head wf.nonnil]

    theorem code!_eq_code {P : Program} {K : CallStack} (Kwf : P ⊢ K WF-stack) : K.code! P = K.code Kwf :=
      by rw[CallStack.code!,
            CallStack.code,
            CallStack.head!_eq_head,
            Kwf.current.code!_eq_code]

    theorem code {P : Program} (Pwf : P WF-program) :
                 {K : CallStack} -> (Kwf : P ⊢ K WF-stack) ->
                 P.fsigs; (P[(K.head Kwf.nonnil).f]'Kwf.current.flt).B; (K.bsig Kwf) ⊢
                   (K.code Kwf) WF-code
      | K ⬝ k, Kwf ⬝wf kwf =>
        let flt := kwf.flt
        let blt : k.b < P[k.f].size :=
          by simpa using kwf.blt
        let Xlen : (P[k.f].B[k.b]'kwf.blt).Γ ≤ k.X.length :=
          by simpa only [Option.getD_none, Nat.add_zero] using kwf.bsig.1
        by simp only [getters, CallStack.code, StackFrame.code, CallStack.bsig, StackFrame.bsig]
           rw[← kwf.bsig.2,
              ← Nat.add_sub_of_le Xlen]
           simpa using Pwf⁅k.f⁆⁅k.b⁆.code.weaken_Γ

    theorem code! {P : Program} (Pwf : P WF-program) {K : CallStack} (Kwf : P ⊢ K WF-stack) :
                  P.fsigs; P[K.head!.f]!.B; (K.bsig! P) ⊢ (K.code! P) WF-code :=
      K.head!_eq_head Kwf.nonnil ▸
      getElem!_pos P (K.head Kwf.nonnil).f Kwf.current.flt ▸
      code!_eq_code Kwf ▸
      bsig!_eq_bsig Kwf ▸
      code Pwf Kwf

    theorem spawn {P : Program} {f : FuncIdx} {bspwn : SpawnBlock}
                  (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                  P ⊢ spawn f bspwn WF-stack :=
      .nil ⬝wf (.spawn flt bwf)

    theorem promote {P get K f bspwn u p X b} (kprom : K.allPromoted) : {K' : CallStack} ->
                    P; get ⊢ K ⬝ ⟨f, ⟨bspwn :: u, p⟩, X, b⟩ ++ K' WF-stack ->
                    P; get ⊢ K ⬝ ⟨f, ⟨u, bspwn :: p⟩, X, b⟩ ++ K' WF-stack
      | .nil, Kwf ⬝wf kwf =>
        Kwf ⬝wf (kwf.promote kprom)
      | K' ⬝ k', K'wf ⬝wf k'wf =>
        promote kprom K'wf ⬝wf (k'wf.changeStack (λ x => by simp at x))
  end WF
end CallStack

namespace Thread
  inductive WF (P : Program) : Thread -> Prop where
    | mk {K c} :
         P ⊢ K WF-stack ->
         P.fsigs; P[K.head!.f]!.B; (K.bsig! P) ⊢ c WF-code ->
         WF P (K ⋄ c)

  namespace WF
    notation (name := notationwf) P:arg " ⊢ " T " WF-thread" => WF P T

    theorem K {P} {T : Thread} : (wf : P ⊢ T WF-thread) -> P ⊢ T.K WF-stack
      | .mk K _c => K
    theorem c! {P} {T : Thread} : P ⊢ T WF-thread ->
              P.fsigs; (P[T.K.head!.f]!).B; (T.K.bsig! P) ⊢ T.c WF-code
      | .mk _K c => c
    theorem c {P} {T : Thread} (wf : P ⊢ T WF-thread) :
              P.fsigs; (P[(T.K.head wf.K.nonnil).f]'wf.K.current.flt).B; (T.K.bsig wf.K) ⊢ T.c WF-code :=
      getElem!_pos P (T.K.head wf.K.nonnil).f wf.K.current.flt ▸
      T.K.head!_eq_head wf.K.nonnil ▸
      wf.K.bsig!_eq_bsig ▸
      wf.c!

    theorem nonnil {P} {T : Thread} (wf : P ⊢ T WF-thread) : T.K ≠ .nil := wf.K.nonnil

    instance {P} : {T : Thread} -> Decidable (P ⊢ T WF-thread)
      | .nil ⋄ c => isFalse (λ p => by contradiction)
      | K ⬝ k ⋄ c =>
        decidable_of_iff (P ⊢ (K ⬝ k) WF-stack ∧
                          P.fsigs; P[k.f]!.B; ((K ⬝ k).bsig! P) ⊢ c WF-code)
          ⟨λ ⟨a, b⟩ => ⟨a, b⟩, λ ⟨a, b⟩ => ⟨a, b⟩⟩
  end WF

  @[simp] def fromStack {P : Program} (K : CallStack) (Kwf : P ⊢ K WF-stack) : Thread :=
    K ⋄ K.code Kwf

  @[simp] def spawn (P : Program) (f : FuncIdx) (bspwn : SpawnBlock)
                    (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) : Thread :=
    @fromStack P (.spawn f bspwn) (.spawn flt bwf)

  namespace WF
    theorem fromStack!_eq_fromStack {P K} (Kwf : P ⊢ K WF-stack) :
                                    fromStack! P K = fromStack K Kwf := by
      simp
      rw[K.head!_eq_head Kwf.nonnil,
         getElem!_pos P (K.head Kwf.nonnil).f Kwf.current.flt,
         getElem!_pos (P[(K.head Kwf.nonnil).f]'Kwf.current.flt) (K.head Kwf.nonnil).b Kwf.current.blt']

    theorem fromStack! {P K} (Pwf : P WF-program) (Kwf : P ⊢ K WF-stack) : P ⊢ fromStack! P K WF-thread :=
      .mk Kwf (Kwf.code! Pwf)

    theorem fromStack {P K} (Pwf : P WF-program) (Kwf : P ⊢ K WF-stack) : P ⊢ fromStack K Kwf WF-thread :=
      fromStack!_eq_fromStack Kwf ▸
      fromStack! Pwf Kwf

    theorem spawn!_eq_spawn {P f bspwn} (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                            spawn! P f bspwn = spawn P f bspwn flt bwf :=
      by simp; rw[codeOfGetElem flt bwf.b']

    theorem spawn! {P f bspwn} (Pwf : P WF-program) (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                   P ⊢ spawn! P f bspwn WF-thread :=
      fromStack! Pwf (.spawn flt bwf)
    
    theorem spawn {P f bspwn} (Pwf : P WF-program) (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                  P ⊢ spawn P f bspwn flt bwf WF-thread :=
      fromStack Pwf (.spawn flt bwf)

    theorem promote {P K f bspwn u p X b K' c} (kprom : K.allPromoted)
                    (wf : P ⊢ (K ⬝ ⟨f, ⟨bspwn :: u, p⟩, X, b⟩ ++ K') ⋄ c WF-thread) :
                    P ⊢ (K ⬝ ⟨f, ⟨u, bspwn :: p⟩, X, b⟩ ++ K') ⋄ c WF-thread :=
      .mk (wf.K.promote kprom)
          (let wfc := wf.c
           by cases K' <;>
              (rw[← getElem!_pos P, ← CallStack.head!_eq_head,
                  CallStack.WF.bsig!_eq_bsig] at wfc; exact wfc))
  end WF
end Thread

namespace ThreadTree
  inductive WF (P : Program) : ThreadTree -> Prop where
    | thread {T} :
           (Twf : P ⊢ T WF-thread) ->
           (thread T).WF P
    | node {Rp Rc} :
          (Rpwf : Rp.WF P) ->
          (Rcwf : Rc.WF P) ->
          ((Rp.promsig P).head? = some (Rc.exitsig P)) ->
          (Rc.prom = []) ->
          (Rp ⋏ Rc).WF P

  namespace WF
    notation (name := notationwf) P:arg " ⊢ " R " WF-tree" => WF P R

    theorem get {P T} : P ⊢ .thread T WF-tree -> P ⊢ T WF-thread
      | thread Twf => Twf
    theorem child {P Rp Rc} : P ⊢ Rp ⋏ Rc WF-tree -> Rc.WF P
      | node _Rpwf Rcwf _Rpprom _Rcprom => Rcwf
    theorem parent {P Rp Rc} : (Rp ⋏ Rc).WF P -> Rp.WF P
      | node Rpwf _Rcwf _Rprom _Rcprom => Rpwf
    theorem parent_prom {P Rp Rc} : (Rp ⋏ Rc).WF P ->
                                 (Rp.promsig P).head? = some (Rc.exitsig P)
      | node _Rpwf _Rcwf Rpprom _Rcprom => Rpprom
    theorem child_prom {P Rp Rc} : (Rp ⋏ Rc).WF P -> Rc.prom = []
      | node _Rpwf _Rcwf _Rpprom Rcprom => Rcprom

    instance instDecidable {P} : (R : ThreadTree) -> Decidable (R.WF P)
      | .thread T => decidable_of_iff (P ⊢ T WF-thread)
          ⟨thread, λ | thread Kwf => Kwf⟩
      | Rp ⋏ Rc =>
        let _ : Decidable (Rp.WF P) := instDecidable Rp
        let _ : Decidable (Rc.WF P) := instDecidable Rc
        decidable_of_iff (Rp.WF P ∧
                          Rc.WF P ∧
                          (Rp.promsig P).head? = some (Rc.exitsig P) ∧
                          Rc.prom = [])
          ⟨λ ⟨Rwf, Rcwf, Rp, Rcp⟩ => node Rwf Rcwf Rp Rcp,
           λ | node Rwf Rcwf Rp Rcp => ⟨Rwf, Rcwf, Rp, Rcp⟩⟩
  end WF

  @[simp] def spawn (P : Program) (f : FuncIdx) (bspwn : SpawnBlock)
                    (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) : ThreadTree :=
    thread (.spawn P f bspwn flt bwf)

  @[simp] def init (P : Program) (Pwf : P WF-program) : ThreadTree :=
    let main := 0 -- first function in program is main()
    let entry := SpawnBlock.mk 0 [] -- entry block with no args (since main takes none)
    let zlt := Pwf.main.zero_lt
    spawn P main entry zlt (.init Pwf)

  namespace WF
    theorem spawn!_eq_spawn {P f bspwn} (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                            spawn! P f bspwn = spawn P f bspwn flt bwf := by
      simp only [spawn!, spawn]
      rw[Thread.WF.spawn!_eq_spawn flt bwf]
    
    theorem spawn! {P f bspwn} (Pwf : P WF-program) (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                   P ⊢ spawn! P f bspwn WF-tree :=
      .thread (.spawn! Pwf flt bwf)

    theorem spawn {P f bspwn} (Pwf : P WF-program) (flt : f < P.size) (bwf : P[f].B ⊢ bspwn WF-spawn) :
                  P ⊢ spawn P f bspwn flt bwf WF-tree :=
      .thread (.spawn Pwf flt bwf)

    theorem init!_eq_init {P} (Pwf : P WF-program) : init! P = init P Pwf :=
      by simp only [init!, init]
         rw[spawn!_eq_spawn Pwf.main.zero_lt (by simpa using .init Pwf)]
    
    theorem init! {P} (Pwf : P WF-program) : P ⊢ init! P WF-tree :=
      spawn! Pwf Pwf.main.zero_lt (.init Pwf)

    theorem init {P} (Pwf : P WF-program) : P ⊢ init P Pwf WF-tree :=
      spawn Pwf Pwf.main.zero_lt (.init Pwf)
  end WF
end ThreadTree
