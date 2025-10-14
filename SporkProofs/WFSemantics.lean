import SporkProofs.Syntax
import SporkProofs.WFSyntax
import SporkProofs.Semantics
import SporkProofs.IVec
import SporkProofs.HeadIs

namespace StackFrameCode
  inductive WF (fsigs B bsig ret) : StackFrameCode -> Prop
    | code {c} : c.WF fsigs B bsig -> (code c).WF fsigs B bsig ret
    | cont {b} : b.WFRets B bsig ret -> (cont b).WF fsigs B bsig ret

  namespace WF
    notation (name := notationwf) fsigs:arg " ; " B:arg " ; " bsig:arg " ; " ret:arg " ⊢ " c:arg " WF-sfc" => WF fsigs B bsig ret c

    instance {fsigs B bsig ret} : (c : StackFrameCode) ->
             Decidable (fsigs; B; bsig; ret ⊢ c WF-sfc)
      | .code c =>
        decidable_of_iff (fsigs; B; bsig ⊢ c WF-code)
          ⟨code, λ (code p) => p⟩
      | .cont b =>
        decidable_of_iff (B; bsig ⊢ b(ret) WF-cont)
          ⟨cont, λ (cont p) => p⟩

    theorem c {fsigs B bsig ret c} :
             fsigs; B; bsig; ret ⊢ (.code c) WF-sfc ->
             fsigs; B; bsig ⊢ c WF-code
      | code c => c

    theorem b {fsigs B bsig b ret} :
             fsigs; B; bsig; ret ⊢ (.cont b) WF-sfc ->
             B; bsig ⊢ b(ret) WF-cont
      | cont b => b
  end WF
end StackFrameCode

/-
  inductive WF (B : BlockSigs) (bsig : BlockSig) (b : Cont) : Prop where
    | mk (_ : b.b < B.length)
         (_ : B[b.b] = ⟨b.args.length, bsig.σ⟩)
         (_ : IVec (bsig.Γ ⊢ · WF-var) b.args)
-/

namespace SpawnBlock
  inductive WF (B : BlockSigs) (bspwn : SpawnBlock) : Prop where
    | mk (_ : bspwn.b < B.length)
         (_ : B[bspwn.b].Γ = bspwn.args.length)
         (_ : B[bspwn.b].σ.isExit)

  namespace WF
    notation (name := notationwf) B:arg " ⊢ " bspwn:arg " WF-spawn" => WF B bspwn
    
    instance {B: BlockSigs} (bspwn: SpawnBlock): Decidable (B ⊢ bspwn WF-spawn) :=
      decidable_of_iff (∃ _ :bspwn.b < B.length,
                        B[bspwn.b].Γ = bspwn.args.length ∧
                        B[bspwn.b].σ.isExit)
        ⟨λ ⟨a, b, c⟩ => .mk a b c, λ | .mk a b c => ⟨a, b, c⟩⟩

    theorem b {B bspwn}: B ⊢ bspwn WF-spawn -> bspwn.b < B.length
      | mk b _args _ex => b
    theorem args {B bspwn}: (wf : B ⊢ bspwn WF-spawn) -> (B[bspwn.b]'(b wf)).Γ = bspwn.args.length
      | mk _b args _ex => args
    theorem isExit {B bspwn}: (wf : B ⊢ bspwn WF-spawn) -> (B[bspwn.b]'(b wf)).σ.isExit
      | mk _b _args ex => ex
    abbrev getExit {B bspwn} (wf: B ⊢ bspwn WF-spawn): Nat :=
      (B[bspwn.b]'(b wf)).σ.getExit wf.isExit
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
    notation (name := notationwf) B:arg " ; " canProm:arg " ⊢ " ρ:arg " WF-deque" => WF B canProm ρ
  
    instance {B canProm} : (ρ : SpawnDeque) -> Decidable (B; canProm ⊢ ρ WF-deque)
      | .mk u p => decidable_of_iff
          (IVec (B ⊢ · WF-spawn) u ∧ SpawnOrder canProm p)
          ⟨λ ⟨a, b⟩ => ⟨a, b⟩, λ ⟨a, b⟩ => ⟨a, b⟩⟩
    
    theorem unpr {fsigs canProm} {ρ : SpawnDeque} : fsigs; canProm ⊢ ρ WF-deque -> IVec (fsigs ⊢ · WF-spawn) ρ.unpr | mk u _p => u
    theorem prom {fsigs canProm} {ρ : SpawnDeque} : fsigs; canProm ⊢ ρ WF-deque -> SpawnOrder canProm ρ.prom | mk _u p => p

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

  -- abbrev oblg : (ex: Nat) -> SpawnDeque -> Oblg
  --   | ex,
  -- inductive MatchesOblg (B : List BlockSig) : SpawnDeque -> Oblg -> Prop where
  --   | join_π (bspwn : SpawnBlock) (π : List SpawnBlock) (σ : Oblg) :
  --            MatchesOblg B ⟨[], π⟩ σ ->
  --            MatchesOblg B ⟨[], bspwn :: π⟩ (σ.join B[bspwn.b]!.σ.last)
  --   | spoin_π (bspwn : SpawnBlock) (π : List SpawnBlock) (σ : Oblg) :
  --             MatchesOblg B ⟨[], π⟩ σ ->
  --             MatchesOblg B ⟨[], bspwn :: π⟩ (σ.spoin B[bspwn.b]!.σ.last)
  --   | spoin_υ (bspwn : SpawnBlock) (υ π : List SpawnBlock) (σ : Oblg) :
  --             MatchesOblg B ⟨υ, π⟩ σ ->
  --             MatchesOblg B ⟨υ.concat bspwn, π⟩ (σ.spoin B[bspwn.b]!.σ.last)
  --   | retn (n : Nat) : MatchesOblg B ⟨[], []⟩ (.retn n)
  --   | exit (n : Nat) : MatchesOblg B ⟨[], []⟩ (.exit n)

  -- namespace MatchesOblg
  --   instance decide_matches_oblg {B: List BlockSig} :
  --                                (ρ : SpawnDeque) -> (σ : Oblg) ->
  --                                Decidable (MatchesOblg B ρ σ)
  --     | ⟨[], bspwn :: π⟩, .join σ n => sorry
  --     | ⟨[], bspwn :: π⟩, .spoin σ n => sorry
  --     | ⟨b_end :: υ, π⟩, .spoin σ n => sorry
  --     | ⟨[], []⟩, .retn n => isTrue sorry
  --     | ⟨[], []⟩, .exit n => isTrue sorry
  --     | ⟨_ :: _, _⟩, .retn n => isFalse sorry
  --     | ⟨_, _ :: _⟩, .retn n => isFalse sorry
  --     | ⟨_ :: _, _⟩, .exit n => isFalse sorry
  --     | ⟨_, _ :: _⟩, .exit n => isFalse sorry
  --     | ⟨_ :: _, _⟩, .join σ n => isFalse sorry
  --     | ⟨[], []⟩, .join σ n => isFalse sorry
  --     | ⟨[], []⟩, .spoin σ n => isFalse
  -- end MatchesOblg
end SpawnDeque

namespace StackFrame
  inductive WF (P : Program) (curr : Option Nat) (K : CallStack) (σ : Oblg) :
               StackFrame -> Prop where
    | mk {f ρ X c} :
         (_ : f < P.size) ->
         (σ : Oblg) ->
         ρ.sig P[f].B = σ.sig ->
         ρ.WF P[f].B K.allPromoted ->
         (if curr.isNone then c.isCode else c.isCont) = true ->
         c.WF P P[f].B ⟨X.length, σ⟩
                (curr.elim P[f].fsig.ret id) ->
         (mk f ρ X c).WF P curr K

  namespace WF
    instance {P curr K} : (k : StackFrame) -> Decidable (k.WF P curr K)
      | .mk f ρ X c =>
        decidable_of_iff (∃ _ : f < P.size,
                          
                          ρ.WF P[f].B K.allPromoted ∧
                          (if curr.isNone then c.isCode else c.isCont) = true ∧
                          c.WF P.fsigs P[f].B ⟨X.length, ρ.sig⟩
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
                k.c.WF P.fsigs (k.func kwf).B k.bsig
                         (curr.elim (k.func kwf).fsig.ret id)
      | .mk _f _ρ _X _c, mk _flt _ρwf _cb cwf => cwf
    theorem cwf' {P curr canProm} : {k : StackFrame} -> (kwf : k.WF P curr canProm) ->
                 k.c.WF P.fsigs P[k.f]!.B k.bsig
                          (curr.elim P[k.f]!.fsig.ret id)
      | .mk f _ρ _X _c, mk flt _ρwf _cb cwf =>
        getElem!_pos P f flt ▸ cwf
    theorem cwf'' {P curr canProm} : {k : StackFrame} -> (kwf : k.WF P curr canProm) ->
                  let flt : k.f < P.size := kwf.flt
                  k.c.WF P.fsigs P[k.f].B k.bsig
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
      let c' : Code.WF P.fsigs P[f].B P[f].fsig.ret
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
        (bnext_wf : bnext.WFRets P[f].B ⟨X.length, ρ.sig⟩ y.length)
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
                      P.fsigs P[f].B P[f].fsig.ret
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
        (bnext_wf : bnext.WF P[f].B ⟨X.length, ρ.sig⟩) :
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
end StackFrame


namespace CallStack
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

    theorem spawn {P f args ret} (Pwf : P.WF) (fwf : SpawnBlock.WF P.fsigs (.mk f args ret)) :
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
