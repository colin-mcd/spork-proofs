inductive IVec {α : Type} (β : α -> Sort) : List α -> Sort where
  | nil : IVec β []
  | cons : {h : α} -> {t : List α} -> β h -> IVec β t -> IVec β (h :: t)

namespace IVec
  /--
    get the jth index in an ivec
  -/
  def get {α : Type} {β : α -> Sort} {l : List α} : IVec β l -> (j : Fin l.length) -> β l[j]
    | cons h' _, ⟨0, _⟩ => h'
    | cons _ t', ⟨Nat.succ j, pj⟩ => get t' ⟨j, Nat.lt_of_succ_lt_succ pj⟩

  @[inherit_doc get]
  syntax:max term noWs "⁅" withoutPosition(term) "⁆" : term
  macro_rules | `($x⁅$i⁆) => `(($x).get (Fin.mk $i (by get_elem_tactic)))

  def head {α : Type} {β : α -> Sort} {l : List α} :
           (v : IVec β l) -> (p : l ≠ []) -> β (l.head p)
    | cons h _t, _p => h

  def head' {α : Type} {β : α -> Sort} {a : α} {l : List α} :
           (v : IVec β (a :: l)) -> β a
    | cons h _t => h

  def tail {α : Type} {β : α -> Sort} {l : List α} :
           IVec β l -> IVec β l.tail
    | nil => nil
    | cons _h t => t

  def map {α α' : Type} {β : α -> Sort} : {l : List α} -> ((a : α) -> β a -> α') -> IVec β l -> List α'
    | [], _f, _n => []
    | a :: _as, f, v => f a (head' v) :: v.tail.map f

  theorem map_length {α α' : Type} {β : α -> Sort} : {l : List α} -> (f : (a : α) -> β a -> α') -> (v : IVec β l) -> (l.length = (v.map f).length)
    | [], _f, _n => rfl
    | a :: as, f, cons v vs => by simp; exact map_length f vs ▸ rfl

  instance instDecidable {α : Type} {β : α -> Prop} [DecidablePred β] : {l : List α} -> Decidable (IVec β l)
    | [] => isTrue nil
    | a :: as =>
      let _ : Decidable (IVec β as) := instDecidable
      dite (β a)
        (decidable_of_iff (IVec β as) ⟨cons ·, tail⟩)
        (isFalse ∘ λ f (.cons h _t) => f h)

  def append {α β} : {l l' : List α} -> IVec β l -> IVec β l' -> IVec β (l ++ l')
    | [], _bs, nil, ws => ws
    | _a :: _as, _bs, cons v vs, ws => cons v (append vs ws)

  def unappend {α : Type} {β : α -> Sort} :
           {l l' : List α} -> IVec β (l ++ l') -> IVec β l ×' IVec β l'
    | [], _l', xs => ⟨nil, xs⟩
    | _a :: _l, _l', v => let ⟨v1, v2⟩ := unappend v.tail; ⟨cons v.head' v1, v2⟩

  def singleton {α β} {a : α} (b : β a) : IVec β [a] := nil.cons b
end IVec
