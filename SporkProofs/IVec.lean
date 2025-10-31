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

  def list_map {α α' : Type} {β : α -> Sort} : {l : List α} -> ((a : α) -> β a -> α') -> IVec β l -> List α'
    | [], _f, _n => []
    | a :: _as, f, v => f a (head' v) :: v.tail.list_map f

  theorem map_length {α α' : Type} {β : α -> Sort} : {l : List α} -> (f : (a : α) -> β a -> α') -> (v : IVec β l) -> (l.length = (v.list_map f).length)
    | [], _f, _n => rfl
    | a :: as, f, cons v vs => by simp; exact map_length f vs ▸ rfl

  theorem from_map {α α' : Type} {β : α -> Sort} {β' : α' -> Sort} : {l : List α} -> (f : (a : α) -> β a -> α') -> ((a : α) -> (b : β a) -> β' (f a b)) -> (v : IVec β l) -> IVec β' (list_map f v)
    | [], _f, _g, _v => nil
    | a :: _as, f, g, cons va vas =>
      cons (g a va) (vas.from_map f g)

  theorem from_map' {α α' : Type} {β : α -> Sort} {β' : α' -> Sort} : {l : List α} -> (f : α -> α') -> ((a : α) -> (b : β a) -> β' (f a)) -> (v : IVec β l) -> IVec β' (l.map f)
    | [], _f, _g, _v => nil
    | a :: _as, f, g, cons va vas =>
      cons (g a va) (vas.from_map' f g)

  theorem from_map_list {α α' : Type} {β : α' -> Sort} {f : α -> α'} (p : (a : α) -> β (f a)) : {l : List α} -> IVec β (l.map f)
    | [] => nil
    | a :: as => cons (p a) (from_map_list p (l := as))

  theorem from_mapIdx {α α' : Type} {β : α -> Sort} {β' : α' -> Sort} : {l : List α} -> (f : (i : Nat) -> α -> α') -> (g : (i : Nat) -> (ilt : i < l.length) -> (a : α) -> (a = l[i]) -> (b : β a) -> β' (f i a)) -> (v : IVec β l) -> IVec β' (l.mapIdx f)
    | [], _f, _g, _v => nil
    | a :: as, f, g, cons va vas =>
      List.mapIdx_cons ▸
      cons (g 0 as.length.zero_lt_succ a rfl va)
           (vas.from_mapIdx (λ i => f i.succ)
             (λ i ilt a aeq => g i.succ (by simp; exact ilt) a (by simp; exact aeq)))

  theorem from_mapIdx' {α α' : Type} {β : α -> Sort} {β' : α' -> Sort} : {l : List α} -> (f : α -> α') -> (g : (i : Nat) -> (ilt : i < l.length) -> (a : α) -> (a = l[i]) -> (b : β a) -> β' (f a)) -> (v : IVec β l) -> IVec β' (l.map f)
    | [], _f, _g, _v => nil
    | a :: as, f, g, cons va vas =>
      cons (g 0 as.length.zero_lt_succ a rfl va)
           (vas.from_mapIdx' f
             (λ i ilt a aeq => g i.succ (by simp; exact ilt) a (by simp; exact aeq)))
  
  theorem zip {α : Type} {β₁ : α -> Sort} {β₂ : α -> Sort} : {l : List α} -> IVec β₁ l -> IVec β₂ l -> IVec (λ a => β₁ a ∧ β₂ a) l
    | [], nil, nil => nil
    | _a :: _as, cons b₁ bs₁, cons b₂ bs₂ => cons ⟨b₁, b₂⟩ (zip bs₁ bs₂)
  
  theorem unzip {α : Type} {β₁ : α -> Sort} {β₂ : α -> Sort} : {l : List α} -> IVec (λ a => β₁ a ∧ β₂ a) l -> IVec β₁ l ∧ IVec β₂ l
    | [], nil => ⟨nil, nil⟩
    | _a :: _as, cons ⟨b₁, b₂⟩ bs₁₂ =>
      let ⟨bs₁, bs₂⟩ := unzip bs₁₂
      ⟨cons b₁ bs₁, cons b₂ bs₂⟩

  theorem map {α : Type} {β β' : α -> Sort} : {l : List α} -> ((a : α) -> β a -> β' a) -> IVec β l -> IVec β' l
    | [], _g, _v => nil
    | a :: _as, g, v => cons (g a v.head') (v.tail.map g)

  -- def mapVec {α α' : Type} {β : α -> Sort} {β : α' -> Sort} : {l : List α} -> (f :  -> IVec β l -> List α'
  --   | [], _f, _n => []
  --   | a :: _as, f, v => f a (head' v) :: v.tail.map f

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

  def concat {α β} : {l : List α} -> {a : α} -> IVec β l -> β a -> IVec β (l.concat a)
    | [], _a, nil, b => singleton b
    | _a :: _as, _a', cons b bs, b' => cons b (concat bs b')

  def unconcat {α : Type} {β : α -> Sort} :
               {l : List α} -> {a : α} -> IVec β (l.concat a) -> IVec β l ×' β a
    | [], _a', xs => ⟨nil, xs.head'⟩
    | _a :: _l, _l', v => let ⟨v1, v2⟩ := unconcat v.tail; ⟨cons v.head' v1, v2⟩

  def peephole {α : Type} {β : α -> Sort} :
               {l₁ : List α} -> {a a' : α} -> {l₂ : List α} ->
               (β a -> β a') -> IVec β (l₁ ++ [a] ++ l₂) -> IVec β (l₁ ++ [a'] ++ l₂)
    | [], _a, _a', _l₂, ba_ba', v =>
      cons (ba_ba' v.head') v.tail
    | _a₁ :: _l₁, _a, _a', _l₂, ba_ba', v =>
      cons v.head' (peephole ba_ba' v.tail)

  def get_peep {α : Type} {β : α -> Sort} :
               {l₁ : List α} -> (a : α) -> {l₂ : List α} ->
               IVec β (l₁ ++ [a] ++ l₂) -> β a
    | [], _a, _l₂, v => v.head'
    | _a₁ :: _l₁, a, _l₂, v => v.tail.get_peep a

end IVec
