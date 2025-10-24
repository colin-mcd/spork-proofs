inductive HeadIs {α β : Type} (l : List α) (m : α -> β) (b : β) : Prop where
  | mk (h : m <$> l.head? = some b)

namespace HeadIs
  abbrev head?eq {α β : Type} {l : List α} {m : α -> β} {b : β} : HeadIs l m b -> m <$> l.head? = some b
    | mk h => h

  theorem nonnil {α β : Type} {l : List α} {m : α -> β} {b : β} (h : HeadIs l m b) : l ≠ [] :=
    match (generalizing := true) l, h with
      | a :: as, mk p => by simp

  theorem nonnil_map {α β : Type} {l : List α} {m : α -> β} {b : β} (h : HeadIs l m b) : l.map m ≠ [] :=
    match (generalizing := true) l, h with
      | a :: as, mk p => by simp

  theorem headeq {α β : Type} {l : List α} {m : α -> β} {b : β} (h : HeadIs l m b) : m (l.head h.nonnil) = b :=
    match (generalizing := true) l, h with
      | _a :: _as, mk p => Option.some_inj.mp p

  theorem headeq_map {α β : Type} {l : List α} {m : α -> β} {b : β} (h : HeadIs l m b) : (l.map m).head h.nonnil_map = b :=
    match (generalizing := true) l, h with
      | _a :: _as, mk p => Option.some_inj.mp p

  theorem head!eq {α β : Type} [Inhabited α] {l : List α}
                  {m : α -> β} {b : β} (h : HeadIs l m b) :
                  l.head h.nonnil = l.head! := by
    cases l
    · case nil => nomatch h
    · case cons => rfl

  theorem zero_lt {α β : Type} : {l : List α} -> {m : α -> β} -> {b : β} -> (h : HeadIs l m b) -> 0 < l.length
    | _ :: _, _, _, _ => by simp

  theorem zero_lt_map {α β : Type} : {l : List α} -> {m : α -> β} -> {b : β} -> (h : HeadIs l m b) -> 0 < (l.map m).length
    | _ :: _, _, _, _ => by simp

  theorem get0eq {α β : Type} {l : List α} {m : α -> β} {b : β} (h : HeadIs l m b) : m (l[0]'h.zero_lt) = b :=
    List.head_eq_getElem h.nonnil ▸ headeq h

  theorem get0eq_map {α β : Type} {l : List α} {m : α -> β} {b : β} (h : HeadIs l m b) : (l.map m)[0]'h.zero_lt_map = b :=
    List.head_eq_getElem h.nonnil_map ▸ headeq_map h

  theorem headtail {α β : Type} {l : List α} {m : α -> β} {b : β} (h : HeadIs l m b) : l = l.head h.nonnil :: l.tail :=
    by cases l
       · case nil => nomatch h
       · case cons => rfl

  theorem map_head {α β : Type} {l : List α} {m : α -> β} {b : β} (h : HeadIs l m b) : (l.map m).head? = some b :=
    by cases l
       · case nil => nomatch h
       · case cons => exact h.head?eq

  theorem append {α β : Type} {l₁ l₂ : List α} {m : α -> β} {b : β} (h : HeadIs l₁ m b) : HeadIs (l₁ ++ l₂) m b :=
    by cases l₁
       · case nil => nomatch h
       · case cons => apply mk; simpa using h.headeq

  instance instDecidable {α β : Type} {m : α -> β} {b : β} [DecidableEq β] : {l : List α} -> Decidable (HeadIs l m b)
    | l => decidable_of_iff (m <$> l.head? = some b) ⟨mk, λ | mk h => h⟩
end HeadIs
