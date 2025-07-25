-- induction exercises

namespace Hidden

/-
A list of elements of type `α` is either the empty list, `nil`, or an element `h : α` followed by a list `t : List α`. The first element, `h`, is commonly known as the "head" of the list, and the remainder, `t`, is known as the "tail."
-/

inductive List (α : Type u) where
| nil  : List α
| cons : α → List α → List α

namespace List

/-
We can define the append operation recursively on the first argument (as opposed to addition for natural numbers, which is recursive on the second argument).
-/
def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as := by
  rfl

theorem cons_append (a : α) (as bs : List α)
        : append (cons a as) bs = cons a (append as bs) := by
  rfl

/-
Prove that appending nil to any list results in that list.
-/
theorem append_nil (as : List α) : append as nil = as := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [cons_append, ih]

/-
Prove that list append is associative.
-/
theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [cons_append, cons_append, cons_append, ih]

/-
Define a function that returns the length of a list.
-/
def length {α : Type u} (as : List α) : Nat :=
  match as with
  | nil => 0
  | cons _ as => 1 + length as

/-
With your definition, prove that it interacts with `append` as expected.
You may use facts from the `Nat` namespace.
-/

#check Nat

theorem length_append (as bs : List α)
        : length (append as bs) = length as + length bs := by
  induction as with
  | nil => rw [nil_append, length, Nat.zero_add]
  | cons a as ih =>
        rw [cons_append, length, length, ih]
        rw [Nat.add_assoc]

end List
end Hidden
