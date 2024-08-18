-- inductive propositions exercises

namespace Hidden

/-
We reuse the list definition and append function from last exercise.
-/

inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil        => bs
  | cons a as' => cons a (append as' bs)

/- allows us to use `++` as an infix notation for `append` -/
instance (α : Type u) : Append (List α) where
  append := append

theorem nil_append (as : List α) : nil ++ as = as := by
  rfl

theorem cons_append (a : α) (as bs : List α)
        : (cons a as) ++ bs = cons a (as ++ bs) := by
  rfl

/-
Insert your proofs from last exercise.
-/

theorem append_nil (as : List α) : as ++ nil = as := by
  induction as with
  | nil        => rfl
  | cons a as' ih => rw [cons_append, ih]

theorem append_assoc (as bs cs : List α)
        : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil        => rfl
  | cons a as' ih => rw [cons_append, cons_append, cons_append, ih]

/-
We define the reverse function on a list.
-/

def reverse {α : Type u} (as : List α) : List α :=
  match as with
  | nil        => nil
  | cons a as' => reverse as' ++ cons a nil

/-
Prove that the reverse of a singleton set is itself.
-/
theorem singleton_reverse (a : α) : reverse (cons a nil) = cons a nil := by
  rfl

/-
Prove this interaction between `reverse` and `append`.
-/
theorem reverse_append {α : Type u} (as bs : List α)
    : reverse (as ++ bs) = reverse bs ++ reverse as := by
  induction as with
  | nil =>
      rw [nil_append, reverse, append_nil]
  | cons a as' ih =>
      rw [cons_append, reverse, reverse, ih, append_assoc]

/-
A _palindrome_ is a sequence that reads the same backwards as forwards.

An inductive proposition that captures what it means to be a palindrome may be defined as follows.
-/

inductive Palindrome {α : Type} : List α → Prop where
  | nil : Palindrome nil
  | single (x : α) : Palindrome (cons x nil)
  | sandwich (x : α) (xs : List α)
      : Palindrome xs → Palindrome (cons x xs ++ cons x nil)

namespace Palindrome

/-
Prove that a list appended to its reverse is always a palindrome.
-/
theorem Palindrome_app_rev {α : Type} (l : List α) : Palindrome (l ++ reverse l) := by
  induction l with
  | nil => rw [nil_append, reverse]; exact nil
  | cons x xs ih =>
    rw [cons_append, reverse, ←append_assoc, ←cons_append]
    apply sandwich x
    exact ih
/-
Prove that if a list is a palindrome, then its reverse is equal to itself.
Hint: you might need to use `rw (config := {occs := .pos [2]}) [???]`
-/

theorem Palindrome_rev {α : Type} (l : List α)
    : Palindrome l → l = reverse l := by
  intro lPal
  induction lPal with
  | nil => rfl
  | single x => rfl
  | sandwich x xs xsPal xsRev =>
    rw [reverse_append, reverse, reverse, nil_append, reverse, ←xsRev]
    rw [cons_append, ←append_assoc, cons_append, nil_append, cons_append]

end Palindrome
end List
end Hidden
