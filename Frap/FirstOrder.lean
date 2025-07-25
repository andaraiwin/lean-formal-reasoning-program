/-
## Sectioning

Sometimes, it is helpful to limit names to a local scope.
Use `section` ... `end` to indicate a scope.

Optionally, we can give a name to section, in which case the name must follow both `section` and `end`.
-/
section

/-
## Variables

In each proposition we have proven, we often introduce propositional variables like `p` and `q`.
Although we could write them down in each individual proposition, we can declare "global" variables for the entire file, using the `variable` command.
-/

variable (p q r : Prop)

/-
## Anonymous constructors

In a proof having a conjunction in the hypothesis, we had to use the `cases` command to break it down into conjuncts.
This can be tedious.
-/
example : p ∧ q → q ∧ p := by
  intro hand
  cases hand with
  | intro hp hq =>
      apply And.intro
      . exact hq
      . exact hp
/-
For elements that can be constructed in one way, e.g., conjunctions, we can instead use the _anonymous constructor_ notation `⟨arg1, arg2, ...⟩` to break down the elements into its constituents.
These angle brackets can be typed using `\<` and `\>` shortcuts.

Now, we can deconstruct a conjunction at the time of the introduction.
-/
example : p ∧ q → q ∧ p := by
  intro ⟨hp, hq⟩
  apply And.intro
  . exact hq
  . exact hp
/-
In certain scenarios, we might not be able to deconstruct a conjunction at the time of its introduction.
We can use the `obtain` tactic to break down a conjunction appearing in a hypothesis later on.
-/
example : p ∧ q → q ∧ p := by
  intro h
  obtain ⟨hp, hq⟩ := h
  apply And.intro
  . exact hq
  . exact hp

end

/-
## Disjunction tactics, redux

Previously, when we prove a disjunction, we apply the `Or.inl` or `Or.inr` rule.
We can also use the `left` or `right` tactic.
-/

example (p q : Prop) : p → p ∨ q := by
  intro hp
  left
  exact hp

example (p q : Prop) : q → p ∨ q := by
  intro hp
  right
  exact hp

section quantifiers

/-
## Predicates

So far, all of our propositions are not parameterized: each proposition can be immediately interpreted as true or false.
To make them more versatile, we can parameterize propositions into _predicates_, whose truth values depends on the value of their parameters.
A predicate expecting one parameter is called a _unary predicate_.
A predicate expecting two parameters is callled a _binary predicate_.

For a unary predicate named `p`, if the type of its parameter is `α`, then `p` is a function of type `α → Prop`, so that if `x : α`, then `p x : Prop`.
Note that we are more familiar with the notation `p(x)`, but Lean doesn't require us to write down parentheses in this context.

The notation `x : α` might be more familiar if seen as `x ∈ α`.
This also applies to when we write `p : Prop`.

Likewise, for a binary predicate named `p`, if the type of its first parameter is `α` and the type of its second parameter is `β`, then `p` is a function of type `α → β → Prop`, so that if `x : α` and `y : β`, then `p x y : Prop`.
Note that we are more familiar with the notation `p(x, y)`, but Lean doesn't require us to write down parentheses or commas in this context.

We can use binary predicates to represent a relation between `α` and `β`.
If `α = β`, then we have a _relation on `α`_.

## Universal quantifier

The universal quantifier (∀) can be typed using `\forall` shortcut.

A universally quantified statement `∀ x : α, p x` is true when, for every `x : α`, `p x` holds.

To prove that a universally quantified statement holds, we use the ∀-introduction rule, which states that, given a proof of `p x` in a context where `x : α` is arbitrary, we obtain a proof of `∀ x : α, p x`.
This can be seen as a _generalization_ of predicate `p`.
We can use the `intro` tactic to introduce the universally quantified variable into the hypothesis.

To use a universally quantified statement in the hypothesis, we use the ∀-elimination rule, which states that, given a proof of `∀ x : α, p x` and any term `t : α`, we obtain a proof of `p t`.
This can be seen as a _specialization_ of predicate `p` on a given term of type `α`.
We can use the `apply` tactic for a specialization, or the `specialize` tactic, along with the name of the assumption and the variable name to specialize on.
-/

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y := by
  intro h
  intro y
  apply And.left
  apply h

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y := by
  intro h
  intro y
  specialize h y
  apply And.left
  exact h

section relations
/-
In this subsection, we demonstrate the use of universal quantifiers in the hypothesis.
-/

variable (α : Type) (r : α → α → Prop)

/-
Here, we assume that the relation `r` is reflexive, symmetric, and transitive.
This is done by declaring variables that represent proofs of these properties.
-/
variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) : r a b → r c b → r c d → r a d  := by
  intro hab hcb hcd
  apply trans_r
  . exact hab
  . apply trans_r
    . apply symm_r
      exact hcb
    . exact hcd
end relations

variable (α : Type) (p q : α → Prop) (r : Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor  -- can be used in place of `apply Iff.intro`
  . intro h
    constructor  -- can be used in place of `apply And.intro`
    . intro x
      apply And.left
      apply h
    . intro x
      apply And.right
      apply h
  . intro ⟨hp, hq⟩
    intro x
    constructor
    . apply hp
    . apply hq

/-
exercise (1-star)
-/
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  sorry

/-
exercise (1-star)
-/
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  sorry

/-
It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable.
-/

/-
exercise (1-star)
-/
example : (∀ x, p x) ∨ r → (∀ x, p x ∨ r)  := by
  sorry

/-
exercise (1-star)
-/
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  sorry

/-
## Existential quantifier

The existential quantifier (∃) can be typed using `\exists` shortcut.

An existentially quantified statement `∃ x : α, p x` is true when there is an `x : α` (an element `x` of type `α`) such that `p x` holds.

To prove that an existentially quantified statement holds, we use the ∃-introduction rule, which states that, if there is a term `t : α` for which we can prove that `p t` holds, then we have a proof of `∃ x : α, p x` by forgetting the details about the evidence `t`.
This can be seen as an _information hiding_ operation.
We can apply the `Exists.intro` rule to break down an existential statement into two subgoals: one for providing the evidence, the other for providing the proof that the evidence works.
These subgoals are resolved in reversed order because Lean 4 works backwards on the premises of the rule.
-/

#check Exists.intro

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  apply Exists.intro
  . exact hr
  . exact a

/-
Alternatively, we can use the `exists` tactic to provide the evidence immediately.
Any unresolved subgoals will remain.
-/

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  exists a

/-
To use an existentially quantified statement in the hypothesis, we use the ∃-elimination rule, which does the opposite of the ∃-introduction rule.
It states that since we know `∃ x : α, p x`, there is an `x` satisfying `p x`, so we can give it a name, e.g., `w`.
This can be seen as an _instantiation_ of predicate `p` on such a `w` that makes `p w` true.
We can apply the `Exists.elim` rule to the existential statement in the hypothesis.
-/

#check Exists.elim

example : (∃ x : α, r) → r := by
  intro h
  apply Exists.elim h
  intro x hr
  exact hr

/-
An existential proof has two parts: evidence and proof that the evidence works.
This is similar to the proof of a conjunction: the proof of left and right conjuncts.
We can use the anonymous constructor notation to break down an existential proof.
-/

example : (∃ x : α, r) → r := by
  intro ⟨x, hr⟩
  exact hr

/-
In the proof above, we happened not to use the instantiated variable.
That's why Lean 4 issues a warning `unused variable`.
We can replace such occurrences with `_`.
-/

example : (∃ x : α, r) → r := by
  intro ⟨_, hr⟩
  exact hr

/-
Let's try some more proofs having ∃ in both the goal and hypothesis.
-/

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨x, ⟨hp ,hq⟩⟩
  exists x

/-
In the proof above, the `exists` tactic automatically takes care of the rest of the proof.
Without such tactic, the proof would look like follows.
-/

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨x, ⟨hp, hq⟩⟩
  apply Exists.intro
  apply And.intro
  . exact hq
  . exact hp

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  . intro ⟨x, ⟨hpx, hr⟩⟩
    constructor
    . exists x
    . exact hr
  . intro ⟨⟨x, hp⟩, hr⟩
    exists x

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  . intro ⟨x, h⟩
    cases h with
    | inl hp => left; exists x
    | inr hq => right; exists x
  . intro h
    cases h with
    | inl hp => obtain ⟨x, hp'⟩ := hp; exists x; left; assumption
    | inr hq => obtain ⟨x, hq'⟩ := hq; exists x; right; assumption

/-
exercise (1-star)
Prove that a postcondition within a universal statement not mentioning the universal variable can be pulled out of the universal, as long as there is an element satisfying the predicate.
Conversely, if a predicate is satisfiable, a postcondition can be moved as a consequent of the predicate on any element of the domain.
-/
example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor
  . intro h
    intro ⟨x, hp⟩
    apply h
    exact hp
  . intro h
    intro x
    intro hp
    apply h
    exists x

/-
exercise (1-star)
Prove that a postcondition within an existential statement not mentioning the existential variable can be pulled out of the existential, assuming that every element satisfies the predicate.
-/
example : (∃ x, p x → r) → (∀ x, p x) → r := by
  intro h
  obtain ⟨x, hr⟩ := h
  intro h
  apply hr
  apply h

/-
exercise (1-star)
Proe that a precondition within an existential statement not mentioning the existential variable can be pulled out of the existential.
-/
example : (∃ x, r → p x) → (r → ∃ x, p x) := by

  sorry

end quantifiers

section equality
/-
## Equality

Equality is one of the most fundamental notions in formal reasoning.
It states when two things are equal, and hence we can _substitute_ one for the other.
Equality allows us to perform _equational reasoning_.
-/

#check Eq

/-
Equality is an equivalence relation, i.e., it is reflexive, symmetric, and transitive.
We can apply these rules within a proof.
-/

#check Eq.refl
#check Eq.symm
#check Eq.trans

/-
We can specialize the example from an earlier section to the equality relation:
-/
variable (α : Type) (a b c d : α)  -- a, b, c, d are elements of some type

example : a = b → c = b → c = d → a = d  := by
  intro hab hcb hcd
  apply Eq.trans
  . exact hab
  . apply Eq.trans
    . apply Eq.symm
      exact hcb
    . exact hcd

/-
The power of equality lies in substitution.
We can apply the `Eq.subst` rule
-/

#check Eq.subst

example (α : Type) (a b : α) (p : α → Prop) : a = b → p a → p b := by
  intro heq hpa
  apply Eq.subst
  . exact heq
  . exact hpa

/-
For many rules we have seen, including `Eq.subst`, we can view them as a method in the objec-oriented-programming sense.
The first argument to the method is in fact the receiver object, and we can name it before the method name.
This automatically takes care of the first subgoal (which appears last in the proof).
-/

example (α : Type) (a b : α) (p : α → Prop) : a = b → p a → p b := by
  intro heq hpa
  apply heq.subst
  exact hpa

/-
exercise (1-star)
Prove the following substitution property.
-/
example (α β : Type) (a b : α) (f g : α → β) : a = b → f = g → f a = g b := by
  intro h₁ h₂
  apply h₁.subst
  apply h₂.subst
  rfl

end equality

/-
We will look at more basic types and what we can do with them next time.
-/

/-
## references
- [Theorem Proving in Lean 4: Quantifiers and Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html)
-/
