/-
You may import additional lecture and exercise files here as necessary.
-/

import Frap.Hoare2
import Frap.Imp
import Frap.Equiv
import Aesop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
-- import Mathlib.Algebra.Ring.Basic
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Algebra.GroupPower.Basic

/- [add more here] -/


example : α → α := by
  aesop

-- example (x y : ℝ) : x^3-y^3=(x-y)*(x^2+x*y+y^2) := by
--   ring

/-
# 261497-frap 1/2567 final exam

## Identifying information

* Name: [**Raiwin Inthasit**]
* Student ID: [**640610665**]

### Survey questions

* หากประเมินจากระดับความพยายามของตนเองในภาคเรียนที่ผ่านมา จะให้เกรดอะไรแก่ตนเองในวิชานี้ (pick one and delete the rest)
 * B


* หากประเมินจากความเป็นจริงเท่าที่มีอยู่ คาดว่าตนเองจะได้เกรดอะไรในวิชานี้ (pick one and delete the rest)
 * B

## Instructions

You have 72 hours to complete this exam.

You may use any results, proven or unproven, from lectures and exercises.
Simply import relevant files at the top of this file.

Collaboration with classmates is not permitted for this exam.

If you consult any external resources, you must declare them here.
* For websites, include URLs.
* For generative AI, such as ChatGPT, include all prompts and timestamps (when you send the prompts).
* For humans, include their names and summarize your exchange.
* For other resources, declare them as appropriate.

If you are not sure how to declare a particular resource, ask on Ed as a private thread.
If you are not sure whether a certain resource may be used, ask on Ed as a private thread before using it.

### Declaration of external resource use

[**
  Tactics in Lean4, https://github.com/madvorak/lean4-tactics, accessed at 2024-10-25, 4:24 AMm
  Propositions and Proofs, https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html, accessed at 2024-10-25, 11:27 PM

**]
-/

-- namespace Imp
-- open AExp
-- open BExp

-- attribute [local simp]
--   aeval beval aequiv bequiv cequiv update x y z

/-
## Problems

1. Exploration of classical logic

Here's a familiar law from classical logic: the law of excluded middle.
-/

def excluded_middle := ∀ (p : Prop), p ∨ ¬ p

/-
(a) Although we cannot prove this law in constructive logic, it is possible to double negate it and prove the resulting proposition.
Prove the following theorem.
-/

theorem excluded_middle_dbl_neg p : ¬¬(p ∨ ¬ p) := by
  intro contra
  apply contra
  right
  intro h
  apply contra
  left
  exact h

/-
It turns out that we can use other laws to characterize classical logic.
That is, we can replace excluded middle with any of these laws.
-/

def dbl_neg_elim := ∀ (p : Prop), ¬¬p → p
def implies_to_or := ∀ (p q : Prop), (p → q) → (¬p ∨ q)

/-
(b) Prove that these laws are equivalent to the law of excluded middle by proving this circular chain of three implications.
-/

theorem excluded_middle__dbl_neg_elim : excluded_middle → dbl_neg_elim := by
  unfold excluded_middle dbl_neg_elim
  intros hExcl p dbl_neg
  cases hExcl p with
  | inl hp => exact hp
  | inr hnp => contradiction

#check False
#check True

theorem dbl_neg_elim__implies_to_or : dbl_neg_elim → implies_to_or := by
  unfold dbl_neg_elim implies_to_or
  intros hDblNeg p q h
  apply hDblNeg
  intro hnp
  apply hnp
  left
  intro hp
  apply hnp
  right
  apply h
  exact hp

theorem implies_to_or__excluded_middle : implies_to_or → excluded_middle := by
  unfold implies_to_or excluded_middle
  intros hImpl p
  cases hImpl p p (fun hp => hp) with
  | inl hnp => right; exact hnp
  | inr hp => left; exact hp

/-
2. Exponentiation on natural numbers

In class, we defined natural numbers inductively.
We also defined addition and multiplications on natural numbers as follows.
-/

namespace LocalNat

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

open Nat

def add (m n : Nat) : Nat :=
  match n with
  | zero    => m -- m + 0 = m
  | succ n' => succ (add m n') -- m + n = m + (n - 1) + 1

def mul (m n : Nat) : Nat :=
  match n with
  | zero    => zero -- m * 0 = 0
  | succ n' => add (mul m n') m -- m + (n - 1)(m)

/-
We then proved these properties (no need to reprove them here):
-/

axiom zero_add (n : Nat) : add zero n = n
axiom succ_add (m n : Nat) : succ (add m n) = add (succ m) n
axiom add_assoc (m n k : Nat) : add (add m n) k = add m (add n k)
axiom add_comm (m n : Nat) : add m n = add n m
axiom mul_assoc (m n k : Nat) : mul (mul m n) k = mul m (mul n k)
axiom mul_comm (m n : Nat) : mul m n = mul n m

/-
(a) Prove these additional properties on multiplication.
-/

theorem zero_mul (n : Nat) : mul zero n = zero := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp [mul, ih]
    apply zero_add

theorem one_mul (n : Nat) : mul (succ zero) n = n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp [mul, ih]
    apply succ_add

/-
We can then define exponentiation using multiplication.
-/

def exp (a n : Nat) : Nat :=
  /- here, `a` is base and `n` is exponent -/
  match n with
  | zero => succ zero -- a^0 = 1
  | succ n' => mul (exp a n') a -- a^(n) = a^(n-1) * a

/-
(b) Prove the following properties on exponentiation.
-/

theorem exp_mul__add_exponent (a m n : Nat)
    : exp a (add m n) = mul (exp a m) (exp a n) := by -- a^(m + n) = a^(m) * a^(n)
  induction n with
  | zero => simp [exp, mul, zero_add]; rfl
  | succ n ih => simp [exp, ih]; apply mul_assoc

theorem mul_exp__exp_mul (a b n : Nat)
    : exp (mul a b) n = mul (exp a n) (exp b n) := by --  (a * b)^(n) = a^(n) * b^(n)
  /- hint: use `congr i`, where `i` is the recursion depth -/
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [exp, ih]
    rw [mul_assoc, mul_assoc]
    congr 1
    rw [mul_comm, mul_assoc, mul_comm (exp b n)]

theorem exp_exp__mul_exponent (a m n : Nat)
    : exp (exp a m) n = exp a (mul m n) := by -- (a^(m))^(n) = a^(m * n)
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [exp, ih, mul]
    rw [exp_mul__add_exponent]

end LocalNat

/-
3. Program equivalence
-/

namespace Imp

open CEval
attribute [local simp]
  aeval cequiv update x y lookup_update_neq lookup_update_eq

/-
(a) Prove the following properties about state updates.
-/

theorem update_overwrite x e₁ e₂ st
    : (x !-> e₂; x !-> e₁; st) = (x !-> e₂; st) := by
  unfold update
  funext x'
  sorry

theorem update_swap x y e₁ e₂ st : x ≠ y
    → (y !-> e₂; x !-> e₁; st) = (x !-> e₁; y !-> e₂; st) := by
  intro hxy
  unfold update
  funext z
  by_cases hx : z = x
  case pos =>
    sorry
  case neg => sorry

/-
(b) Show that these two programs are not equivalent.
-/

example : ¬ cequiv
    <{
      x := x + y;
      y := x + y
    }>
    <{
      y := x + y;
      x := x + y
    }>
    := by
  /- hint: use determinism of evaluation -/


  sorry


/-
(c) Let `x₁`, `x₂` be program variables, and `e₁`, `e₂` be expressions.
State a condition when these two programs are equivalent, and briefly justify your claim.
Your condition should be as weak as possible, i.e., covers as many cases as possible.

  ```
    x₁ := e₁;
    x₂ := e₂
  ```
  vs
  ```
    x₂ := e₂;
    x₁ := e₁
  ```

Answer:
[**fill in here**]
-/

/-
4. Hoare logic

Consider the following program:
```
  z := 0;
  x := n;
  while x != 0 do
    y := x;
    while y != 0 do
      z := z + 1;
      y := y - 1
    end
    x := x - 1
  end
```

(a) Explain what this program does without going into the details of the program.

Answer:
[**The program will gradually increase the value `z` using the value from `x` while reducing the value of `x` to zero if not already zero at first**]
-/

/-
(b) Fill in valid decorations for the following program.
(If you need to add more consequence rules or remove some, feel free to do so.)

```
  { True } ->>
  { **FILL IN HERE** }
    z := 0;
                    { **FILL IN HERE** }
    x := n;
                    { **FILL IN HERE** }
    while x != 0 do
                    { **FILL IN HERE** } ->>
                    { **FILL IN HERE** }
      y := x;
                    { **FILL IN HERE** }
      while y != 0 do
                    { **FILL IN HERE** } ->>
                    { **FILL IN HERE** }
        z := z + 1;
                    { **FILL IN HERE** }
        y := y - 1
                    { **FILL IN HERE** }
      end
                    { **FILL IN HERE** } ->>
                    { **FILL IN HERE** }
      x := x - 1
                    { **FILL IN HERE** }
    end
  { **FILL IN HERE** } ->>
  { **FILL IN HERE** }
```
-/

/-
(c) Here is a skeleton of the formal decorated version of the program above.
Replace all occurrences of `FILL IN HERE` with appropriate assertions and fill in the proof (which should leave with simple arithmetic justifications).

If you modified your decorated program in part (b), be sure to propagate the changes here accordingly.
-/

namespace Hoare

abbrev n := "n"
attribute [local simp] beval z n

open DCom
open Decorated

def prog : Decorated := decorated
  (fun st => True) $
    dc_pre (fun st => /-**FILL IN HERE**-/ True) $
    dc_seq (dc_asgn z <{0}>
      (fun st => /-**FILL IN HERE**-/ True)) $
    dc_seq (dc_asgn x <{n}>
      (fun st => /-**FILL IN HERE**-/ True)) $
    dc_post (dc_while <{x != 0}>
        (fun st => /-**FILL IN HERE**-/ True) (
      dc_pre (fun st => /-**FILL IN HERE**-/ True) $
      dc_seq (dc_asgn y <{x}>
        (fun st => /-**FILL IN HERE**-/ True)) $
      dc_seq (dc_while <{y != 0}>
          (fun st => /-**FILL IN HERE**-/ True) (
        dc_pre (fun st => /-**FILL IN HERE**-/ True) $
        dc_seq (dc_asgn z <{z + 1}>
          (fun st => /-**FILL IN HERE**-/ True)) $
        dc_asgn y <{y - 1}>
          (fun st => /-**FILL IN HERE**-/ True)
      ) (fun st => /-**FILL IN HERE**-/ True)) $
      dc_asgn x <{x - 1}>
        (fun st => /-**FILL IN HERE**-/ True)
    ) (fun st => /-**FILL IN HERE**-/ True))
  (fun st => /-**FILL IN HERE**-/ True)

attribute [local simp]
  prog

/-
You may use the following axioms within your proof.
If your proof requires other facts of similar nature, feel free to include them, but indicate clearly.
-/

axiom add_cumul n : n ≠ 0 → n * (n + 1) / 2 = (n - 1) * n / 2 + n
axiom neg_dist e n : n ≠ 0 → e - n + 1 = e - (n - 1)
axiom dec_inc n : n ≠ 0 → n - 1 + 1 = n

/- [fill in additional axioms here as needed] -/

theorem prog_correct : outer_triple_valid prog := by
  verify

/-
(d) [Extra credits]
Prove the aforementioned axioms.
-/

theorem add_cumul' n : n ≠ 0 → n * (n + 1) / 2 = (n - 1) * n / 2 + n := by
  intro h
  induction n with
  | zero => contradiction -- n ≠ 0
  | succ n' ih =>
    induction n' with
    | zero => aesop -- base case n = 1
    | succ n'' ih' => -- inductive case
      ring_nf
      simp [*] at *

      -- -- rw [<-ih]
      -- ring_nf
      -- have heq : 3 + n'' * 2 + (n'' + n'' ^ 2) / 2 = (6 + n'' * 5 + n'' ^ 2) / 2 := by
      --   ring_nf
      --   sorry
      -- rw [heq]
      sorry

theorem neg_dist' e n : n ≠ 0 -> e - n + 1 = e - (n - 1) := by
  intro h
  induction n with
  | zero => contradiction
  | succ n' ih =>
    simp [ih]
    sorry

#check Nat

theorem dec_inc' n : n ≠ 0 → n - 1 + 1 = n := by
  intro h_neg0

  sorry

end Hoare
end Imp

/-
Thank you for choosing this course.
-/
