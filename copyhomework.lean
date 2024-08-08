Supasan Ruangchutipopan
-- Hoare logic 2 exercises

import Frap.Hoare2

namespace Imp
namespace Hoare
open AExp
open BExp
open Com
open CEval
open DCom
open Decorated
attribute [local simp]
  aeval beval aequiv bequiv cequiv update x y z

/-
exercise (2-star)
Prove the theorem below using hoare_if.
-/

theorem if_minus_plus :
    -- { True }
    {* fun _ => True *}
      <{if x <= y then z := y - x else y := x + z end}>
    -- { y = x + z }
    {* fun st => st y = st x + st z *} := by
    apply hoare_if
    . apply hoare_consequence_pre
      . apply hoare_asgn
      . simp
        intro st h
        simp [h]
    . apply hoare_consequence_pre
      . apply hoare_asgn
      . intros st _
        simp [*]


/-
exercise (2-star)
Fill in valid decorations for the following program:

  { True }
    if x <= y then
                    (1) { True ∧ x ≤ y } ->>
                    (2) {  y = x + (y - x) }
      z := y - x
                    (3) { y = x + z }
    else
                    (4) { True ∧ ¬(x ≤ y) } ->>
                    (5)  {(x + z) = x + z}
      y := x + z
                    (6) { y = x + z }
    end
  { y = x + z }

Briefly justify each use of ->>.

* We start with the outer precondition { True } and postcondition { y = x + z }.
* Following the format dictated by the hoare_if rule, we copy the postcondition { y = x + z } to (3) and (6).
    We conjoin the precondition { True } with the guard of the conditional to obtain (1).
    We conjoin { True } with the negated guard of the conditional to obtain (4).
* In order to use the assignment rule and obtain (2),
  we substitute z by y - x in (3).
  * (1) { True ∧ x ≤ y } ->> (2) {  y = x + (y - x) } *
  To obtain (5) we substitute y by x + z in (6).
  * (4) { True ∧ ¬(x ≤ y) } ->> (5)  {(x + z) = x + z} *
* Finally, we verify that (1) implies (2) and (4) implies (5).
  Both of these implications crucially depend on the ordering of x and y obtained from the guard.
  For instance, knowing that x ≤ y ensures that subtracting x from y and then adding front x produces y, as required by the first disjunct of (2).
  For instance, knowing that natural numbers is reflexive in adding front x from z natural numbers, as required by the second disjunct of (5).
-/

/-
exercise (2-star)
Here is a skeleton of the formal decorated version of the if_minus_plus program above.
Replace all occurrences of FILL IN HERE with appropriate assertions and fill in the proof (which should be just as straightforward as in the examples from lecture).
-/
def if_minus_plus_dec : Decorated := decorated
  (fun _ => True) $
    dc_if <{x <= y}>
      (fun st => True ∧ st x ≤ st y )
      (dc_pre (fun st => st y = st x + (st y - st x) ) $
    dc_asgn z <{y - x}>
      (fun st => st y = st x + st z))

      (fun st => True ∧ ¬(st x ≤ st y))
      (dc_pre (fun st => (st x + st z) =st  x + st z) $
    dc_asgn y <{x + z}>
      (fun st => st y = st x + st z))
  (fun st => st y = st x + st z)

theorem if_minus_plus_correct : outer_triple_valid if_minus_plus_dec := by
  verify
