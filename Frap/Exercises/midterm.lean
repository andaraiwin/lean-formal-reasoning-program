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
{True}
Program:
    if x ≤ 0
      then y := x + 1
      else y := x - 1
    end
{y ≠ x}.
-/

theorem if_add_simple :
    -- { True }
    {* fun _ => True *}
      <{if x <= 0 then y := x + 1 else y := x - 1 end}>
    -- { y ≠ x }
    {* fun st => st y ≠ st x *} := by
  apply hoare_if
  . apply hoare_consequence_pre
    . apply hoare_asgn
    . simp
      intro st h
      omega
  . apply hoare_consequence_pre
    . apply hoare_asgn
    . simp
      intro st h
      omega

/-
Fill in valid decorations for the following program:

```
  { True }
    if x ≤ 0 then
                    { True ∧ x ≤ 0 } ->>
                    { x + 1 ≠ x }
      y := x + 1
                    { y ≠ x }
    else
                    { True ∧ ¬(x ≤ 0) } ->>
                    { x - 1 ≠ x}
      y := x - 1
                    { y ≠ x}
    end
  { y ≠ x }
```
-/

def if_add_simple_dec : Decorated := decorated
  (fun _ => True) $
    dc_if <{x <= 0}>
      (fun st => True ∧ (st x ≤ 0))
      (dc_pre (fun st => st x + 1 ≠ st x) $

    dc_asgn y <{x + 1}>
      (fun st => st y ≠ st x))

      (fun st => True ∧ ¬(st x ≤ 0))
      (dc_pre (fun st => st x - 1 ≠ st x) $

    dc_asgn y <{x - 1}>
      (fun st => st y ≠ st x))
  (fun st => st y ≠ st x)

theorem if_add_simple_correct : outer_triple_valid if_add_simple_dec := by
verify

end Hoare
end Imp
