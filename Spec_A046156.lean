import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- OEIS A046156 verbatim : "Limit set for operation of
    repeatedly replacing a number with the sum of the cubes of
    its digits". Data : 0, 1, 55, 133, 136, 153, 160, 217, 244,
    250, 352, 370, 371, 407, 919, 1459. fini,full. Enonce : les
    points periodiques sont exactement ces 16 elements. -/
abbrev SpecPropA046156 : Prop :=
  ∀ m : ℕ,
    ((∃ k : ℕ, 0 < k ∧
       (Nat.iterate (fun x => ((Nat.digits 10 x).map (· ^ 3)).sum)
         k m) = m) ↔
     m ∈ [0, 1, 55, 133, 136, 153, 160, 217, 244, 250, 352, 370,
          371, 407, 919, 1459])
