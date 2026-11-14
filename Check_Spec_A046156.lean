import Spec_A046156
import A046156

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Fermeture N0 : A046156_seq realise le spec verbatim. -/
theorem proven_spec_a046156 : SpecPropA046156 := by
  intro m
  exact A046156_seq m

#print axioms A046156_seq
