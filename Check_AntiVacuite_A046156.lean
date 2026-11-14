import A046156

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! N3 anti-vacuite pour A046156. -/

/-- (a) Satisfiabilite : les cycles sont fermes numeriquement
    (55→250→133→55 ; 136↔244 ; 160→217→352→160 ; 919↔1459 ;
    fixes 0,1,153,370,371,407). -/
theorem sat156_c3 : cubeSum 55 = 250 ∧ cubeSum 250 = 133 ∧
    cubeSum 133 = 55 := by
  unfold cubeSum; decide

theorem sat156_c3b : cubeSum 160 = 217 ∧ cubeSum 217 = 352 ∧
    cubeSum 352 = 160 := by
  unfold cubeSum; decide

theorem sat156_c2 : cubeSum 136 = 244 ∧ cubeSum 244 = 136 ∧
    cubeSum 919 = 1459 ∧ cubeSum 1459 = 919 := by
  unfold cubeSum; decide

/-- (b) Ancrage : convention 0^3=0 (cubeSum 10 = 1^3+0^3 = 1). -/
theorem anchor156 : cubeSum 10 = 1 ∧ cubeSum 0 = 0 := by
  unfold cubeSum; decide

/-- (c) Ablation : descente satisfiable sur n grand
    (99999 >= 10^4 : 5*729 = 3645 < 10^4). -/
theorem ablation156 : cubeSum 99999 = 3645 ∧
    cubeSum 99999 < 10 ^ 4 := by
  unfold cubeSum; decide

/-- Non-membre : 2 n'est pas dans le limit set. -/
theorem nonmember156 : ¬ (2 ∈ NUMATT156) := by decide

#print axioms A046156_seq
