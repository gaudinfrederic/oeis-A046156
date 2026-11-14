import A046156Defs
import A046156Basin0
import A046156Basin1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-!
# A046156 - limit set de la map "somme des cubes des chiffres"

Verbatim OEIS : "Limit set for operation of repeatedly replacing
a number with the sum of the cubes of its digits". Data : 0, 1,
55, 133, 136, 153, 160, 217, 244, 250, 352, 370, 371, 407, 919,
1459 (16 elements). THEOREMES : convergence + biconditionnel
points periodiques (inconditionnel - 0 est un vrai point fixe
dans les deux conventions).
-/

/-- Pont certificat -> Prop. -/
theorem reachesATT156_true (fuel : ℕ) (M : List ℕ)
    (h : reachesATT156 fuel M = true) :
    ∃ k ≤ fuel, iterateC k M ∈ ATT156 := by
  induction fuel generalizing M with
  | zero => simp [reachesATT156] at h
  | succ f ih =>
      unfold reachesATT156 at h
      rw [Bool.or_eq_true] at h
      rcases h with hin | hrec
      · exact ⟨0, Nat.zero_le _, (List.contains_iff_mem).mp hin⟩
      · obtain ⟨k, hkf, hkm⟩ := ih _ hrec
        exact ⟨k + 1, Nat.succ_le_succ hkf, hkm⟩

/-- Reassemblage des 2 chunks. -/
theorem basin_all156 :
    (genMultisets 4 0).all (fun M => reachesATT156 32 M) = true := by
  rw [List.all_eq_true]
  intro l hl
  rcases mem_take_or_mem_drop14080 _ 500 hl with h | h
  · exact List.all_eq_true.mp basin_chunk156_0 _ h
  exact List.all_eq_true.mp basin_chunk156_1 _ h

/-- Theoreme multiset : tout multiset de gen 4 0 atteint
    l'attracteur en ≤ 32 pas. -/
theorem A046156_multiset (M : List ℕ)
    (hM : M ∈ genMultisets 4 0) :
    ∃ k ≤ 32, iterateC k M ∈ ATT156 := by
  have hck := List.all_eq_true.mp basin_all156 M hM
  obtain ⟨k, hkb, hk⟩ := reachesATT156_true 32 M hck
  exact ⟨k, hkb, hk⟩

/-- Les 16 elements du limit set (ordre OEIS). -/
def NUMATT156 : List ℕ :=
  [0, 1, 55, 133, 136, 153, 160, 217, 244, 250, 352, 370, 371,
   407, 919, 1459]

/-- Chaque classe d'attracteur s'envoie numeriquement sur
    NUMATT156 ([] inclus : cubeSumM [] = 0 qui est dans la
    liste). -/
theorem att156_maps :
    ATT156.all (fun M => NUMATT156.contains (cubeSumM M))
      = true := by
  decide

/-- Pont : cubeSumM (sortedAll m) = cubeSum m pour m < 10^8. -/
theorem cubeSumM_sortedAll (m : ℕ) (hm : m < 10 ^ 8) :
    cubeSumM (sortedAll m) = cubeSum m := by
  unfold cubeSumM sortedAll cubeSum
  rw [digitsFuel_eq_digits 8 m hm]
  exact (List.Perm.sum_eq (List.Perm.map _
    (List.perm_insertionSort _ _)))

/-- m < 10^4 => cubeSum m < 10^4. -/
theorem cubeSum_lt10k (m : ℕ) (hm : m < 10 ^ 4) :
    cubeSum m < 10 ^ 4 := by
  have hL : (Nat.digits 10 m).length ≤ 4 :=
    (Nat.digits_length_le_iff (b := 10) (k := 4)
      (by norm_num) m).mpr hm
  have h2 := cubeSum_le m
  omega

/-- Conjugaison orbite numerique <-> multiset (orbite < 10^4). -/
theorem conj_iterateC (j : ℕ) : ∀ m, m < 10 ^ 4 →
    iterateC j (sortedAll m) =
      sortedAll (Nat.iterate cubeSum j m) := by
  induction j with
  | zero => intro m _; rfl
  | succ j ih =>
      intro m hm
      show iterateC j (phiC (sortedAll m)) =
        sortedAll (Nat.iterate cubeSum (j + 1) m)
      have hconj : phiC (sortedAll m) = sortedAll (cubeSum m) := by
        unfold phiC
        rw [cubeSumM_sortedAll m (by omega)]
      rw [hconj]
      exact ih (cubeSum m) (cubeSum_lt10k m hm)

/-- Orbite < 10^4 invariante. -/
theorem iterC_lt4 (m : ℕ) (hm : m < 10 ^ 4) (j : ℕ) :
    Nat.iterate cubeSum j m < 10 ^ 4 := by
  induction j generalizing m with
  | zero => exact hm
  | succ j ih =>
      show Nat.iterate cubeSum j (cubeSum m) < 10 ^ 4
      exact ih (cubeSum m) (cubeSum_lt10k m hm)

/-- Descente : tout n atteint < 10^4 (borne A046156_bound). -/
theorem desc4 (n : ℕ) :
    ∃ j, Nat.iterate cubeSum j n < 10 ^ 4 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases h4 : n < 10 ^ 4
      · exact ⟨0, h4⟩
      · have hL : 4 < (Nat.digits 10 n).length := by
          by_contra hc
          have hc : (Nat.digits 10 n).length ≤ 4 :=
            Nat.le_of_not_gt hc
          have h1 := Nat.lt_base_pow_length_digits (b := 10)
            (m := n) (by norm_num)
          have h2 : n < 10 ^ 4 := lt_of_lt_of_le h1
            (Nat.pow_le_pow_right (by norm_num) hc)
          omega
        have hdesc := A046156_bound n hL
        obtain ⟨j, hj⟩ := ih (cubeSum n) hdesc
        exact ⟨j + 1, hj⟩

/-- iterate_add156 : f^(j+k) x = f^k (f^j x). -/
theorem iter_add156 (f : ℕ → ℕ) (j k x : ℕ) :
    Nat.iterate f (j + k) x = Nat.iterate f k (Nat.iterate f j x) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
      rw [show j + 1 + k = j + k + 1 from by omega]
      exact ih (f x)

/-- f^(k+1) x = f (f^k x). -/
theorem iter_step156 (f : ℕ → ℕ) (k x : ℕ) :
    Nat.iterate f (k + 1) x = f (Nat.iterate f k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => exact ih (f x)

/-- Theoreme principal : toute orbite atteint l'un des 16
    elements du limit set (0 inclus - aucune restriction). -/
theorem A046156 (n : ℕ) :
    ∃ k, Nat.iterate cubeSum k n ∈ NUMATT156 := by
  obtain ⟨j, hj⟩ := desc4 n
  have hgen : sortedAll (Nat.iterate cubeSum j n) ∈
      genMultisets 4 0 := by
    apply mem_gen _ 4 0 (sortedAll_pairwise _)
    · intro d _; exact Nat.zero_le d
    · intro d hd
      have := sortedAll_mem _ d hd; omega
    · exact sortedAll_length_le4 _ hj
  obtain ⟨k, _, hATT⟩ := A046156_multiset
    (sortedAll (Nat.iterate cubeSum j n)) hgen
  rw [conj_iterateC k (Nat.iterate cubeSum j n) hj] at hATT
  have hlt : Nat.iterate cubeSum k (Nat.iterate cubeSum j n)
      < 10 ^ 4 := iterC_lt4 _ hj k
  have hfm : cubeSumM (sortedAll (Nat.iterate cubeSum k
      (Nat.iterate cubeSum j n))) ∈ NUMATT156 :=
    (List.contains_iff_mem).mp
      (List.all_eq_true.mp att156_maps _ hATT)
  rw [cubeSumM_sortedAll _ (by omega : Nat.iterate cubeSum k
      (Nat.iterate cubeSum j n) < 10 ^ 8)] at hfm
  refine ⟨j + k + 1, ?_⟩
  rw [show j + k + 1 = j + (k + 1) from by omega,
      iter_add156 cubeSum j (k + 1) n, iter_step156 cubeSum k _]
  exact hfm

/-- NUMATT156 est clos sous cubeSum (16 evaluations). -/
theorem numatt156_closed :
    NUMATT156.all (fun p => NUMATT156.contains (cubeSum p))
      = true := by
  decide

/-- L'orbite issue de NUMATT156 reste dans NUMATT156. -/
theorem iter156_mem_numatt (p : ℕ) (hp : p ∈ NUMATT156) (t : ℕ) :
    Nat.iterate cubeSum t p ∈ NUMATT156 := by
  induction t generalizing p with
  | zero => exact hp
  | succ t ih =>
      show Nat.iterate cubeSum t (cubeSum p) ∈ NUMATT156
      have hcl : cubeSum p ∈ NUMATT156 :=
        (List.contains_iff_mem).mp
          (List.all_eq_true.mp numatt156_closed _ hp)
      exact ih _ hcl

/-- m periodique de periode k => m = C^(j*k) m pour tout j. -/
theorem iter156_period_mul (m k : ℕ)
    (hper : Nat.iterate cubeSum k m = m) (j : ℕ) :
    Nat.iterate cubeSum (j * k) m = m := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.add_mul, Nat.one_mul,
          iter_add156 cubeSum (j * k) k m, ih, hper]

/-- Point periodique => dans la liste A046156 (0 inclus). -/
theorem periodic156_mem (m : ℕ)
    (hper : ∃ k, 0 < k ∧ Nat.iterate cubeSum k m = m) :
    m ∈ NUMATT156 := by
  obtain ⟨k, hk0, hper⟩ := hper
  obtain ⟨j, hj⟩ := A046156 m
  cases k with
  | zero => omega
  | succ k' =>
      have hcycle := iter156_period_mul m (k' + 1) hper j
      rw [Nat.mul_succ, Nat.add_comm (j * k') j,
          iter_add156 cubeSum j (j * k') m] at hcycle
      rw [← hcycle]
      exact iter156_mem_numatt _ hj _

/-- Chaque element de la liste est periodique (1, 2 ou 3). -/
theorem mem156_periodic (m : ℕ) (hm : m ∈ NUMATT156) :
    ∃ k, 0 < k ∧ Nat.iterate cubeSum k m = m := by
  fin_cases hm
  · exact ⟨1, Nat.one_pos, by decide⟩
  · exact ⟨1, Nat.one_pos, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, Nat.one_pos, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨1, Nat.one_pos, by decide⟩
  · exact ⟨1, Nat.one_pos, by decide⟩
  · exact ⟨1, Nat.one_pos, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩

/-- A046156 (verbatim OEIS) : les points periodiques de la somme
    des cubes des chiffres sont exactement les 16 nombres de la
    suite - inconditionnel, 0 est un vrai point fixe. -/
theorem A046156_seq (m : ℕ) :
    (∃ k, 0 < k ∧ Nat.iterate cubeSum k m = m) ↔ m ∈ NUMATT156 :=
  ⟨fun h => periodic156_mem m h, fun h => mem156_periodic m h⟩
