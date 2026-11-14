import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-- OEIS A046253 : "Equal to the sum of its nonzero digits raised to
    its own power." (chiffres nuls ignores). -/
def digitPowerSum (n : ℕ) : ℕ :=
  (((Nat.digits 10 n).filter (· ≠ 0)).map (fun d ↦ d ^ d)).sum

def genMultisets : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | k + 1, s =>
      if 10 ≤ s then [[]]
      else [] :: ((List.range' s (10 - s)).flatMap fun d =>
        (genMultisets k d).map fun l => d :: l)

def digitsFuel : ℕ → ℕ → List ℕ
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, n + 1 => ((n + 1) % 10) :: digitsFuel f ((n + 1) / 10)

def certSum (l : List ℕ) : ℕ := (l.map fun d => d ^ d).sum

def sortedNZ (n : ℕ) : List ℕ :=
  ((digitsFuel 11 n).filter (· ≠ 0)).insertionSort (· ≤ ·)

def certCheck (l : List ℕ) : Bool :=
  if sortedNZ (certSum l) == l
  then decide (certSum l = 0 ∨ certSum l = 1 ∨ certSum l = 3435 ∨ certSum l = 438579088)
  else true

theorem pow_le_nine_pow_nine {d : ℕ} (hd : d < 10) : d ^ d ≤ 9 ^ 9 := by
  interval_cases d <;> decide

theorem digitPowerSum_le (n : ℕ) :
    digitPowerSum n ≤ 9 ^ 9 * (Nat.digits 10 n).length := by
  unfold digitPowerSum
  set l := (Nat.digits 10 n).filter (· ≠ 0)
  have hb : ∀ x ∈ l.map (fun d ↦ d ^ d), x ≤ 9 ^ 9 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    exact pow_le_nine_pow_nine (Nat.digits_lt_base (b := 10) (m := n)
      (by norm_num) (List.mem_filter.mp hd).1)
  calc (l.map (fun d ↦ d ^ d)).sum
      ≤ (l.map (fun d ↦ d ^ d)).length * 9 ^ 9 :=
        List.sum_le_length_nsmul _ _ hb
    _ = l.length * 9 ^ 9 := by rw [List.length_map]
    _ ≤ (Nat.digits 10 n).length * 9 ^ 9 :=
        Nat.mul_le_mul_right _ (List.length_filter_le _ _)
    _ = 9 ^ 9 * (Nat.digits 10 n).length := by rw [Nat.mul_comm]

theorem bound_key (k : ℕ) : 9 ^ 9 * (k + 11) < 10 ^ (k + 10) := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hp : (10 : ℕ) ^ (k + 1 + 10) = 10 * 10 ^ (k + 10) := by ring
      have h9 : 9 ^ 9 ≤ (10 : ℕ) ^ (k + 10) := by
        have hb : (10 : ℕ) ^ 10 ≤ 10 ^ (k + 10) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 10 k)
        norm_num at hb ⊢
        omega
      omega

theorem A046253_bound (n : ℕ)
    (h : 10 < (Nat.digits 10 n).length) :
    digitPowerSum n < n := by
  have hn : n ≠ 0 := by
    intro h0
    rw [h0, Nat.digits_zero] at h
    simp at h
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  have hL : (Nat.digits 10 n).length = k + 11 := by omega
  have hbase : 10 ^ (Nat.digits 10 n).length ≤ 10 * n :=
    Nat.base_pow_length_digits_le 10 n (by norm_num) hn
  rw [hL] at hbase
  have hprev : 10 ^ (k + 10) ≤ n := by
    have hp : (10 : ℕ) ^ (k + 11) = 10 * 10 ^ (k + 10) := by ring
    rw [hp] at hbase
    exact Nat.le_of_mul_le_mul_left hbase (by norm_num)
  have h2 := digitPowerSum_le n
  rw [hL] at h2
  have hk2 := bound_key k
  omega

theorem digitsFuel_eq_digits (f n : ℕ) (h : n < 10 ^ f) :
    digitsFuel f n = Nat.digits 10 n := by
  induction f generalizing n with
  | zero =>
      have hn : n = 0 := Nat.lt_one_iff.mp (by simpa using h)
      subst hn; rfl
  | succ f ih =>
      cases n with
      | zero => rfl
      | succ m =>
          have hm : digitsFuel (f + 1) (m + 1) =
              ((m + 1) % 10) :: digitsFuel f ((m + 1) / 10) := rfl
          rw [hm]
          by_cases hlt : m + 1 < 10
          · have hd : (m + 1) / 10 = 0 := by omega
            have hf0 : digitsFuel f 0 = [] := by cases f <;> rfl
            rw [hd, hf0, show (m + 1) % 10 = m + 1 by omega,
                Nat.digits_of_lt 10 (m + 1) (Nat.succ_ne_zero m) hlt]
          · rw [Nat.digits_def' (by norm_num : 1 < 10) (Nat.succ_pos m)]
            congr 1
            apply ih
            rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 10)]
            calc m + 1 < 10 ^ (f + 1) := h
              _ = 10 ^ f * 10 := by rw [pow_succ]

theorem mem_gen (l : List ℕ) (k s : ℕ)
    (hs : l.Pairwise (· ≤ ·))
    (hlo : ∀ d ∈ l, s ≤ d) (hhi : ∀ d ∈ l, d ≤ 9)
    (hk : l.length ≤ k) :
    l ∈ genMultisets k s := by
  induction k generalizing l s with
  | zero =>
      have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hk)
      subst this; simp [genMultisets]
  | succ k ih =>
      show l ∈ genMultisets (k + 1) s
      unfold genMultisets
      by_cases h10 : 10 ≤ s
      · rw [if_pos h10]
        have hl : l = [] := by
          rcases l with _ | ⟨d, t⟩
          · rfl
          · exfalso
            have a := hlo d (@List.mem_cons_self _ d t)
            have b := hhi d (@List.mem_cons_self _ d t)
            omega
        subst hl; simp
      · rw [if_neg h10]
        rcases l with _ | ⟨d0, t⟩
        · simp
        · have hd0s : s ≤ d0 := hlo d0 (@List.mem_cons_self _ d0 t)
          have hd09 : d0 ≤ 9 := hhi d0 (@List.mem_cons_self _ d0 t)
          have hd0r : d0 ∈ List.range' s (10 - s) := by
            rw [List.mem_range']
            exact ⟨d0 - s, by omega, by omega⟩
          have ht_sorted : t.Pairwise (· ≤ ·) :=
            (List.pairwise_cons.mp hs).2
          have ht_ge : ∀ d ∈ t, d0 ≤ d :=
            (List.pairwise_cons.mp hs).1
          have ht_hi : ∀ d ∈ t, d ≤ 9 :=
            fun d hd => hhi d (List.mem_cons_of_mem d0 hd)
          have ht_len : t.length ≤ k := by
            have := hk; simp at this; omega
          have htmem : t ∈ genMultisets k d0 :=
            ih t d0 ht_sorted ht_ge ht_hi ht_len
          rw [List.mem_cons]
          right
          rw [List.mem_flatMap]
          exact ⟨d0, hd0r, List.mem_map.mpr ⟨t, htmem, rfl⟩⟩


/-- Extraction : M dans genMultisets k s => longueur <= k et
    chiffres dans [s, 9]. -/
theorem gen_spec (l : List ℕ) (k s : ℕ)
    (h : l ∈ genMultisets k s) :
    l.length ≤ k ∧ ∀ d ∈ l, s ≤ d ∧ d ≤ 9 := by
  induction k generalizing l s with
  | zero =>
      have h' : l = [] := by
        simpa [genMultisets] using h
      subst h'
      exact ⟨le_refl _, fun d hd => absurd hd List.not_mem_nil⟩
  | succ k ih =>
      unfold genMultisets at h
      by_cases h10 : 10 ≤ s
      · rw [if_pos h10] at h
        have h' : l = [] := by simpa using h
        subst h'
        exact ⟨Nat.zero_le _, fun d hd => absurd hd List.not_mem_nil⟩
      · rw [if_neg h10] at h
        rw [List.mem_cons] at h
        rcases h with rfl | h
        · exact ⟨Nat.zero_le _, fun d hd => absurd hd List.not_mem_nil⟩
        rw [List.mem_flatMap] at h
        obtain ⟨d, hd, h⟩ := h
        rw [List.mem_map] at h
        obtain ⟨t, ht, rfl⟩ := h
        obtain ⟨htl, htd⟩ := ih t d ht
        rw [List.mem_range'] at hd
        obtain ⟨e, he_lt, he_eq⟩ := hd
        refine ⟨by simp only [List.length_cons]; omega, fun x hx => ?_⟩
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · obtain ⟨hd1, hd2⟩ := htd x hx
          omega
