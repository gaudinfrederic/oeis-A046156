import A014080Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-!
# A046156 - definitions : map "somme des cubes des chiffres"
#   (0^3 = 0 ; 0 est un VRAI point fixe dans les deux
#   conventions - OEIS data inclut 0, et Nat.digits 10 0 = []
#   donne cubeSum 0 = 0 - aucune restriction de domaine).
-/

/-- Somme des cubes des chiffres (A055012). -/
def cubeSum (n : ℕ) : ℕ := ((Nat.digits 10 n).map (· ^ 3)).sum

/-- Idem sur un multiset de chiffres. -/
def cubeSumM (l : List ℕ) : ℕ := (l.map (· ^ 3)).sum

/-- Pas de la dynamique multiset : cubeSumM puis re-tri. -/
def phiC (M : List ℕ) : List ℕ := sortedAll (cubeSumM M)

/-- Iteration de phiC. -/
def iterateC : ℕ → List ℕ → List ℕ
  | 0, M => M
  | k + 1, M => iterateC k (phiC M)

/-- Les 16 classes-multisets attractrices (limit set A046156). -/
def ATT156 : List (List ℕ) :=
  [ [], [1], [1, 3, 5], [0, 3, 7], [1, 3, 7], [0, 4, 7],
    [1, 3, 6], [2, 4, 4], [1, 9, 9], [1, 4, 5, 9],
    [5, 5], [0, 2, 5], [1, 3, 3],
    [0, 1, 6], [1, 2, 7], [2, 3, 5] ]

/-- Appartenance a l'attracteur. -/
def inATT156 (M : List ℕ) : Bool := ATT156.contains M

/-- Certificat : atteint l'attracteur en au plus `fuel` pas. -/
def reachesATT156 : ℕ → List ℕ → Bool
  | 0, _ => false
  | fuel + 1, M => inATT156 M || reachesATT156 fuel (phiC M)

/-- Cloture de l'attracteur (16 evaluations). -/
theorem att156_closed :
    ATT156.all (fun M => inATT156 (phiC M)) = true := by
  decide

/-- cubeSum n <= 729 * nombre de chiffres (chaque d <= 9). -/
theorem cubeSum_le (n : ℕ) :
    cubeSum n ≤ 729 * (Nat.digits 10 n).length := by
  unfold cubeSum
  have hb : ∀ x ∈ (Nat.digits 10 n).map (· ^ 3), x ≤ 729 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    have h9 := Nat.digits_lt_base (b := 10) (m := n)
      (by norm_num) hd
    calc d ^ 3 ≤ 9 ^ 3 := Nat.pow_le_pow_left (by omega) 3
    _ = 729 := by decide
  calc ((Nat.digits 10 n).map (· ^ 3)).sum
      ≤ ((Nat.digits 10 n).map (· ^ 3)).length * 729 :=
        List.sum_le_length_nsmul _ _ hb
    _ = (Nat.digits 10 n).length * 729 := by rw [List.length_map]
    _ = 729 * (Nat.digits 10 n).length := by rw [Nat.mul_comm]

/-- Clef de la borne : 729·(k+5) < 10^(k+4) pour tout k.
    Base : 729·5 = 3645 < 10^4. -/
theorem bound_key156 (k : ℕ) : 729 * (k + 5) < 10 ^ (k + 4) := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hp : (10 : ℕ) ^ (k + 1 + 4) = 10 * 10 ^ (k + 4) := by ring
      have hlin : 729 * (k + 1 + 5) = 729 * (k + 5) + 729 := by ring
      have h9 : (729 : ℕ) ≤ (10 : ℕ) ^ (k + 4) := by
        have hb : (10 : ℕ) ^ 4 ≤ 10 ^ (k + 4) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 4 k)
        omega
      have ha : 0 < (10 : ℕ) ^ (k + 4) := by positivity
      omega

/-- Descente : a `L > 4` chiffres, somme <= 729·L < 10^(L-1) <= n
    - reduit a n < 10^4 (borne Hasler/Poole). -/
theorem A046156_bound (n : ℕ)
    (h : 4 < (Nat.digits 10 n).length) :
    cubeSum n < n := by
  have hn : n ≠ 0 := by
    intro h0
    rw [h0, Nat.digits_zero] at h
    simp at h
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  have hL : (Nat.digits 10 n).length = k + 5 := by omega
  have hbase : 10 ^ (Nat.digits 10 n).length ≤ 10 * n :=
    Nat.base_pow_length_digits_le 10 n (by norm_num) hn
  rw [hL] at hbase
  have hprev : 10 ^ (k + 4) ≤ n := by
    have hp : (10 : ℕ) ^ (k + 5) = 10 * 10 ^ (k + 4) := by ring
    rw [hp] at hbase
    exact Nat.le_of_mul_le_mul_left hbase (by norm_num)
  have h2 := cubeSum_le n
  rw [hL] at h2
  have hk2 := bound_key156 k
  omega

/-- n < 10^4 => sortedAll n a au plus 4 chiffres. -/
theorem sortedAll_length_le4 (n : ℕ) (hn : n < 10 ^ 4) :
    (sortedAll n).length ≤ 4 := by
  unfold sortedAll
  rw [(List.perm_insertionSort _ _).length_eq]
  calc (digitsFuel 8 n).length
      = (Nat.digits 10 n).length := by
        rw [digitsFuel_eq_digits 8 n (by omega)]
    _ ≤ 4 := (Nat.digits_length_le_iff (b := 10) (k := 4)
        (by norm_num) n).mpr hn

/-- phiC reste dans le domaine fini gen 4 0. -/
theorem phiC_mem_gen (M : List ℕ) (hM : M ∈ genMultisets 4 0) :
    phiC M ∈ genMultisets 4 0 := by
  obtain ⟨hlen, hdg⟩ := gen_spec M 4 0 hM
  have hall : ∀ d ∈ M, d < 10 := by
    intro d hd; obtain ⟨_, h2⟩ := hdg d hd; omega
  have hcs : cubeSumM M ≤ 729 * M.length := by
    unfold cubeSumM
    have hb : ∀ x ∈ M.map (· ^ 3), x ≤ 729 := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      calc d ^ 3 ≤ 9 ^ 3 :=
        Nat.pow_le_pow_left (by have := hall d hd; omega) 3
      _ = 729 := by decide
    calc (M.map (· ^ 3)).sum
        ≤ (M.map (· ^ 3)).length * 729 :=
          List.sum_le_length_nsmul _ _ hb
      _ = M.length * 729 := by rw [List.length_map]
      _ = 729 * M.length := by rw [Nat.mul_comm]
  have hlt : cubeSumM M < 10 ^ 4 := by omega
  apply mem_gen _ 4 0 (sortedAll_pairwise _)
  · intro d _; exact Nat.zero_le d
  · intro d hd; exact Nat.lt_succ_iff.mp (sortedAll_mem _ d hd)
  · exact sortedAll_length_le4 _ hlt
