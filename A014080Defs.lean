import Mathlib
import A046253Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-- OEIS A014080 : "Factorions: equal to the sum of the factorials
    of their digits in base 10" — chiffres 0 INCLUS (0! = 1),
    contrairement a A046253. -/
def factSum (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).map Nat.factorial).sum

/-- factSum sur un multiset de chiffres (reutilise genMultisets
    de A046253Defs). -/
def factSumM (l : List ℕ) : ℕ := (l.map Nat.factorial).sum

/-- Tous les chiffres de n tries (zeros inclus). Fuel 8 :
    factSumM ≤ 7·9! < 10^8 et le domaine apres borne est n < 10^7. -/
def sortedAll (n : ℕ) : List ℕ :=
  (digitsFuel 8 n).insertionSort (· ≤ ·)

/-- Certificat : si l est un multiset de chiffres invariant
    (sortedAll (factSumM l) = l), sa valeur doit etre dans la liste
    {0, 1, 2, 145, 40585} (0 = multiset vide). -/
def certCheck14080 (l : List ℕ) : Bool :=
  if sortedAll (factSumM l) == l
  then decide (factSumM l = 0 ∨ factSumM l = 1 ∨ factSumM l = 2 ∨
    factSumM l = 145 ∨ factSumM l = 40585)
  else true

/-- Decoupage take/drop (nom suffixe pour eviter l'homonymie
    avec mem_take_or_mem_drop de A046253.lean au sceau N5). -/
theorem mem_take_or_mem_drop14080 {α : Type} (l : List α) (n : ℕ) {x : α}
    (h : x ∈ l) : x ∈ l.take n ∨ x ∈ l.drop n := by
  rw [← List.take_append_drop n l] at h
  exact List.mem_append.mp h

theorem fact_le_nine {d : ℕ} (hd : d < 10) :
    Nat.factorial d ≤ Nat.factorial 9 := Nat.factorial_le (Nat.le_of_lt_succ hd)

/-- Chaque chiffre produit par digitsFuel est < 10 (meme preuve
    que digitsFuel_mem_lt de A214301 ; nom distinct pour eviter
    l'homonymie au sceau). -/
theorem digitsFuel_lt (f n d : ℕ) (hd : d ∈ digitsFuel f n) : d < 10 := by
  induction f generalizing n with
  | zero => simp [digitsFuel] at hd
  | succ f ih =>
      cases n with
      | zero => simp [digitsFuel] at hd
      | succ m =>
          simp only [digitsFuel] at hd
          rw [List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact Nat.mod_lt _ (by norm_num)
          · exact ih _ hd

theorem factSum_le (n : ℕ) :
    factSum n ≤ Nat.factorial 9 * (Nat.digits 10 n).length := by
  unfold factSum
  have hb : ∀ x ∈ (Nat.digits 10 n).map Nat.factorial, x ≤ Nat.factorial 9 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    exact fact_le_nine (Nat.digits_lt_base (b := 10) (m := n)
      (by norm_num) hd)
  calc ((Nat.digits 10 n).map Nat.factorial).sum
      ≤ ((Nat.digits 10 n).map Nat.factorial).length * Nat.factorial 9 :=
        List.sum_le_length_nsmul _ _ hb
    _ = (Nat.digits 10 n).length * Nat.factorial 9 := by rw [List.length_map]
    _ = Nat.factorial 9 * (Nat.digits 10 n).length := by rw [Nat.mul_comm]

/-- Clef de la borne : 9!·(k+8) < 10^(k+7) pour tout k.
    Base : 8·9! = 2 903 040 < 10^7. -/
theorem bound_key14080 (k : ℕ) : Nat.factorial 9 * (k + 8) < 10 ^ (k + 7) := by
  induction k with
  | zero => decide
  | succ k ih =>
      have hp : (10 : ℕ) ^ (k + 1 + 7) = 10 * 10 ^ (k + 7) := by ring
      have hlin : Nat.factorial 9 * (k + 1 + 8) =
          Nat.factorial 9 * (k + 8) + Nat.factorial 9 := by ring
      have h9 : Nat.factorial 9 ≤ (10 : ℕ) ^ (k + 7) := by
        have hb : (10 : ℕ) ^ 7 ≤ 10 ^ (k + 7) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 7 k)
        norm_num at hb ⊢
        omega
      have ha : 0 < (10 : ℕ) ^ (k + 7) := by positivity
      omega

/-- Borne de finitude (commentaire Poole/Hasler) : a `L > 7` chiffres,
    somme ≤ 9!·L < 10^(L-1) ≤ n — reduit a n < 10^7. -/
theorem A014080_bound (n : ℕ)
    (h : 7 < (Nat.digits 10 n).length) :
    factSum n < n := by
  have hn : n ≠ 0 := by
    intro h0
    rw [h0, Nat.digits_zero] at h
    simp at h
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  have hL : (Nat.digits 10 n).length = k + 8 := by omega
  have hbase : 10 ^ (Nat.digits 10 n).length ≤ 10 * n :=
    Nat.base_pow_length_digits_le 10 n (by norm_num) hn
  rw [hL] at hbase
  have hprev : 10 ^ (k + 7) ≤ n := by
    have hp : (10 : ℕ) ^ (k + 8) = 10 * 10 ^ (k + 7) := by ring
    rw [hp] at hbase
    exact Nat.le_of_mul_le_mul_left hbase (by norm_num)
  have h2 := factSum_le n
  rw [hL] at h2
  have hk2 := bound_key14080 k
  omega

/-- Chiffre de sortedAll est < 10. -/
theorem sortedAll_mem (n d : ℕ) (hd : d ∈ sortedAll n) : d < 10 := by
  unfold sortedAll at hd
  rw [List.mem_insertionSort] at hd
  exact digitsFuel_lt _ _ _ hd

theorem sortedAll_pairwise (n : ℕ) :
    (sortedAll n).Pairwise (· ≤ ·) := by
  unfold sortedAll
  exact List.pairwise_insertionSort _ _

/-- n < 10^7 => sortedAll n a au plus 7 chiffres. -/
theorem sortedAll_length_le (n : ℕ) (hn : n < 10 ^ 7) :
    (sortedAll n).length ≤ 7 := by
  unfold sortedAll
  rw [(List.perm_insertionSort _ _).length_eq]
  calc (digitsFuel 8 n).length
      = (Nat.digits 10 n).length := by
        rw [digitsFuel_eq_digits 8 n (by omega)]
    _ ≤ 7 := (Nat.digits_length_le_iff (k := 7)
        (by norm_num) n).mpr hn
