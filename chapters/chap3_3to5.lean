import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic

example : -5 ≡ 1 [ZMOD 3] := by
  norm_num

-- 3.3.12
example : 34 ≡ 104 [ZMOD 5] := by
  norm_num

example : a + n * c ≡ a [ZMOD n] := by
  rw [Int.modEq_iff_dvd]
  use -c
  ring

example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  calc
    2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by rel[h]

example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
  calc
    3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by rel[h]

example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
    4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  calc
    4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by rel[hb]

-- 3.4.5
example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] :=
  calc
    n ^ 3 + 7 * n ≡ 1 ^ 3 + 7 * 1 [ZMOD 3] := by rel[hn]
    _ ≡ 2 [ZMOD 3] := by norm_num

example {a : ℤ} (ha : a ≡ 3 [ZMOD 4]) :
    a ^ 3 + 4 * a ^ 2 + 2 ≡ 1 [ZMOD 4] :=
  calc
    a ^ 3 + 4 * a ^ 2 + 2 ≡ 3 ^ 3 + 4 * 3 ^ 2 + 2 [ZMOD 4] := by rel[ha]

example (a b : ℤ) : (a + b) ^ 3 ≡ a ^ 3 + b ^ 3 [ZMOD 3] := by
  rw [Int.modEq_iff_dvd]
  use -(a * b * (a + b))
  ring

example : ∃ a : ℤ, 4 * a ≡ 1 [ZMOD 7] := by
  use 2
  norm_num

example : ∃ k : ℤ, 5 * k ≡ 6 [ZMOD 8] := by
  use 6
  norm_num

example (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] := by
  mod_cases hn : n % 2
  · -- Case n is even: n % 2 = 0
    calc
      5 * n ^ 2 + 3 * n + 7 ≡ 5 * 0 ^ 2 + 3 * 0 + 7 [ZMOD 2] := by rel [hn]
      _ ≡ 1 [ZMOD 2] := by decide
  · -- Case n is odd: n % 2 = 1
    calc
      5 * n ^ 2 + 3 * n + 7 ≡ 5 * 1 ^ 2 + 3 * 1 + 7 [ZMOD 2] := by rel [hn]
      _ ≡ 1 [ZMOD 2] := by decide

example {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases h : x % 5
  · -- x ≡ 0 [ZMOD 5]
    calc
      x ^ 5 ≡ 0 ^ 5 [ZMOD 5] := by rel [h]
      _ ≡ 0 [ZMOD 5] := by decide
      _ ≡ x [ZMOD 5] := h.symm
  · -- x ≡ 1 [ZMOD 5]
    calc
      x ^ 5 ≡ 1 ^ 5 [ZMOD 5] := by rel [h]
      _ ≡ 1 [ZMOD 5] := by decide
      _ ≡ x [ZMOD 5] := h.symm
  · -- x ≡ 2 [ZMOD 5]
    calc
      x ^ 5 ≡ 2 ^ 5 [ZMOD 5] := by rel [h]
      _ ≡ 2 [ZMOD 5] := by decide
      _ ≡ x [ZMOD 5] := h.symm
  · -- x ≡ 3 [ZMOD 5]
    calc
      x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by rel [h]
      _ ≡ 3 [ZMOD 5] := by decide
      _ ≡ x [ZMOD 5] := h.symm
  · -- x ≡ 4 [ZMOD 5]
    calc
      x ^ 5 ≡ 4 ^ 5 [ZMOD 5] := by rel [h]
      _ ≡ 4 [ZMOD 5] := by decide
      _ ≡ x [ZMOD 5] := h.symm

-- 3.5.2
example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  have h2 : n = 2 * (3 * n) - 5 * n := by ring
  rw [h2]
  apply dvd_sub
  · apply dvd_mul_of_dvd_right h1
  · exact dvd_mul_right 5 n

-- 3.5.4
example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  have h2 : n = 5 * (11 * n) - 6 * (9 * n) := by ring
  rw [h2]
  apply dvd_sub
  · apply dvd_mul_of_dvd_right hn
  · exact dvd_mul_right 6 (9 * n)

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  have h : a = 3 * (5 * a) - 7 * (2 * a) := by ring
  rw [h]
  apply dvd_sub
  · apply dvd_mul_of_dvd_right ha
  · exact dvd_mul_right 7 (2 * a)

example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨j, hj⟩ := h2
  use 4 * j - 3 * k
  calc
    n = 28 * (9 * j) - 27 * (7 * k) := by rw [← hj, ← hk]; ring
    _ = 63 * (4 * j - 3 * k) := by ring

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨j, hj⟩ := h2
  use 8 * j - 3 * k
  calc
    n = 40 * (13 * j) - 39 * (5 * k) := by rw [← hj, ← hk]; ring
    _ = 65 * (8 * j - 3 * k) := by ring
