import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic

example : (-2 : ℤ) ∣ 6 := by
  use -3
  norm_num

-- 3.2.4
example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨j, hj⟩ := hbc
  use k^2 * j
  calc
    c = (a * k) ^ 2 * j := by rw[hj, hk]
    _ = a^2 * (k^2 * j) := by ring

-- 3.2.5
example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by
  obtain ⟨k, hk⟩ := h
  use y * k
  linarith

-- 3.2.8
example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  obtain ⟨k, hk⟩ := hab
  nlinarith

-- 3.2.9
example (t : ℤ) : t ∣ 0 := by
  use 0
  norm_num

example : ¬(3 : ℤ) ∣ -10 := by
  decide

example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨k, hk⟩ := h
  use 3 * k - 4 * x * k^2
  calc
    3 * y - 4 * y ^ 2 = 3 * (x * k) - 4 * (x * k)^2 := by rw[hk]
    _ = x * (3 * k - 4 * x * k^2 ) := by ring

example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  obtain ⟨k, hk⟩ := h
  use 2 * m^2 * k^3 + k
  calc
    2 * n ^ 3 + n = 2 * (m * k)^3 + (m * k) := by rw[hk]
    _ = m * (2 * m^2 * k^3 + k) := by ring

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k, hk⟩ := hab
  use 2 * a^2 * k^3 - a * k^2 + 3 * k
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b = 2 * (a * k) ^ 3 - (a * k) ^ 2 + 3 * (a * k) := by rw[hk]
    _ = a * (2 * a^2 * k^3 - a * k^2 + 3 * k) := by ring

example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨j, hj⟩ := h2
  use n^3 * j
  calc
    m = l^3 * j := by exact hj
    _ =(k * n)^3 * j := by rw[hn]
    _ = k^3 * (n^3 * j) := by ring

example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  obtain ⟨k, hk⟩ := hpq
  obtain ⟨j, hj⟩ := hqr
  use k^2 * j
  calc
    r = q^2 * j := by exact hj
    _ = (p^3 * k)^2 * j := by rw[hk]
    _ = p^6 * (k^2 * j) := by ring

example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by
  use 6
  norm_num

example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by
  use 2, 1
  norm_num
