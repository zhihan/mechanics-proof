import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic

/- Chapter 2-/
section Sec1

-- 2.1.3
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by linarith
  have h4 : r ≤ 3 - s := by linarith
  calc
    r = (r + r) / 2 := by ring
    _ ≤ (3 - s + (3 + s)) / 2 := by gcongr
    _ = 3 := by ring


-- 2.1.6
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have hx0: x < 0 := by linarith
  calc
    y ≥ 3 - 2 * x := by linarith
    _ > 3 - 2 * 0 := by gcongr
    _ = 3 := by ring

-- 2.1.7
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h1' : 0 ≤ b + a := by linarith
  have h2' : 0 ≤ b - a := by linarith
  have h' : 0 ≤ b ^ 2 - a ^ 2 :=
    calc
      0 ≤ (b + a) * (b - a) := by nlinarith
      _ = b ^ 2 - a ^ 2 := by ring
  calc
    a ^ 2 ≤ b ^ 2 := by linarith

-- 2.1.8
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have h1 : 0 ≤ b - a := by linarith
  have h2 : b ^ 2 + a * b + a ^2 ≥ 0 :=
    calc
      b ^ 2 + a * b + a ^2 = ( (b - a)^2 + 3 * (b + a)^2)/4 := by ring
      _ ≥ 0 := by nlinarith
  have h2 : b^3 - a^3 ≥ 0 :=
    calc
      b^3 - a^3 = (b - a) * (b ^ 2 + a * b + a ^2) := by ring
      _ ≥ 0 := by nlinarith
  calc
    a ^ 3 ≤ b ^ 3 := by linarith

-- 2.1.9
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h1 : (x + 2) * (x - 2) = 0 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 - 4 := by ring
      _ = 0 := by rw[h1]; ring
  have h2 : x + 2 > 0 := by linarith
  nlinarith

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h1: (n - 2) ^ 2 = 0 :=
    calc
      (n - 2) ^ 2 = n ^ 2 - 4 * n + 4 := by ring
      _ = 0 := by linarith
  nlinarith

example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have h1 : x > 0 := by linarith
  nlinarith

end Sec1

section Sec2

-- 2.2.2
example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  have hy : y ^ 2 + 1 > 0 :=
    calc
      y ^ 2 + 1 ≥ 1 := by nlinarith
      _ > 0 := by norm_num
  apply ne_of_gt
  exact hy

-- 2.2.4
example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  have hm1 : m > 2 := by
    calc
      m = 4 := by linarith
      _ > 2 := by norm_num
  apply ne_of_gt
  linarith

example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  have h3 : s ≤ -2 := by
    calc
      s ≤ -6 / 3 := by linarith
      _ = -2 := by norm_num
  have h4 : s ≥ -2:= by
    calc
      s ≥ -4 / 2 := by linarith
      _ = -2 := by norm_num
  exact le_antisymm h3 h4

-- 2.3.2
example {n : ℕ} : n ^ 2 ≠ 2 := by
  rcases lt_or_ge n 2 with hn | hn
  · apply ne_of_lt
    nlinarith
  · apply ne_of_gt
    nlinarith

-- 2.3.4
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h21 | h22
  . apply Or.inl
    linarith
  . apply Or.inr
    linarith

-- 2.3.6
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  rcases h with h1 | h2
  . calc
      x ^2 + 1 = 4 ^ 2 + 1 := by rw[h1]
      _ = 17 := by norm_num
  . calc
      x^2 + 1 = (-4)^2 + 1 := by rw[h2]
      _ = 17 := by norm_num

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  rcases h with h1 | h2
  . calc
      x ^ 2 - 3 * x + 2 = 1 ^ 2 - 3 * 1 + 2 := by rw[h1]
      _ = 0 := by norm_num
  . calc
      x ^ 2 - 3 * x + 2 = 2 ^ 2 - 3 * 2 + 2 := by rw[h2]
      _ = 0 := by norm_num

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  rcases h with h1 | h2
  · calc
      t ^ 2 - t - 6 = (-2) ^ 2 - (-2) - 6 := by rw [h1]
      _ = 0 := by norm_num
  · calc
      t ^ 2 - t - 6 = 3 ^ 2 - 3 - 6 := by rw [h2]
      _ = 0 := by norm_num

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  rcases h with h1 | h2
  · calc
      x * y + 2 * x = 2 * y + 2 * 2 := by rw [h1]
      _ = 2 * y + 4 := by ring
  · calc
      x * y + 2 * x = x * (-2) + 2 * x := by rw [h2]
      _ = 2 * (-2) + 4 := by ring
      _ = 2 * y + 4 := by rw [h2]

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  apply Or.inl
  linarith

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  apply Or.inr
  linarith

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  apply Or.inl
  linarith

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h1 : (x + 3) * (x - 1) = 0 :=
    calc
      (x + 3) * (x - 1) = x ^ 2 + 2 * x - 3 := by ring
      _ = 0 := by rw[hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h21 | h22
  . apply Or.inl
    linarith
  . apply Or.inr
    linarith

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h1 : (a - b) * (a - 2 * b ) = 0 :=
    calc
      (a - b) * (a - 2 * b ) = a ^ 2 + 2 * b ^ 2 - 3 * a * b := by ring
      _ = 0 := by linarith
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h21 | h22
  . apply Or.inl
    linarith
  . apply Or.inr
    linarith

example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 : (t - 1) * t ^ 2 = 0 :=
    calc
      (t - 1) * t ^ 2 = t ^ 3 - t ^ 2 := by ring
      _ = 0 := by linarith
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h21 | h22
  . apply Or.inl
    linarith
  . apply Or.inr
    nlinarith

example {n : ℕ} : n ^ 2 ≠ 7 := by
  rcases le_or_gt n 2 with hn | hn
  · apply ne_of_lt
    nlinarith
  · apply ne_of_gt
    nlinarith

example {x : ℤ} : 2 * x ≠ 3 := by
  rcases le_or_gt x 1 with hn | hn
  · apply ne_of_lt
    nlinarith
  · apply ne_of_gt
    nlinarith

example {t : ℤ} : 5 * t ≠ 18 := by
  rcases le_or_gt t 3 with hn | hn
  · apply ne_of_lt
    nlinarith
  · apply ne_of_gt
    nlinarith

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  rcases le_or_gt m 5 with hn | hn
  · apply ne_of_lt
    nlinarith
  · apply ne_of_gt
    nlinarith

-- 2.4.2
example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc
      p ^ 2 ≤ 9 := by linarith
      _ = 3 ^ 2 := by norm_num
    norm_num
  linarith

-- 2.5.2
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  . nlinarith
  . have hxt' : 0 < (-x) * t := by
      calc
        0 = - (x * t) + (x * t) := by ring
        _ < - (x * t) + 0       := by rel [hxt]
        _ = (-x) * t            := by ring
    nlinarith

-- 2.5.5
example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  norm_num

-- 2.5.6
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

-- 2.5.7
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use p/2 + q/2
  apply And.intro
  . linarith
  . linarith

-- 2.5.9
example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  norm_num

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 9, 2
  norm_num

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  norm_num

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  norm_num

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  rcases le_or_gt x 0 with hn | hp
  . use x - 1
    nlinarith
  . use x + 1
    nlinarith

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hxt⟩ := h
  have h0 : (x - 1) * (t - 1) < 0 :=
    calc
      (x - 1) * (t - 1) = x * t - x - t + 1 := by ring
      _ < 0 := by linarith
  rintro rfl  -- t ≠ 1 is t = 0 → False
  nlinarith

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨x, hxt⟩ := h
  omega

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  use |n| + 2
  have h1 : n ≤ |n| := le_abs_self n
  have h2 : 0 ≤ |n| := abs_nonneg n
  have h_cube : (|n| + 2) ^ 3 = (|n| + 2) * (|n| + 2) * (|n| + 2) := by ring
  rw [h_cube]
  nlinarith

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (b + c - a)/2, (a + c - b)/2, (a + b - c)/2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  . linarith
  . linarith
  . linarith
  . ring
  . ring
  . ring

end Sec2
