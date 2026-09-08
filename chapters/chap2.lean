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
