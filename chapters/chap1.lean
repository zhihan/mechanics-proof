import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.Real.Basic  -- Note this works with lean 4.33.1
import Mathlib.Data.Rat.Init
import Mathlib.Tactic

/- Chapter 1: Proofs by calculation. -/

-- Equalities section 1.3
section Sec_1_3

example {a b : ℚ}
  (h1 : a - b = 4) (h2 : a * b = 1) :
  (a + b) ^ 2 = 20 := by
  calc
  (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring  -- algebra
  _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
  _ = 20 := by ring

example {r s : ℝ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
  calc
  r = r + 2 * s - 2 * s := by ring
  _ = -1 - 2 * s := by rw [h2]
  _ = -1 - 2 * 3 := by rw [h1]
  _ = -7 := by ring

example {a b m n : ℤ} (h1 : a * m + b * n = 1) (h2 : b ^ 2 = 2 * a ^ 2) :
    (2 * a * n + b * m) ^ 2 = 2 :=
  calc
  (2 * a * n + b * m) ^ 2
    = 2 * (a * m + b * n) ^ 2 + (m ^ 2 - 2 * n ^ 2) * (b ^ 2 - 2 * a ^ 2) := by ring
  _ = 2 * 1 ^ 2 + (m ^ 2 - 2 * n ^ 2) * (2 * a ^ 2 - 2 * a ^ 2) := by rw[h1, h2]
  _ = 2 := by ring

example {a b c d e f : ℤ} (h1 : a * d = b * c) (h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 :=
  calc
  d * (a * f - b * e) = d * a * f - d * b * e := by ring
  _ = a * d * f - d * e * b := by ring
  _ = b * c * f - c * f * b := by rw[h1, h2]
  _ = b * c * f - b * c * f := by ring
  _ = 0 := by ring

example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
  a = a := by ring
  _ = 2 * b + 5 := by rw[h1]
  _ = 2 * 3 + 5 := by rw[h2]
  _ = 11 := by ring

example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
  x = x + 4 - 4 := by ring
  _ = 2 - 4 := by rw[h1]
  _ = -2 := by ring

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
  a = a - 5 * b + 5 * b := by ring
  _ = 4 + 5 * b := by rw[h1]
  _ = 4 + 5 * (b + 2 -2) := by ring
  _ = 4 + 5 * (3 - 2) := by rw[h2]
  _ = 9 := by ring

example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
  w = (3 * w + 1 -1) / 3 := by ring
  _ = (4 - 1) / 3 := by rw[h1]
  _ = 1 := by ring

example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  calc
  x = 2 * x + 3 - x - 3 := by ring
  _ = x - x - 3 := by rw[h1]
  _ = -3 := by ring

example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  calc
  x = (2 * x - y) + (y - x + 1) - 1 := by ring
  _ = 4 + 2 - 1 := by rw[h1, h2]
  _ = 5 := by ring

example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
  u = (u + 2 * v) / 2 + (u - 2 * v) / 2 := by ring
  _ = 4 / 2 + 6 / 2 := by rw[h1, h2]
  _ = 5 := by ring

example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
  x = (3 * (x + y) + (5 * x - 3 * y)) / 8 := by ring
  _ = (3 * 4 + 4) / 8 := by rw[h1, h2]
  _ = 2 := by ring

example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
  a ^ 2 - a + 3 = ((a - 3) + 3)^2 - (a - 3) - 3 + 3 := by ring
  _ = (2 * b + 3) ^ 2 - 2 * b - 3 + 3 := by rw[h1]
  _ = 4 * b ^ 2 + 10 * b + 9 := by ring

example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
  z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 =
    (z ^ 2 - 2 + 2) ^ 2 - z * (z ^ 2 - 2) - (z ^ 2 - 2 + 2) + 1 := by ring
  _ = ( 0 + 2 )^2 - z * 0 - (0 + 2) + 1 := by rw[h1]
  _ = 3 := by ring

example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  calc
  y = 4 * x - 3 := by rw[h2]
  _ = 4 * 3 - 3 := by rw[h1]
  _ = 9 := by ring

example {a b : ℤ} (h : a - b = 0) : a = b :=
  calc
  a = (a - b) + b := by ring
  _ = 0 + b := by rw[h]
  _ = b := by ring

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  calc
  x = x - (x - 3 * y) + (x - 3 * y) := by ring
  _ = 3 * y + (x - 3 * y) := by ring
  _ = 3 * 3 + 5 := by rw[h1, h2]  -- Note this order also matters
  _ = 14 := by ring

example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 :=
  calc
  x = x + (x + 2 * y) - (x + 2 * y) := by ring
  _ = x + (x + 2 * y) - (x + 2 * (y + 1) - 2) := by ring
  _ = x + 3 - (x + 2 * 3 - 2) := by rw[h2, h1]
  _ = -1 := by ring

example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 :=
  calc
  p = p + (p + 4 * q) - (p + 4 * q) := by ring
  _ = p + (p + 4 * q) - (p + 4 * (q - 1) + 4) := by ring
  _ = p + 1 - (p + 4 * 2 + 4) := by rw[h1, h2]
  _ = -11 := by ring

example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  calc
  a = a + (a + 2 * b + 3 * c) - (a + 2 * b + 3 * c) := by ring
  _ = a + (a + 2 * b + 3 * c) - (a + 2 * (b + 2 * c) - c) := by ring
  _ = a + 7 - (a + 2 * 3 - 1) := by rw[h1, h2, h3]
  _ = 2 := by ring

example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  calc
  u = ((4 * u + v) - v) / 4 := by ring
  _ = (3 - 2) / 4 := by rw[h1, h2]
  _ = 1/4 := by ring

example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 :=
  calc
  c = (4 * c + 1 - 1) - 3 * c := by ring
  _ = (3 * c - 2 - 1) - 3 * c := by rw[h1]
  _ = -3 := by ring

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 :=
  calc
  p = ((5 * p - 3 + 3) - 3 * p) / 2 := by ring
  _ = (3 * p + 1 + 3 - 3 * p) / 2 := by rw[h1]
  _ = 2 := by ring

example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 :=
  calc
  x = (2 * x + y) - (x + y) := by ring
  _ = 4 - 1 := by rw[h1, h2]
  _ = 3 := by ring

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 :=
  calc
  a = (2 * (a - b) + (a + 2 * b)) / 3 := by ring
  _ = (2 * 1 + 4) / 3 := by rw[h2, h1]
  _ = 2 := by ring

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  calc
  u ^ 2 + 3 * u + 1 = (u + 1 - 1)^2 + 3 * (u + 1 - 1) + 1 := by ring
  _ = (v - 1) ^ 2 + 3 * (v - 1) + 1 := by rw[h1]
  _ = v ^ 2 + v - 1 := by ring

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  calc
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 =
      (t^2 - 4 + 4)^2 + 3 * t * (t^2 - 4 + 4) - 3 * (t ^ 2 -4 + 4) - 2 * t - 2 := by ring
    _ = (0 + 4)^2 + 3 * t * (0 + 4) - 3 * (0 + 4) - 2 * t - 2 := by rw[ht]
    _ = 10 * t + 2 := by ring

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  have hx : x = 2 :=
    calc
    x = x + 3 - 3 := by ring
    _ = 5 - 3 := by rw[h1]
    _ = 2 := by ring
  have hy : 2 * y = 4:=
    calc
    2 * y = 2 * y + (2 * x - y * x) := by rw[h2]; ring
    _ = 2 * y + (2 * 2 - 2 * y) := by rw[hx]; ring
    _ = 4 := by ring
  calc
  y = (2 * y) / 2 := by ring
  _ = 4 / 2 := by rw[hy]
  _ = 2 := by ring


example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  calc
  p ^ 2 + q ^ 2 + r ^ 2 =
    (p + q + r )^2 - 2 * (p * q + p * r + q * r ) := by ring
  _ = 0 ^ 2 - 2 * 2 := by rw[h1, h2]
  _ = -4 := by ring

end Sec_1_3

-- Inequalities section 1.4
section Sec_1_4

-- 1.4.2
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by gcongr
    _ = 3 := by ring

-- 1.4.3
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  calc
    x + y ≤  -2 + x + 5 := by linarith
    _ ≤ -2 - 2 + 5 := by linarith
    _ = 1 := by ring
    _ < 2 := by norm_num

-- 1.4.4
example {u v x y A B : ℝ} (_h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by gcongr
    _ ≤ A * B + A * B + A * v := by gcongr
    _ ≤ A * B + A * B + 1 * v := by gcongr
    _ ≤ A * B + A * B + B * v := by gcongr
    _ < A * B + A * B + B * A := by gcongr
    _ = 3 * A * B := by ring

-- 1.4.5
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by ring
    _ ≥ 10 * t - 3 * t - 17 := by gcongr
    _ = 7 * t - 17 := by ring
    _ ≥ 7 * 10 - 17 := by gcongr
    _ ≥ 5 := by norm_num

-- 1.4.6
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc
  n ^ 2 = n * n := by ring
  _ ≥  5 * n := by gcongr
  _ = 2 * n + 3 * n := by ring
  _ ≥  2 * n + 3 * 5 := by gcongr
  _ = 2 * n + 15 := by ring
  _ > 2 * n + 11 := by norm_num

-- 1.4.8
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by nlinarith
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 1 := by gcongr
    _ < 3 := by norm_num

-- 1.4.9
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by nlinarith
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring
    _ ≤ 2 * (8 * b) + 8 * a + a := by gcongr
    _ = 7 * b + 9 * (a + b) := by ring
    _ ≤ 7 * b + 9 * 8 := by gcongr
    _ = 7 * b + 72 := by norm_num

-- 1.4.11
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc
    x = x + 3 - 3 := by ring
    _ ≥ 2 * y - 3 := by gcongr
    _ ≥ 2 * 1 - 3 := by gcongr
    _ >= -1 := by norm_num

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = (a + (a + 2 * b)) / 2 := by ring
    _ ≥ (3 + 4) / 2 := by gcongr
    _ ≥ 3 := by norm_num

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
  have hx0 : 0 ≤ x := by linarith
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = (x - 8) * x ^ 2 + 2 * x := by ring
    _ ≥ (9 - 8) * x ^ 2 + 2 * x := by gcongr
    _ = x ^ 2 +  2 * x := by ring
    _ ≥ 9^2 + 2 * 9 := by gcongr
    _ ≥ 3 := by norm_num

example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 := by
  calc
    n ^ 4 - 2 * n ^ 2 = n * (n ^ 3) - 2 * n ^ 2 := by ring
    _ ≥ 10 * n ^3 - 2 * n ^2 := by gcongr
    _ = 3 * n ^3 + (7 * n - 2) * n ^ 2 := by ring
    _ > 3 * n ^ 3 := by nlinarith

example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  calc
    n ^ 2 - 2 * n + 3 = (n - 2) * n + 3 := by ring
    _ ≥ (5 - 2) * n + 3 := by nlinarith
    _ = 3 * n + 3 := by norm_num
    _ ≥ 3 * 5 + 3 := by gcongr
    _ > 14 := by norm_num

example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  calc
    x ^ 2 - 2 * x = (x ^ 2 - 2 * x + 1) - 1 := by ring
    _ = (x - 1) ^ 2 - 1 := by ring
    _ ≥ 0 - 1 := by nlinarith
    _ = -1 := by norm_num

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
  calc
    a ^ 2 + b ^ 2 = (a - b) ^ 2 + 2 * a * b := by ring
    _ ≥ 2 * a * b := by nlinarith

end Sec_1_4
