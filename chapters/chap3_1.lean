import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic
import Mathlib.Algebra.Ring.Int.Parity

-- 3.1.1
example : Odd (7:ℤ) := by
  use 3  -- 2 * k + 1
  norm_num

-- 3.1.2
example : Odd (-3 : ℤ) := by
  dsimp[Odd]
  use -2
  norm_num

-- 3.1.4
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4 := by rw[hk]
    _ = 14 * k + 3 := by ring
  ring

-- 3.1.6
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  use 2 * m * n + m + 3 * n + 1
  calc
    x * y + 2 * y = (2 * m + 1) * (2 * n + 1) + 2 * (2 * n + 1) := by rw[hm, hn]
    _ = 4 * m * n + 2 * m + 6 * n + 3 := by ring
  ring

-- 3.1.7
example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  obtain ⟨k, hk⟩ := hm
  use 3 * k - 1
  calc
    3 * m - 5 = 3 * (2 * k + 1) - 5 := by rw[hk]
    _ = 6 * k - 2 := by ring
  ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨k, hk⟩ := hn
  use 2 * k^2 + 2 *k - 3
  calc
    n ^ 2 + 2 * n - 5 = (k + k) ^ 2 + 2 * (k + k) - 5 := by rw[hk]
    _ = 4 * k^2 + 4 * k - 5 := by ring
  ring

-- 3.1.10
example : Odd (-9 : ℤ) := by
  use -5
  norm_num

example : Even (26 : ℤ) := by
  use 13
  norm_num

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨k, hk⟩ := hm
  obtain ⟨j, hj⟩ := hn
  use k + j
  calc
    n + m = j + j  + (2 * k + 1) := by rw[hj, hk]
    _ = 2 * (k + j) + 1 := by ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨k, hk⟩ := hp
  obtain ⟨j, hj⟩ := hq
  use k - j - 2
  calc
    p - q - 4 = (2 * k + 1) - (j + j) - 4 := by rw[hk, hj]
    _ = 2 * (k - j - 2) + 1 := by ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨j, hj⟩ := hb
  use 3 * k + j - 1
  calc
    3 * a + b - 3 = 3 * (k + k) + (2 * j + 1) - 3 := by rw[hk, hj]
    _ = 2 * (3 * k + j - 1) := by ring
  ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨k, hk⟩ := hr
  obtain ⟨j, hj⟩ := hs
  use 3 * k - 5 * j - 1
  calc
    3 * r - 5 * s = 3 * (2 * k + 1) - 5 * (2 * j + 1) := by rw[hk, hj]
    _ = 2 * (3 * k - 5 * j - 1) := by ring
  ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨k, hk⟩ := hx
  use 4 * k^3 + 6 * k^2 + 3 * k
  calc
    x ^ 3 = (2 * k + 1) ^ 3 := by rw[hk]
    _ = 8 * k^3 + 12 * k^2 + 6 * k + 1 := by ring
    _ = 2 * (4 * k^3 + 6 * k^2 + 3 * k) + 1 := by ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  obtain ⟨k, hk⟩ := hn
  use 2 * k^2 - k
  calc
    n ^ 2 - 3 * n + 2 = (2 * k + 1) ^ 2 - 3 * (2 * k + 1) + 2 := by rw[hk]
    _ = 4 * k^2 - 2 * k := by ring
  ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨k, hk⟩ := ha
  use 2 * k^2 + 4 * k - 1
  calc
    a ^ 2 + 2 * a - 4 = (2 * k + 1) ^ 2 + 2 * (2 * k + 1) - 4 := by rw[hk]
    _ = 4 * k^2 + 8 * k - 1 := by ring
  ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨k, hk⟩ := hp
  use 2 * k^2 + 5 * k - 1
  calc
    p ^ 2 + 3 * p - 5 = (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 5 := by rw[hk]
    _ = 4 * k^2 + 10 * k - 1 := by ring
  ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨j, hj⟩ := hy
  use 2 * k * j + k + j
  calc
    x * y = (2 * k + 1) * (2 * j + 1) := by rw[hk, hj]
    _ = 4 * k * j + 2 * k + 2 * j + 1 := by ring
  ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  rcases Int.even_or_odd n with he | ho
  . obtain ⟨k, hk⟩ := he
    use 6* k^2 + 3 * k - 1
    calc
      3 * n ^ 2 + 3 * n - 1 = 3 * (k + k)^2 + 3 * (k + k) - 1 := by rw[hk]
      _ = 2 * (6 * k^2 + 3 * k - 1) + 1 := by ring
  . obtain ⟨k, hk⟩ := ho
    use 6 * k^2 + 9 * k + 2
    calc
      3 * n ^ 2 + 3 * n - 1 = 3 * (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 1  := by rw[hk]
      _ = 2 * (6 * k^2 + 9 * k + 2) + 1 := by ring

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  rcases Int.even_or_odd n with he | ho
  . obtain ⟨k, hk⟩ := he
    use 2 * k + 1
    apply And.intro
    . linarith
    . use k
  . obtain ⟨k, hk⟩ := ho
    use n
    apply And.intro
    . linarith
    . use k

example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  rcases Int.even_or_odd a with ha | ha'
  . rcases Int.even_or_odd b with hb | hb'
    . obtain ⟨k, hk⟩ := ha
      obtain ⟨j, hj⟩ := hb
      apply Or.inl
      use k - j
      linarith
    . rcases Int.even_or_odd c with hc | hc'
      . obtain ⟨k, hk⟩ := ha
        obtain ⟨j, hj⟩ := hc
        apply Or.inr
        apply Or.inl
        use k + j
        linarith
      . obtain ⟨k, hk⟩ := hb'
        obtain ⟨j, hj⟩ := hc'
        apply Or.inr
        apply Or.inr
        use k - j
        linarith
  . rcases Int.even_or_odd b with hb | hb'
    . rcases Int.even_or_odd c with hc | hc'
      . obtain ⟨k, hk⟩ := hb
        obtain ⟨j, hj⟩ := hc
        apply Or.inr
        apply Or.inr
        use k - j
        linarith
      . obtain ⟨k, hk⟩ := ha'
        obtain ⟨j, hj⟩ := hc'
        apply Or.inr
        apply Or.inl
        use k + j + 1
        linarith
    . obtain ⟨k, hk⟩ := ha'
      obtain ⟨j, hj⟩ := hb'
      apply Or.inl
      use k - j
      linarith
