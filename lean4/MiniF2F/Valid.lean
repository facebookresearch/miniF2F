/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng, Stanislas Polu, David Renshaw, OpenAI GPT-f

! This file was ported from Lean 3 source module valid
-/
import MiniF2F.Minif2fImport

open BigOperators

open Real

open Nat

open Topology

theorem amc12a_2019_p21 (z : ℂ) (h₀ : z = (1 + Complex.I) / Real.sqrt 2) :
    ((∑ k in Finset.Icc 1 12, z ^ k ^ 2) * ∑ k in Finset.Icc 1 12, 1 / z ^ k ^ 2) = 36 := by sorry
#align amc12a_2019_p21 amc12a_2019_p21

theorem amc12a_2015_p10 (x y : ℤ) (h₀ : 0 < y) (h₁ : y < x) (h₂ : x + y + x * y = 80) : x = 26 := by
  sorry
#align amc12a_2015_p10 amc12a_2015_p10

theorem amc12a_2008_p8 (x y : ℝ) (h₀ : 0 < x ∧ 0 < y) (h₁ : y ^ 3 = 1)
    (h₂ : 6 * x ^ 2 = 2 * (6 * y ^ 2)) : x ^ 3 = 2 * Real.sqrt 2 := by sorry
#align amc12a_2008_p8 amc12a_2008_p8

theorem mathd_algebra_182 (y : ℂ) : 7 * (3 * y + 2) = 21 * y + 14 := by ring_nf
#align mathd_algebra_182 mathd_algebra_182

theorem aime_1984_p5 (a b : ℝ) (h₀ : Real.logb 8 a + Real.logb 4 (b ^ 2) = 5)
    (h₁ : Real.logb 8 b + Real.logb 4 (a ^ 2) = 7) : a * b = 512 := by sorry
#align aime_1984_p5 aime_1984_p5

theorem mathd_numbertheory_780 (m x : ℕ) (h₀ : 10 ≤ m) (h₁ : m ≤ 99) (h₂ : 6 * x % m = 1)
    (h₃ : (x - 6 ^ 2) % m = 0) : m = 43 := by sorry
#align mathd_numbertheory_780 mathd_numbertheory_780

theorem mathd_algebra_116 (k x : ℝ) (h₀ : x = (13 - Real.sqrt 131) / 4)
    (h₁ : 2 * x ^ 2 - 13 * x + k = 0) : k = 19 / 4 :=
  by
  rw [h₀] at h₁
  rw [eq_comm.mp (add_eq_zero_iff_neg_eq.mp h₁)]
  norm_num
  rw [pow_two]
  rw [mul_sub]
  rw [sub_mul, sub_mul]
  rw [Real.mul_self_sqrt _]
  ring
  linarith
#align mathd_algebra_116 mathd_algebra_116

theorem mathd_numbertheory_13 (u v : ℕ) (S : Set ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 0 < n ∧ 14 * n % 100 = 46) (h₁ : IsLeast S u)
    (h₂ : IsLeast (S \ {u}) v) : (u + v : ℚ) / 2 = 64 := by sorry
#align mathd_numbertheory_13 mathd_numbertheory_13

theorem mathd_numbertheory_169 : Nat.gcd 20! 200000 = 40000 := by sorry
#align mathd_numbertheory_169 mathd_numbertheory_169

theorem amc12a_2009_p9 (a b c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f (x + 3) = 3 * x ^ 2 + 7 * x + 4)
    (h₁ : ∀ x, f x = a * x ^ 2 + b * x + c) : a + b + c = 2 := by sorry
#align amc12a_2009_p9 amc12a_2009_p9

theorem amc12a_2019_p9 (a : ℕ → ℚ) (h₀ : a 1 = 1) (h₁ : a 2 = 3 / 7)
    (h₂ : ∀ n, a (n + 2) = a n * a (n + 1) / (2 * a n - a (n + 1))) :
    ↑(a 2019).den + (a 2019).num = 8078 := by sorry
#align amc12a_2019_p9 amc12a_2019_p9

theorem mathd_algebra_13 (a b : ℝ)
    (h₀ : ∀ x, x - 3 ≠ 0 ∧ x - 5 ≠ 0 → 4 * x / (x ^ 2 - 8 * x + 15) = a / (x - 3) + b / (x - 5)) :
    a = -6 ∧ b = 10 := by sorry
#align mathd_algebra_13 mathd_algebra_13

theorem induction_sum2kp1npqsqm1 (n : ℕ) :
    ↑(∑ k in Finset.range n, 2 * k) + 3 = ↑(n + 1) ^ 2 - (1 : ℤ) := by sorry
#align induction_sum2kp1npqsqm1 induction_sum2kp1npqsqm1

theorem aime_1991_p6 (r : ℝ) (h₀ : (∑ k in Finset.Icc (19 : ℕ) 91, Int.floor (r + k / 100)) = 546) :
    Int.floor (100 * r) = 743 := by sorry
#align aime_1991_p6 aime_1991_p6

theorem mathd_numbertheory_149 :
    (∑ k in Finset.filter (fun x => x % 8 = 5 ∧ x % 6 = 3) (Finset.range 50), k) = 66 := by sorry
#align mathd_numbertheory_149 mathd_numbertheory_149

theorem imo_1984_p2 (a b : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : ¬7 ∣ a) (h₂ : ¬7 ∣ b) (h₃ : ¬7 ∣ a + b)
    (h₄ : 7 ^ 7 ∣ (a + b) ^ 7 - a ^ 7 - b ^ 7) : 19 ≤ a + b := by sorry
#align imo_1984_p2 imo_1984_p2

theorem amc12a_2008_p4 : (∏ k in Finset.Icc (1 : ℕ) 501, ((4 : ℝ) * k + 4) / (4 * k)) = 502 := by
  sorry
#align amc12a_2008_p4 amc12a_2008_p4

theorem imo_2006_p6 (a b c : ℝ) :
    a * b * (a ^ 2 - b ^ 2) + b * c * (b ^ 2 - c ^ 2) + c * a * (c ^ 2 - a ^ 2) ≤
      9 * Real.sqrt 2 / 32 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 :=
  by sorry
#align imo_2006_p6 imo_2006_p6

theorem mathd_algebra_462 : ((1 : ℚ) / 2 + 1 / 3) * (1 / 2 - 1 / 3) = 5 / 36 := by norm_num
#align mathd_algebra_462 mathd_algebra_462

theorem imo_1964_p1_2 (n : ℕ) : ¬7 ∣ 2 ^ n + 1 := by sorry
#align imo_1964_p1_2 imo_1964_p1_2

theorem mathd_numbertheory_221 (S : Finset ℕ)
    (h₀ : ∀ x : ℕ, x ∈ S ↔ 0 < x ∧ x < 1000 ∧ x.divisors.card = 3) : S.card = 11 := by sorry
#align mathd_numbertheory_221 mathd_numbertheory_221

theorem mathd_numbertheory_64 : IsLeast { x : ℕ | 30 * x ≡ 42 [MOD 47] } 39 := by sorry
#align mathd_numbertheory_64 mathd_numbertheory_64

theorem imo_1987_p4 (f : ℕ → ℕ) : ∃ n, f (f n) ≠ n + 1987 := by sorry
#align imo_1987_p4 imo_1987_p4

theorem mathd_numbertheory_33 (n : ℕ) (h₀ : n < 398) (h₁ : n * 7 % 398 = 1) : n = 57 := by sorry
#align mathd_numbertheory_33 mathd_numbertheory_33

theorem amc12_2001_p9 (f : ℝ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x / y) (h₁ : f 500 = 3) :
    f 600 = 5 / 2 := by
  specialize h₀ 500 _ (6 / 5) _
  · linarith
  · linarith
  calc
    f 600 = f (500 * (6 / 5)) := by
      congr
      norm_num
    _ = f 500 / (6 / 5) := by rw [h₀]
    _ = 3 / (6 / 5) := by rw [h₁]
    _ = 5 / 2 := by norm_num
    
#align amc12_2001_p9 amc12_2001_p9

theorem imo_1965_p1 (x : ℝ) (h₀ : 0 ≤ x) (h₁ : x ≤ 2 * π)
    (h₂ :
      2 * Real.cos x ≤ abs (Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))))
    (h₃ : abs (Real.sqrt (1 + Real.sin (2 * x)) - Real.sqrt (1 - Real.sin (2 * x))) ≤ Real.sqrt 2) :
    π / 4 ≤ x ∧ x ≤ 7 * π / 4 := by sorry
#align imo_1965_p1 imo_1965_p1

theorem mathd_numbertheory_48 (b : ℕ) (h₀ : 0 < b) (h₁ : 3 * b ^ 2 + 2 * b + 1 = 57) : b = 4 := by
  nlinarith
#align mathd_numbertheory_48 mathd_numbertheory_48

theorem numbertheory_sqmod4in01d (a : ℤ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by sorry
#align numbertheory_sqmod4in01d numbertheory_sqmod4in01d

theorem mathd_numbertheory_466 : (∑ k in Finset.range 11, k) % 9 = 1 := by sorry
#align mathd_numbertheory_466 mathd_numbertheory_466

theorem mathd_algebra_48 (q e : ℂ) (h₀ : q = 9 - 4 * Complex.I) (h₁ : e = -3 - 4 * Complex.I) :
    q - e = 12 := by
  rw [h₀, h₁]
  ring
#align mathd_algebra_48 mathd_algebra_48

theorem amc12_2000_p15 (f : ℂ → ℂ) (h₀ : ∀ x, f (x / 3) = x ^ 2 + x + 1)
    (h₁ : Fintype (f ⁻¹' {7})) : (∑ y in (f ⁻¹' {7}).toFinset, y / 3) = -1 / 9 := by sorry
#align amc12_2000_p15 amc12_2000_p15

theorem mathd_numbertheory_132 : 2004 % 12 = 0 := by norm_num
#align mathd_numbertheory_132 mathd_numbertheory_132

theorem amc12a_2009_p5 (x : ℝ) (h₀ : x ^ 3 - (x + 1) * (x - 1) * x = 5) : x ^ 3 = 125 := by sorry
#align amc12a_2009_p5 amc12a_2009_p5

theorem mathd_numbertheory_188 : Nat.gcd 180 168 = 12 := by norm_num
#align mathd_numbertheory_188 mathd_numbertheory_188

theorem mathd_algebra_224 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ Real.sqrt n < 7 / 2 ∧ 2 < Real.sqrt n) : S.card = 8 := by sorry
#align mathd_algebra_224 mathd_algebra_224

theorem induction_divisibility_3divnto3m2n (n : ℕ) : 3 ∣ n ^ 3 + 2 * n := by sorry
#align induction_divisibility_3divnto3m2n induction_divisibility_3divnto3m2n

theorem induction_sum_1oktkp1 (n : ℕ) :
    (∑ k in Finset.range n, (1 : ℝ) / ((k + 1) * (k + 2))) = n / (n + 1) := by sorry
#align induction_sum_1oktkp1 induction_sum_1oktkp1

theorem mathd_numbertheory_32 (S : Finset ℕ) (h₀ : ∀ n : ℕ, n ∈ S ↔ n ∣ 36) : (∑ k in S, k) = 91 :=
  by sorry
#align mathd_numbertheory_32 mathd_numbertheory_32

theorem mathd_algebra_422 (x : ℝ) (σ : Equiv ℝ ℝ) (h₀ : ∀ x, σ.1 x = 5 * x - 12)
    (h₁ : σ.1 (x + 1) = σ.2 x) : x = 47 / 24 :=
  by
  field_simp [h₀, mul_add, add_mul, sub_add_cancel, mul_assoc, add_comm]
  have := congr_arg σ.to_fun h₁
  rw [h₀] at this
  rw [h₀] at this
  symm
  norm_num at this
  linarith
#align mathd_algebra_422 mathd_algebra_422

theorem amc12b_2002_p11 (a b : ℕ) (h₀ : Nat.Prime a) (h₁ : Nat.Prime b) (h₂ : Nat.Prime (a + b))
    (h₃ : Nat.Prime (a - b)) : Nat.Prime (a + b + (a - b + (a + b))) := by sorry
#align amc12b_2002_p11 amc12b_2002_p11

theorem mathd_algebra_73 (p q r x : ℂ) (h₀ : (x - p) * (x - q) = (r - p) * (r - q)) (h₁ : x ≠ r) :
    x = p + q - r := by sorry
#align mathd_algebra_73 mathd_algebra_73

theorem mathd_numbertheory_109 (v : ℕ → ℕ) (h₀ : ∀ n, v n = 2 * n - 1) :
    (∑ k in Finset.Icc 1 100, v k) % 7 = 4 :=
  by
  norm_num
  simp [h₀]
  have h₁ : Finset.Icc 1 100 = Finset.Ico 1 101 := rfl
  rw [h₁]
  norm_num [Finset.sum_Ico_succ_top]
#align mathd_numbertheory_109 mathd_numbertheory_109

theorem algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3 (x y z : ℤ)
    (h₀ : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = x * y * z) :
    x + y + z + 6 ∣ x ^ 3 + y ^ 3 + z ^ 3 := by sorry
#align algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3 algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3

theorem imo_1962_p4 (S : Set ℝ)
    (h₀ : S = { x : ℝ | Real.cos x ^ 2 + Real.cos (2 * x) ^ 2 + Real.cos (3 * x) ^ 2 = 1 }) :
    S =
      { x : ℝ |
        ∃ m : ℤ,
          x = π / 2 + m * π ∨
            x = π / 4 + m * π / 2 ∨ x = π / 6 + m * π / 6 ∨ x = 5 * π / 6 + m * π / 6 } :=
  by sorry
#align imo_1962_p4 imo_1962_p4

theorem mathd_numbertheory_236 : 1999 ^ 2000 % 5 = 1 := by sorry
#align mathd_numbertheory_236 mathd_numbertheory_236

theorem mathd_numbertheory_24 : (∑ k in Finset.Icc 1 9, 11 ^ k) % 100 = 59 :=
  by
  norm_num
  have h₁ : Finset.Icc 1 9 = Finset.Ico 1 10 := rfl
  rw [h₁]
  norm_num [Finset.sum_Ico_succ_top]
#align mathd_numbertheory_24 mathd_numbertheory_24

theorem algebra_amgm_prod1toneq1_sum1tongeqn (a : ℕ → NNReal) (n : ℕ)
    (h₀ : Finset.prod (Finset.range n) a = 1) : Finset.sum (Finset.range n) a ≥ n := by sorry
#align algebra_amgm_prod1toneq1_sum1tongeqn algebra_amgm_prod1toneq1_sum1tongeqn

theorem mathd_algebra_101 (x : ℝ) (h₀ : x ^ 2 - 5 * x - 4 ≤ 10) : x ≥ -2 ∧ x ≤ 7 := by
  constructor <;> nlinarith
#align mathd_algebra_101 mathd_algebra_101

theorem mathd_numbertheory_257 (x : ℕ) (h₀ : 1 ≤ x ∧ x ≤ 100)
    (h₁ : 77 ∣ (∑ k in Finset.range 101, k) - x) : x = 45 := by sorry
#align mathd_numbertheory_257 mathd_numbertheory_257

theorem amc12_2000_p5 (x p : ℝ) (h₀ : x < 2) (h₁ : abs (x - 2) = p) : x - p = 2 - 2 * p :=
  by
  suffices abs (x - 2) = -(x - 2) by
    rw [h₁] at this
    linarith
  apply abs_of_neg
  linarith
#align amc12_2000_p5 amc12_2000_p5

theorem mathd_algebra_547 (x y : ℝ) (h₀ : x = 5) (h₁ : y = 2) : Real.sqrt (x ^ 3 - 2 ^ y) = 11 := by
  sorry
#align mathd_algebra_547 mathd_algebra_547

theorem mathd_numbertheory_200 : 139 % 11 = 7 := by norm_num
#align mathd_numbertheory_200 mathd_numbertheory_200

theorem mathd_algebra_510 (x y : ℝ) (h₀ : x + y = 13) (h₁ : x * y = 24) :
    Real.sqrt (x ^ 2 + y ^ 2) = 11 := by sorry
#align mathd_algebra_510 mathd_algebra_510

theorem mathd_algebra_140 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : ∀ x, 24 * x ^ 2 - 19 * x - 35 = (a * x - 5) * (2 * (b * x) + c)) : a * b - 3 * c = -9 :=
  by
  have h₂ := h₁ 0
  have h₂ := h₁ 1
  have h₃ := h₁ (-1)
  linarith
#align mathd_algebra_140 mathd_algebra_140

theorem mathd_algebra_455 (x : ℝ) (h₀ : 2 * (2 * (2 * (2 * x))) = 48) : x = 3 := by linarith
#align mathd_algebra_455 mathd_algebra_455

theorem mathd_numbertheory_45 : Nat.gcd 6432 132 + 11 = 23 :=
  by
  simp only [Nat.gcd_comm]
  norm_num
#align mathd_numbertheory_45 mathd_numbertheory_45

theorem aime_1994_p4 (n : ℕ) (h₀ : 0 < n)
    (h₀ : (∑ k in Finset.Icc 1 n, Int.floor (Real.logb 2 k)) = 1994) : n = 312 := by sorry
#align aime_1994_p4 aime_1994_p4

theorem mathd_numbertheory_739 : 9! % 10 = 0 := by norm_num
#align mathd_numbertheory_739 mathd_numbertheory_739

theorem mathd_algebra_245 (x : ℝ) (h₀ : x ≠ 0) :
    (4 / x)⁻¹ * (3 * x ^ 3 / x) ^ 2 * (1 / (2 * x))⁻¹ ^ 3 = 18 * x ^ 8 := by
  field_simp [show x ≠ 0 by simpa using h₀, mul_comm x] <;> ring
#align mathd_algebra_245 mathd_algebra_245

theorem algebra_apb4leq8ta4pb4 (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) :=
  by sorry
#align algebra_apb4leq8ta4pb4 algebra_apb4leq8ta4pb4

theorem mathd_algebra_28 (c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x ^ 2 + 5 * x + c)
    (h₁ : ∃ x, f x ≤ 0) : c ≤ 25 / 8 := by sorry
#align mathd_algebra_28 mathd_algebra_28

theorem mathd_numbertheory_543 : (∑ k in Nat.divisors (30 ^ 4), 1) - 2 = 123 := by sorry
#align mathd_numbertheory_543 mathd_numbertheory_543

theorem mathd_algebra_480 (f : ℝ → ℝ) (h₀ : ∀ x < 0, f x = -x ^ 2 - 1)
    (h₁ : ∀ x, 0 ≤ x ∧ x < 4 → f x = 2) (h₂ : ∀ x ≥ 4, f x = Real.sqrt x) : f π = 2 := by sorry
#align mathd_algebra_480 mathd_algebra_480

theorem mathd_algebra_69 (rows seats : ℕ) (h₀ : rows * seats = 450)
    (h₁ : (rows + 5) * (seats - 3) = 450) : rows = 25 := by sorry
#align mathd_algebra_69 mathd_algebra_69

theorem mathd_algebra_433 (f : ℝ → ℝ) (h₀ : ∀ x, f x = 3 * Real.sqrt (2 * x - 7) - 8) : f 8 = 1 :=
  by sorry
#align mathd_algebra_433 mathd_algebra_433

theorem mathd_algebra_126 (x y : ℝ) (h₀ : 2 * 3 = x - 9) (h₁ : 2 * -5 = y + 1) : x = 15 ∧ y = -11 :=
  by constructor <;> linarith
#align mathd_algebra_126 mathd_algebra_126

theorem aimeII_2020_p6 (t : ℕ → ℚ) (h₀ : t 1 = 20) (h₁ : t 2 = 21)
    (h₂ : ∀ n ≥ 3, t n = (5 * t (n - 1) + 1) / (25 * t (n - 2))) :
    ↑(t 2020).den + (t 2020).num = 626 := by sorry
#align aimeII_2020_p6 aimeII_2020_p6

theorem amc12a_2008_p2 (x : ℝ) (h₀ : x * (1 / 2 + 2 / 3) = 1) : x = 6 / 7 := by linarith
#align amc12a_2008_p2 amc12a_2008_p2

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ≠ » 0) -/
theorem mathd_algebra_35 (p q : ℝ → ℝ) (h₀ : ∀ x, p x = 2 - x ^ 2)
    (h₁ : ∀ (x) (_ : x ≠ 0), q x = 6 / x) : p (q 2) = -7 :=
  by
  rw [h₀, h₁]
  ring
  linarith
#align mathd_algebra_35 mathd_algebra_35

theorem algebra_amgm_faxinrrp2msqrt2geq2mxm1div2x :
    ∀ x > 0, 2 - Real.sqrt 2 ≥ 2 - x - 1 / (2 * x) :=
  by
  intro x h
  suffices : Real.sqrt 2 ≤ x + 1 / (2 * x)
  linarith
  have h₀ :=
    (NNReal.geom_mean_le_arith_mean2_weighted (1 / 2) (1 / 2) (Real.toNNReal x)
        (Real.toNNReal (1 / (2 * x))))
      _
  norm_num at h₀
  rw [← NNReal.mul_rpow, ← Real.toNNReal_mul] at h₀
  have h₁ : x * (1 / (2 * x)) = 1 / 2 :=
    by
    rw [mul_div_left_comm, one_mul, div_eq_div_iff]
    ring
    apply ne_of_gt
    repeat' linarith
  rw [h₁] at h₀
  have h₂ : Real.toNNReal (1 / 2) ^ ((1 : ℝ) / 2) = Real.toNNReal ((1 / 2) ^ ((1 : ℝ) / 2)) :=
    by
    refine' nnreal.coe_eq.mp _
    rw [Real.coe_toNNReal, NNReal.coe_rpow, Real.coe_toNNReal]
    linarith
    apply le_of_lt
    exact Real.rpow_pos_of_pos (by norm_num) _
  rw [h₂, ← NNReal.coe_le_coe, Real.coe_toNNReal, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul,
    Real.coe_toNNReal, Real.coe_toNNReal] at h₀
  have h₃ :
    2 * (1 / 2) ^ ((1 : ℝ) / 2) ≤
      2 * (↑((1 : NNReal) / 2) * x + ↑((1 : NNReal) / 2) * (1 / (2 * x))) :=
    by
    refine' (mul_le_mul_left _).mpr _
    linarith
    exact h₀
  have h₄ : 2 * (1 / 2) ^ ((1 : ℝ) / 2) = Real.sqrt 2 :=
    by
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq]
    calc
      (2 : ℝ) * (1 / (2 : ℝ)) ^ (1 / (2 : ℝ)) * ((2 : ℝ) * (1 / (2 : ℝ)) ^ (1 / (2 : ℝ))) =
          (2 : ℝ) * (2 : ℝ) * ((1 / (2 : ℝ)) ^ (1 / (2 : ℝ)) * (1 / (2 : ℝ)) ^ (1 / (2 : ℝ))) :=
        by ring
      _ = (2 : ℝ) * (2 : ℝ) * (1 / (2 : ℝ)) ^ (1 / (2 : ℝ) + 1 / (2 : ℝ)) :=
        by
        rw [Real.rpow_add]
        linarith
      _ = (2 : ℝ) * (2 : ℝ) * (1 / (2 : ℝ)) ^ (1 : ℝ) :=
        by
        congr
        apply add_halves
      _ = (2 : ℝ) * (2 : ℝ) * (1 / (2 : ℝ)) := by simp
      _ = (2 : ℝ) := by norm_num
      
    linarith
    apply le_of_lt
    norm_num
    exact Real.rpow_pos_of_pos (by norm_num) _
  have h₅ : 2 * (↑((1 : NNReal) / 2) * x + ↑((1 : NNReal) / 2) * (1 / (2 * x))) = x + 1 / (2 * x) :=
    by
    rw [mul_add, ← mul_assoc, ← mul_assoc, NNReal.coe_div, NNReal.coe_one]
    have h₆ : ↑(2 : NNReal) = (2 : ℝ) := rfl
    rw [h₆]
    ring
  rwa [← h₄, ← h₅]
  apply div_nonneg_iff.mpr
  left
  constructor
  repeat' linarith
  apply le_of_lt
  exact Real.rpow_pos_of_pos (by norm_num) _
  apply add_halves
#align algebra_amgm_faxinrrp2msqrt2geq2mxm1div2x algebra_amgm_faxinrrp2msqrt2geq2mxm1div2x

theorem mathd_numbertheory_335 (n : ℕ) (h₀ : n % 7 = 5) : 5 * n % 7 = 4 := by sorry
#align mathd_numbertheory_335 mathd_numbertheory_335

theorem mathd_numbertheory_35 (S : Finset ℕ) (h₀ : ∀ n : ℕ, n ∣ Nat.sqrt 196) :
    (∑ k in S, k) = 24 := by sorry
#align mathd_numbertheory_35 mathd_numbertheory_35

theorem amc12a_2021_p7 (x y : ℝ) : 1 ≤ (x * y - 1) ^ 2 + (x + y) ^ 2 :=
  by
  ring_nf
  nlinarith
#align amc12a_2021_p7 amc12a_2021_p7

theorem mathd_algebra_327 (a : ℝ) (h₀ : 1 / 5 * abs (9 + 2 * a) < 1) : -7 < a ∧ a < -2 :=
  by
  have h₁ := (mul_lt_mul_left (show 0 < (5 : ℝ) by linarith)).mpr h₀
  have h₂ : abs (9 + 2 * a) < 5; linarith
  have h₃ := abs_lt.mp h₂
  cases' h₃ with h₃ h₄
  constructor <;> nlinarith
#align mathd_algebra_327 mathd_algebra_327

theorem aime_1984_p15 (x y z w : ℝ)
    (h₀ :
      x ^ 2 / (2 ^ 2 - 1) + y ^ 2 / (2 ^ 2 - 3 ^ 2) + z ^ 2 / (2 ^ 2 - 5 ^ 2) +
          w ^ 2 / (2 ^ 2 - 7 ^ 2) =
        1)
    (h₁ :
      x ^ 2 / (4 ^ 2 - 1) + y ^ 2 / (4 ^ 2 - 3 ^ 2) + z ^ 2 / (4 ^ 2 - 5 ^ 2) +
          w ^ 2 / (4 ^ 2 - 7 ^ 2) =
        1)
    (h₂ :
      x ^ 2 / (6 ^ 2 - 1) + y ^ 2 / (6 ^ 2 - 3 ^ 2) + z ^ 2 / (6 ^ 2 - 5 ^ 2) +
          w ^ 2 / (6 ^ 2 - 7 ^ 2) =
        1)
    (h₃ :
      x ^ 2 / (8 ^ 2 - 1) + y ^ 2 / (8 ^ 2 - 3 ^ 2) + z ^ 2 / (8 ^ 2 - 5 ^ 2) +
          w ^ 2 / (8 ^ 2 - 7 ^ 2) =
        1) :
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 36 :=
  by
  revert x y z w h₀ h₁ h₂ h₃
  ring_nf
  intro x y z w h
  intro h
  intros <;> linarith
#align aime_1984_p15 aime_1984_p15

theorem algebra_amgm_sqrtxymulxmyeqxpy_xpygeq4 (x y : ℝ) (h₀ : 0 < x ∧ 0 < y) (h₁ : y ≤ x)
    (h₂ : Real.sqrt (x * y) * (x - y) = x + y) : x + y ≥ 4 := by sorry
#align algebra_amgm_sqrtxymulxmyeqxpy_xpygeq4 algebra_amgm_sqrtxymulxmyeqxpy_xpygeq4

theorem amc12a_2002_p21 (u : ℕ → ℕ) (h₀ : u 0 = 4) (h₁ : u 1 = 7)
    (h₂ : ∀ n ≥ 2, u (n + 2) = (u n + u (n + 1)) % 10) :
    ∀ n, (∑ k in Finset.range n, u k) > 10000 → 1999 ≤ n := by sorry
#align amc12a_2002_p21 amc12a_2002_p21

theorem mathd_algebra_192 (q e d : ℂ) (h₀ : q = 11 - 5 * Complex.I) (h₁ : e = 11 + 5 * Complex.I)
    (h₂ : d = 2 * Complex.I) : q * e * d = 292 * Complex.I :=
  by
  rw [h₀, h₁, h₂]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring
#align mathd_algebra_192 mathd_algebra_192

theorem amc12b_2002_p6 (a b : ℝ) (h₀ : a ≠ 0 ∧ b ≠ 0)
    (h₁ : ∀ x, x ^ 2 + a * x + b = (x - a) * (x - b)) : a = 1 ∧ b = -2 :=
  by
  have h₂ := h₁ a
  have h₃ := h₁ b
  have h₄ := h₁ 0
  simp at *
  have h₅ : b * (1 - a) = 0; linarith
  simp at h₅
  cases' h₅ with h₅ h₆
  exfalso
  exact absurd h₅ h₀.2
  have h₆ : a = 1; linarith
  constructor
  exact h₆
  rw [h₆] at h₂
  linarith
#align amc12b_2002_p6 amc12b_2002_p6

theorem mathd_numbertheory_102 : 2 ^ 8 % 5 = 1 := by norm_num
#align mathd_numbertheory_102 mathd_numbertheory_102

theorem amc12a_2010_p22 (x : ℝ) : 49 ≤ ∑ k in Finset.Icc 1 119, abs (↑k * x - 1) := by sorry
#align amc12a_2010_p22 amc12a_2010_p22

theorem mathd_numbertheory_81 : 71 % 3 = 2 := by norm_num
#align mathd_numbertheory_81 mathd_numbertheory_81

theorem mathd_numbertheory_155 :
    Finset.card (Finset.filter (fun x => x % 19 = 7) (Finset.Icc 100 999)) = 48 := by sorry
#align mathd_numbertheory_155 mathd_numbertheory_155

theorem imo_1978_p5 (n : ℕ) (a : ℕ → ℕ) (h₀ : Function.Injective a) (h₁ : a 0 = 0) (h₂ : 0 < n) :
    (∑ k in Finset.Icc 1 n, (1 : ℝ) / k) ≤ ∑ k in Finset.Icc 1 n, a k / k ^ 2 := by sorry
#align imo_1978_p5 imo_1978_p5

theorem amc12a_2017_p7 (f : ℕ → ℝ) (h₀ : f 1 = 2) (h₁ : ∀ n, 1 < n ∧ Even n → f n = f (n - 1) + 1)
    (h₂ : ∀ n, 1 < n ∧ Odd n → f n = f (n - 2) + 2) : f 2017 = 2018 := by sorry
#align amc12a_2017_p7 amc12a_2017_p7

theorem mathd_numbertheory_42 (S : Set ℕ) (u v : ℕ) (h₀ : ∀ a : ℕ, a ∈ S ↔ 0 < a ∧ 27 * a % 40 = 17)
    (h₁ : IsLeast S u) (h₂ : IsLeast (S \ {u}) v) : u + v = 62 := by sorry
#align mathd_numbertheory_42 mathd_numbertheory_42

theorem mathd_algebra_110 (q e : ℂ) (h₀ : q = 2 - 2 * Complex.I) (h₁ : e = 5 + 5 * Complex.I) :
    q * e = 20 := by
  rw [h₀, h₁]
  ring_nf
  rw [pow_two, Complex.I_mul_I]
  ring
#align mathd_algebra_110 mathd_algebra_110

theorem amc12b_2021_p21 (S : Finset ℝ)
    (h₀ : ∀ x : ℝ, x ∈ S ↔ 0 < x ∧ x ^ (2 : ℝ) ^ Real.sqrt 2 = Real.sqrt 2 ^ (2 : ℝ) ^ x) :
    (↑2 ≤ ∑ k in S, k) ∧ (∑ k in S, k) < 6 := by sorry
#align amc12b_2021_p21 amc12b_2021_p21

theorem mathd_algebra_405 (S : Finset ℕ) (h₀ : ∀ x, x ∈ S ↔ 0 < x ∧ x ^ 2 + 4 * x + 4 < 20) :
    S.card = 2 := by sorry
#align mathd_algebra_405 mathd_algebra_405

theorem numbertheory_sumkmulnckeqnmul2pownm1 (n : ℕ) (h₀ : 0 < n) :
    (∑ k in Finset.Icc 1 n, k * Nat.choose n k) = n * 2 ^ (n - 1) := by sorry
#align numbertheory_sumkmulnckeqnmul2pownm1 numbertheory_sumkmulnckeqnmul2pownm1

theorem mathd_algebra_393 (σ : Equiv ℝ ℝ) (h₀ : ∀ x, σ.1 x = 4 * x ^ 3 + 1) : σ.2 33 = 2 := by sorry
#align mathd_algebra_393 mathd_algebra_393

theorem amc12b_2004_p3 (x y : ℕ) (h₀ : 2 ^ x * 3 ^ y = 1296) : x + y = 8 := by sorry
#align amc12b_2004_p3 amc12b_2004_p3

theorem mathd_numbertheory_303 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 2 ≤ n ∧ 171 ≡ 80 [MOD n] ∧ 468 ≡ 13 [MOD n]) : (∑ k in S, k) = 111 := by
  sorry
#align mathd_numbertheory_303 mathd_numbertheory_303

theorem mathd_algebra_151 : Int.ceil (Real.sqrt 27) - Int.floor (Real.sqrt 26) = 1 := by sorry
#align mathd_algebra_151 mathd_algebra_151

theorem amc12a_2011_p18 (x y : ℝ) (h₀ : abs (x + y) + abs (x - y) = 2) :
    x ^ 2 - 6 * x + y ^ 2 ≤ 8 := by sorry
#align amc12a_2011_p18 amc12a_2011_p18

theorem mathd_algebra_15 (s : ℕ → ℕ → ℕ)
    (h₀ : ∀ a b, 0 < a ∧ 0 < b → s a b = a ^ (b : ℕ) + b ^ (a : ℕ)) : s 2 6 = 100 :=
  by
  rw [h₀]
  rfl
  norm_num
#align mathd_algebra_15 mathd_algebra_15

theorem mathd_numbertheory_211 :
    Finset.card (Finset.filter (fun n => 6 ∣ 4 * ↑n - (2 : ℤ)) (Finset.range 60)) = 20 :=
  by-- apply le_antisymm,
  -- -- haveI := classical.prop_decidable,
  -- swap,
  -- dec_trivial!,
  -- apply le_trans,
  -- swap,
  -- apply nat.le_of_dvd,
  -- { norm_num, },
  -- -- haveI := classical.dec,
  -- simp,
  sorry
#align mathd_numbertheory_211 mathd_numbertheory_211

theorem mathd_numbertheory_640 : (91145 + 91146 + 91147 + 91148) % 4 = 2 := by norm_num
#align mathd_numbertheory_640 mathd_numbertheory_640

theorem amc12b_2003_p6 (a r : ℝ) (u : ℕ → ℝ) (h₀ : ∀ k, u k = a * r ^ k) (h₁ : u 1 = 2)
    (h₂ : u 3 = 6) : u 0 = 2 / Real.sqrt 3 ∨ u 0 = -(2 / Real.sqrt 3) := by sorry
#align amc12b_2003_p6 amc12b_2003_p6

theorem algebra_2rootsintpoly_am10tap11eqasqpam110 (a : ℂ) :
    (a - 10) * (a + 11) = a ^ 2 + a - 110 := by ring
#align algebra_2rootsintpoly_am10tap11eqasqpam110 algebra_2rootsintpoly_am10tap11eqasqpam110

theorem aime_1991_p1 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : x * y + (x + y) = 71)
    (h₂ : x ^ 2 * y + x * y ^ 2 = 880) : x ^ 2 + y ^ 2 = 146 := by sorry
#align aime_1991_p1 aime_1991_p1

theorem mathd_algebra_43 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x + b) (h₁ : f 7 = 4)
    (h₂ : f 6 = 3) : f 3 = 0 := by
  rw [h₀] at *
  linarith
#align mathd_algebra_43 mathd_algebra_43

theorem imo_1988_p6 (a b : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a * b + 1 ∣ a ^ 2 + b ^ 2) :
    ∃ x : ℕ, (x ^ 2 : ℝ) = (a ^ 2 + b ^ 2) / (a * b + 1) := by sorry
#align imo_1988_p6 imo_1988_p6

theorem aime_1996_p5 (a b c r s t : ℝ) (f g : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 3 + 3 * x ^ 2 + 4 * x - 11) (h₁ : ∀ x, g x = x ^ 3 + r * x ^ 2 + s * x + t)
    (h₂ : f a = 0) (h₃ : f b = 0) (h₄ : f c = 0) (h₅ : g (a + b) = 0) (h₆ : g (b + c) = 0)
    (h₇ : g (c + a) = 0) (h₈ : List.Pairwise (· ≠ ·) [a, b, c]) : t = 23 := by sorry
#align aime_1996_p5 aime_1996_p5

theorem mathd_algebra_55 (q p : ℝ) (h₀ : q = 2 - 4 + 6 - 8 + 10 - 12 + 14)
    (h₁ : p = 3 - 6 + 9 - 12 + 15 - 18 + 21) : q / p = 2 / 3 :=
  by
  rw [h₀, h₁]
  ring
#align mathd_algebra_55 mathd_algebra_55

theorem algebra_sqineq_2at2pclta2c2p41pc (a c : ℝ) :
    2 * a * (2 + c) ≤ a ^ 2 + c ^ 2 + 4 * (1 + c) :=
  by
  suffices : 0 ≤ (c - a) ^ 2 + 2 ^ 2 + 2 * 2 * (c - a); nlinarith
  suffices : 0 ≤ (c - a + 2) ^ 2; nlinarith
  exact pow_two_nonneg (c - a + 2)
#align algebra_sqineq_2at2pclta2c2p41pc algebra_sqineq_2at2pclta2c2p41pc

theorem mathd_numbertheory_43 : IsGreatest { n : ℕ | 15 ^ n ∣ 942! } 233 := by sorry
#align mathd_numbertheory_43 mathd_numbertheory_43

theorem mathd_algebra_214 (a : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * (x - 2) ^ 2 + 3) (h₁ : f 4 = 4) :
    f 6 = 7 := by
  revert h₁
  simp [h₀]
  intro
  nlinarith
#align mathd_algebra_214 mathd_algebra_214

theorem mathd_algebra_96 (x y z a : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (h₁ : Real.log x - Real.log y = a) (h₂ : Real.log y - Real.log z = 15)
    (h₃ : Real.log z - Real.log x = -7) : a = -8 := by nlinarith [h₁, h₂, h₃]
#align mathd_algebra_96 mathd_algebra_96

theorem amc12_2001_p2 (a b n : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9) (h₂ : n = 10 * a + b)
    (h₃ : n = a * b + a + b) : b = 9 := by
  rw [h₂] at h₃
  simp at h₃
  have h₄ : 10 * a = (b + 1) * a; linarith
  simp at h₄
  cases' h₄ with h₅ h₆
  linarith
  exfalso
  simp_all [le_refl]
#align amc12_2001_p2 amc12_2001_p2

theorem mathd_algebra_185 (s : Finset ℤ) (f : ℤ → ℤ) (h₀ : ∀ x, f x = abs (x + 4))
    (h₁ : ∀ x, x ∈ s ↔ f x < 9) : s.card = 17 := by sorry
#align mathd_algebra_185 mathd_algebra_185

theorem algebra_binomnegdiscrineq_10alt28asqp1 (a : ℝ) : 10 * a ≤ 28 * a ^ 2 + 1 := by sorry
#align algebra_binomnegdiscrineq_10alt28asqp1 algebra_binomnegdiscrineq_10alt28asqp1

theorem mathd_numbertheory_284 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
    (h₁ : 10 * a + b = 2 * (a + b)) : 10 * a + b = 18 := by sorry
#align mathd_numbertheory_284 mathd_numbertheory_284

theorem amc12a_2009_p2 : 1 + 1 / (1 + 1 / (1 + 1)) = (5 : ℚ) / 3 := by norm_num
#align amc12a_2009_p2 amc12a_2009_p2

theorem mathd_numbertheory_709 (n : ℕ) (h₀ : 0 < n) (h₁ : Finset.card (Nat.divisors (2 * n)) = 28)
    (h₂ : Finset.card (Nat.divisors (3 * n)) = 30) : Finset.card (Nat.divisors (6 * n)) = 35 := by
  sorry
#align mathd_numbertheory_709 mathd_numbertheory_709

theorem amc12a_2013_p8 (x y : ℝ) (h₀ : x ≠ 0) (h₁ : y ≠ 0) (h₂ : x ≠ y)
    (h₃ : x + 2 / x = y + 2 / y) : x * y = 2 := by sorry
#align amc12a_2013_p8 amc12a_2013_p8

theorem mathd_numbertheory_461 (n : ℕ)
    (h₀ : n = Finset.card (Finset.filter (fun x => gcd x 8 = 1) (Finset.Icc 1 7))) :
    3 ^ n % 8 = 1 := by sorry
#align mathd_numbertheory_461 mathd_numbertheory_461

theorem mathd_algebra_59 (b : ℝ) (h₀ : (4 : ℝ) ^ b + 2 ^ 3 = 12) : b = 1 :=
  by
  have h₁ : (4 : ℝ) ^ b = 4
  linarith
  by_contra h
  clear h₀
  change b ≠ 1 at h
  by_cases b₀ : b < 1
  have key₁ : (4 : ℝ) ^ b < (4 : ℝ) ^ (1 : ℝ) :=
    by
    apply Real.rpow_lt_rpow_of_exponent_lt _ _
    linarith
    exact b₀
  simp at key₁
  have key₂ : (4 : ℝ) ^ b ≠ (4 : ℝ) := ne_of_lt key₁
  exact h (False.ndrec (b = 1) (key₂ h₁))
  have key₃ : 1 < b := by
    refine' h.symm.le_iff_lt.mp _
    exact not_lt.mp b₀
  have key₄ : (4 : ℝ) ^ (1 : ℝ) < (4 : ℝ) ^ b :=
    by
    apply Real.rpow_lt_rpow_of_exponent_lt _ _
    linarith
    exact key₃
  simp at key₄
  have key₂ : (4 : ℝ) ^ b ≠ (4 : ℝ) := by
    rw [ne_comm]
    exact ne_of_lt key₄
  exact h (False.ndrec (b = 1) (key₂ h₁))
#align mathd_algebra_59 mathd_algebra_59

theorem mathd_algebra_234 (d : ℝ) (h₀ : 27 / 125 * d = 9 / 25) : 3 / 5 * d ^ 3 = 25 / 9 :=
  by
  field_simp
  rw [mul_right_comm, pow_succ, mul_comm]
  · nlinarith
#align mathd_algebra_234 mathd_algebra_234

theorem imo_1973_p3 (a b : ℝ) (h₀ : ∃ x, x ^ 4 + a * x ^ 3 + b * x ^ 2 + a * x + 1 = 0) :
    4 / 5 ≤ a ^ 2 + b ^ 2 := by sorry
#align imo_1973_p3 imo_1973_p3

theorem amc12b_2020_p5 (a b : ℕ) (h₀ : (5 : ℚ) / 8 * b = 2 / 3 * a + 7)
    (h₁ : (b : ℚ) - 5 / 8 * b = a - 2 / 3 * a + 7) : a = 42 := by sorry
#align amc12b_2020_p5 amc12b_2020_p5

theorem numbertheory_sqmod3in01d (a : ℤ) : a ^ 2 % 3 = 0 ∨ a ^ 2 % 3 = 1 := by sorry
#align numbertheory_sqmod3in01d numbertheory_sqmod3in01d

theorem mathd_algebra_131 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x ^ 2 - 7 * x + 2)
    (h₁ : f a = 0) (h₂ : f b = 0) (h₃ : a ≠ b) : 1 / (a - 1) + 1 / (b - 1) = -1 := by sorry
#align mathd_algebra_131 mathd_algebra_131

theorem amc12b_2003_p17 (x y : ℝ) (h₀ : 0 < x ∧ 0 < y) (h₁ : Real.log (x * y ^ 3) = 1)
    (h₂ : Real.log (x ^ 2 * y) = 1) : Real.log (x * y) = 3 / 5 := by sorry
#align amc12b_2003_p17 amc12b_2003_p17

theorem mathd_algebra_536 : ↑3! * ((2 : ℝ) ^ 3 + Real.sqrt 9) / 2 = (33 : ℝ) := by sorry
#align mathd_algebra_536 mathd_algebra_536

theorem mathd_algebra_22 : Real.logb (5 ^ 2) (5 ^ 4) = 2 := by sorry
#align mathd_algebra_22 mathd_algebra_22

theorem numbertheory_xsqpysqintdenomeq (x y : ℚ) (h₀ : (x ^ 2 + y ^ 2).den = 1) : x.den = y.den :=
  by sorry
#align numbertheory_xsqpysqintdenomeq numbertheory_xsqpysqintdenomeq

theorem aimeII_2001_p3 (x : ℕ → ℤ) (h₀ : x 1 = 211) (h₂ : x 2 = 375) (h₃ : x 3 = 420)
    (h₄ : x 4 = 523) (h₆ : ∀ n ≥ 5, x n = x (n - 1) - x (n - 2) + x (n - 3) - x (n - 4)) :
    x 531 + x 753 + x 975 = 898 := by sorry
#align aimeII_2001_p3 aimeII_2001_p3

theorem mathd_numbertheory_22 (b : ℕ) (h₀ : b < 10)
    (h₁ : Nat.sqrt (10 * b + 6) * Nat.sqrt (10 * b + 6) = 10 * b + 6) : b = 3 ∨ b = 1 := by sorry
#align mathd_numbertheory_22 mathd_numbertheory_22

theorem aime_1987_p8 :
    IsGreatest { n : ℕ | 0 < n ∧ ∃! k : ℕ, (8 : ℝ) / 15 < n / (n + k) ∧ (n : ℝ) / (n + k) < 7 / 13 }
      112 :=
  by sorry
#align aime_1987_p8 aime_1987_p8

theorem mathd_numbertheory_136 (n : ℕ) (h₀ : 123 * n + 17 = 39500) : n = 321 := by linarith
#align mathd_numbertheory_136 mathd_numbertheory_136

theorem amc12_2000_p11 (a b : ℝ) (h₀ : a ≠ 0 ∧ b ≠ 0) (h₁ : a * b = a - b) :
    a / b + b / a - a * b = 2 := by
  field_simp [h₀.1, h₀.2]
  simp only [h₁, mul_comm, mul_sub]
  ring
#align amc12_2000_p11 amc12_2000_p11

theorem amc12b_2003_p9 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x + b) (h₁ : f 6 - f 2 = 12) :
    f 12 - f 2 = 30 := by
  revert h₁
  simp only [h₀]
  intro
  linarith
#align amc12b_2003_p9 amc12b_2003_p9

theorem algebra_2complexrootspoly_xsqp49eqxp7itxpn7i (x : ℂ) :
    x ^ 2 + 49 = (x + 7 * Complex.I) * (x + -7 * Complex.I) :=
  by
  ring_nf
  rw [pow_two, pow_two, Complex.I_mul_I]
  ring
#align algebra_2complexrootspoly_xsqp49eqxp7itxpn7i algebra_2complexrootspoly_xsqp49eqxp7itxpn7i

theorem mathd_numbertheory_198 : 5 ^ 2005 % 100 = 25 := by sorry
#align mathd_numbertheory_198 mathd_numbertheory_198

theorem mathd_algebra_149 (f : ℝ → ℝ) (h₀ : ∀ x < -5, f x = x ^ 2 + 5)
    (h₁ : ∀ x ≥ -5, f x = 3 * x - 8) (h₂ : Fintype (f ⁻¹' {10})) :
    (∑ k in (f ⁻¹' {10}).toFinset, k) = 6 := by sorry
#align mathd_algebra_149 mathd_algebra_149

theorem mathd_algebra_132 (x : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 2) (h₁ : ∀ x, g x = x ^ 2)
    (h₂ : f (g x) = g (f x)) : x = -1 / 2 := by
  norm_num
  simp_all [-one_div]
  field_simp [h₁]
  linarith
#align mathd_algebra_132 mathd_algebra_132

theorem mathd_numbertheory_37 : Nat.lcm 9999 100001 = 90900909 :=
  by
  let e : Empty → Fin 1 → ℕ := fun _ => 1
  have : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
  unfold Nat.lcm
  have : Fintype.card (Fin 1) = 1 := Fintype.card_fin 1
  simp only [eq_comm] at this
  rw [this]
  simp [bit1]
  norm_num
#align mathd_numbertheory_37 mathd_numbertheory_37

theorem aime_1983_p9 (x : ℝ) (h₀ : 0 < x ∧ x < Real.pi) :
    12 ≤ (9 * (x ^ 2 * Real.sin x ^ 2) + 4) / (x * Real.sin x) :=
  by
  let y := x * Real.sin x
  rw [← mul_pow]
  change 12 ≤ (9 * y ^ 2 + 4) / y
  refine' (le_div_iff _).mpr _
  apply mul_pos h₀.1
  apply Real.sin_pos_of_pos_of_lt_pi h₀.1 h₀.2
  suffices : 0 ≤ (3 * y - 2) ^ 2; nlinarith
  exact pow_two_nonneg (3 * y - 2)
#align aime_1983_p9 aime_1983_p9

theorem mathd_algebra_37 (x y : ℝ) (h₀ : x + y = 7) (h₁ : 3 * x + y = 45) : x ^ 2 - y ^ 2 = 217 :=
  by nlinarith
#align mathd_algebra_37 mathd_algebra_37

theorem mathd_numbertheory_458 (n : ℕ) (h₀ : n % 8 = 7) : n % 4 = 3 := by sorry
#align mathd_numbertheory_458 mathd_numbertheory_458

theorem amc12a_2008_p15 (k : ℕ) (h₀ : k = 2008 ^ 2 + 2 ^ 2008) : (k ^ 2 + 2 ^ k) % 10 = 6 := by
  sorry
#align amc12a_2008_p15 amc12a_2008_p15

theorem mathd_numbertheory_301 (j : ℕ) (h₀ : 0 < j) : 3 * (7 * ↑j + 3) % 7 = 2 := by
  calc
    3 * (7 * ↑j + 3) % 7 = (3 * 3 + 3 * ↑j * 7) % 7 := by ring_nf
    _ = 3 * 3 % 7 := by apply Nat.add_mul_mod_self_right
    _ = 2 := by norm_num
    
#align mathd_numbertheory_301 mathd_numbertheory_301

theorem amc12a_2009_p15 (n : ℕ) (h₀ : 0 < n)
    (h₁ : (∑ k in Finset.Icc 1 n, ↑k * Complex.I ^ k) = 48 + 49 * Complex.I) : n = 97 := by sorry
#align amc12a_2009_p15 amc12a_2009_p15

theorem algebra_sqineq_36azm9asqle36zsq (z a : ℝ) : 36 * (a * z) - 9 * a ^ 2 ≤ 36 * z ^ 2 :=
  by
  suffices : 4 * (a * z) - a ^ 2 ≤ 4 * z ^ 2; nlinarith
  suffices : 0 ≤ (a - 2 * z) ^ 2; nlinarith
  exact pow_two_nonneg (a - 2 * z)
#align algebra_sqineq_36azm9asqle36zsq algebra_sqineq_36azm9asqle36zsq

theorem amc12a_2013_p7 (s : ℕ → ℝ) (h₀ : ∀ n, s (n + 2) = s (n + 1) + s n) (h₁ : s 9 = 110)
    (h₂ : s 7 = 42) : s 4 = 10 := by sorry
#align amc12a_2013_p7 amc12a_2013_p7

theorem mathd_algebra_104 (x : ℝ) (h₀ : 125 / 8 = x / 12) : x = 375 / 2 := by linarith
#align mathd_algebra_104 mathd_algebra_104

theorem mathd_numbertheory_252 : 7! % 23 = 3 := by sorry
#align mathd_numbertheory_252 mathd_numbertheory_252

theorem amc12a_2020_p21 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 5 ∣ n ∧ Nat.lcm 5! n = 5 * Nat.gcd 10! n) : S.card = 48 := by sorry
#align amc12a_2020_p21 amc12a_2020_p21

theorem mathd_algebra_493 (f : ℝ → ℝ) (h₀ : ∀ x, f x = x ^ 2 - 4 * Real.sqrt x + 1) :
    f (f 4) = 70 := by sorry
#align mathd_algebra_493 mathd_algebra_493

theorem numbertheory_nckeqnm1ckpnm1ckm1 (n k : ℕ) (h₀ : 0 < n ∧ 0 < k) (h₁ : k ≤ n) :
    Nat.choose n k = Nat.choose (n - 1) k + Nat.choose (n - 1) (k - 1) := by sorry
#align numbertheory_nckeqnm1ckpnm1ckm1 numbertheory_nckeqnm1ckpnm1ckm1

theorem algebra_3rootspoly_amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta (b c d a : ℂ) :
    (a - d) * (a - c) * (a - b) =
      -((a ^ 2 - (b + c) * a + c * b) * d) + (a ^ 2 - (b + c) * a + c * b) * a :=
  by ring
#align algebra_3rootspoly_amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta algebra_3rootspoly_amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta

theorem mathd_numbertheory_403 : (∑ k in Nat.properDivisors 198, k) = 270 := by sorry
#align mathd_numbertheory_403 mathd_numbertheory_403

theorem mathd_algebra_190 : ((3 : ℝ) / 8 + 7 / 8) / (4 / 5) = 25 / 16 := by norm_num
#align mathd_algebra_190 mathd_algebra_190

theorem mathd_numbertheory_269 : (2005 ^ 2 + 2005 ^ 0 + 2005 ^ 0 + 2005 ^ 5) % 100 = 52 := by sorry
#align mathd_numbertheory_269 mathd_numbertheory_269

theorem aime_1990_p2 :
    (52 + 6 * Real.sqrt 43) ^ ((3 : ℝ) / 2) - (52 - 6 * Real.sqrt 43) ^ ((3 : ℝ) / 2) = 828 := by
  sorry
#align aime_1990_p2 aime_1990_p2

theorem mathd_numbertheory_101 : 17 * 18 % 4 = 2 := by norm_num
#align mathd_numbertheory_101 mathd_numbertheory_101

theorem algebra_sqineq_4bap1lt4bsqpap1sq (a b : ℝ) : 4 * b * (a + 1) ≤ 4 * b ^ 2 + (a + 1) ^ 2 :=
  by
  suffices : 0 ≤ (2 * b - (a + 1)) ^ 2; nlinarith
  exact pow_two_nonneg (2 * b - (a + 1))
#align algebra_sqineq_4bap1lt4bsqpap1sq algebra_sqineq_4bap1lt4bsqpap1sq

theorem mathd_numbertheory_156 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (n + 7) (2 * n + 1) ≤ 13 := by sorry
#align mathd_numbertheory_156 mathd_numbertheory_156

theorem mathd_algebra_451 (σ : Equiv ℝ ℝ) (h₀ : σ.2 (-15) = 0) (h₁ : σ.2 0 = 3) (h₂ : σ.2 3 = 9)
    (h₃ : σ.2 9 = 20) : σ.1 (σ.1 9) = 0 :=
  by
  simp only [Equiv.invFun_as_coe, eq_comm] at h₀ h₁ h₂ h₃
  simp only [Equiv.toFun_as_coe]
  rw [← Equiv.apply_eq_iff_eq_symm_apply σ] at h₂
  rw [← Equiv.apply_eq_iff_eq_symm_apply σ] at h₁
  have h₄ := (Equiv.apply_eq_iff_eq σ).mpr h₂
  rw [h₁] at h₄
  exact h₄
#align mathd_algebra_451 mathd_algebra_451

theorem mathd_algebra_144 (a b c d : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) (h₀ : (c : ℤ) - b = d)
    (h₁ : (b : ℤ) - a = d) (h₂ : a + b + c = 60) (h₃ : a + b > c) : d < 10 := by sorry
#align mathd_algebra_144 mathd_algebra_144

theorem mathd_algebra_282 (f : ℝ → ℝ) (h₀ : ∀ x, ¬Irrational x → f x = abs (Int.floor x))
    (h₁ : ∀ x, Irrational x → f x = Int.ceil x ^ 2) :
    f (8 ^ (1 / 3)) + f (-Real.pi) + f (Real.sqrt 50) + f (9 / 2) = 79 := by sorry
#align mathd_algebra_282 mathd_algebra_282

theorem mathd_algebra_410 (x y : ℝ) (h₀ : y = x ^ 2 - 6 * x + 13) : 4 ≤ y := by sorry
#align mathd_algebra_410 mathd_algebra_410

theorem mathd_numbertheory_232 (x y z : ZMod 31) (h₀ : x = 3⁻¹) (h₁ : y = 5⁻¹)
    (h₂ : z = (x + y)⁻¹) : z = 29 := by sorry
#align mathd_numbertheory_232 mathd_numbertheory_232

theorem mathd_algebra_77 (a b : ℝ) (f : ℝ → ℝ) (h₀ : a ≠ 0 ∧ b ≠ 0) (h₁ : a ≠ b)
    (h₂ : ∀ x, f x = x ^ 2 + a * x + b) (h₃ : f a = 0) (h₄ : f b = 0) : a = 1 ∧ b = -2 := by sorry
#align mathd_algebra_77 mathd_algebra_77

theorem imo_1974_p5 (a b c d s : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : s = a / (a + b + d) + b / (a + b + c) + c / (b + c + d) + d / (a + c + d)) :
    1 < s ∧ s < 2 := by sorry
#align imo_1974_p5 imo_1974_p5

theorem aime_1988_p3 (x : ℝ) (h₀ : 0 < x)
    (h₁ : Real.logb 2 (Real.logb 8 x) = Real.logb 8 (Real.logb 2 x)) : Real.logb 2 x ^ 2 = 27 := by
  sorry
#align aime_1988_p3 aime_1988_p3

theorem mathd_numbertheory_530 (n k : ℕ) (h₀ : 0 < n ∧ 0 < k) (h₀ : (n : ℝ) / k < 6)
    (h₁ : (5 : ℝ) < n / k) : 22 ≤ Nat.lcm n k / Nat.gcd n k := by sorry
#align mathd_numbertheory_530 mathd_numbertheory_530

theorem mathd_algebra_109 (a b : ℝ) (h₀ : 3 * a + 2 * b = 12) (h₁ : a = 4) : b = 0 := by linarith
#align mathd_algebra_109 mathd_algebra_109

theorem imo_1967_p3 (k m n : ℕ) (c : ℕ → ℕ) (h₀ : 0 < k ∧ 0 < m ∧ 0 < n)
    (h₁ : ∀ s, c s = s * (s + 1)) (h₂ : Nat.Prime (k + m + 1)) (h₃ : n + 1 < k + m + 1) :
    (∏ i in Finset.Icc 1 n, c i) ∣ ∏ i in Finset.Icc 1 n, c (m + i) - c k := by sorry
#align imo_1967_p3 imo_1967_p3

theorem mathd_algebra_11 (a b : ℝ) (h₀ : a ≠ b) (h₁ : a ≠ 2 * b)
    (h₂ : (4 * a + 3 * b) / (a - 2 * b) = 5) : (a + 11 * b) / (a - b) = 2 :=
  by
  rw [eq_comm]
  refine' (eq_div_iff _).mpr _
  exact sub_ne_zero_of_ne h₀
  rw [eq_comm] at h₂
  suffices : a = 13 * b; linarith
  have key : 5 * (a - 2 * b) = 4 * a + 3 * b; rwa [(eq_div_iff (sub_ne_zero_of_ne h₁)).mp]
  linarith
#align mathd_algebra_11 mathd_algebra_11

theorem amc12a_2003_p1 (u v : ℕ → ℕ) (h₀ : ∀ n, u n = 2 * n + 2) (h₁ : ∀ n, v n = 2 * n + 1) :
    ((∑ k in Finset.range 2003, u k) - ∑ k in Finset.range 2003, v k) = 2003 := by sorry
#align amc12a_2003_p1 amc12a_2003_p1

theorem numbertheory_aneqprodakp4_anmsqrtanp1eq2 (a : ℕ → ℝ) (h₀ : a 0 = 1)
    (h₁ : ∀ n, a (n + 1) = (∏ k in Finset.range (n + 1), a k) + 4) :
    ∀ n ≥ 1, a n - Real.sqrt (a (n + 1)) = 2 := by sorry
#align numbertheory_aneqprodakp4_anmsqrtanp1eq2 numbertheory_aneqprodakp4_anmsqrtanp1eq2

theorem algebra_2rootspoly_apatapbeq2asqp2ab (a b : ℂ) :
    (a + a) * (a + b) = 2 * a ^ 2 + 2 * (a * b) := by ring
#align algebra_2rootspoly_apatapbeq2asqp2ab algebra_2rootspoly_apatapbeq2asqp2ab

theorem induction_sum_odd (n : ℕ) : (∑ k in Finset.range n, 2 * k) + 1 = n ^ 2 := by sorry
#align induction_sum_odd induction_sum_odd

theorem mathd_algebra_568 (a : ℝ) :
    (a - 1) * (a + 1) * (a + 2) - (a - 2) * (a + 1) = a ^ 3 + a ^ 2 := by linarith
#align mathd_algebra_568 mathd_algebra_568

theorem mathd_algebra_616 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x ^ 3 + 2 * x + 1)
    (h₁ : ∀ x, g x = x - 1) : f (g 1) = 1 := by sorry
#align mathd_algebra_616 mathd_algebra_616

theorem mathd_numbertheory_690 :
    IsLeast { a : ℕ | 0 < a ∧ a ≡ 2 [MOD 3] ∧ a ≡ 4 [MOD 5] ∧ a ≡ 6 [MOD 7] ∧ a ≡ 8 [MOD 9] } 314 :=
  by sorry
#align mathd_numbertheory_690 mathd_numbertheory_690

theorem amc12a_2016_p2 (x : ℝ) (h₀ : (10 : ℝ) ^ x * 100 ^ (2 * x) = 1000 ^ 5) : x = 3 := by sorry
#align amc12a_2016_p2 amc12a_2016_p2

theorem mathd_numbertheory_405 (a b c : ℕ) (t : ℕ → ℕ) (h₀ : t 0 = 0) (h₁ : t 1 = 1)
    (h₂ : ∀ n > 1, t n = t (n - 2) + t (n - 1)) (h₃ : a ≡ 5 [MOD 16]) (h₄ : b ≡ 10 [MOD 16])
    (h₅ : c ≡ 15 [MOD 16]) : (t a + t b + t c) % 7 = 5 := by sorry
#align mathd_numbertheory_405 mathd_numbertheory_405

theorem mathd_numbertheory_110 (a b : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ b ≤ a) (h₁ : (a + b) % 10 = 2)
    (h₂ : (2 * a + b) % 10 = 1) : (a - b) % 10 = 6 := by sorry
#align mathd_numbertheory_110 mathd_numbertheory_110

theorem amc12a_2003_p25 (a b : ℝ) (f : ℝ → ℝ) (h₀ : 0 < b)
    (h₁ : ∀ x, f x = Real.sqrt (a * x ^ 2 + b * x)) (h₂ : { x | 0 ≤ f x } = f '' { x | 0 ≤ f x }) :
    a = 0 ∨ a = -4 := by sorry
#align amc12a_2003_p25 amc12a_2003_p25

theorem amc12a_2010_p10 (p q : ℝ) (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = p) (h₂ : a 2 = 9) (h₃ : a 3 = 3 * p - q) (h₄ : a 4 = 3 * p + q) : a 2010 = 8041 :=
  by
  have h₅ := h₀ 1
  have h₆ := h₀ 2
  have p_val : p = 5
  linarith
  have q_val : q = 2
  linarith
  have l₀ : ∀ n ≥ 1, a (n + 1) - a n = 4 :=
    by
    apply Nat.le_induction
    · linarith
    · intro n h hn
      have h₇ := h₀ n
      linarith
  have l₁ : ∀ n ≥ 1, a n = 5 + 4 * (n - 1) :=
    by
    apply Nat.le_induction
    · norm_cast
      linarith
    · intro n h hn
      have h₇ := l₀ n h
      have h₈ : a (n + 1) = a n + 4
      linarith
      rw [h₈, hn]
      ring_nf
      norm_cast
  have l₃ := l₁ 2010 (by norm_num)
  rw [l₃]
  norm_cast
  norm_num
#align amc12a_2010_p10 amc12a_2010_p10

theorem mathd_algebra_509 :
    Real.sqrt ((5 / Real.sqrt 80 + Real.sqrt 845 / 9 + Real.sqrt 45) / Real.sqrt 5) = 13 / 6 := by
  sorry
#align mathd_algebra_509 mathd_algebra_509

theorem mathd_algebra_159 (b : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = 3 * x ^ 4 - 7 * x ^ 3 + 2 * x ^ 2 - b * x + 1) (h₁ : f 1 = 1) : b = -2 :=
  by
  rw [h₀] at h₁
  linarith
#align mathd_algebra_159 mathd_algebra_159

theorem aime_1997_p11 (x : ℝ)
    (h₀ :
      x =
        (∑ n in Finset.Icc (1 : ℕ) 44, Real.cos (n * π / 180)) /
          ∑ n in Finset.Icc (1 : ℕ) 44, Real.sin (n * π / 180)) :
    Int.floor (100 * x) = 241 := by sorry
#align aime_1997_p11 aime_1997_p11

theorem aimeI_2000_p7 (x y z : ℝ) (m : ℚ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x * y * z = 1)
    (h₂ : x + 1 / z = 5) (h₃ : y + 1 / x = 29) (h₄ : z + 1 / y = m) (h₅ : 0 < m) :
    ↑m.den + m.num = 5 := by sorry
#align aimeI_2000_p7 aimeI_2000_p7

theorem aime_1988_p4 (n : ℕ) (a : ℕ → ℝ) (h₀ : ∀ n, abs (a n) < 1)
    (h₁ : (∑ k in Finset.range n, abs (a k)) = 19 + abs (∑ k in Finset.range n, a k)) : 20 ≤ n := by
  sorry
#align aime_1988_p4 aime_1988_p4

theorem induction_divisibility_9div10tonm1 (n : ℕ) (h₀ : 0 < n) : 9 ∣ 10 ^ n - 1 := by sorry
#align induction_divisibility_9div10tonm1 induction_divisibility_9div10tonm1

theorem mathd_numbertheory_126 (x a : ℕ) (h₀ : 0 < x ∧ 0 < a) (h₁ : Nat.gcd a 40 = x + 3)
    (h₂ : Nat.lcm a 40 = x * (x + 3))
    (h₃ : ∀ b : ℕ, 0 < b → Nat.gcd b 40 = x + 3 ∧ Nat.lcm b 40 = x * (x + 3) → a ≤ b) : a = 8 := by
  sorry
#align mathd_numbertheory_126 mathd_numbertheory_126

theorem mathd_algebra_323 (σ : Equiv ℝ ℝ) (h : ∀ x, σ.1 x = x ^ 3 - 8) : σ.2 (σ.1 (σ.2 19)) = 3 :=
  by
  revert h
  simp
  intro h
  apply σ.injective
  simp [h, σ.apply_symm_apply]
  norm_num
#align mathd_algebra_323 mathd_algebra_323

theorem mathd_algebra_421 (a b c d : ℝ) (h₀ : b = a ^ 2 + 4 * a + 6)
    (h₁ : b = 1 / 2 * a ^ 2 + a + 6) (h₂ : d = c ^ 2 + 4 * c + 6) (h₃ : d = 1 / 2 * c ^ 2 + c + 6)
    (h₄ : a < c) : c - a = 6 := by sorry
#align mathd_algebra_421 mathd_algebra_421

theorem imo_1987_p6 (p : ℕ) (f : ℕ → ℕ) (h₀ : ∀ x, f x = x ^ 2 + x + p)
    (h₀ : ∀ k : ℕ, k ≤ Nat.floor (Real.sqrt (p / 3)) → Nat.Prime (f k)) :
    ∀ i ≤ p - 2, Nat.Prime (f i) := by sorry
#align imo_1987_p6 imo_1987_p6

theorem amc12a_2009_p25 (a : ℕ → ℝ) (h₀ : a 1 = 1) (h₁ : a 2 = 1 / Real.sqrt 3)
    (h₂ : ∀ n, 1 ≤ n → a (n + 2) = (a n + a (n + 1)) / (1 - a n * a (n + 1))) : abs (a 2009) = 0 :=
  by sorry
#align amc12a_2009_p25 amc12a_2009_p25

theorem imo_1961_p1 (x y z a b : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x ≠ y) (h₂ : y ≠ z)
    (h₃ : z ≠ x) (h₄ : x + y + z = a) (h₅ : x ^ 2 + y ^ 2 + z ^ 2 = b ^ 2) (h₆ : x * y = z ^ 2) :
    0 < a ∧ b ^ 2 < a ^ 2 ∧ a ^ 2 < 3 * b ^ 2 := by sorry
#align imo_1961_p1 imo_1961_p1

theorem mathd_algebra_31 (x : NNReal) (u : ℕ → NNReal) (h₀ : ∀ n, u (n + 1) = NNReal.sqrt (x + u n))
    (h₁ : Filter.Tendsto u Filter.atTop (𝓝 9)) : 9 = NNReal.sqrt (x + 9) := by sorry
#align mathd_algebra_31 mathd_algebra_31

theorem algebra_manipexpr_apbeq2cceqiacpbceqm2 (a b c : ℂ) (h₀ : a + b = 2 * c)
    (h₁ : c = Complex.I) : a * c + b * c = -2 :=
  by
  rw [← add_mul, h₀, h₁, mul_assoc, Complex.I_mul_I]
  ring
#align algebra_manipexpr_apbeq2cceqiacpbceqm2 algebra_manipexpr_apbeq2cceqiacpbceqm2

theorem mathd_numbertheory_370 (n : ℕ) (h₀ : n % 7 = 3) : (2 * n + 1) % 7 = 0 := by sorry
#align mathd_numbertheory_370 mathd_numbertheory_370

theorem mathd_algebra_437 (x y : ℝ) (n : ℤ) (h₀ : x ^ 3 = -45) (h₁ : y ^ 3 = -101) (h₂ : x < n)
    (h₃ : ↑n < y) : n = -4 := by sorry
#align mathd_algebra_437 mathd_algebra_437

theorem imo_1966_p5 (x a : ℕ → ℝ) (h₀ : a 1 ≠ a 2) (h₁ : a 1 ≠ a 3) (h₂ : a 1 ≠ a 4)
    (h₃ : a 2 ≠ a 3) (h₄ : a 2 ≠ a 4) (h₅ : a 3 ≠ a 4) (h₆ : a 1 > a 2) (h₇ : a 2 > a 3)
    (h₈ : a 3 > a 4)
    (h₉ : abs (a 1 - a 2) * x 2 + abs (a 1 - a 3) * x 3 + abs (a 1 - a 4) * x 4 = 1)
    (h₁₀ : abs (a 2 - a 1) * x 1 + abs (a 2 - a 3) * x 3 + abs (a 2 - a 4) * x 4 = 1)
    (h₁₁ : abs (a 3 - a 1) * x 1 + abs (a 3 - a 2) * x 2 + abs (a 3 - a 4) * x 4 = 1)
    (h₁₂ : abs (a 4 - a 1) * x 1 + abs (a 4 - a 2) * x 2 + abs (a 4 - a 3) * x 3 = 1) :
    x 2 = 0 ∧ x 3 = 0 ∧ x 1 = 1 / abs (a 1 - a 4) ∧ x 4 = 1 / abs (a 1 - a 4) := by sorry
#align imo_1966_p5 imo_1966_p5

theorem mathd_algebra_89 (b : ℝ) (h₀ : b ≠ 0) :
    (7 * b ^ 3) ^ 2 * (4 * b ^ 2) ^ (-(3 : ℤ)) = 49 / 64 :=
  by
  ring_nf
  field_simp
  norm_cast
  refine' (div_eq_iff _).mpr _
  · norm_num
    assumption
  ring
#align mathd_algebra_89 mathd_algebra_89

theorem imo_1966_p4 (n : ℕ) (x : ℝ) (h₀ : ∀ k : ℕ, 0 < k → ∀ m : ℤ, x ≠ m * π / 2 ^ k)
    (h₁ : 0 < n) :
    (∑ k in Finset.Icc 1 n, 1 / Real.sin (2 ^ k * x)) = 1 / Real.tan x - 1 / Real.tan (2 ^ n * x) :=
  by sorry
#align imo_1966_p4 imo_1966_p4

theorem mathd_algebra_67 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 5 * x + 3) (h₁ : ∀ x, g x = x ^ 2 - 2) :
    g (f (-1)) = 2 := by
  rw [h₀, h₁]
  ring
#align mathd_algebra_67 mathd_algebra_67

theorem mathd_numbertheory_326 (n : ℕ) (h₀ : (↑n - 1) * ↑n * (↑n + 1) = (720 : ℤ)) : n + 1 = 10 :=
  by sorry
#align mathd_numbertheory_326 mathd_numbertheory_326

theorem induction_divisibility_3div2tooddnp1 (n : ℕ) : 3 ∣ 2 ^ (2 * n + 1) + 1 := by sorry
#align induction_divisibility_3div2tooddnp1 induction_divisibility_3div2tooddnp1

theorem mathd_algebra_123 (a b : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a + b = 20) (h₂ : a = 3 * b) :
    a - b = 10 := by
  rw [h₂] at h₁
  rw [h₂]
  have h₃ : b = 5 := by linarith
  rw [h₃]
  norm_num
#align mathd_algebra_123 mathd_algebra_123

theorem algebra_2varlineareq_xpeeq7_2xpeeq3_eeq11_xeqn4 (x e : ℂ) (h₀ : x + e = 7)
    (h₁ : 2 * x + e = 3) : e = 11 ∧ x = -4 := by sorry
#align algebra_2varlineareq_xpeeq7_2xpeeq3_eeq11_xeqn4 algebra_2varlineareq_xpeeq7_2xpeeq3_eeq11_xeqn4

theorem imo_1993_p5 : ∃ f : ℕ → ℕ, f 1 = 2 ∧ ∀ n, f (f n) = f n + n ∧ ∀ n, f n < f (n + 1) := by
  sorry
#align imo_1993_p5 imo_1993_p5

theorem numbertheory_prmdvsneqnsqmodpeq0 (n : ℤ) (p : ℕ) (h₀ : Nat.Prime p) :
    ↑p ∣ n ↔ n ^ 2 % p = 0 :=
  by
  simp [Nat.dvd_prime_pow (show Nat.Prime p from h₀), pow_succ]
  simp only [Int.coe_nat_dvd_right, Int.coe_nat_dvd_left, Int.natAbs_mul]
  rw [Nat.Prime.dvd_mul]
  · tauto
  assumption
#align numbertheory_prmdvsneqnsqmodpeq0 numbertheory_prmdvsneqnsqmodpeq0

theorem imo_1964_p1_1 (n : ℕ) (h₀ : 7 ∣ 2 ^ n - 1) : 3 ∣ n := by sorry
#align imo_1964_p1_1 imo_1964_p1_1

theorem imo_1990_p3 (n : ℕ) (h₀ : 2 ≤ n) (h₁ : n ^ 2 ∣ 2 ^ n + 1) : n = 3 := by sorry
#align imo_1990_p3 imo_1990_p3

theorem induction_ineq_nsqlefactn (n : ℕ) (h₀ : 4 ≤ n) : n ^ 2 ≤ n ! :=
  by
  simp only [sq]
  cases' n with n
  exact by decide
  simp
  apply Nat.succ_le_of_lt
  apply Nat.lt_factorial_self
  exact nat.succ_le_succ_iff.mp h₀
#align induction_ineq_nsqlefactn induction_ineq_nsqlefactn

theorem mathd_numbertheory_30 :
    (33818 ^ 2 + 33819 ^ 2 + 33820 ^ 2 + 33821 ^ 2 + 33822 ^ 2) % 17 = 0 := by norm_num
#align mathd_numbertheory_30 mathd_numbertheory_30

theorem mathd_algebra_267 (x : ℝ) (h₀ : x ≠ 1) (h₁ : x ≠ -2)
    (h₂ : (x + 1) / (x - 1) = (x - 2) / (x + 2)) : x = 0 :=
  by
  revert x h₀ h₁ h₂
  norm_num
  intro a ha
  intro ha
  intro h
  rw [← sub_eq_zero] at *
  simp
  field_simp  at *
  linarith
#align mathd_algebra_267 mathd_algebra_267

theorem mathd_numbertheory_961 : 2003 % 11 = 1 := by norm_num
#align mathd_numbertheory_961 mathd_numbertheory_961

theorem induction_seq_mul2pnp1 (n : ℕ) (u : ℕ → ℕ) (h₀ : u 0 = 0)
    (h₁ : ∀ n, u (n + 1) = 2 * u n + (n + 1)) : u n = 2 ^ (n + 1) - (n + 2) := by sorry
#align induction_seq_mul2pnp1 induction_seq_mul2pnp1

theorem amc12a_2002_p12 (f : ℝ → ℝ) (k : ℝ) (a b : ℕ) (h₀ : ∀ x, f x = x ^ 2 - 63 * x + k)
    (h₁ : f a = 0 ∧ f b = 0) (h₂ : a ≠ b) (h₃ : Nat.Prime a ∧ Nat.Prime b) : k = 122 := by sorry
#align amc12a_2002_p12 amc12a_2002_p12

theorem algebra_manipexpr_2erprsqpesqeqnrpnesq (e r : ℂ) :
    2 * (e * r) + (e ^ 2 + r ^ 2) = (-r + -e) ^ 2 := by ring
#align algebra_manipexpr_2erprsqpesqeqnrpnesq algebra_manipexpr_2erprsqpesqeqnrpnesq

theorem mathd_algebra_119 (d e : ℝ) (h₀ : 2 * d = 17 * e - 8) (h₁ : 2 * e = d - 9) : e = 2 := by
  linarith
#align mathd_algebra_119 mathd_algebra_119

theorem amc12a_2020_p13 (a b c : ℕ) (n : NNReal) (h₀ : n ≠ 1) (h₁ : 1 < a ∧ 1 < b ∧ 1 < c)
    (h₂ : (n * (n * n ^ (1 / c)) ^ (1 / b)) ^ (1 / a) = (n ^ 25) ^ (1 / 36)) : b = 3 := by sorry
#align amc12a_2020_p13 amc12a_2020_p13

theorem imo_1977_p5 (a b q r : ℕ) (h₀ : r < a + b) (h₁ : a ^ 2 + b ^ 2 = (a + b) * q + r)
    (h₂ : q ^ 2 + r = 1977) :
    abs ((a : ℤ) - 22) = 15 ∧ abs ((b : ℤ) - 22) = 28 ∨
      abs ((a : ℤ) - 22) = 28 ∧ abs ((b : ℤ) - 22) = 15 :=
  by sorry
#align imo_1977_p5 imo_1977_p5

theorem numbertheory_2dvd4expn (n : ℕ) (h₀ : n ≠ 0) : 2 ∣ 4 ^ n :=
  by
  revert n h₀
  rintro ⟨k, rfl⟩
  · norm_num
  apply dvd_pow
  norm_num
#align numbertheory_2dvd4expn numbertheory_2dvd4expn

theorem amc12a_2010_p11 (x b : ℝ) (h₀ : 0 < b) (h₁ : (7 : ℝ) ^ (x + 7) = 8 ^ x)
    (h₂ : x = Real.logb b (7 ^ 7)) : b = 8 / 7 := by sorry
#align amc12a_2010_p11 amc12a_2010_p11

theorem amc12a_2003_p24 :
    IsGreatest { y : ℝ | ∃ a b : ℝ, 1 < b ∧ b ≤ a ∧ y = Real.logb a (a / b) + Real.logb b (b / a) }
      0 :=
  by sorry
#align amc12a_2003_p24 amc12a_2003_p24

theorem amc12a_2002_p1 (f : ℂ → ℂ) (h₀ : ∀ x, f x = (2 * x + 3) * (x - 4) + (2 * x + 3) * (x - 6))
    (h₁ : Fintype (f ⁻¹' {0})) : (∑ y in (f ⁻¹' {0}).toFinset, y) = 7 / 2 := by sorry
#align amc12a_2002_p1 amc12a_2002_p1

theorem mathd_algebra_206 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = x ^ 2 + a * x + b) (h₁ : 2 * a ≠ b)
    (h₂ : f (2 * a) = 0) (h₃ : f b = 0) : a + b = -1 := by sorry
#align mathd_algebra_206 mathd_algebra_206

theorem mathd_numbertheory_92 (n : ℕ) (h₀ : 5 * n % 17 = 8) : n % 17 = 5 := by sorry
#align mathd_numbertheory_92 mathd_numbertheory_92

theorem mathd_algebra_482 (m n : ℕ) (k : ℝ) (f : ℝ → ℝ) (h₀ : Nat.Prime m) (h₁ : Nat.Prime n)
    (h₂ : ∀ x, f x = x ^ 2 - 12 * x + k) (h₃ : f m = 0) (h₄ : f n = 0) (h₅ : m ≠ n) : k = 35 := by
  sorry
#align mathd_algebra_482 mathd_algebra_482

theorem amc12b_2002_p3 (S : Finset ℕ)
    -- note: we use (n^2 + 2 - 3 * n) over (n^2 - 3 * n + 2) because nat subtraction truncates the latter at 1 and 2
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 0 < n ∧ Nat.Prime (n ^ 2 + 2 - 3 * n)) :
    S.card = 1 := by sorry
#align amc12b_2002_p3 amc12b_2002_p3

theorem mathd_numbertheory_668 (l r : ZMod 7) (h₀ : l = (2 + 3)⁻¹) (h₁ : r = 2⁻¹ + 3⁻¹) :
    l - r = 1 := by sorry
#align mathd_numbertheory_668 mathd_numbertheory_668

theorem mathd_algebra_251 (x : ℝ) (h₀ : x ≠ 0) (h₁ : 3 + 1 / x = 7 / x) : x = 2 :=
  by
  field_simp [h₀]  at h₁
  linarith
#align mathd_algebra_251 mathd_algebra_251

theorem mathd_numbertheory_84 : Int.floor ((9 : ℝ) / 160 * 100) = 5 :=
  by
  rw [Int.floor_eq_iff]
  constructor
  all_goals norm_num
#align mathd_numbertheory_84 mathd_numbertheory_84

theorem mathd_numbertheory_412 (x y : ℕ) (h₀ : x % 19 = 4) (h₁ : y % 19 = 7) :
    (x + 1) ^ 2 * (y + 5) ^ 3 % 19 = 13 := by sorry
#align mathd_numbertheory_412 mathd_numbertheory_412

theorem mathd_algebra_181 (n : ℝ) (h₀ : n ≠ 3) (h₁ : (n + 5) / (n - 3) = 2) : n = 11 :=
  by
  rw [div_eq_iff] at h₁
  linarith
  exact sub_ne_zero.mpr h₀
#align mathd_algebra_181 mathd_algebra_181

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y «expr ≠ » 0) -/
theorem amc12a_2016_p3 (f : ℝ → ℝ → ℝ)
    (h₀ : ∀ x, ∀ (y) (_ : y ≠ 0), f x y = x - y * Int.floor (x / y)) :
    f (3 / 8) (-(2 / 5)) = -(1 / 40) := by sorry
#align amc12a_2016_p3 amc12a_2016_p3

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (n «expr = » 3) -/
theorem mathd_algebra_247 (t s : ℝ) (n : ℤ) (h₀ : t = 2 * s - s ^ 2) (h₁ : s = n ^ 2 - 2 ^ n + 1)
    (n) (_ : n = 3) : t = 0 := by sorry
#align mathd_algebra_247 mathd_algebra_247

theorem algebra_sqineq_2unitcircatblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 2) : a * b ≤ 1 :=
  by
  have hu := sq_nonneg a
  have hv := sq_nonneg b
  have H₁ := add_nonneg hu hv
  have H₂ : 0 ≤ (a - b) ^ 2 := by nlinarith
  nlinarith
#align algebra_sqineq_2unitcircatblt1 algebra_sqineq_2unitcircatblt1

theorem mathd_numbertheory_629 : IsLeast { t : ℕ | 0 < t ∧ Nat.lcm 12 t ^ 3 = (12 * t) ^ 2 } 18 :=
  by sorry
#align mathd_numbertheory_629 mathd_numbertheory_629

theorem amc12a_2017_p2 (x y : ℝ) (h₀ : x ≠ 0) (h₁ : y ≠ 0) (h₂ : x + y = 4 * (x * y)) :
    1 / x + 1 / y = 4 := by sorry
#align amc12a_2017_p2 amc12a_2017_p2

theorem algebra_amgm_sumasqdivbsqgeqsumbdiva (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) :
    a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 ≥ b / a + c / b + a / c := by sorry
#align algebra_amgm_sumasqdivbsqgeqsumbdiva algebra_amgm_sumasqdivbsqgeqsumbdiva

theorem mathd_numbertheory_202 : (19 ^ 19 + 99 ^ 99) % 10 = 8 := by sorry
#align mathd_numbertheory_202 mathd_numbertheory_202

theorem imo_1979_p1 (p q : ℕ) (h₀ : 0 < q)
    (h₁ : (∑ k in Finset.Icc (1 : ℕ) 1319, (-1) ^ (k + 1) * ((1 : ℝ) / k)) = p / q) : 1979 ∣ p := by
  sorry
#align imo_1979_p1 imo_1979_p1

theorem mathd_algebra_51 (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a + b = 35) (h₂ : a = 2 / 5 * b) :
    b - a = 15 := by linarith
#align mathd_algebra_51 mathd_algebra_51

theorem mathd_algebra_10 : abs ((120 : ℝ) / 100 * 30 - 130 / 100 * 20) = 10 := by norm_num
#align mathd_algebra_10 mathd_algebra_10

