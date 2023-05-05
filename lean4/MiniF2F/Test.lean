/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng, Kudzo Ahegbebu, Stanislas Polu, David Renshaw, OpenAI GPT-f

! This file was ported from Lean 3 source module test
-/
import MiniF2F.Minif2fImport

open BigOperators

open Nat Real Rat

theorem mathd_algebra_478 (b h v : ℝ) (h₀ : 0 < b ∧ 0 < h ∧ 0 < v) (h₁ : v = 1 / 3 * (b * h))
    (h₂ : b = 30) (h₃ : h = 13 / 2) : v = 65 :=
  by
  rw [h₂, h₃] at h₁
  rw [h₁]
  norm_num
#align mathd_algebra_478 mathd_algebra_478

theorem numbertheory_4x3m7y3neq2003 (x y : ℤ) : 4 * x ^ 3 - 7 * y ^ 3 ≠ 2003 :=
  by
  intro hneq
  apply_fun (coe : ℤ → ZMod 7)  at hneq
  push_cast at hneq
  have : (2003 : ZMod 7) = (1 : ZMod 7)
  decide
  rw [this] at hneq
  have : (7 : ZMod 7) = (0 : ZMod 7)
  decide
  rw [this] at hneq
  rw [MulZeroClass.zero_mul] at hneq
  rw [sub_zero] at hneq
  have main : ∀ x : ZMod 7, x ^ 3 ∈ [(0 : ZMod 7), 1, -1]
  decide
  rcases main x with (h' | h' | h' | h)
  iterate 3 
    rw [h'] at hneq
    revert hneq
    decide
  exact h
#align numbertheory_4x3m7y3neq2003 numbertheory_4x3m7y3neq2003

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by sorry
#align aime_1983_p1 aime_1983_p1

theorem amc12_2001_p5 :
    Finset.prod (Finset.filter (fun x => ¬Even x) (Finset.range 10000)) (id : ℕ → ℕ) =
      10000! / (2 ^ 5000 * 5000!) :=
  by sorry
#align amc12_2001_p5 amc12_2001_p5

theorem mathd_algebra_141 (a b : ℝ) (h₁ : a * b = 180) (h₂ : 2 * (a + b) = 54) :
    a ^ 2 + b ^ 2 = 369 := by
  replace h₂ : a + b = 27
  linarith
  have h₃ : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by ring
  rw [h₃, h₂, h₁]
  norm_num
#align mathd_algebra_141 mathd_algebra_141

theorem mathd_numbertheory_3 : (∑ x in Finset.range 10, (x + 1) ^ 2) % 10 = 5 := by decide!
#align mathd_numbertheory_3 mathd_numbertheory_3

theorem imo_1969_p2 (m n : ℝ) (k : ℕ) (a : ℕ → ℝ) (y : ℝ → ℝ) (h₀ : 0 < k)
    (h₁ : ∀ x, y x = ∑ i in Finset.range k, Real.cos (a i + x) / 2 ^ i) (h₂ : y m = 0)
    (h₃ : y n = 0) : ∃ t : ℤ, m - n = t * π := by sorry
#align imo_1969_p2 imo_1969_p2

theorem mathd_algebra_209 (σ : Equiv ℝ ℝ) (h₀ : σ.2 2 = 10) (h₁ : σ.2 10 = 1) (h₂ : σ.2 1 = 2) :
    σ.1 (σ.1 10) = 1 := by
  rw [← h₀, ← h₂]
  simp
#align mathd_algebra_209 mathd_algebra_209

theorem mathd_numbertheory_1124 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 18 ∣ 374 * 10 + n) : n = 4 := by sorry
#align mathd_numbertheory_1124 mathd_numbertheory_1124

theorem imo_1983_p6 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) : 0 ≤ a ^ 2 * b * (a - b) + b ^ 2 * c * (b - c) + c ^ 2 * a * (c - a) := by
  sorry
#align imo_1983_p6 imo_1983_p6

theorem mathd_numbertheory_237 : (∑ k in Finset.range 101, k) % 6 = 4 := by sorry
#align mathd_numbertheory_237 mathd_numbertheory_237

theorem mathd_algebra_33 (x y z : ℝ) (h₀ : x ≠ 0) (h₁ : 2 * x = 5 * y) (h₂ : 7 * y = 10 * z) :
    z / x = 7 / 25 := by
  field_simp
  nlinarith
#align mathd_algebra_33 mathd_algebra_33

theorem amc12b_2021_p3 (x : ℝ) (h₀ : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53) : x = 3 / 4 :=
  by sorry
#align amc12b_2021_p3 amc12b_2021_p3

theorem mathd_numbertheory_299 : 1 * 3 * 5 * 7 * 9 * 11 * 13 % 10 = 5 := by norm_num
#align mathd_numbertheory_299 mathd_numbertheory_299

theorem amc12b_2020_p2 :
    (100 ^ 2 - 7 ^ 2 : ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) =
      1 :=
  by norm_num
#align amc12b_2020_p2 amc12b_2020_p2

theorem algebra_sqineq_unitcircatbpabsamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + abs (a - b) ≤ 1 := by sorry
#align algebra_sqineq_unitcircatbpabsamblt1 algebra_sqineq_unitcircatbpabsamblt1

theorem imo_1977_p6 (f : ℕ → ℕ) (h₀ : ∀ n, 0 < f n) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1)) :
    ∀ n, 0 < n → f n = n := by sorry
#align imo_1977_p6 imo_1977_p6

theorem mathd_algebra_419 (a b : ℝ) (h₀ : a = -1) (h₁ : b = 5) : -a - b ^ 2 + 3 * (a * b) = -39 :=
  by
  rw [h₀, h₁]
  norm_num
#align mathd_algebra_419 mathd_algebra_419

theorem amc12a_2020_p10 (n : ℕ) (h₀ : 0 < n)
    (h₁ : Real.logb 2 (Real.logb 16 n) = Real.logb 4 (Real.logb 4 n)) :
    (Nat.digits 10 n).Sum = 13 := by sorry
#align amc12a_2020_p10 amc12a_2020_p10

theorem imo_1960_p2 (x : ℝ) (h₀ : 0 ≤ 1 + 2 * x) (h₁ : (1 - Real.sqrt (1 + 2 * x)) ^ 2 ≠ 0)
    (h₂ : 4 * x ^ 2 / (1 - Real.sqrt (1 + 2 * x)) ^ 2 < 2 * x + 9) : -(1 / 2) ≤ x ∧ x < 45 / 8 := by
  sorry
#align imo_1960_p2 imo_1960_p2

theorem mathd_numbertheory_427 (a : ℕ) (h₀ : a = ∑ k in Nat.divisors 500, k) :
    (∑ k in Finset.filter (fun x => Nat.Prime x) (Nat.divisors a), k) = 25 := by sorry
#align mathd_numbertheory_427 mathd_numbertheory_427

theorem numbertheory_x5neqy2p4 (x y : ℤ) : x ^ 5 ≠ y ^ 2 + 4 := by sorry
#align numbertheory_x5neqy2p4 numbertheory_x5neqy2p4

theorem imosl_2007_algebra_p6 (a : ℕ → NNReal) (h₀ : (∑ x in Finset.range 100, a (x + 1) ^ 2) = 1) :
    (∑ x in Finset.range 99, a (x + 1) ^ 2 * a (x + 2)) + a 100 ^ 2 * a 1 < 12 / 25 := by sorry
#align imosl_2007_algebra_p6 imosl_2007_algebra_p6

theorem mathd_algebra_398 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 9 * b = 20 * c)
    (h₂ : 7 * a = 4 * b) : 63 * a = 80 * c := by linarith
#align mathd_algebra_398 mathd_algebra_398

theorem imo_1963_p5 : Real.cos (π / 7) - Real.cos (2 * π / 7) + Real.cos (3 * π / 7) = 1 / 2 := by
  sorry
#align imo_1963_p5 imo_1963_p5

theorem mathd_numbertheory_430 (a b c : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 1 ≤ b ∧ b ≤ 9)
    (h₂ : 1 ≤ c ∧ c ≤ 9) (h₃ : a ≠ b) (h₄ : a ≠ c) (h₅ : b ≠ c) (h₆ : a + b = c)
    (h₇ : 10 * a + a - b = 2 * c) (h₈ : c * b = 10 * a + a + a) : a + b + c = 8 := by sorry
#align mathd_numbertheory_430 mathd_numbertheory_430

theorem mathd_algebra_459 (a b c d : ℚ) (h₀ : 3 * a = b + c + d) (h₁ : 4 * b = a + c + d)
    (h₂ : 2 * c = a + b + d) (h₃ : 8 * a + 10 * b + 6 * c = 24) : ↑d.den + d.num = 28 :=
  by
  have h₄ : d = 13 / 15; linarith
  sorry
#align mathd_algebra_459 mathd_algebra_459

theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ 4 ^ (n + 1) + 20 :=
  by
  have dvd_of_dvd_add_mul_left : ∀ a b n : ℕ, a ∣ b + a * n → a ∣ b :=
    by
    intro a b n
    refine' (Nat.dvd_add_left _).mp
    exact dvd_mul_right a n
  induction' n with k IH
  · decide
  · rw [pow_succ]
    -- If we add 60 to RHS, then we can factor the 4 to use IH
    apply dvd_of_dvd_add_mul_left 12 (4 * 4 ^ k.succ + 20) 5
    exact dvd_mul_of_dvd_right IH 4
#align induction_12dvd4expnp1p20 induction_12dvd4expnp1p20

theorem mathd_algebra_320 (x : ℝ) (a b c : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 ≤ x)
    (h₁ : 2 * x ^ 2 = 4 * x + 9) (h₂ : x = (a + Real.sqrt b) / c) (h₃ : c = 2) : a + b + c = 26 :=
  by sorry
#align mathd_algebra_320 mathd_algebra_320

theorem mathd_algebra_137 (x : ℕ) (h₀ : ↑x + (4 : ℝ) / (100 : ℝ) * ↑x = 598) : x = 575 :=
  by
  have h₁ : ↑x = (575 : ℝ); linarith
  assumption_mod_cast
#align mathd_algebra_137 mathd_algebra_137

theorem imo_1997_p5 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : x ^ y ^ 2 = y ^ x) :
    (x, y) = (1, 1) ∨ (x, y) = (16, 2) ∨ (x, y) = (27, 3) := by sorry
#align imo_1997_p5 imo_1997_p5

theorem mathd_numbertheory_277 (m n : ℕ) (h₀ : Nat.gcd m n = 6) (h₁ : Nat.lcm m n = 126) :
    60 ≤ m + n := by sorry
#align mathd_numbertheory_277 mathd_numbertheory_277

theorem mathd_numbertheory_559 (x y : ℕ) (h₀ : x % 3 = 2) (h₁ : y % 5 = 4) (h₂ : x % 10 = y % 10) :
    14 ≤ x := by sorry
#align mathd_numbertheory_559 mathd_numbertheory_559

theorem mathd_algebra_160 (n x : ℝ) (h₀ : n + x = 97) (h₁ : n + 5 * x = 265) : n + 2 * x = 139 := by
  linarith
#align mathd_algebra_160 mathd_algebra_160

theorem mathd_algebra_24 (x : ℝ) (h₀ : x / 50 = 40) : x = 2000 := by nlinarith
#align mathd_algebra_24 mathd_algebra_24

theorem mathd_algebra_176 (x : ℝ) : (x + 1) ^ 2 * x = x ^ 3 + 2 * x ^ 2 + x := by ring_nf
#align mathd_algebra_176 mathd_algebra_176

theorem induction_nfactltnexpnm1ngt3 (n : ℕ) (h₀ : 3 ≤ n) : n ! < n ^ (n - 1) :=
  by
  induction' h₀ with k h₀ IH
  · norm_num
  · have k_ge_one : 1 ≤ k := le_trans (by decide) h₀
    calc
      k.succ.factorial = k.succ * k.factorial := rfl
      _ < k.succ * k ^ (k - 1) := ((mul_lt_mul_left (Nat.succ_pos k)).mpr IH)
      _ ≤ k.succ * k.succ ^ (k - 1) :=
        (Nat.mul_le_mul_left _ <| Nat.pow_le_pow_of_le_left (Nat.le_succ k) (k - 1))
      _ = k.succ ^ (k - 1 + 1) := by rw [← pow_succ k.succ (k - 1)]
      _ = k.succ ^ k := by rw [Nat.sub_add_cancel k_ge_one]
      
#align induction_nfactltnexpnm1ngt3 induction_nfactltnexpnm1ngt3

theorem mathd_algebra_208 : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 := by sorry
#align mathd_algebra_208 mathd_algebra_208

theorem mathd_numbertheory_353 (s : ℕ) (h₀ : s = ∑ k in Finset.Icc 2010 4018, k) : s % 2009 = 0 :=
  by sorry
#align mathd_numbertheory_353 mathd_numbertheory_353

theorem numbertheory_notequiv2i2jasqbsqdiv8 :
    ¬∀ a b : ℤ, (∃ i j, a = 2 * i ∧ b = 2 * j) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k :=
  by
  refine' not_forall_of_exists_not _
  use 2
  refine' not_forall_of_exists_not _
  use 4
  refine' not_iff.mpr _
  refine' Iff.symm _
  apply iff_not_comm.mpr
  refine' iff_of_true _ _
  · use 1
    use 2
    norm_num
  · norm_num
    intro k
    refine' ne_comm.mp _
    apply ne_iff_lt_or_gt.mpr
    by_cases k ≤ 2
    · left
      linarith
    · right
      linarith
#align numbertheory_notequiv2i2jasqbsqdiv8 numbertheory_notequiv2i2jasqbsqdiv8

theorem mathd_algebra_156 (x y : ℝ) (f g : ℝ → ℝ) (h₀ : ∀ t, f t = t ^ 4)
    (h₁ : ∀ t, g t = 5 * t ^ 2 - 6) (h₂ : f x = g x) (h₃ : f y = g y) (h₄ : x ^ 2 < y ^ 2) :
    y ^ 2 - x ^ 2 = 1 := by sorry
#align mathd_algebra_156 mathd_algebra_156

theorem mathd_numbertheory_12 :
    Finset.card (Finset.filter (fun x => 20 ∣ x) (Finset.Icc 15 85)) = 4 := by sorry
#align mathd_numbertheory_12 mathd_numbertheory_12

theorem mathd_numbertheory_345 : (2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) % 7 = 0 := by
  norm_num
#align mathd_numbertheory_345 mathd_numbertheory_345

theorem mathd_numbertheory_447 :
    (∑ k in Finset.filter (fun x => 3 ∣ x) (Finset.Icc 1 49), k % 10) = 78 := by sorry
#align mathd_numbertheory_447 mathd_numbertheory_447

theorem mathd_numbertheory_328 : 5 ^ 999999 % 7 = 6 := by sorry
#align mathd_numbertheory_328 mathd_numbertheory_328

theorem mathd_numbertheory_451 (S : Finset ℕ)
    (h₀ :
      ∀ n : ℕ,
        n ∈ S ↔
          2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (Nat.divisors m).card = 4 ∧ (∑ p in Nat.divisors m, p) = n) :
    (∑ k in S, k) = 2016 := by sorry
#align mathd_numbertheory_451 mathd_numbertheory_451

theorem aime_1997_p9 (a : ℝ) (h₀ : 0 < a)
    (h₁ : 1 / a - Int.floor (1 / a) = a ^ 2 - Int.floor (a ^ 2)) (h₂ : 2 < a ^ 2) (h₃ : a ^ 2 < 3) :
    a ^ 12 - 144 * (1 / a) = 233 := by sorry
#align aime_1997_p9 aime_1997_p9

theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 :=
  by
  suffices : 0 ≤ a ^ 2 - 2 * a + 1; nlinarith
  suffices : 0 ≤ (a - 1) ^ 2; nlinarith
  nlinarith
#align algebra_sqineq_at2malt1 algebra_sqineq_at2malt1

theorem algebra_apbmpcneq0_aeq0anbeq0anceq0 (a b c : ℚ) (m n : ℝ) (h₀ : 0 < m ∧ 0 < n)
    (h₁ : m ^ 3 = 2) (h₂ : n ^ 3 = 4) (h₃ : (a : ℝ) + b * m + c * n = 0) : a = 0 ∧ b = 0 ∧ c = 0 :=
  by sorry
#align algebra_apbmpcneq0_aeq0anbeq0anceq0 algebra_apbmpcneq0_aeq0anbeq0anceq0

theorem mathd_algebra_171 (f : ℝ → ℝ) (h₀ : ∀ x, f x = 5 * x + 4) : f 1 = 9 :=
  by
  rw [h₀]
  linarith
#align mathd_algebra_171 mathd_algebra_171

theorem mathd_numbertheory_227 (x y n : ℕ+) (h₀ : ↑x / (4 : ℝ) + y / 6 = (x + y) / n) : n = 5 :=
  by
  field_simp  at h₀
  have h₂ : (6 : ℝ) * x * (n - 4) = 4 * y * (6 - n) :=
    by
    field_simp
    ring_nf
    linarith [h₀]
  have p₁ : (0 : ℝ) < y
  norm_num
  have p₂ : (0 : ℝ) < x
  norm_num
  have repl₁ : ↑(6 : ℕ+) = (6 : ℕ) := by
    apply @PNat.toPNat'_coe 6
    norm_num
  have repl₂ : ↑(4 : ℕ+) = (4 : ℕ) := by
    apply @PNat.toPNat'_coe 4
    norm_num
  by_contra h
  change n ≠ 5 at h
  by_cases b₀ : n < 5
  · have k₁ : (0 : ℝ) < 4 * ↑y * (6 - ↑n) :=
      by
      suffices (0 : ℝ) < 6 - ↑n by nlinarith [this, p₁]
      norm_num [b₀]
      norm_cast
      rw [← repl₁]
      norm_cast
      clear h₀ h₂ h repl₁
      suffices (5 : ℕ+) < 6 by exact lt_trans b₀ this
      decide!
    rw [← h₂] at k₁
    have k₂ : 6 * ↑x * (↑n - 4) ≤ (0 : ℝ) :=
      by
      suffices ↑n - 4 ≤ (0 : ℝ) by nlinarith [this, p₂]
      norm_num
      norm_cast
      rw [← repl₂]
      norm_cast
      apply pnat.lt_add_one_iff.mp
      suffices 4 + 1 = (5 : ℕ+) by rwa [this]
      decide!
    revert k₂
    contrapose!
    intro k₃
    exact k₁
  · have b₁ : 5 < n := by
      push_neg  at b₀
      exact (Ne.symm h).le_iff_lt.mp b₀
    have k₁ : 4 * ↑y * (6 - ↑n) ≤ (0 : ℝ) :=
      by
      suffices 6 - ↑n ≤ (0 : ℝ) by nlinarith [this, p₁]
      norm_num
      norm_cast
      rw [← repl₁]
      norm_cast
      exact b₁
    have k₂ : (0 : ℝ) < 6 * ↑x * (↑n - 4) :=
      by
      suffices (0 : ℝ) < ↑n - 4 by nlinarith [this, p₂]
      norm_num
      norm_cast
      rw [← repl₂]
      norm_cast
      refine' lt_trans _ b₁
      decide!
    rw [← h₂] at k₁
    revert k₂
    contrapose!
    intro k₃
    exact k₁
#align mathd_numbertheory_227 mathd_numbertheory_227

theorem mathd_algebra_188 (σ : Equiv ℝ ℝ) (h : σ.1 2 = σ.2 2) : σ.1 (σ.1 2) = 2 := by simp [h]
#align mathd_algebra_188 mathd_algebra_188

theorem mathd_numbertheory_765 (x : ℤ) (h₀ : x < 0) (h₁ : 24 * x % 1199 = 15) : x ≤ -449 := by sorry
#align mathd_numbertheory_765 mathd_numbertheory_765

theorem imo_1959_p1 (n : ℕ) (h₀ : 0 < n) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by sorry
#align imo_1959_p1 imo_1959_p1

theorem mathd_numbertheory_175 : 2 ^ 2010 % 10 = 4 := by sorry
#align mathd_numbertheory_175 mathd_numbertheory_175

theorem induction_sumkexp3eqsumksq (n : ℕ) :
    (∑ k in Finset.range n, k ^ 3) = (∑ k in Finset.range n, k) ^ 2 :=
  by
  symm
  induction' n with j IH
  · rfl
  ·
    calc
      (∑ k : ℕ in Finset.range j.succ, k) ^ 2 = ((∑ k : ℕ in Finset.range j, k) + j) ^ 2 := by
        rw [Finset.sum_range_succ]
      _ = (∑ k : ℕ in Finset.range j, k) ^ 2 + (2 * ∑ k : ℕ in Finset.range j, k) * j + j ^ 2 := by
        rw [add_sq _ _]
      _ = (∑ k : ℕ in Finset.range j, k) ^ 2 + (∑ k : ℕ in Finset.range j, k) * 2 * j + j ^ 2 := by
        ring
      _ = (∑ k : ℕ in Finset.range j, k) ^ 2 + j * (j - 1) * j + j ^ 2 := by
        rw [Finset.sum_range_id_mul_two j]
      _ = (∑ k : ℕ in Finset.range j, k ^ 3) + j * (j - 1) * j + j ^ 2 := by rw [IH]
      _ = (∑ k : ℕ in Finset.range j, k ^ 3) + j ^ 2 * (j - 1) + j ^ 2 := by ring_nf
      _ = (∑ k : ℕ in Finset.range j, k ^ 3) + j ^ 3 := by cases j <;> [norm_num, ring_nf]
      _ = ∑ k : ℕ in Finset.range j.succ, k ^ 3 := by rw [← Finset.sum_range_succ]
      
#align induction_sumkexp3eqsumksq induction_sumkexp3eqsumksq

theorem numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown (m n : ℕ) (f : ℕ → ℕ)
    (h₀ : ∀ x, f x = 4 ^ x + 6 ^ x + 9 ^ x) (h₁ : 0 < m ∧ 0 < n) (h₂ : m ≤ n) :
    f (2 ^ m) ∣ f (2 ^ n) := by sorry
#align numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown

theorem imo_1992_p1 (p q r : ℤ) (h₀ : 1 < p ∧ p < q ∧ q < r)
    (h₁ : (p - 1) * (q - 1) * (r - 1) ∣ p * q * r - 1) :
    (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by sorry
#align imo_1992_p1 imo_1992_p1

theorem imo_1982_p1 (f : ℕ → ℕ)
    (h₀ : ∀ m n, 0 < m ∧ 0 < n → f (m + n) - f m - f n = 0 ∨ f (m + n) - f m - f n = 1)
    (h₁ : f 2 = 0) (h₂ : 0 < f 3) (h₃ : f 9999 = 3333) : f 1982 = 660 := by sorry
#align imo_1982_p1 imo_1982_p1

theorem aime_1987_p5 (x y : ℤ) (h₀ : y ^ 2 + 3 * (x ^ 2 * y ^ 2) = 30 * x ^ 2 + 517) :
    3 * (x ^ 2 * y ^ 2) = 588 := by sorry
#align aime_1987_p5 aime_1987_p5

theorem mathd_algebra_346 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = 2 * x - 3) (h₁ : ∀ x, g x = x + 1) :
    g (f 5 - 1) = 7 := by
  rw [h₀, h₁]
  norm_num
#align mathd_algebra_346 mathd_algebra_346

theorem mathd_algebra_487 (a b c d : ℝ) (h₀ : b = a ^ 2) (h₁ : a + b = 1) (h₂ : d = c ^ 2)
    (h₃ : c + d = 1) (h₄ : a ≠ c) : Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2) = Real.sqrt 10 := by sorry
#align mathd_algebra_487 mathd_algebra_487

theorem mathd_numbertheory_728 : (29 ^ 13 - 5 ^ 13) % 7 = 3 := by norm_num
#align mathd_numbertheory_728 mathd_numbertheory_728

theorem mathd_algebra_184 (a b : NNReal) (h₀ : 0 < a ∧ 0 < b) (h₁ : a ^ 2 = 6 * b)
    (h₂ : a ^ 2 = 54 / b) : a = 3 * NNReal.sqrt 2 :=
  by
  have key₁ : b ≠ 0 := ne_of_gt h₀.2
  have h₄ : 0 ≤ a := zero_le _
  suffices a ^ 2 = 18 by
    rw [eq_comm]
    have h₅ : 3 * NNReal.sqrt 2 = NNReal.sqrt 18 := by
      calc
        3 * NNReal.sqrt 2 = NNReal.sqrt 9 * NNReal.sqrt 2 :=
          by
          rw [eq_comm]
          simp
          rw [NNReal.sqrt_eq_iff_sq_eq]
          ring
        _ = NNReal.sqrt (9 * 2) := by rw [← NNReal.sqrt_mul]
        _ = NNReal.sqrt 18 := by ring_nf
        
    rw [h₅, NNReal.sqrt_eq_iff_sq_eq]
    rw [← this]
  have key₂ : 6 * b * b = 54 := by
    rw [h₁] at h₂
    exact (eq_div_iff key₁).mp h₂
  have key₃ : b = 3 :=
    by
    have key₅ : (6 : NNReal) ≠ 0 := by
      refine' nnreal.ne_iff.mp _
      norm_num
    calc
      b = NNReal.sqrt (b * b) := by
        rw [eq_comm]
        apply NNReal.sqrt_mul_self
      _ = NNReal.sqrt (6 * b * b / 6) :=
        by
        refine' congr_arg (⇑NNReal.sqrt) _
        ring_nf
        refine' (eq_div_iff _).mpr _
        · exact key₅
        rw [mul_comm]
      _ = NNReal.sqrt (54 / 6) := by rw [key₂]
      _ = NNReal.sqrt 9 := by
        refine' congr_arg (⇑NNReal.sqrt) _
        refine' (div_eq_iff key₅).mpr _
        ring
      _ = 3 := by
        rw [NNReal.sqrt_eq_iff_sq_eq]
        ring
      
  rw [key₃] at h₁
  rw [h₁]
  ring
#align mathd_algebra_184 mathd_algebra_184

theorem mathd_numbertheory_552 (f g h : ℕ+ → ℕ) (h₀ : ∀ x, f x = 12 * x + 7)
    (h₁ : ∀ x, g x = 5 * x + 2) (h₂ : ∀ x, h x = Nat.gcd (f x) (g x)) (h₃ : Fintype (Set.range h)) :
    (∑ k in (Set.range h).toFinset, k) = 12 := by sorry
#align mathd_numbertheory_552 mathd_numbertheory_552

theorem amc12b_2021_p9 :
    Real.log 80 / Real.log 2 / (Real.log 2 / Real.log 40) -
        Real.log 160 / Real.log 2 / (Real.log 2 / Real.log 20) =
      2 :=
  by sorry
#align amc12b_2021_p9 amc12b_2021_p9

theorem aime_1994_p3 (x : ℤ) (f : ℤ → ℤ) (h0 : f x + f (x - 1) = x ^ 2) (h1 : f 19 = 94) :
    f 94 % 1000 = 561 := by sorry
#align aime_1994_p3 aime_1994_p3

theorem mathd_algebra_44 (s t : ℝ) (h₀ : s = 9 - 2 * t) (h₁ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
  constructor <;> linarith
#align mathd_algebra_44 mathd_algebra_44

theorem mathd_algebra_215 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ (x + 3) ^ 2 = 121) :
    (∑ k in S, k) = -6 := by sorry
#align mathd_algebra_215 mathd_algebra_215

theorem mathd_numbertheory_293 (n : ℕ) (h₀ : n ≤ 9) (h₁ : 11 ∣ 20 * 100 + 10 * n + 7) : n = 5 := by
  sorry
#align mathd_numbertheory_293 mathd_numbertheory_293

theorem mathd_numbertheory_769 : (129 ^ 34 + 96 ^ 38) % 11 = 9 := by sorry
#align mathd_numbertheory_769 mathd_numbertheory_769

theorem mathd_algebra_452 (a : ℕ → ℝ) (h₀ : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n)
    (h₁ : a 1 = 2 / 3) (h₂ : a 9 = 4 / 5) : a 5 = 11 / 15 := by
  linarith [h₀ 1, h₀ 2, h₀ 3, h₀ 4, h₀ 5, h₀ 6, h₀ 7]
#align mathd_algebra_452 mathd_algebra_452

theorem mathd_numbertheory_5 (n : ℕ) (h₀ : 10 ≤ n) (h₁ : ∃ x, x ^ 2 = n) (h₂ : ∃ t, t ^ 3 = n) :
    64 ≤ n := by sorry
#align mathd_numbertheory_5 mathd_numbertheory_5

theorem mathd_numbertheory_207 : 8 * 9 ^ 2 + 5 * 9 + 2 = 695 := by norm_num
#align mathd_numbertheory_207 mathd_numbertheory_207

theorem mathd_numbertheory_342 : 54 % 6 = 0 := by norm_num
#align mathd_numbertheory_342 mathd_numbertheory_342

theorem mathd_numbertheory_483 (a : ℕ → ℕ) (h₀ : a 1 = 1) (h₁ : a 2 = 1)
    (h₂ : ∀ n, a (n + 2) = a (n + 1) + a n) : a 100 % 4 = 3 := by sorry
#align mathd_numbertheory_483 mathd_numbertheory_483

theorem amc12b_2020_p21 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt n)) : S.card = 6 :=
  by sorry
#align amc12b_2020_p21 amc12b_2020_p21

theorem amc12a_2003_p5 (A M C : ℕ) (h₀ : A ≤ 9 ∧ M ≤ 9 ∧ C ≤ 9)
    (h₁ : Nat.ofDigits 10 [0, 1, C, M, A] + Nat.ofDigits 10 [2, 1, C, M, A] = 123422) :
    A + M + C = 14 := by sorry
#align amc12a_2003_p5 amc12a_2003_p5

theorem mathd_numbertheory_495 (a b : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a % 10 = 2) (h₂ : b % 10 = 4)
    (h₃ : Nat.gcd a b = 6) : 108 ≤ Nat.lcm a b := by sorry
#align mathd_numbertheory_495 mathd_numbertheory_495

theorem mathd_algebra_296 : abs ((3491 - 60) * (3491 + 60) - 3491 ^ 2 : ℤ) = 3600 :=
  by
  rw [abs_of_nonpos]
  norm_num
  norm_num
#align mathd_algebra_296 mathd_algebra_296

theorem algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : 3 ≤ a * b + b * c + c * a) :
    3 / Real.sqrt 2 ≤ a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a) := by
  sorry
#align algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2 algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 (f z : ℂ) (h₀ : f + 3 * z = 11)
    (h₁ : 3 * (f - 1) - 5 * z = -68) : f = -10 ∧ z = 7 := by sorry
#align algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7

theorem mathd_numbertheory_247 (n : ℕ) (h₀ : 3 * n % 2 = 11) : n % 11 = 8 := by sorry
#align mathd_numbertheory_247 mathd_numbertheory_247

theorem induction_pord1p1on2powklt5on2 (n : ℕ) (h₀ : 0 < n) :
    (∏ k in Finset.Icc 1 n, 1 + (1 : ℝ) / 2 ^ k) < 5 / 2 := by sorry
#align induction_pord1p1on2powklt5on2 induction_pord1p1on2powklt5on2

theorem mathd_algebra_107 (x y : ℝ) (h₀ : x ^ 2 + 8 * x + y ^ 2 - 6 * y = 0) :
    (x + 4) ^ 2 + (y - 3) ^ 2 = 5 ^ 2 := by linarith
#align mathd_algebra_107 mathd_algebra_107

theorem numbertheory_2pownm1prime_nprime (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.Prime (2 ^ n - 1)) :
    Nat.Prime n := by sorry
#align numbertheory_2pownm1prime_nprime numbertheory_2pownm1prime_nprime

theorem mathd_algebra_412 (x y : ℝ) (h₀ : x + y = 25) (h₁ : x - y = 11) : x = 18 := by linarith
#align mathd_algebra_412 mathd_algebra_412

theorem amc12a_2013_p4 : (2 ^ 2014 + 2 ^ 2012) / (2 ^ 2014 - 2 ^ 2012) = (5 : ℝ) / 3 := by sorry
#align amc12a_2013_p4 amc12a_2013_p4

theorem mathd_algebra_392 (n : ℕ) (h₀ : Even n)
    (h₁ : (↑n - 2) ^ 2 + ↑n ^ 2 + (↑n + 2) ^ 2 = (12296 : ℤ)) :
    (↑n - 2) * ↑n * (↑n + 2) / 8 = (32736 : ℤ) := by sorry
#align mathd_algebra_392 mathd_algebra_392

theorem mathd_numbertheory_314 (r n : ℕ) (h₀ : r = 1342 % 13) (h₁ : 0 < n) (h₂ : 1342 ∣ n)
    (h₃ : n % 13 < r) : 6710 ≤ n := by sorry
#align mathd_numbertheory_314 mathd_numbertheory_314

theorem induction_prod1p1onk3le3m1onn (n : ℕ) (h₀ : 0 < n) :
    (∏ k in Finset.Icc 1 n, 1 + (1 : ℝ) / k ^ 3) ≤ (3 : ℝ) - 1 / ↑n := by sorry
#align induction_prod1p1onk3le3m1onn induction_prod1p1onk3le3m1onn

theorem mathd_numbertheory_343 : (∏ k in Finset.range 6, 2 * k + 1) % 10 = 5 := by sorry
#align mathd_numbertheory_343 mathd_numbertheory_343

theorem mathd_algebra_756 (a b : ℝ) (h₀ : (2 : ℝ) ^ a = 32) (h₁ : a ^ b = 125) : b ^ a = 243 := by
  sorry
#align mathd_algebra_756 mathd_algebra_756

theorem amc12b_2002_p7 (a b c : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : b = a + 1) (h₂ : c = b + 1)
    (h₃ : a * b * c = 8 * (a + b + c)) : a ^ 2 + (b ^ 2 + c ^ 2) = 77 := by sorry
#align amc12b_2002_p7 amc12b_2002_p7

theorem mathd_algebra_80 (x : ℝ) (h₀ : x ≠ -1) (h₁ : (x - 9) / (x + 1) = 2) : x = -11 :=
  by
  revert x h₀ h₁
  norm_num
  intro _ hx
  simp [hx, two_mul, sub_eq_add_neg]
  intro H
  rwa [div_eq_iff_mul_eq] at H
  linarith
  norm_num
  intro h
  exact hx (add_eq_zero_iff_eq_neg.1 h)
#align mathd_algebra_80 mathd_algebra_80

theorem mathd_numbertheory_457 (n : ℕ) (h₀ : 0 < n) (h₁ : 80325 ∣ n !) : 17 ≤ n := by sorry
#align mathd_numbertheory_457 mathd_numbertheory_457

theorem amc12_2000_p12 (a m c : ℕ) (h₀ : a + m + c = 12) :
    a * m * c + a * m + m * c + a * c ≤ 112 := by sorry
#align amc12_2000_p12 amc12_2000_p12

theorem mathd_numbertheory_135 (n A B C : ℕ) (h₀ : n = 3 ^ 17 + 3 ^ 10) (h₁ : 11 ∣ n + 1)
    (h₂ : [A, B, C].Pairwise (· ≠ ·)) (h₃ : {A, B, C} ⊂ Finset.Icc 0 9) (h₄ : Odd A ∧ Odd C)
    (h₅ : ¬3 ∣ B) (h₆ : Nat.digits 10 n = [B, A, B, C, C, A, C, B, A]) :
    100 * A + 10 * B + C = 129 := by sorry
#align mathd_numbertheory_135 mathd_numbertheory_135

theorem mathd_algebra_275 (x : ℝ) (h : ((11 : ℝ) ^ (1 / 4)) ^ (3 * x - 3) = 1 / 5) :
    ((11 : ℝ) ^ (1 / 4)) ^ (6 * x + 2) = 121 / 25 :=
  by
  revert x h
  norm_num
#align mathd_algebra_275 mathd_algebra_275

theorem mathd_algebra_388 (x y z : ℝ) (h₀ : 3 * x + 4 * y - 12 * z = 10)
    (h₁ : -2 * x - 3 * y + 9 * z = -4) : x = 14 := by linarith
#align mathd_algebra_388 mathd_algebra_388

theorem amc12a_2020_p7 (a : ℕ → ℕ) (h₀ : a 0 ^ 3 = 1) (h₁ : a 1 ^ 3 = 8) (h₂ : a 2 ^ 3 = 27)
    (h₃ : a 3 ^ 3 = 64) (h₄ : a 4 ^ 3 = 125) (h₅ : a 5 ^ 3 = 216) (h₆ : a 6 ^ 3 = 343) :
    ↑(∑ k in Finset.range 7, 6 * a k ^ 2) - ↑(2 * ∑ k in Finset.range 6, a k ^ 2) = (658 : ℤ) := by
  sorry
#align amc12a_2020_p7 amc12a_2020_p7

theorem imo_1981_p6 (f : ℕ → ℕ → ℕ) (h₀ : ∀ y, f 0 y = y + 1) (h₁ : ∀ x, f (x + 1) 0 = f x 1)
    (h₂ : ∀ x y, f (x + 1) (y + 1) = f x (f (x + 1) y)) : ∀ y, f 4 (y + 1) = 2 ^ (f 4 y + 3) - 3 :=
  by sorry
#align imo_1981_p6 imo_1981_p6

theorem mathd_algebra_263 (y : ℝ) (h₀ : 0 ≤ 19 + 3 * y) (h₁ : Real.sqrt (19 + 3 * y) = 7) :
    y = 10 := by
  revert y h₀ h₁
  intro x hx
  rw [Real.sqrt_eq_iff_sq_eq hx]
  swap
  norm_num
  intro h
  nlinarith
#align mathd_algebra_263 mathd_algebra_263

theorem mathd_numbertheory_34 (x : ℕ) (h₀ : x < 100) (h₁ : x * 9 % 100 = 1) : x = 89 := by sorry
#align mathd_numbertheory_34 mathd_numbertheory_34

theorem mathd_numbertheory_764 (p : ℕ) (h₀ : Nat.Prime p) (h₁ : 7 ≤ p) :
    (∑ k in Finset.Icc 1 (p - 2), (k : ZMod p)⁻¹ * ((k : ZMod p) + 1)⁻¹) = 2 := by sorry
#align mathd_numbertheory_764 mathd_numbertheory_764

theorem amc12b_2021_p4 (m a : ℕ) (h₀ : 0 < m ∧ 0 < a) (h₁ : ↑m / ↑a = (3 : ℝ) / 4) :
    (84 * ↑m + 70 * ↑a) / (↑m + ↑a) = (76 : ℝ) :=
  by
  have h₂ : (a : ℝ) ≠ 0 := by
    norm_cast
    linarith
  calc
    ((84 : ℝ) * ↑m + 70 * ↑a) / (↑m + ↑a) = (84 * ↑m + 70 * ↑a) / ↑a / ((↑m + ↑a) / ↑a) := by
      rw [← div_div_div_cancel_right (84 * ↑m + 70 * ↑a) h₂]
    _ = (84 * ↑m / ↑a + 70 * ↑a / ↑a) / (↑m / ↑a + ↑a / ↑a) := by repeat' rw [← div_add_div_same]
    _ = (84 * (↑m / ↑a) + 70) / (↑m / ↑a + 1) := by simp only [mul_div_assoc, div_self h₂, mul_one]
    _ = (84 * (3 / 4) + 70) / (3 / 4 + 1) := by rw [h₁]
    _ = (76 : ℝ) := by norm_num
    
#align amc12b_2021_p4 amc12b_2021_p4

theorem imo_1962_p2 (x : ℝ) (h₀ : 0 ≤ 3 - x) (h₁ : 0 ≤ x + 1)
    (h₂ : 1 / 2 < Real.sqrt (3 - x) - Real.sqrt (x + 1)) : -1 ≤ x ∧ x < 1 - Real.sqrt 31 / 8 := by
  sorry
#align imo_1962_p2 imo_1962_p2

theorem mathd_algebra_170 (S : Finset ℤ) (h₀ : ∀ n : ℤ, n ∈ S ↔ abs (n - 2) ≤ 5 + 6 / 10) :
    S.card = 11 := by sorry
#align mathd_algebra_170 mathd_algebra_170

theorem mathd_algebra_432 (x : ℝ) : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := by linarith
#align mathd_algebra_432 mathd_algebra_432

theorem mathd_algebra_598 (a b c d : ℝ) (h₁ : (4 : ℝ) ^ a = 5) (h₂ : (5 : ℝ) ^ b = 6)
    (h₃ : (6 : ℝ) ^ c = 7) (h₄ : (7 : ℝ) ^ d = 8) : a * b * c * d = 3 / 2 := by sorry
#align mathd_algebra_598 mathd_algebra_598

theorem algebra_bleqa_apbon2msqrtableqambsqon8b (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : b ≤ a) :
    (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by sorry
#align algebra_bleqa_apbon2msqrtableqambsqon8b algebra_bleqa_apbon2msqrtableqambsqon8b

theorem mathd_algebra_276 (a b : ℤ)
    (h₀ : ∀ x : ℝ, 10 * x ^ 2 - x - 24 = (a * x - 8) * (b * x + 3)) : a * b + b = 12 :=
  by
  have h₁ := h₀ 1
  have h₂ := h₀ (-1)
  ring_nf  at h₁ h₂
  have h₃ :
    (-13 : ℝ) + (-15 : ℝ) = (↑b - 3) * ↑a + (8 * ↑b - 24) + ((↑b + 3) * ↑a + (-(8 * ↑b) - 24)) :=
    by
    refine' congr (congr _ _) _
    · rfl
    · exact h₂
    · exact h₁
  ring_nf  at h₃
  have h₄ : ↑a * ↑b = (10 : ℝ)
  linarith
  rw [sub_mul, mul_comm, h₄] at h₂
  rw [add_mul, mul_comm, h₄] at h₁
  have h₆ : (8 : ℝ) * ↑b - 3 * ↑a = 1
  linarith
  norm_cast  at h₆
  norm_cast  at h₄
  clear h₀ h₁ h₂ h₃
  suffices l₀ : b = 2
  · rw [l₀]
    linarith
  have h₇ := Dvd.intro_left a h₄
  have h₈ : ∀ n : ℤ, n ∣ 10 ↔ n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 10 ∨ n = -1 ∨ n = -2 ∨ n = -5 ∨ n = -10 :=
    by
    intro n
    have coe := @Int.coe_nat_dvd_right 10 n
    norm_cast  at coe
    rw [coe]
    have h_div : Nat.divisors 10 = ⟨Quot.mk _ [1, 2, 5, 10], _⟩ := rfl
    rw [← nat.mem_divisors.trans (and_iff_left (by norm_num : 10 ≠ 0)), h_div]
    change n.nat_abs ∈ (_ : List _) ↔ _
    simp only [List.mem_cons, List.mem_singleton, Int.natAbs_eq_iff, Int.ofNat_succ, Int.ofNat_zero,
      zero_add, Int.ofNat_bit0, Int.ofNat_bit1]
    finish
  have h₉ := (h₈ b).mp h₇
  clear h₈
  cases h₉
  · rw [h₉] at h₄ h₆
    norm_num at h₆ h₄
    rw [h₄] at h₆
    contradiction
  · cases h₉
    · exact h₉
    · cases h₉
      · rw [h₉] at h₄ h₆
        norm_num at h₆ h₄
        have a_val : a = 2
        linarith
        rw [a_val] at h₆
        norm_num at h₆
      cases h₉
      · rw [h₉] at h₄ h₆
        norm_num at h₆ h₄
        have a_val : a = 1
        linarith
        rw [a_val] at h₆
        norm_num at h₆
      · cases h₉
        · rw [h₉] at h₄ h₆
          norm_num at h₆ h₄
          have a_val : a = -1
          linarith
          rw [a_val] at h₆
          norm_num at h₆
        · cases h₉
          · rw [h₉] at h₄ h₆
            norm_num at h₆ h₄
            have a_val : a = -2
            linarith
            rw [a_val] at h₆
            norm_num at h₆
          · cases h₉
            · rw [h₉] at h₄ h₆
              norm_num at h₆ h₄
              have a_val : a = -5
              linarith
              rw [a_val] at h₆
              norm_num at h₆
            · rw [h₉] at h₄ h₆
              norm_num at h₆ h₄
              have a_val : a = -10
              linarith
              rw [a_val] at h₆
              norm_num at h₆
#align mathd_algebra_276 mathd_algebra_276

theorem amc12a_2021_p14 :
    ((∑ k in Finset.Icc 1 20, Real.logb (5 ^ k) (3 ^ k ^ 2)) *
        ∑ k in Finset.Icc 1 100, Real.logb (9 ^ k) (25 ^ k)) =
      21000 :=
  by sorry
#align amc12a_2021_p14 amc12a_2021_p14

theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
    (∑ k in Finset.Icc (2 : ℕ) 10000, 1 / Real.sqrt k) < 198 := by sorry
#align algebra_sum1onsqrt2to1onsqrt10000lt198 algebra_sum1onsqrt2to1onsqrt10000lt198

theorem mathd_numbertheory_618 (n : ℕ) (p : ℕ → ℕ) (h₀ : ∀ x, p x = x ^ 2 - x + 41)
    (h₁ : 1 < Nat.gcd (p n) (p (n + 1))) : 41 ≤ n := by sorry
#align mathd_numbertheory_618 mathd_numbertheory_618

theorem amc12a_2020_p4 (S : Finset ℕ)
    (h₀ : ∀ n : ℕ, n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
    S.card = 100 := by sorry
#align amc12a_2020_p4 amc12a_2020_p4

theorem amc12b_2020_p6 (n : ℕ) (h₀ : 9 ≤ n) : ∃ x : ℕ, (x : ℝ) ^ 2 = ((n + 2)! - (n + 1)!) / n ! :=
  by sorry
#align amc12b_2020_p6 amc12b_2020_p6

theorem mathd_numbertheory_435 (k : ℕ) (h₀ : 0 < k) (h₁ : ∀ n, gcd (6 * n + k) (6 * n + 3) = 1)
    (h₂ : ∀ n, gcd (6 * n + k) (6 * n + 2) = 1) (h₃ : ∀ n, gcd (6 * n + k) (6 * n + 1) = 1) :
    5 ≤ k := by sorry
#align mathd_numbertheory_435 mathd_numbertheory_435

theorem algebra_others_exirrpowirrrat : ∃ a b, Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) :=
  by
  let sqrt_2 := Real.sqrt 2
  by_cases Irrational (sqrt_2 ^ sqrt_2)
  · have h' : ¬Irrational ((sqrt_2 ^ sqrt_2) ^ sqrt_2) :=
      by
      intro h
      rw [← Real.rpow_mul (Real.sqrt_nonneg 2) (Real.sqrt 2) (Real.sqrt 2)] at h
      have zlet : 0 ≤ (2 : ℝ) := by norm_num
      rw [← Real.sqrt_mul zlet 2] at h
      rw [Real.sqrt_mul_self zlet] at h
      have x : Real.sqrt 2 ^ (2 : ℕ) = Real.sqrt 2 ^ (2 : ℝ) := by norm_cast
      rw [← x] at h
      rw [Real.sq_sqrt zlet] at h
      have tnotira : ¬Irrational 2 := by
        convert Rat.not_irrational 2
        norm_cast
      exact tnotira h
    exact ⟨sqrt_2 ^ sqrt_2, sqrt_2, h, irrational_sqrt_two, h'⟩
  · exact ⟨sqrt_2, sqrt_2, irrational_sqrt_two, irrational_sqrt_two, h⟩
#align algebra_others_exirrpowirrrat algebra_others_exirrpowirrrat

theorem mathd_algebra_427 (x y z : ℝ) (h₀ : 3 * x + y = 17) (h₁ : 5 * y + z = 14)
    (h₂ : 3 * x + 5 * z = 41) : x + y + z = 12 :=
  by
  have h₃ := congr (congr_arg Add.add h₀) h₁
  linarith
#align mathd_algebra_427 mathd_algebra_427

theorem mathd_algebra_76 (f : ℤ → ℤ) (h₀ : ∀ n, Odd n → f n = n ^ 2)
    (h₁ : ∀ n, Even n → f n = n ^ 2 - 4 * n - 1) : f 4 = -1 :=
  by
  suffices : f 4 = 4 ^ 2 - 4 * 4 - 1; rw [this] <;> ring_nf
  apply h₁
  refine' even_iff_two_dvd.mpr _
  exact two_dvd_bit0
#align mathd_algebra_76 mathd_algebra_76

theorem mathd_numbertheory_99 (n : ℕ) (h₀ : 2 * n % 47 = 15) : n % 47 = 31 := by sorry
#align mathd_numbertheory_99 mathd_numbertheory_99

theorem algebra_9onxpypzleqsum2onxpy (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by sorry
#align algebra_9onxpypzleqsum2onxpy algebra_9onxpypzleqsum2onxpy

theorem mathd_numbertheory_233 (b : ZMod (11 ^ 2)) (h₀ : b = 24⁻¹) : b = 116 := by sorry
#align mathd_numbertheory_233 mathd_numbertheory_233

theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa (a b : ℝ) :
    abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by sorry
#align algebra_absapbon1pabsapbleqsumabsaon1pabsa algebra_absapbon1pabsapbleqsumabsaon1pabsa

theorem imo_1984_p6 (a b c d k m : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d) (h₂ : a < b ∧ b < c ∧ c < d) (h₃ : a * d = b * c)
    (h₄ : a + d = 2 ^ k) (h₅ : b + c = 2 ^ m) : a = 1 := by sorry
#align imo_1984_p6 imo_1984_p6

theorem imo_2001_p6 (a b c d : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) (h₁ : d < c) (h₂ : c < b)
    (h₃ : b < a) (h₄ : a * c + b * d = (b + d + a - c) * (b + d + c - a)) :
    ¬Nat.Prime (a * b + c * d) := by sorry
#align imo_2001_p6 imo_2001_p6

theorem mathd_numbertheory_321 (n : ZMod 1399) (h₁ : n = 160⁻¹) : n = 1058 := by sorry
#align mathd_numbertheory_321 mathd_numbertheory_321

theorem mathd_algebra_17 (a : ℝ)
    (h₀ : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) :
    a = 8 :=
  by
  have sq_4 : 4 = Real.sqrt 16 := by
    have h₃ : (16 : ℝ) = 4 ^ 2
    norm_num
    simp only [h₃, Real.sqrt_sq, zero_le_bit0, zero_le_one]
  have sq_3 : 3 = Real.sqrt 9 := by
    have h₃ : (9 : ℝ) = 3 ^ 2
    norm_num
    have h₄ : (0 : ℝ) ≤ 3
    norm_num
    simp only [h₃, h₄, Real.sqrt_sq]
  have h₁ : Real.sqrt (16 + 16 * a) = 4 * Real.sqrt (1 + a) := by
    calc
      Real.sqrt (16 + 16 * a) = Real.sqrt (16 * (1 + a)) :=
        by
        refine' congr_arg Real.sqrt _
        ring_nf
      _ = Real.sqrt 16 * Real.sqrt (1 + a) :=
        by
        rw [Real.sqrt_mul]
        norm_num
      _ = 4 * Real.sqrt (1 + a) := by rw [← sq_4]
      
  rw [h₁] at h₀
  let u := Real.sqrt (1 + a)
  change Real.sqrt (1 + a) with u at h₀
  have sq_2 : 2 = Real.sqrt 4 := by
    have h₄ : (4 : ℝ) = 2 ^ 2
    norm_num
    simp only [h₄, Real.sqrt_sq, zero_le_bit0, zero_le_one]
  have h₂ : Real.sqrt (4 + 4 * u) = 2 * Real.sqrt (1 + u) := by
    calc
      Real.sqrt (4 + 4 * u) = Real.sqrt (4 * (1 + u)) :=
        by
        refine' congr_arg Real.sqrt _
        ring_nf
      _ = Real.sqrt 4 * Real.sqrt (1 + u) :=
        by
        rw [Real.sqrt_mul]
        norm_num
      _ = 2 * Real.sqrt (1 + u) := by rw [← sq_2]
      
  rw [h₂] at h₀
  let v := Real.sqrt (1 + u)
  change Real.sqrt (1 + u) with v at h₀
  have v_val : v = 2
  linarith
  have u_val : u = 3 := by
    dsimp only [v] at v_val
    rw [sq_2] at v_val
    have p₀ : (0 : ℝ) < 4
    norm_num
    have p₁ := le_of_lt p₀
    have p₃ := real.sqrt_pos.mpr p₀
    rw [← v_val] at p₃
    have p₂ := real.sqrt_pos.mp p₃
    have p₄ := le_of_lt p₂
    simp only [p₁, p₄, Real.sqrt_inj] at v_val
    linarith
  dsimp only [u] at u_val
  rw [sq_3] at u_val
  have p₀ : (0 : ℝ) < 9
  norm_num
  have p₁ := le_of_lt p₀
  have p₃ := real.sqrt_pos.mpr p₀
  rw [← u_val] at p₃
  have p₂ := real.sqrt_pos.mp p₃
  have p₄ := le_of_lt p₂
  simp only [p₁, p₄, Real.sqrt_inj] at u_val
  linarith
#align mathd_algebra_17 mathd_algebra_17

theorem mathd_algebra_153 (n : ℝ) (h₀ : n = 1 / 3) :
    Int.floor (10 * n) + Int.floor (100 * n) + Int.floor (1000 * n) + Int.floor (10000 * n) =
      3702 :=
  by sorry
#align mathd_algebra_153 mathd_algebra_153

theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h₀ : a ^ 2 + b ^ 2 = 1) :
    a * b + (a - b) ≤ 1 := by nlinarith [sq_nonneg (a - b)]
#align algebra_sqineq_unitcircatbpamblt1 algebra_sqineq_unitcircatbpamblt1

theorem amc12a_2021_p18 (f : ℚ → ℝ) (h₀ : ∀ x > 0, ∀ y > 0, f (x * y) = f x + f y)
    (h₁ : ∀ p, Nat.Prime p → f p = p) : f (25 /. 11) < 0 := by sorry
#align amc12a_2021_p18 amc12a_2021_p18

theorem mathd_algebra_329 (x y : ℝ) (h₀ : 3 * y = x) (h₁ : 2 * x + 5 * y = 11) : x + y = 4 := by
  linarith
#align mathd_algebra_329 mathd_algebra_329

theorem induction_pprime_pdvdapowpma (p a : ℕ) (h₀ : 0 < a) (h₁ : Nat.Prime p) : p ∣ a ^ p - a := by
  sorry
#align induction_pprime_pdvdapowpma induction_pprime_pdvdapowpma

theorem amc12a_2021_p9 : (∏ k in Finset.range 7, 2 ^ 2 ^ k + 3 ^ 2 ^ k) = 3 ^ 128 - 2 ^ 128 :=
  by
  simp only [Finset.prod_range_succ]
  norm_num
#align amc12a_2021_p9 amc12a_2021_p9

-- Sum a sequence by grouping adjacent terms.
theorem sum_pairs (n : ℕ) (f : ℕ → ℚ) :
    (∑ k in Finset.range (2 * n), f k) = ∑ k in Finset.range n, f (2 * k) + f (2 * k + 1) :=
  by
  induction' n with pn hpn
  · simp only [Finset.sum_empty, Finset.range_zero, MulZeroClass.mul_zero]
  · have hs : 2 * pn.succ = (2 * pn).succ.succ := rfl
    rw [Finset.sum_range_succ, ← hpn, hs, Finset.sum_range_succ, Finset.sum_range_succ]
    ring
#align sum_pairs sum_pairs

theorem aime_1984_p1 (u : ℕ → ℚ) (h₀ : ∀ n, u (n + 1) = u n + 1)
    (h₁ : (∑ k in Finset.range 98, u k.succ) = 137) :
    (∑ k in Finset.range 49, u (2 * k.succ)) = 93 :=
  by
  -- We will use sum_pairs and h₀ to rewrite h₁ and the goal in terms of the quantity
  -- ∑ k in finset.range 49, u (2 * k + 1).
  have h₂ : ∀ k, k ∈ Finset.range 49 → u (2 * k + 1 + 1) = u (2 * k + 1) + 1 :=
    by
    intro k hk
    exact h₀ (2 * k + 1)
  have h₃ : (∑ x : ℕ in Finset.range 49, (1 : ℚ)) = 49 := by
    simp only [mul_one, Nat.cast_bit0, Finset.sum_const, nsmul_eq_mul, Nat.cast_bit1,
      Finset.card_range, Nat.cast_one]
  have h98 : 98 = 2 * 49 := by norm_num
  rw [h98, sum_pairs, Finset.sum_add_distrib, Finset.sum_congr rfl h₂, Finset.sum_add_distrib, h₃, ←
    add_assoc] at h₁
  have h₄ :
    (∑ k : ℕ in Finset.range 49, u (2 * k.succ)) = ∑ k : ℕ in Finset.range 49, u (2 * k + 1) + 1 :=
    Finset.sum_congr rfl h₂
  rw [h₄, Finset.sum_add_distrib, h₃]
  linarith
#align aime_1984_p1 aime_1984_p1

theorem amc12a_2021_p22 (a b c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = x ^ 3 + a * x ^ 2 + b * x + c)
    (h₁ :
      f ⁻¹' {0} =
        {Real.cos (2 * Real.pi / 7), Real.cos (4 * Real.pi / 7), Real.cos (6 * Real.pi / 7)}) :
    a * b * c = 1 / 32 := by sorry
#align amc12a_2021_p22 amc12a_2021_p22

theorem mathd_numbertheory_229 : 5 ^ 30 % 7 = 1 :=
  by
  have five_to_thirty_is_one : (5 ^ 30 : ZMod 7) = 1 :=
    by
    have five_to_the_six_is_one : (5 ^ 6 : ZMod 7) = 1 := by decide
    have break_power : (5 ^ 30 : ZMod 7) = (5 ^ 6) ^ 5 := by norm_num
    rw [break_power]
    rw [five_to_the_six_is_one]
    norm_num
  change 5 ^ 30 ≡ 1 [MOD 7]
  rw [← ZMod.eq_iff_modEq_nat]
  exact_mod_cast five_to_thirty_is_one
#align mathd_numbertheory_229 mathd_numbertheory_229

theorem mathd_numbertheory_100 (n : ℕ) (h₀ : 0 < n) (h₁ : Nat.gcd n 40 = 10)
    (h₂ : Nat.lcm n 40 = 280) : n = 70 := by sorry
#align mathd_numbertheory_100 mathd_numbertheory_100

theorem mathd_algebra_313 (v i z : ℂ) (h₀ : v = i * z) (h₁ : v = 1 + Complex.I)
    (h₂ : z = 2 - Complex.I) : i = 1 / 5 + 3 / 5 * Complex.I :=
  by
  rw [h₁, h₂] at h₀
  rw [eq_comm] at h₀
  have h₃ : 2 - Complex.I ≠ 0 := by sorry
  have h₄ := (eq_div_iff h₃).mpr h₀
  rw [h₄]
  rw [eq_comm]
  apply (eq_div_iff h₃).mpr
  sorry
#align mathd_algebra_313 mathd_algebra_313

theorem amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n) (h₁ : (1 /. 2 + 1 /. 3 + 1 /. 7 + 1 /. ↑n).den = 1) :
    n = 42 := by sorry
#align amc12b_2002_p4 amc12b_2002_p4

theorem amc12a_2002_p6 (n : ℕ) (h₀ : 0 < n) : ∃ m, m > n ∧ ∃ p, m * p ≤ m + p :=
  by
  use (n : ℕ).succ
  norm_num
  constructor
  · exact_mod_cast Nat.lt_succ_self _
  use 1
  rw [mul_one]
  apply Nat.succ_le_succ
  exact le_of_lt (Nat.lt_succ_self n)
#align amc12a_2002_p6 amc12a_2002_p6

theorem amc12a_2003_p23 (S : Finset ℕ)
    (h₀ : ∀ k : ℕ, k ∈ S ↔ 0 < k ∧ (k * k : ℕ) ∣ ∏ i in Finset.Icc 1 9, i !) : S.card = 672 := by
  sorry
#align amc12a_2003_p23 amc12a_2003_p23

theorem mathd_algebra_129 (a : ℝ) (h₀ : a ≠ 0) (h₁ : 8⁻¹ / 4⁻¹ - a⁻¹ = 1) : a = -2 :=
  by
  field_simp  at h₁
  linarith
#align mathd_algebra_129 mathd_algebra_129

theorem amc12b_2021_p18 (z : ℂ)
    (h₀ : 12 * Complex.normSq z = 2 * Complex.normSq (z + 2) + Complex.normSq (z ^ 2 + 1) + 31) :
    z + 6 / z = -2 := by sorry
#align amc12b_2021_p18 amc12b_2021_p18

theorem mathd_algebra_484 : Real.log 27 / Real.log 3 = 3 :=
  by
  rw [Real.log_div_log]
  have three_to_three : (27 : ℝ) = (3 : ℝ) ^ (3 : ℝ) := by norm_num
  rw [three_to_three]
  have trivial_ineq : (0 : ℝ) < (3 : ℝ) := by norm_num
  have trivial_neq : (3 : ℝ) ≠ (1 : ℝ) := by norm_num
  exact Real.logb_rpow trivial_ineq trivial_neq
#align mathd_algebra_484 mathd_algebra_484

theorem mathd_numbertheory_551 : 1529 % 6 = 5 := by norm_num
#align mathd_numbertheory_551 mathd_numbertheory_551

theorem mathd_algebra_304 : 91 ^ 2 = 8281 := by norm_num
#align mathd_algebra_304 mathd_algebra_304

theorem amc12a_2021_p8 (d : ℕ → ℕ) (h₀ : d 0 = 0) (h₁ : d 1 = 0) (h₂ : d 2 = 1)
    (h₃ : ∀ n ≥ 3, d n = d (n - 1) + d (n - 3)) : Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by
  sorry
#align amc12a_2021_p8 amc12a_2021_p8

theorem algebra_ineq_nto1onlt2m1on (n : ℕ) : (n : ℝ) ^ ((1 : ℝ) / n) < 2 - 1 / n := by sorry
#align algebra_ineq_nto1onlt2m1on algebra_ineq_nto1onlt2m1on

theorem amc12b_2002_p19 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : a * (b + c) = 152)
    (h₂ : b * (c + a) = 162) (h₃ : c * (a + b) = 170) : a * b * c = 720 := by nlinarith
#align amc12b_2002_p19 amc12b_2002_p19

theorem mathd_numbertheory_341 (a b c : ℕ) (h₀ : a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9)
    (h₁ : Nat.digits 10 (5 ^ 100 % 1000) = [c, b, a]) : a + b + c = 13 := by sorry
#align mathd_numbertheory_341 mathd_numbertheory_341

theorem mathd_numbertheory_711 (m n : ℕ) (h₀ : 0 < m ∧ 0 < n) (h₁ : gcd m n = 8)
    (h₂ : lcm m n = 112) : 72 ≤ m + n := by sorry
#align mathd_numbertheory_711 mathd_numbertheory_711

theorem amc12b_2020_p22 (t : ℝ) : (2 ^ t - 3 * t) * t / 4 ^ t ≤ 1 / 12 := by sorry
#align amc12b_2020_p22 amc12b_2020_p22

theorem mathd_algebra_113 (x : ℝ) : x ^ 2 - 14 * x + 3 ≥ 7 ^ 2 - 14 * 7 + 3 := by sorry
#align mathd_algebra_113 mathd_algebra_113

theorem amc12a_2020_p9 (S : Finset ℝ)
    (h₀ : ∀ x : ℝ, x ∈ S ↔ 0 ≤ x ∧ x ≤ 2 * Real.pi ∧ Real.tan (2 * x) = Real.cos (x / 2)) :
    S.card = 5 := by sorry
#align amc12a_2020_p9 amc12a_2020_p9

theorem amc12_2000_p1 (i m o : ℕ) (h₀ : i ≠ m ∧ m ≠ o ∧ o ≠ i) (h₁ : i * m * o = 2001) :
    i + m + o ≤ 671 := by sorry
#align amc12_2000_p1 amc12_2000_p1

theorem amc12a_2021_p19 (S : Finset ℝ)
    (h₀ :
      ∀ x : ℝ,
        x ∈ S ↔
          0 ≤ x ∧
            x ≤ Real.pi ∧
              Real.sin (Real.pi / 2 * Real.cos x) = Real.cos (Real.pi / 2 * Real.sin x)) :
    S.card = 2 := by sorry
#align amc12a_2021_p19 amc12a_2021_p19

theorem algebra_amgm_sumasqdivbgeqsuma (a b c d : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by sorry
#align algebra_amgm_sumasqdivbgeqsuma algebra_amgm_sumasqdivbgeqsuma

theorem mathd_numbertheory_212 : 16 ^ 17 * 17 ^ 18 * 18 ^ 19 % 10 = 8 := by sorry
#align mathd_numbertheory_212 mathd_numbertheory_212

theorem mathd_numbertheory_320 (n : ℕ) (h₀ : n < 101) (h₁ : 101 ∣ 123456 - n) : n = 34 := by sorry
#align mathd_numbertheory_320 mathd_numbertheory_320

theorem mathd_algebra_125 (x y : ℕ) (h₀ : 0 < x ∧ 0 < y) (h₁ : 5 * x = y)
    (h₂ : ↑x - (3 : ℤ) + (y - (3 : ℤ)) = 30) : x = 6 := by sorry
#align mathd_algebra_125 mathd_algebra_125

theorem induction_1pxpownlt1pnx (x : ℝ) (n : ℕ) (h₀ : -1 < x) (h₁ : 0 < n) :
    1 + ↑n * x ≤ (1 + x) ^ (n : ℕ) := by sorry
#align induction_1pxpownlt1pnx induction_1pxpownlt1pnx

theorem mathd_algebra_148 (c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = c * x ^ 3 - 9 * x + 3)
    (h₁ : f 2 = 9) : c = 3 := by
  rw [h₀] at h₁
  linarith
#align mathd_algebra_148 mathd_algebra_148

theorem amc12a_2019_p12 (x y : ℝ) (h₀ : x ≠ 1 ∧ y ≠ 1)
    (h₁ : Real.log x / Real.log 2 = Real.log 16 / Real.log y) (h₂ : x * y = 64) :
    (Real.log (x / y) / Real.log 2) ^ 2 = 20 := by sorry
#align amc12a_2019_p12 amc12a_2019_p12

theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ 10 ^ n - (-1 : ℤ) ^ n := by sorry
#align induction_11div10tonmn1ton induction_11div10tonmn1ton

theorem algebra_amgm_sum1toneqn_prod1tonleq1 (a : ℕ → NNReal) (n : ℕ)
    (h₀ : (∑ x in Finset.range n, a x) = n) : (∏ x in Finset.range n, a x) ≤ 1 := by sorry
#align algebra_amgm_sum1toneqn_prod1tonleq1 algebra_amgm_sum1toneqn_prod1tonleq1

theorem imo_1985_p6 (f : ℕ → NNReal → ℝ) (h₀ : ∀ x, f 1 x = x)
    (h₁ : ∀ x n, f (n + 1) x = f n x * (f n x + 1 / n)) :
    ∃! a, ∀ n, 0 < n → 0 < f n a ∧ f n a < f (n + 1) a ∧ f (n + 1) a < 1 := by sorry
#align imo_1985_p6 imo_1985_p6

theorem amc12a_2020_p15 (a b : ℂ) (h₀ : a ^ 3 - 8 = 0) (h₁ : b ^ 3 - 8 * b ^ 2 - 8 * b + 64 = 0) :
    Complex.abs (a - b) ≤ 2 * Real.sqrt 21 := by sorry
#align amc12a_2020_p15 amc12a_2020_p15

theorem mathd_algebra_332 (x y : ℝ) (h₀ : (x + y) / 2 = 7) (h₁ : Real.sqrt (x * y) = Real.sqrt 19) :
    x ^ 2 + y ^ 2 = 158 :=
  by
  have h₂ : (x + y) ^ 2 = 14 ^ 2 := by
    suffices : x + y = 14
    rw [this]
    linarith
  have key : 0 < Real.sqrt 19
  norm_num
  have h₃ := (@Real.sqrt_eq_iff_sq_eq (x * y) (Real.sqrt 19) _ _).mp h₁
  · rw [Real.sq_sqrt _] at h₃
    · linarith
    · norm_num
  · refine' le_of_lt _
    apply real.sqrt_pos.mp
    rwa [h₁]
  exact le_of_lt key
#align mathd_algebra_332 mathd_algebra_332

theorem algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778 (r : ℝ)
    (h₀ : r ^ ((1 : ℝ) / 3) + 1 / r ^ ((1 : ℝ) / 3) = 3) : r ^ 3 + 1 / r ^ 3 = 5778 := by sorry
#align algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778 algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778

theorem mathd_algebra_293 (x : NNReal) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) :=
  by
  have h₀ := NNReal.coe_nonneg x
  have h₁ := NNReal.coe_nonneg (60 * x)
  have h₂ := NNReal.coe_nonneg (12 * x)
  have h₃ := NNReal.coe_nonneg (63 * x)
  have h₄ := NNReal.coe_nonneg (35 * x)
  have h₅ := NNReal.coe_nonneg (36 * x)
  simp only [Nonneg.coe_mul, [anonymous], [anonymous], Nonneg.coe_one] at h₁ h₂ h₃ h₄ h₅
  have h₆ := sq_nonneg ((36 : ℝ) * ↑x)
  rw [← Real.sqrt_sq h₅]
  rw [← Real.sqrt_mul', ← Real.sqrt_mul', ← Real.sqrt_mul']
  · refine' (Real.sqrt_inj _ _).mpr _
    · apply mul_nonneg <;> apply mul_nonneg <;> linarith
    · apply mul_nonneg <;> linarith
    ring_nf
  all_goals linarith
#align mathd_algebra_293 mathd_algebra_293

theorem mathd_algebra_440 (x : ℝ) (h₀ : 3 / 2 / 3 = x / 10) : x = 5 :=
  by
  field_simp  at h₀
  linarith
#align mathd_algebra_440 mathd_algebra_440

theorem mathd_numbertheory_254 : (239 + 174 + 83) % 10 = 6 := by norm_num
#align mathd_numbertheory_254 mathd_numbertheory_254

theorem amc12_2000_p6 (p q : ℕ) (h₀ : Nat.Prime p ∧ Nat.Prime q) (h₁ : 4 ≤ p ∧ p ≤ 18)
    (h₂ : 4 ≤ q ∧ q ≤ 18) : ↑p * ↑q - (↑p + ↑q) ≠ (194 : ℤ) :=
  by
  revert p q h₀ h₁ h₂
  intro p q hpq
  rintro ⟨hp, hq⟩
  rintro ⟨h, h⟩
  intro h
  have h₁ := Nat.Prime.ne_zero hpq.1
  have h₂ : q ≠ 0 := by
    rintro rfl
    simp_all
  apply h₁
  revert hpq
  intro h
  simp_all
  apply h₁
  have h₃ : q = 10 * q
  apply Eq.symm
  all_goals decide!
#align amc12_2000_p6 amc12_2000_p6

theorem aime_1988_p8 (f : ℕ → ℕ → ℝ) (h₀ : ∀ x, 0 < x → f x x = x)
    (h₁ : ∀ x y, 0 < x ∧ 0 < y → f x y = f y x)
    (h₂ : ∀ x y, 0 < x ∧ 0 < y → (↑x + ↑y) * f x y = y * f x (x + y)) : f 14 52 = 364 := by sorry
#align aime_1988_p8 aime_1988_p8

theorem mathd_algebra_114 (a : ℝ) (h₀ : a = 8) :
    (16 * (a ^ 2) ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 3) = 4 :=
  by
  rw [h₀]
  have k₁ : 0 ≤ (4 : ℝ)
  linarith
  have k₂ : 3 ≠ 0
  linarith
  have k₃ : (64 : ℝ) = 4 ^ (3 : ℝ) :=
    by
    suffices (64 : ℝ) = 4 ^ ((3 : ℕ) : ℝ) by
      rw [this]
      norm_cast
    suffices (64 : ℝ) = 4 ^ (3 : ℕ) by
      rw [this]
      rw [eq_comm]
      exact Real.rpow_nat_cast (4 : ℝ) 3
    norm_num
  have k₄ : (16 : ℝ) = 4 ^ 2
  linarith
  have k₆ : 0 ≤ (64 : ℝ)
  linarith
  have k₇ : (1 : ℝ) / 3 = (↑3)⁻¹ := by
    norm_cast
    exact one_div 3
  have k₈ : (4 : ℝ) ^ (3 : ℝ) = (4 : ℝ) ^ (3 : ℕ) :=
    by
    suffices (4 : ℝ) ^ ((3 : ℕ) : ℝ) = (4 : ℝ) ^ (3 : ℕ)
      by
      rw [← this]
      norm_num
    exact Real.rpow_nat_cast (4 : ℝ) 3
  have k₅ : ((4 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (4 : ℝ) :=
    by
    rw [k₇]
    rw [k₈]
    refine' Real.pow_nat_rpow_nat_inv k₁ k₂
  norm_num
  rw [k₃]
  rw [k₄]
  rw [k₅]
  suffices (4 : ℝ) ^ 2 * (4 : ℝ) = 4 ^ 3 by
    rw [this]
    rw [k₇]
    refine' Real.pow_nat_rpow_nat_inv k₁ k₂
  norm_num
#align mathd_algebra_114 mathd_algebra_114

theorem imo_2019_p1 (f : ℤ → ℤ) :
    (∀ a b, f (2 * a) + 2 * f b = f (f (a + b))) ↔ ∀ z, f z = 0 ∨ ∃ c, ∀ z, f z = 2 * z + c := by
  sorry
#align imo_2019_p1 imo_2019_p1

theorem mathd_algebra_513 (a b : ℝ) (h₀ : 3 * a + 2 * b = 5) (h₁ : a + b = 2) : a = 1 ∧ b = 1 := by
  constructor <;> linarith
#align mathd_algebra_513 mathd_algebra_513

theorem mathd_algebra_143 (f g : ℝ → ℝ) (h₀ : ∀ x, f x = x + 1) (h₁ : ∀ x, g x = x ^ 2 + 3) :
    f (g 2) = 8 := by
  rw [h₀, h₁]
  norm_num
#align mathd_algebra_143 mathd_algebra_143

theorem mathd_algebra_354 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by linarith
#align mathd_algebra_354 mathd_algebra_354

theorem aime_1984_p7 (f : ℤ → ℤ) (h₀ : ∀ n, 1000 ≤ n → f n = n - 3)
    (h₁ : ∀ n, n < 1000 → f n = f (f (n + 5))) : f 84 = 997 := by sorry
#align aime_1984_p7 aime_1984_p7

theorem mathd_algebra_246 (a b : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5)
    (h₂ : f (-3) = 2) : f 3 = 8 := by
  rw [h₀] at h₂
  simp at h₂
  rw [h₀]
  linarith
#align mathd_algebra_246 mathd_algebra_246

theorem aime_1983_p3 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 2 + (18 * x + 30) - 2 * Real.sqrt (x ^ 2 + (18 * x + 45)))
    (h₁ : Fintype (f ⁻¹' {0})) : (∏ x in (f ⁻¹' {0}).toFinset, x) = 20 := by sorry
#align aime_1983_p3 aime_1983_p3

theorem numbertheory_3pow2pownm1mod2pownp3eq2pownp2 (n : ℕ) (h₀ : 0 < n) :
    (3 ^ 2 ^ n - 1) % 2 ^ (n + 3) = 2 ^ (n + 2) := by sorry
#align numbertheory_3pow2pownm1mod2pownp3eq2pownp2 numbertheory_3pow2pownm1mod2pownp3eq2pownp2

theorem mathd_numbertheory_85 : 1 * 3 ^ 3 + 2 * 3 ^ 2 + 2 * 3 + 2 = 53 := by norm_num
#align mathd_numbertheory_85 mathd_numbertheory_85

theorem amc12_2001_p21 (a b c d : ℕ) (h₀ : a * b * c * d = 8!) (h₁ : a * b + a + b = 524)
    (h₂ : b * c + b + c = 146) (h₃ : c * d + c + d = 104) : ↑a - ↑d = (10 : ℤ) := by sorry
#align amc12_2001_p21 amc12_2001_p21

theorem mathd_numbertheory_239 : (∑ k in Finset.Icc 1 12, k) % 4 = 2 := by sorry
#align mathd_numbertheory_239 mathd_numbertheory_239

theorem amc12b_2002_p2 (x : ℤ) (h₀ : x = 4) :
    (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 11 :=
  by
  rw [h₀]
  linarith
#align amc12b_2002_p2 amc12b_2002_p2

theorem mathd_algebra_196 (S : Finset ℝ) (h₀ : ∀ x : ℝ, x ∈ S ↔ abs (2 - x) = 3) :
    (∑ k in S, k) = 4 := by sorry
#align mathd_algebra_196 mathd_algebra_196

theorem mathd_algebra_342 (a d : ℝ) (h₀ : (∑ k in Finset.range 5, a + k * d) = 70)
    (h₁ : (∑ k in Finset.range 10, a + k * d) = 210) : a = 42 / 5 :=
  by
  revert h₀ h₁
  simp [Finset.sum_range_succ, mul_comm d]
  intros
  linarith
#align mathd_algebra_342 mathd_algebra_342

theorem mathd_numbertheory_517 : 121 * 122 * 123 % 4 = 2 := by sorry
#align mathd_numbertheory_517 mathd_numbertheory_517

theorem amc12a_2009_p7 (x : ℝ) (n : ℕ) (a : ℕ → ℝ)
    (h₁ : ∀ m, a (m + 1) - a m = a (m + 2) - a (m + 1)) (h₂ : a 1 = 2 * x - 3)
    (h₃ : a 2 = 5 * x - 11) (h₄ : a 3 = 3 * x + 1) (h₅ : a n = 2009) : n = 502 := by sorry
#align amc12a_2009_p7 amc12a_2009_p7

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ≠ » «expr- »(2)) -/
theorem mathd_algebra_270 (f : ℝ → ℝ) (h₀ : ∀ (x) (_ : x ≠ -2), f x = 1 / (x + 2)) :
    f (f 1) = 3 / 7 := by
  rw [h₀, h₀]
  norm_num
  linarith
  rw [h₀]
  norm_num
  linarith
#align mathd_algebra_270 mathd_algebra_270

theorem amc12a_2021_p12 (a b c d : ℝ) (f : ℂ → ℂ)
    (h₀ : ∀ z, f z = z ^ 6 - 10 * z ^ 5 + a * z ^ 4 + b * z ^ 3 + c * z ^ 2 + d * z + 16)
    (h₁ : ∀ z, f z = 0 → z.im = 0 ∧ 0 < z.re ∧ ↑(Int.floor z.re) = z.re) : b = -88 := by sorry
#align amc12a_2021_p12 amc12a_2021_p12

theorem mathd_algebra_362 (a b : ℝ) (h₀ : a ^ 2 * b ^ 3 = 32 / 27) (h₁ : a / b ^ 3 = 27 / 4) :
    a + b = 8 / 3 := by sorry
#align mathd_algebra_362 mathd_algebra_362

theorem mathd_numbertheory_521 (m n : ℕ) (h₀ : Even m) (h₁ : Even n) (h₂ : m - n = 2)
    (h₃ : m * n = 288) : m = 18 := by sorry
#align mathd_numbertheory_521 mathd_numbertheory_521

theorem amc12a_2002_p13 (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : a ≠ b) (h₂ : abs (a - 1 / a) = 1)
    (h₃ : abs (b - 1 / b) = 1) : a + b = Real.sqrt 5 := by sorry
#align amc12a_2002_p13 amc12a_2002_p13

theorem imo_1964_p2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : c < a + b) (h₂ : b < a + c)
    (h₃ : a < b + c) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := by sorry
#align imo_1964_p2 imo_1964_p2

theorem mathd_algebra_289 (k t m n : ℕ) (h₀ : Nat.Prime m ∧ Nat.Prime n) (h₁ : t < k)
    (h₂ : (k ^ 2 : ℤ) - m * k + n = 0) (h₃ : (t ^ 2 : ℤ) - m * t + n = 0) :
    m ^ n + n ^ m + k ^ t + t ^ k = 20 := by sorry
#align mathd_algebra_289 mathd_algebra_289

theorem amc12a_2021_p3 (x y : ℕ) (h₀ : x + y = 17402) (h₁ : 10 ∣ x) (h₂ : x / 10 = y) :
    ↑x - ↑y = (14238 : ℤ) := by sorry
#align amc12a_2021_p3 amc12a_2021_p3

theorem amc12a_2008_p25 (a b : ℕ → ℝ) (h₀ : ∀ n, a (n + 1) = Real.sqrt 3 * a n - b n)
    (h₁ : ∀ n, b (n + 1) = Real.sqrt 3 * b n + a n) (h₂ : a 100 = 2) (h₃ : b 100 = 4) :
    a 1 + b 1 = 1 / 2 ^ 98 := by sorry
#align amc12a_2008_p25 amc12a_2008_p25

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 (a b c : ℝ) (h₀ : a ≤ b ∧ b ≤ c)
    (h₁ : a + b + c = 2) (h₂ : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by sorry
#align algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3 algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3

theorem mathd_numbertheory_66 : 194 % 11 = 7 :=
  rfl
#align mathd_numbertheory_66 mathd_numbertheory_66

theorem amc12b_2021_p1 (S : Finset ℤ) (h₀ : ∀ x : ℤ, x ∈ S ↔ ↑(abs x) < 3 * Real.pi) :
    S.card = 19 := by sorry
#align amc12b_2021_p1 amc12b_2021_p1

theorem algebra_apbon2pownleqapownpbpowon2 (a b : ℝ) (n : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : 0 < n) :
    ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by sorry
#align algebra_apbon2pownleqapownpbpowon2 algebra_apbon2pownleqapownpbpowon2

theorem imo_1968_p5_1 (a : ℝ) (f : ℝ → ℝ) (h₀ : 0 < a)
    (h₁ : ∀ x, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) : ∃ b > 0, ∀ x, f (x + b) = f x := by
  sorry
#align imo_1968_p5_1 imo_1968_p5_1

theorem aime_1990_p15 (a b x y : ℝ) (h₀ : a * x + b * y = 3) (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
    (h₂ : a * x ^ 3 + b * y ^ 3 = 16) (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
    a * x ^ 5 + b * y ^ 5 = 20 := by sorry
#align aime_1990_p15 aime_1990_p15

theorem mathd_numbertheory_235 : (29 * 79 + 31 * 81) % 10 = 2 := by norm_num
#align mathd_numbertheory_235 mathd_numbertheory_235

theorem amc12b_2020_p13 :
    Real.sqrt (Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3) =
      Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3) :=
  by sorry
#align amc12b_2020_p13 amc12b_2020_p13

theorem amc12b_2021_p13 (S : Finset ℝ)
    (h₀ :
      ∀ x : ℝ, x ∈ S ↔ 0 < x ∧ x ≤ 2 * Real.pi ∧ 1 - 3 * Real.sin x + 5 * Real.cos (3 * x) = 0) :
    S.card = 6 := by sorry
#align amc12b_2021_p13 amc12b_2021_p13

theorem mathd_numbertheory_234 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9)
    (h₁ : (10 * a + b) ^ 3 = 912673) : a + b = 16 := by sorry
#align mathd_numbertheory_234 mathd_numbertheory_234

theorem numbertheory_aoddbdiv4asqpbsqmod8eq1 (a : ℤ) (b : ℕ) (h₀ : Odd a) (h₁ : 4 ∣ b) :
    (a ^ 2 + b ^ 2) % 8 = 1 := by sorry
#align numbertheory_aoddbdiv4asqpbsqmod8eq1 numbertheory_aoddbdiv4asqpbsqmod8eq1

theorem mathd_numbertheory_222 (b : ℕ) (h₀ : Nat.lcm 120 b = 3720) (h₁ : Nat.gcd 120 b = 8) :
    b = 248 := by sorry
#align mathd_numbertheory_222 mathd_numbertheory_222

theorem aime_1999_p11 (m : ℚ) (h₀ : 0 < m)
    (h₁ : (∑ k in Finset.Icc (1 : ℕ) 35, Real.sin (5 * k * π / 180)) = Real.tan (m * π / 180))
    (h₂ : (m.num : ℝ) / m.den < 90) : ↑m.den + m.num = 177 := by sorry
#align aime_1999_p11 aime_1999_p11

theorem mathd_algebra_359 (y : ℝ) (h₀ : y + 6 + y = 2 * 12) : y = 9 := by linarith
#align mathd_algebra_359 mathd_algebra_359

theorem imo_1965_p2 (x y z : ℝ) (a : ℕ → ℝ) (h₀ : 0 < a 0 ∧ 0 < a 4 ∧ 0 < a 8)
    (h₁ : a 1 < 0 ∧ a 2 < 0) (h₂ : a 3 < 0 ∧ a 5 < 0) (h₃ : a 6 < 0 ∧ a 7 < 0)
    (h₄ : 0 < a 0 + a 1 + a 2) (h₅ : 0 < a 3 + a 4 + a 5) (h₆ : 0 < a 6 + a 7 + a 8)
    (h₇ : a 0 * x + a 1 * y + a 2 * z = 0) (h₈ : a 3 * x + a 4 * y + a 5 * z = 0)
    (h₉ : a 6 * x + a 7 * y + a 8 * z = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by sorry
#align imo_1965_p2 imo_1965_p2

theorem mathd_algebra_288 (x y : ℝ) (n : NNReal) (h₀ : x < 0 ∧ y < 0) (h₁ : abs y = 6)
    (h₂ : Real.sqrt ((x - 8) ^ 2 + (y - 3) ^ 2) = 15)
    (h₃ : Real.sqrt (x ^ 2 + y ^ 2) = Real.sqrt n) : n = 52 := by sorry
#align mathd_algebra_288 mathd_algebra_288

theorem mathd_numbertheory_127 : (∑ k in Finset.range 101, 2 ^ k) % 7 = 3 := by sorry
#align mathd_numbertheory_127 mathd_numbertheory_127

theorem imo_1974_p3 (n : ℕ) :
    ¬5 ∣ ∑ k in Finset.range (n + 1), Nat.choose (2 * n + 1) (2 * k + 1) * 2 ^ (3 * k) := by sorry
#align imo_1974_p3 imo_1974_p3

theorem aime_1991_p9 (x : ℝ) (m : ℚ) (h₀ : 1 / Real.cos x + Real.tan x = 22 / 7)
    (h₁ : 1 / Real.sin x + 1 / Real.tan x = m) : ↑m.den + m.num = 44 := by sorry
#align aime_1991_p9 aime_1991_p9

theorem amc12a_2009_p6 (m n p q : ℝ) (h₀ : p = 2 ^ m) (h₁ : q = 3 ^ n) :
    p ^ (2 * n) * q ^ m = 12 ^ (m * n) := by sorry
#align amc12a_2009_p6 amc12a_2009_p6

theorem mathd_algebra_158 (a : ℕ) (h₀ : Even a)
    (h₁ : ↑(∑ k in Finset.range 8, 2 * k + 1) - ↑(∑ k in Finset.range 5, a + 2 * k) = (4 : ℤ)) :
    a = 8 := by sorry
#align mathd_algebra_158 mathd_algebra_158

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 (x : ℝ)
    (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) : 0 ≤ x ∧ x ≤ 1 := by sorry
#align algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1

theorem aime_1990_p4 (x : ℝ) (h₀ : 0 < x) (h₁ : x ^ 2 - 10 * x - 29 ≠ 0)
    (h₂ : x ^ 2 - 10 * x - 45 ≠ 0) (h₃ : x ^ 2 - 10 * x - 69 ≠ 0)
    (h₄ : 1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) - 2 / (x ^ 2 - 10 * x - 69) = 0) :
    x = 13 := by sorry
#align aime_1990_p4 aime_1990_p4

theorem mathd_numbertheory_541 (m n : ℕ) (h₀ : 1 < m) (h₁ : 1 < n) (h₂ : m * n = 2005) :
    m + n = 406 := by sorry
#align mathd_numbertheory_541 mathd_numbertheory_541

theorem mathd_algebra_314 (n : ℕ) (h₀ : n = 11) : (1 / 4) ^ (n + 1) * 2 ^ (2 * n) = 1 / 4 :=
  by
  rw [h₀]
  norm_num
#align mathd_algebra_314 mathd_algebra_314

theorem amc12_2000_p20 (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) (h₁ : x + 1 / y = 4)
    (h₂ : y + 1 / z = 1) (h₃ : z + 1 / x = 7 / 3) : x * y * z = 1 := by sorry
#align amc12_2000_p20 amc12_2000_p20

theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -(1 / 4) := by norm_num
#align mathd_algebra_302 mathd_algebra_302

theorem aime_1983_p2 (x p : ℝ) (f : ℝ → ℝ) (h₀ : 0 < p ∧ p < 15) (h₁ : p ≤ x ∧ x ≤ 15)
    (h₂ : f x = abs (x - p) + abs (x - 15) + abs (x - p - 15)) : 15 ≤ f x := by sorry
#align aime_1983_p2 aime_1983_p2

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ≠ » 0) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y «expr ≠ » 0) -/
theorem mathd_algebra_139 (s : ℝ → ℝ → ℝ)
    (h₀ : ∀ (x) (_ : x ≠ 0), ∀ (y) (_ : y ≠ 0), s x y = (1 / y - 1 / x) / (x - y)) :
    s 3 11 = 1 / 33 := by norm_num [h₀]
#align mathd_algebra_139 mathd_algebra_139

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (n «expr ≠ » N) -/
theorem amc12a_2021_p25 (N : ℕ) (f : ℕ → ℝ)
    (h₀ : ∀ n, 0 < n → f n = (Nat.divisors n).card / n ^ ((1 : ℝ) / 3))
    (h₁ : ∀ (n) (_ : n ≠ N), 0 < n → f n < f N) : (Nat.digits 10 N).Sum = 9 := by sorry
#align amc12a_2021_p25 amc12a_2021_p25

theorem amc12a_2020_p25 (a : ℚ) (S : Finset ℝ)
    (h₀ : ∀ x : ℝ, x ∈ S ↔ ↑⌊x⌋ * (x - ↑⌊x⌋) = ↑a * x ^ 2) (h₁ : (∑ k in S, k) = 420) :
    ↑a.den + a.num = 929 := by sorry
#align amc12a_2020_p25 amc12a_2020_p25

theorem mathd_numbertheory_150 (n : ℕ) (h₀ : ¬Nat.Prime (7 + 30 * n)) : 6 ≤ n := by sorry
#align mathd_numbertheory_150 mathd_numbertheory_150

theorem aime_1989_p8 (a b c d e f g : ℝ)
    (h₀ : a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g = 1)
    (h₁ : 4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g = 12)
    (h₂ : 9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g = 123) :
    16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by sorry
#align aime_1989_p8 aime_1989_p8

theorem mathd_numbertheory_296 (n : ℕ) (h₀ : 2 ≤ n) (h₁ : ∃ x, x ^ 3 = n) (h₂ : ∃ t, t ^ 4 = n) :
    4096 ≤ n := by sorry
#align mathd_numbertheory_296 mathd_numbertheory_296

theorem mathd_algebra_142 (m b : ℝ) (h₀ : m * 7 + b = -1) (h₁ : m * -1 + b = 7) : m + b = 5 := by
  linarith
#align mathd_algebra_142 mathd_algebra_142

theorem numbertheory_exk2powkeqapb2mulbpa2_aeq1 (a b : ℕ) (h₀ : 0 < a ∧ 0 < b)
    (h₁ : ∃ k > 0, 2 ^ k = (a + b ^ 2) * (b + a ^ 2)) : a = 1 := by sorry
#align numbertheory_exk2powkeqapb2mulbpa2_aeq1 numbertheory_exk2powkeqapb2mulbpa2_aeq1

theorem mathd_algebra_400 (x : ℝ) (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) : x = 50 := by linarith
#align mathd_algebra_400 mathd_algebra_400

theorem aime_1995_p7 (k m n : ℕ) (t : ℝ) (h₀ : 0 < k ∧ 0 < m ∧ 0 < n) (h₁ : Nat.gcd m n = 1)
    (h₂ : (1 + Real.sin t) * (1 + Real.cos t) = 5 / 4)
    (h₃ : (1 - Real.sin t) * (1 - Real.cos t) = m / n - Real.sqrt k) : k + m + n = 27 := by sorry
#align aime_1995_p7 aime_1995_p7

theorem mathd_numbertheory_185 (n : ℕ) (h₀ : n % 5 = 3) : 2 * n % 5 = 1 := by sorry
#align mathd_numbertheory_185 mathd_numbertheory_185

theorem mathd_algebra_441 (x : ℝ) (h₀ : x ≠ 0) :
    12 / (x * x) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 :=
  by
  field_simp
  ring_nf
#align mathd_algebra_441 mathd_algebra_441

theorem mathd_numbertheory_582 (n : ℕ) (h₀ : 0 < n) (h₁ : 3 ∣ n) :
    (n + 4 + (n + 6) + (n + 8)) % 9 = 0 := by sorry
#align mathd_numbertheory_582 mathd_numbertheory_582

theorem mathd_algebra_338 (a b c : ℝ) (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 :=
  by
  have ha : a = -4; linarith
  have hb : b = 2; linarith
  have hc : c = 7; linarith
  rw [ha, hb, hc]
  norm_num
#align mathd_algebra_338 mathd_algebra_338

