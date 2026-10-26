import HallRay.ContinuedFraction.Mobius

/-! The exact nine-digit error bound used to replace a distant tail. -/

namespace Berstein
open HallRay.ContinuedFraction

/-- Both continuants grow at least as fast as the all-ones continuants. -/
theorem continuants_ge_fibonacci (w : Word) :
    Nat.fib w.length ≤ (mobiusCoeffs w).A ∧
      Nat.fib (w.length + 1) ≤ (mobiusCoeffs w).C := by
  induction w with
  | nil => norm_num [mobiusCoeffs]
  | cons a w ih =>
      simp only [List.length_cons, mobiusCoeffs]
      refine ⟨ih.2, ?_⟩
      have ha : 1 ≤ a.val := a.property
      have hm : (mobiusCoeffs w).C ≤ a.val * (mobiusCoeffs w).C := by
        simpa using Nat.mul_le_mul_right (mobiusCoeffs w).C ha
      rw [Nat.fib_add_two]
      omega

/-- The Möbius formula in fractional-tail coordinates, including tail zero. -/
theorem tailMap_eq_mobius (w : Word) (x : ℝ) (hx : 0 ≤ x) :
    tailMap w x =
      ((mobiusCoeffs w).A + (mobiusCoeffs w).B * x) /
        ((mobiusCoeffs w).C + (mobiusCoeffs w).D * x) := by
  induction w with
  | nil => simp [mobiusCoeffs]
  | cons a w ih =>
      have hC : (0 : ℝ) < (mobiusCoeffs w).C := by
        exact_mod_cast mobius_C_pos w
      have hden : (0 : ℝ) < (mobiusCoeffs w).C + (mobiusCoeffs w).D * x := by
        positivity
      have ha : (0 : ℝ) < a.val := by exact_mod_cast a.property
      have hnum : (0 : ℝ) ≤ (mobiusCoeffs w).A + (mobiusCoeffs w).B * x := by
        positivity
      rw [tailMap_cons, ih]
      simp only [mobiusCoeffs, Nat.cast_add, Nat.cast_mul]
      have hsum : (0 : ℝ) < a.val +
          ((mobiusCoeffs w).A + (mobiusCoeffs w).B * x) /
            ((mobiusCoeffs w).C + (mobiusCoeffs w).D * x) :=
        add_pos_of_pos_of_nonneg ha (div_nonneg hnum hden.le)
      have hnew : (0 : ℝ) <
          (a.val * (mobiusCoeffs w).C + (mobiusCoeffs w).A) +
          (a.val * (mobiusCoeffs w).D + (mobiusCoeffs w).B) * x := by
        nlinarith [mul_pos ha hden]
      field_simp [ne_of_gt hden, ne_of_gt hsum, ne_of_gt hnew]
      ring

theorem abs_tailMap_sub_exact (w : Word) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |tailMap w x - tailMap w y| = |x-y| /
      (((mobiusCoeffs w).C + (mobiusCoeffs w).D * x) *
       ((mobiusCoeffs w).C + (mobiusCoeffs w).D * y)) := by
  have hC : (0 : ℝ) < (mobiusCoeffs w).C := by exact_mod_cast mobius_C_pos w
  have hdx : (0 : ℝ) < (mobiusCoeffs w).C + (mobiusCoeffs w).D * x := by positivity
  have hdy : (0 : ℝ) < (mobiusCoeffs w).C + (mobiusCoeffs w).D * y := by positivity
  rw [tailMap_eq_mobius w x hx, tailMap_eq_mobius w y hy,
    div_sub_div _ _ (ne_of_gt hdx) (ne_of_gt hdy), abs_div,
    abs_of_pos (mul_pos hdx hdy)]
  have heq :
      ((mobiusCoeffs w).A + (mobiusCoeffs w).B * x : ℝ) *
          ((mobiusCoeffs w).C + (mobiusCoeffs w).D * y) -
        ((mobiusCoeffs w).C + (mobiusCoeffs w).D * x) *
          ((mobiusCoeffs w).A + (mobiusCoeffs w).B * y) =
      ((mobiusCoeffs w).A * (mobiusCoeffs w).D -
          (mobiusCoeffs w).B * (mobiusCoeffs w).C : ℝ) * (y-x) := by ring
  rw [heq, abs_mul, abs_mobius_det, one_mul, abs_sub_comm]

theorem nine_digit_tail_bound (w : Word) (hw : w.length = 9)
    (x y : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |tailMap w x - tailMap w y| ≤ 1/3025 := by
  have hq := (continuants_ge_fibonacci w).2
  rw [hw] at hq
  norm_num [Nat.fib] at hq
  have hC : (55 : ℝ) ≤ (mobiusCoeffs w).C := by exact_mod_cast hq
  have hdx : (55 : ℝ) ≤ (mobiusCoeffs w).C + (mobiusCoeffs w).D * x := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (mobiusCoeffs w).D) hx.1]
  have hdy : (55 : ℝ) ≤ (mobiusCoeffs w).C + (mobiusCoeffs w).D * y := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (mobiusCoeffs w).D) hy.1]
  have hden : (3025 : ℝ) ≤
      ((mobiusCoeffs w).C + (mobiusCoeffs w).D * x) *
      ((mobiusCoeffs w).C + (mobiusCoeffs w).D * y) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdx) (sub_nonneg.mpr hdy)]
  have hxy : |x-y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  rw [abs_tailMap_sub_exact w x y hx.1 hy.1]
  apply (div_le_iff₀ (by linarith : (0 : ℝ) <
    ((mobiusCoeffs w).C + (mobiusCoeffs w).D * x) *
    ((mobiusCoeffs w).C + (mobiusCoeffs w).D * y))).2
  linarith

/-- Two actual infinite continued fractions with nine common digits differ
by at most 1/3025, with no bound on their later positive digits. -/
theorem nine_digit_value_bound (a b : ℕ → PartialQuotient)
    (h : ∀ k < 9, a k = b k) : |value 0 a - value 0 b| ≤ 1/3025 := by
  rw [value_zero_eq_tailMap_prefix a 9, value_zero_eq_tailMap_prefix b 9]
  have hp : (List.range 9).map a = (List.range 9).map b := by
    apply List.map_congr_left
    intro k hk
    exact h k (List.mem_range.mp hk)
  rw [← hp]
  exact nine_digit_tail_bound _ (by simp) _ _
    (value_zero_mem_Icc _) (value_zero_mem_Icc _)

end Berstein
