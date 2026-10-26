import Berstein.Normalization
import Berstein.ClosedCover

/-! Bounded scale ratios and progress force both actual cylinders to shrink. -/

namespace Berstein
open HallRay.ContinuedFraction
open Filter
open scoped Topology

theorem square_ratio_balance {a b K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hK : 0 < K) (hlo : 1 / K^2 ≤ a^2 / b^2)
    (hhi : a^2 / b^2 ≤ K^2) : a ≤ K*b ∧ b ≤ K*a := by
  have hab : a^2 ≤ K^2*b^2 := (div_le_iff₀ (sq_pos_of_pos hb)).mp hhi
  have hba : b^2 ≤ K^2*a^2 := by
    have := (div_le_div_iff₀ (sq_pos_of_pos hK) (sq_pos_of_pos hb)).mp hlo
    nlinarith
  constructor
  · exact le_of_sq_le_sq (by nlinarith) (mul_pos hK hb).le
  · exact le_of_sq_le_sq (by nlinarith) (mul_pos hK ha).le

theorem paired_scales_tendsto_zero (a b : ℕ → ℝ) (K : ℝ)
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (hK : 0 < K)
    (hlo : ∀ n, 1 / K^2 ≤ (a n)^2 / (b n)^2)
    (hhi : ∀ n, (a n)^2 / (b n)^2 ≤ K^2)
    (hgrowth : Tendsto (fun n => a n+b n) atTop atTop) :
    Tendsto (fun n => 4*(1/(a n)^2+1/(b n)^2)) atTop (𝓝 0) := by
  have hbal := fun n => square_ratio_balance (ha n) (hb n) hK (hlo n) (hhi n)
  obtain ⟨hat, hbt⟩ := balanced_growth hK.le (fun n => (hbal n).1)
    (fun n => (hbal n).2) hgrowth
  have halim := (tendsto_inv_atTop_zero.comp hat).pow 2
  have hblim := (tendsto_inv_atTop_zero.comp hbt).pow 2
  simpa [one_div, inv_pow] using (halim.add hblim).const_mul 4

theorem paired_scales_shrink (a b : ℕ → ℝ) (K : ℝ)
    (ha : ∀ n, 0 < a n) (hb : ∀ n, 0 < b n) (hK : 0 < K)
    (hlo : ∀ n, 1 / K^2 ≤ (a n)^2 / (b n)^2)
    (hhi : ∀ n, (a n)^2 / (b n)^2 ≤ K^2)
    (hgrowth : Tendsto (fun n => a n+b n) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) : ∃ n, 4*(1/(a n)^2+1/(b n)^2) < ε := by
  have ht := paired_scales_tendsto_zero a b K ha hb hK hlo hhi hgrowth
  exact (ht.eventually (gt_mem_nhds hε)).exists

/-- Every two points in a CF hull are within four times the anchor scale. -/
theorem tailMap_width_le_four_scale (w : Word) {anchor x y : ℝ}
    (ha : anchor ∈ Set.Icc (0 : ℝ) 1) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |tailMap w x-tailMap w y| ≤ 4*Normalization.scale w anchor := by
  have hC : (0 : ℝ) < (mobiusCoeffs w).C := by exact_mod_cast mobius_C_pos w
  have hD : (0 : ℝ) ≤ (mobiusCoeffs w).D := by positivity
  have hDC : ((mobiusCoeffs w).D : ℝ) ≤ (mobiusCoeffs w).C := by
    exact_mod_cast mobius_D_le_C w
  have hax : (0 : ℝ) < (mobiusCoeffs w).C+(mobiusCoeffs w).D*x := add_pos_of_pos_of_nonneg hC (mul_nonneg hD hx.1)
  have hay : (0 : ℝ) < (mobiusCoeffs w).C+(mobiusCoeffs w).D*y := add_pos_of_pos_of_nonneg hC (mul_nonneg hD hy.1)
  have haa : (0 : ℝ) < (mobiusCoeffs w).C+(mobiusCoeffs w).D*anchor := add_pos_of_pos_of_nonneg hC (mul_nonneg hD ha.1)
  have hdprod : ((mobiusCoeffs w).C : ℝ)^2 ≤
      ((mobiusCoeffs w).C+(mobiusCoeffs w).D*x)*
      ((mobiusCoeffs w).C+(mobiusCoeffs w).D*y) := by
    nlinarith [mul_nonneg hD hx.1, mul_nonneg hD hy.1,
      mul_nonneg (mul_nonneg hD hx.1) (mul_nonneg hD hy.1)]
  have han : ((mobiusCoeffs w).C+(mobiusCoeffs w).D*anchor : ℝ)^2 ≤
      4*((mobiusCoeffs w).C : ℝ)^2 := by
    have h : (mobiusCoeffs w).C+(mobiusCoeffs w).D*anchor ≤
        2*((mobiusCoeffs w).C : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left ha.2 hD]
    nlinarith
  have hxy : |x-y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  rw [abs_tailMap_sub_exact w x y hx.1 hy.1]
  calc
    _ ≤ 1/((mobiusCoeffs w).C : ℝ)^2 :=
      div_le_div₀ (by norm_num) hxy (sq_pos_of_pos hC) hdprod
    _ ≤ 4*Normalization.scale w anchor := by
      unfold Normalization.scale
      rw [mul_one_div, div_le_div_iff₀ (sq_pos_of_pos hC) (sq_pos_of_pos haa)]
      simpa using han

end Berstein
