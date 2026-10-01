import Berstein.Constants
import Berstein.RootGeometry
import Berstein.Forbidden31313
import Berstein.Normalization

namespace Berstein
open HallRay.ContinuedFraction Forbidden31313

theorem root_lower_sum :
    tailMap prefix322 (exactUpper 0) + tailMap prefix431 (exactUpper 2) = L := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 462)
  have h0 := (exactBounds_unit 0)
  have h2 := (exactBounds_unit 2)
  have hden : (0 : ℝ) < 17+7*exactUpper 0 := by linarith [h0.1.trans h0.2.1]
  have hden' : (0 : ℝ) < 17+13*exactUpper 2 := by linarith [h2.1.trans h2.2.1]
  rw [tailMap_eq_mobius _ _ (h0.1.trans h0.2.1),
    tailMap_eq_mobius _ _ (h2.1.trans h2.2.1), prefix322_coefficients, prefix431_coefficients]
  norm_num only [Nat.cast_ofNat]
  rw [div_add_div _ _ (ne_of_gt hden) (ne_of_gt hden')]
  apply (div_eq_iff (mul_ne_zero (ne_of_gt hden) (ne_of_gt hden'))).mpr
  unfold exactUpper L
  norm_num
  field_simp
  have hs3 : Real.sqrt (462 : ℝ)^3 = 462*Real.sqrt 462 := by rw [pow_succ, hs]
  nlinarith [hs, hs3]

theorem root_upper_sum :
    tailMap prefix322 (exactLower 0) + tailMap prefix431 (exactLower 2) = H := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 462)
  have h0 := (exactBounds_unit 0)
  have h2 := (exactBounds_unit 2)
  rw [tailMap_eq_mobius _ _ h0.1, tailMap_eq_mobius _ _ h2.1,
    prefix322_coefficients, prefix431_coefficients]
  have hd : (0 : ℝ) < 17+7*exactLower 0 := by linarith [h0.1]
  have he : (0 : ℝ) < 17+13*exactLower 2 := by linarith [h2.1]
  norm_num only [Nat.cast_ofNat]
  rw [div_add_div _ _ (ne_of_gt hd) (ne_of_gt he)]
  apply (div_eq_iff (mul_ne_zero (ne_of_gt hd) (ne_of_gt he))).mpr
  unfold exactLower H
  norm_num
  field_simp
  have hs3 : Real.sqrt (462 : ℝ)^3 = 462*Real.sqrt 462 := by rw [pow_succ, hs]
  nlinarith [hs, hs3]

theorem root_scale_ratio :
    Normalization.scale prefix431 (exactUpper 2) /
      Normalization.scale prefix322 (exactUpper 0) = S := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 462)
  have h0 := (exactBounds_unit 0)
  have h2 := (exactBounds_unit 2)
  have hd : (0 : ℝ) < 17+7*exactUpper 0 := by linarith [h0.1.trans h0.2.1]
  have he : (0 : ℝ) < 17+13*exactUpper 2 := by linarith [h2.1.trans h2.2.1]
  unfold Normalization.scale
  rw [prefix322_coefficients, prefix431_coefficients]
  norm_num only [Nat.cast_ofNat]
  field_simp [ne_of_gt hd, ne_of_gt he]
  unfold exactUpper S
  norm_num
  field_simp
  have hs3 : Real.sqrt (462 : ℝ)^3 = 462*Real.sqrt 462 := by rw [pow_succ, hs]
  nlinarith [hs, hs3]

theorem root_left_shape : denominatorRatio prefix322 ∈ Set.Icc (9/22 : ℝ) (14/33) := by
  rw [prefix322_shape]
  norm_num

theorem root_right_shape : denominatorRatio prefix431 ∈ Set.Icc (13/17 : ℝ) (19/24) := by
  rw [prefix431_shape]
  norm_num

end Berstein
