import Mathlib

namespace Berstein

noncomputable def L : ℝ := (8512493 + 28004 * Real.sqrt 462) / 17339617

noncomputable def H : ℝ := (1352829 - 8081 * Real.sqrt 462) / 2233974

noncomputable def filledLower : ℝ := 4 + L + (H - L) / 16

noncomputable def filledUpper : ℝ := 4 + L + 7 * (H - L) / 8

noncomputable def targetLower : ℝ := 226289 / 50000

noncomputable def targetUpper : ℝ := 226377 / 50000

noncomputable def theta : ℝ := 4 * Real.sqrt 462 / 19 + 1 / 3025

noncomputable def freimanConstant : ℝ :=
  (2221564096 + 283748 * Real.sqrt 462) / 491993569

noncomputable def S : ℝ :=
  (55792801 + 2467176 * Real.sqrt 462) / 159491641

private noncomputable def sqrt462Lower : ℝ := 214941852602 / 10000000000

private noncomputable def sqrt462Upper : ℝ := 214941852603 / 10000000000

private theorem sqrt462_bounds : sqrt462Lower < Real.sqrt 462 ∧
    Real.sqrt 462 < sqrt462Upper := by
  have hsqrt : 0 ≤ Real.sqrt (462 : ℝ) := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt (462 : ℝ)) ^ 2 = 462 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 462)]
  have hlo : sqrt462Lower ^ 2 < 462 := by
    norm_num [sqrt462Lower]
  have hhi : 462 < sqrt462Upper ^ 2 := by
    norm_num [sqrt462Upper]
  constructor
  · unfold sqrt462Lower at *
    nlinarith [sq_nonneg (Real.sqrt (462 : ℝ) - (214941852602 / 10000000000 : ℝ))]
  · unfold sqrt462Upper at *
    nlinarith [sq_nonneg (Real.sqrt (462 : ℝ) - (214941852603 / 10000000000 : ℝ))]

private theorem sqrt462_bounds_numeric :
    (214941852602 / 10000000000 : ℝ) < Real.sqrt 462 ∧
      Real.sqrt 462 < 214941852603 / 10000000000 := by
  simpa [sqrt462Lower, sqrt462Upper] using sqrt462_bounds

theorem L_lt_H : L < H := by
  rcases sqrt462_bounds_numeric with ⟨hlo, hhi⟩
  unfold L H
  nlinarith

theorem theta_lt_filledLower : theta < filledLower := by
  rcases sqrt462_bounds_numeric with ⟨hlo, hhi⟩
  unfold theta filledLower L H
  nlinarith

theorem rational_spectral_bound_lt_filledLower :
    (4525423/1000000 : ℝ) < filledLower := by
  rcases sqrt462_bounds_numeric with ⟨hlo, hhi⟩
  unfold filledLower L H
  nlinarith

theorem filledLower_lt_targetLower : filledLower < targetLower := by
  rcases sqrt462_bounds_numeric with ⟨hlo, hhi⟩
  unfold filledLower L H targetLower
  nlinarith

theorem targetLower_lt_targetUpper : targetLower < targetUpper := by
  norm_num [targetLower, targetUpper]

theorem targetUpper_lt_filledUpper : targetUpper < filledUpper := by
  rcases sqrt462_bounds_numeric with ⟨hlo, hhi⟩
  unfold filledUpper L H targetUpper
  nlinarith

theorem filledUpper_lt_freimanConstant : filledUpper < freimanConstant := by
  rcases sqrt462_bounds_numeric with ⟨hlo, hhi⟩
  unfold filledUpper L H freimanConstant
  nlinarith

theorem S_strictly_in_bin_minus20 :
    (50 / 51 : ℝ) ^ 20 < S ∧ S < (50 / 51 : ℝ) ^ 19 := by
  rcases sqrt462_bounds_numeric with ⟨hlo, hhi⟩
  unfold S
  constructor <;> nlinarith

theorem S_mem_bin_minus20 :
    (50 / 51 : ℝ) ^ 20 ≤ S ∧ S ≤ (50 / 51 : ℝ) ^ 19 := by
  rcases S_strictly_in_bin_minus20 with ⟨hlo, hhi⟩
  exact ⟨le_of_lt hlo, le_of_lt hhi⟩

theorem constant_order :
    theta < filledLower ∧
    filledLower < targetLower ∧
    targetLower < targetUpper ∧
    targetUpper < filledUpper ∧
    filledUpper < freimanConstant := by
  exact ⟨theta_lt_filledLower, filledLower_lt_targetLower,
    targetLower_lt_targetUpper, targetUpper_lt_filledUpper,
    filledUpper_lt_freimanConstant⟩

theorem target_interval_subset_filled :
    Set.Icc targetLower targetUpper ⊆ Set.Icc filledLower filledUpper := by
  intro x hx
  rcases constant_order with ⟨_, hlo, _, hhi, _⟩
  exact ⟨le_of_lt (lt_of_lt_of_le hlo hx.1), le_trans hx.2 (le_of_lt hhi)⟩

theorem target_interval_below_freimanConstant :
    Set.Icc targetLower targetUpper ⊆ Set.Iio freimanConstant := by
  intro x hx
  rcases constant_order with ⟨_, _, _, hhi, hconstant⟩
  exact lt_of_le_of_lt hx.2 (lt_trans hhi hconstant)

theorem target_interval_subset_filled_and_below_constant :
    Set.Icc targetLower targetUpper ⊆
      Set.Icc filledLower filledUpper ∩ Set.Iio freimanConstant := by
  intro x hx
  exact ⟨target_interval_subset_filled hx, target_interval_below_freimanConstant hx⟩

end Berstein
