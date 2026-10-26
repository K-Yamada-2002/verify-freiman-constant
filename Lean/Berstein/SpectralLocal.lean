import Berstein.Markov
import Berstein.CylinderBound

/-!
# Elementary reductions for noncentral local values

These lemmas justify the easy cases in the noncentral enumeration. They do
not prove the required uniform `NoncentralBound` for the glued construction.
-/

namespace Berstein

open HallRay.ContinuedFraction

/-- The first continued-fraction digit bounds the whole fractional tail. -/
theorem value_zero_le_inv_first (digits : ℕ → PartialQuotient) :
    value 0 digits ≤ 1 / ((digits 0).1 : ℝ) := by
  rw [value_zero_eq_tailMap_prefix digits 1]
  simp only [List.range_one, List.map_cons, List.map_nil, tailMap_cons, tailMap_nil]
  have ht := (value_zero_mem_Icc (fun k ↦ digits (1 + k))).1
  have ha : (0 : ℝ) < (digits 0).1 := by
    have h := one_le_partialQuotient (digits 0)
    linarith
  exact div_le_div_of_nonneg_left (by norm_num) ha (by linarith)

/-- A first digit at least two gives a fractional tail at most one half. -/
theorem value_zero_le_half_of_two_le_first (digits : ℕ → PartialQuotient)
    (h : 2 ≤ (digits 0).1) : value 0 digits ≤ 1 / 2 := by
  have ha : (2 : ℝ) ≤ (digits 0).1 := by exact_mod_cast h
  exact (value_zero_le_inv_first digits).trans
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha)

/-- Centers with digit one or two have local value at most four. -/
theorem localValue_le_four_of_digit_le_two (A : BiSequence) (n : ℤ)
    (h : (A n).1 ≤ 2) : localValue A n ≤ 4 := by
  have hd : ((A n).1 : ℝ) ≤ 2 := by exact_mod_cast h
  have hb := localValue_le_digit_add_two A n
  linarith

/-- For a center of digit at most three, a neighboring digit at least two
forces the local value to be at most `9/2`. -/
theorem localValue_le_nine_halves_of_adjacent_ge_two (A : BiSequence) (n : ℤ)
    (hcenter : (A n).1 ≤ 3)
    (hadjacent : 2 ≤ (A (n - 1)).1 ∨ 2 ≤ (A (n + 1)).1) :
    localValue A n ≤ 9 / 2 := by
  have hd : ((A n).1 : ℝ) ≤ 3 := by exact_mod_cast hcenter
  rcases hadjacent with hl | hr
  · have hlhalf : value 0 (leftDigits A n) ≤ 1 / 2 :=
      value_zero_le_half_of_two_le_first (leftDigits A n) (by simpa [leftDigits] using hl)
    have hrone := (value_zero_mem_Icc (rightDigits A n)).2
    dsimp [localValue]
    linarith
  · have hrhalf : value 0 (rightDigits A n) ≤ 1 / 2 :=
      value_zero_le_half_of_two_le_first (rightDigits A n) (by simpa [rightDigits] using hr)
    have hlone := (value_zero_mem_Icc (leftDigits A n)).2
    dsimp [localValue]
    linarith

/-- Replacing the left tail after nine digits changes the local value by at
most `1/3025`, provided the central digit and the other tail are preserved. -/
theorem localValue_perturbation_left_nine (A B : BiSequence) (n m : ℤ)
    (hcenter : A n = B m) (hright : rightDigits A n = rightDigits B m)
    (hleft : ∀ k < 9, leftDigits A n k = leftDigits B m k) :
    |localValue A n - localValue B m| ≤ 1 / 3025 := by
  have heq : localValue A n - localValue B m =
      value 0 (leftDigits A n) - value 0 (leftDigits B m) := by
    dsimp [localValue]
    rw [hcenter, hright]
    ring
  rw [heq]
  exact nine_digit_value_bound _ _ hleft

/-- The corresponding reduction to a known bound for a replacement sequence. -/
theorem localValue_le_of_left_nine_replacement (A B : BiSequence) (n m : ℤ)
    (hcenter : A n = B m) (hright : rightDigits A n = rightDigits B m)
    (hleft : ∀ k < 9, leftDigits A n k = leftDigits B m k)
    (bulk : ℝ) (hbulk : localValue B m ≤ bulk) :
    localValue A n ≤ bulk + 1 / 3025 := by
  have h := (abs_le.mp (localValue_perturbation_left_nine A B n m
    hcenter hright hleft)).2
  linarith

/-- The symmetric replacement estimate for the right tail. -/
theorem localValue_perturbation_right_nine (A B : BiSequence) (n m : ℤ)
    (hcenter : A n = B m) (hleft : leftDigits A n = leftDigits B m)
    (hright : ∀ k < 9, rightDigits A n k = rightDigits B m k) :
    |localValue A n - localValue B m| ≤ 1 / 3025 := by
  have heq : localValue A n - localValue B m =
      value 0 (rightDigits A n) - value 0 (rightDigits B m) := by
    dsimp [localValue]
    rw [hcenter, hleft]
    ring
  rw [heq]
  exact nine_digit_value_bound _ _ hright

theorem localValue_le_of_right_nine_replacement (A B : BiSequence) (n m : ℤ)
    (hcenter : A n = B m) (hleft : leftDigits A n = leftDigits B m)
    (hright : ∀ k < 9, rightDigits A n k = rightDigits B m k)
    (bulk : ℝ) (hbulk : localValue B m ≤ bulk) :
    localValue A n ≤ bulk + 1 / 3025 := by
  have h := (abs_le.mp (localValue_perturbation_right_nine A B n m
    hcenter hleft hright)).2
  linarith

end Berstein
