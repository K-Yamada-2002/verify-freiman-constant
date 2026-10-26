import Mathlib

/-!
A small, kernel-checkable certificate format for finite interval covers.

This is a soundness layer, not a replay of `graph_wide`. In particular,
passing the tests below does not certify any row of the external table.
-/

namespace Berstein
namespace IntervalCover

/-- Rational endpoints; reversed endpoints denote an empty interval. -/
structure QInterval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

def QInterval.carrier (I : QInterval) : Set ℝ :=
  Set.Icc (I.lower : ℝ) (I.upper : ℝ)

/-- A chain certificate. Each next interval starts before the current covered
endpoint. Acceptance requires actually reaching the requested right endpoint. -/
def check (left right : ℚ) : List QInterval → Bool
  | [] => false
  | I :: rest =>
      decide (I.lower ≤ left) &&
        (decide (right ≤ I.upper) || check I.upper right rest)

/-- Acceptance implies coverage of every real point, not just rational points. -/
theorem check_sound (intervals : List QInterval) (left right : ℚ)
    (h : check left right intervals = true) :
    ∀ x ∈ Set.Icc (left : ℝ) (right : ℝ),
      ∃ I ∈ intervals, x ∈ I.carrier := by
  induction intervals generalizing left with
  | nil => simp [check] at h
  | cons I rest ih =>
      have h' : I.lower ≤ left ∧ (right ≤ I.upper ∨ check I.upper right rest = true) := by
        simpa [check, Bool.and_eq_true, Bool.or_eq_true] using h
      intro x hx
      have hlo : (I.lower : ℝ) ≤ left := by exact_mod_cast h'.1
      by_cases hxi : x ≤ (I.upper : ℝ)
      · exact ⟨I, List.mem_cons_self, hlo.trans hx.1, hxi⟩
      · have hrest : check I.upper right rest = true := by
          rcases h'.2 with hr | hr
          · have hr' : (right : ℝ) ≤ I.upper := by exact_mod_cast hr
            exact (hxi (hx.2.trans hr')).elim
          · exact hr
        obtain ⟨J, hJ, hxJ⟩ := ih I.upper hrest x ⟨le_of_not_ge hxi, hx.2⟩
        exact ⟨J, List.mem_cons_of_mem I hJ, hxJ⟩

/-- The actual 25 root bands, in normalized hull coordinates. -/
def rootBands : List QInterval :=
  (List.range 25).map fun k =>
    ⟨((k : ℚ) + 2) / 32, ((k : ℚ) + 4) / 32⟩

theorem rootBands_checked : check (1/16) (7/8) rootBands = true := by norm_num [check, rootBands, List.range_succ]

theorem rootBands_cover (x : ℝ) (hx : x ∈ Set.Icc (1/16 : ℝ) (7/8)) :
    ∃ I ∈ rootBands, x ∈ I.carrier := by
  exact check_sound rootBands (1/16) (7/8) rootBands_checked x (by norm_num; exact hx)

/-- The coverage is preserved by any increasing affine hull parametrization. -/
theorem rootBands_affine_cover (L H t : ℝ) (hLH : L < H)
    (ht : t ∈ Set.Icc (L + (H-L)/16) (L + 7*(H-L)/8)) :
    ∃ I ∈ rootBands,
      t ∈ Set.Icc (L + (I.lower : ℝ)*(H-L)) (L + (I.upper : ℝ)*(H-L)) := by
  have hpos : 0 < H-L := sub_pos.mpr hLH
  have hu : (t-L)/(H-L) ∈ Set.Icc (1/16 : ℝ) (7/8) := by
    constructor
    · apply (le_div_iff₀ hpos).2
      linarith [ht.1]
    · apply (div_le_iff₀ hpos).2
      linarith [ht.2]
  obtain ⟨I, hI, hlo, hhi⟩ := rootBands_cover ((t-L)/(H-L)) hu
  refine ⟨I, hI, ?_, ?_⟩
  · have := (le_div_iff₀ hpos).1 hlo
    linarith
  · have := (div_le_iff₀ hpos).1 hhi
    linarith

/- Negative controls protect the particular root interval and the overlap test. -/
theorem missing_left_rejected : check (1/16) (7/8) rootBands.tail = false := by norm_num [check, rootBands, List.range_succ]

theorem missing_right_rejected :
    check (1/16) (7/8) (rootBands.take 24) = false := by norm_num [check, rootBands, List.range_succ]

theorem internal_gap_rejected :
    check 0 1 [⟨0, 1/3⟩, ⟨2/3, 1⟩] = false := by norm_num [check, rootBands, List.range_succ]

theorem touching_intervals_accepted :
    check 0 1 [⟨0, 1/2⟩, ⟨1/2, 1⟩] = true := by norm_num [check, rootBands, List.range_succ]

end IntervalCover
end Berstein
