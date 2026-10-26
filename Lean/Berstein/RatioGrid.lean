import Berstein.IntervalArithmetic
import Mathlib.Tactic.NormNum

/-!
# Verified destination-bin coverage

Grid boundaries may themselves be enclosed by rational intervals. A witness
gives a consecutive range of child bins. The checker requires both outside
grid cuts to lie beyond the entire ratio image and requires adoption of every
bin in the range. This is a witness checker, not the binary-search heuristic
which proposes the range.
-/

namespace Berstein.RatioGrid

/-- Consecutive grid cells cover the interval between the outside cuts.
No unstated monotonicity or strictness condition is needed for this direction. -/
theorem between_cuts (cut : ℕ → ℝ) (n : ℕ) (x : ℝ)
    (hl : cut 0 ≤ x) (hr : x ≤ cut (n+1)) :
    ∃ k ≤ n, cut k ≤ x ∧ x ≤ cut (k+1) := by
  induction n with
  | zero => exact ⟨0, le_rfl, hl, hr⟩
  | succ n ih =>
      by_cases h : x ≤ cut (n+1)
      · obtain ⟨k, hk, hkl, hkr⟩ := ih h
        exact ⟨k, hk.trans (Nat.le_succ _), hkl, hkr⟩
      · exact ⟨n+1, le_rfl, (lt_of_not_ge h).le, hr⟩

def check (bounds : ℕ → QBounds) (image : QBounds) (active : ℕ → Bool)
    (first last : ℕ) : Bool :=
  decide (first ≤ last) &&
    (decide ((bounds first).hi ≤ image.lo) &&
      (decide (image.hi ≤ (bounds (last+1)).lo) &&
        (List.range (last-first+1)).all (fun k => active (first+k))))

/-- Acceptance covers every actual ratio in the image by an adopted cell.
The real grid cuts need only satisfy their rational enclosures. -/
theorem check_sound (bounds : ℕ → QBounds) (image : QBounds) (active : ℕ → Bool)
    (first last : ℕ) (h : check bounds image active first last = true)
    (cut : ℕ → ℝ) (hcut : ∀ k, (bounds k).mem (cut k))
    (x : ℝ) (hx : image.mem x) :
    ∃ k, first ≤ k ∧ k ≤ last ∧ active k = true ∧ cut k ≤ x ∧ x ≤ cut (k+1) := by
  have hc : first ≤ last ∧ (bounds first).hi ≤ image.lo ∧
      image.hi ≤ (bounds (last+1)).lo ∧
      ∀ k ∈ List.range (last-first+1), active (first+k) = true := by
    simpa [check, Bool.and_eq_true, List.all_eq_true] using h
  have hlo : ((bounds first).hi : ℝ) ≤ image.lo := by exact_mod_cast hc.2.1
  have hhi : (image.hi : ℝ) ≤ (bounds (last+1)).lo := by exact_mod_cast hc.2.2.1
  have hl : cut first ≤ x := ((hcut first).2.trans hlo).trans hx.1
  have hr : x ≤ cut (last+1) := (hx.2.trans hhi).trans (hcut (last+1)).1
  have hlast : first + (last-first+1) = last+1 := by omega
  obtain ⟨k, hk, hkl, hkr⟩ := between_cuts (fun j => cut (first+j)) (last-first) x
    (by simpa using hl) (by simpa [hlast] using hr)
  refine ⟨first+k, by omega, by omega, hc.2.2.2 k ?_, hkl, ?_⟩
  · exact List.mem_range.mpr (by omega)
  · simpa [Nat.add_assoc] using hkr

private def exactCuts (k : ℕ) : QBounds := QBounds.point k

theorem positive_control :
    check exactCuts ⟨1/4, 7/4⟩ (fun _ => true) 0 1 = true := by
  norm_num [check, exactCuts, QBounds.point, List.range_succ]

/-- Choosing only the first destination bin loses the upper part of the image. -/
theorem short_cover_rejected :
    check exactCuts ⟨1/4, 7/4⟩ (fun _ => true) 0 0 = false := by
  norm_num [check, exactCuts, QBounds.point, List.range_succ]

theorem missing_bin_rejected :
    check exactCuts ⟨1/4, 7/4⟩ (fun k => k == 0) 0 1 = false := by
  norm_num [check, exactCuts, QBounds.point, List.range_succ]

end Berstein.RatioGrid
