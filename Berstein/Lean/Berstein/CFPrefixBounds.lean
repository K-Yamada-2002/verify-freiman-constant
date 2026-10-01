import Berstein.CylinderBound
import Berstein.IntervalArithmetic

/-! Executable rational enclosures for finite continued-fraction prefixes. -/

namespace Berstein.CFPrefixBounds
open HallRay.ContinuedFraction

def step (d : PartialQuotient) (b : QBounds) : QBounds :=
  ⟨1 / ((d.val : ℚ) + b.hi), 1 / ((d.val : ℚ) + b.lo)⟩

def enclose : Word → QBounds → QBounds
  | [], b => b
  | d :: w, b => step d (enclose w b)

theorem step_nonneg (d : PartialQuotient) (b : QBounds) (hb : 0 ≤ b.lo)
    (horder : b.lo ≤ b.hi) : 0 ≤ (step d b).lo := by
  have hhi : 0 ≤ b.hi := hb.trans horder
  dsimp [step]
  positivity

theorem step_order (d : PartialQuotient) (b : QBounds) (hb : 0 ≤ b.lo)
    (horder : b.lo ≤ b.hi) : (step d b).lo ≤ (step d b).hi := by
  have hd : (0 : ℚ) < d.val := by exact_mod_cast d.property
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem step_sound (d : PartialQuotient) (b : QBounds) (hb : 0 ≤ b.lo)
    {x : ℝ} (hx : b.mem x) : (step d b).mem (1 / ((d.val : ℝ) + x)) := by
  have hd : (0 : ℝ) < d.val := by exact_mod_cast d.property
  have hb' : (0 : ℝ) ≤ b.lo := by exact_mod_cast hb
  simp only [QBounds.mem, step, Rat.cast_div, Rat.cast_one, Rat.cast_add,
    Rat.cast_natCast]
  exact ⟨one_div_le_one_div_of_le (by linarith [hx.1]) (by linarith [hx.2]),
    one_div_le_one_div_of_le (by linarith) (by linarith [hx.1])⟩

theorem enclose_valid (w : Word) (b : QBounds) (hb : 0 ≤ b.lo)
    (horder : b.lo ≤ b.hi) :
    0 ≤ (enclose w b).lo ∧ (enclose w b).lo ≤ (enclose w b).hi := by
  induction w with
  | nil => exact ⟨hb, horder⟩
  | cons d w ih => exact ⟨step_nonneg d _ ih.1 ih.2, step_order d _ ih.1 ih.2⟩

theorem enclose_sound (w : Word) (b : QBounds) (hb : 0 ≤ b.lo)
    {x : ℝ} (hx : b.mem x) : (enclose w b).mem (tailMap w x) := by
  have horder : b.lo ≤ b.hi := by exact_mod_cast hx.1.trans hx.2
  induction w with
  | nil => exact hx
  | cons d w ih =>
      exact step_sound d _ (enclose_valid w b hb horder).1 ih

theorem value_sound (u : ℕ → PartialQuotient) (n : ℕ) (b : QBounds)
    (hb : 0 ≤ b.lo) (hx : b.mem (value 0 (fun k => u (n+k)))) :
    (enclose ((List.range n).map u) b).mem (value 0 u) := by
  rw [value_zero_eq_tailMap_prefix u n]
  exact enclose_sound _ _ hb hx

end Berstein.CFPrefixBounds
