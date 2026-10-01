import Berstein.CylinderBound
import Berstein.IntervalArithmetic

/-! Semantic identities behind the normalized graph comparisons. -/

namespace Berstein.Normalization
open HallRay.ContinuedFraction

noncomputable def ratio (r anchor x : ℝ) : ℝ := (1+r*anchor)/(1+r*x)

theorem ratio_den_pos {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) : 0 < 1+r*x := by
  nlinarith [mul_nonneg hr hx]

theorem ratio_mono {r s anchor x : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hx : 0 ≤ x) (hax : x ≤ anchor) : ratio r anchor x ≤ ratio s anchor x := by
  unfold ratio
  apply (div_le_div_iff₀ (ratio_den_pos hr hx) (ratio_den_pos (hr.trans hrs) hx)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hrs) (sub_nonneg.mpr hax)]

theorem ratio_anti {r s anchor x : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hx : 0 ≤ x) (hax : anchor ≤ x) : ratio s anchor x ≤ ratio r anchor x := by
  unfold ratio
  apply (div_le_div_iff₀ (ratio_den_pos (hr.trans hrs) hx) (ratio_den_pos hr hx)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hrs) (sub_nonneg.mpr hax)]

theorem ratio_mem_uIcc {lo hi r anchor x : ℝ} (hlo : 0 ≤ lo)
    (hr : r ∈ Set.Icc lo hi) (hx : 0 ≤ x) :
    ratio r anchor x ∈ Set.uIcc (ratio lo anchor x) (ratio hi anchor x) := by
  rcases le_total x anchor with h | h
  · exact Set.mem_uIcc_of_le (ratio_mono hlo hr.1 hx h)
      (ratio_mono (hlo.trans hr.1) hr.2 hx h)
  · exact Set.mem_uIcc_of_ge (ratio_anti (hlo.trans hr.1) hr.2 hx h)
      (ratio_anti hlo hr.1 hx h)

theorem ratio_enclosure {lo hi r anchor x : ℝ} (hlo : 0 ≤ lo)
    (hr : r ∈ Set.Icc lo hi) (hx : 0 ≤ x) (out : QBounds)
    (hl : out.mem (ratio lo anchor x)) (hh : out.mem (ratio hi anchor x)) :
    out.mem (ratio r anchor x) := by
  have h := ratio_mem_uIcc hlo hr hx (anchor := anchor)
  exact ⟨(le_min hl.1 hh.1).trans h.1, h.2.trans (max_le hl.2 hh.2)⟩

theorem ratio_self {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) : ratio r x x = 1 :=
  div_self (ne_of_gt (ratio_den_pos hr hx))

theorem determinant_signed (w : Word) :
    ((mobiusCoeffs w).B : ℝ)*(mobiusCoeffs w).C -
      (mobiusCoeffs w).A*(mobiusCoeffs w).D = (-1 : ℝ)^w.length := by
  induction w with
  | nil => norm_num [mobiusCoeffs]
  | cons a w ih =>
      simp only [mobiusCoeffs, List.length_cons, Nat.cast_add, Nat.cast_mul, pow_succ]
      calc
        _ = -(((mobiusCoeffs w).B : ℝ)*(mobiusCoeffs w).C -
          (mobiusCoeffs w).A*(mobiusCoeffs w).D) := by ring
        _ = _ := by rw [ih]; ring

theorem tailMap_sub (w : Word) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    tailMap w x - tailMap w y = (-1 : ℝ)^w.length*(x-y) /
      (((mobiusCoeffs w).C+(mobiusCoeffs w).D*x)*
       ((mobiusCoeffs w).C+(mobiusCoeffs w).D*y)) := by
  have hC : (0 : ℝ) < (mobiusCoeffs w).C := by exact_mod_cast mobius_C_pos w
  have hdx : (0 : ℝ) < (mobiusCoeffs w).C+(mobiusCoeffs w).D*x := by positivity
  have hdy : (0 : ℝ) < (mobiusCoeffs w).C+(mobiusCoeffs w).D*y := by positivity
  rw [tailMap_eq_mobius w x hx, tailMap_eq_mobius w y hy,
    div_sub_div _ _ (ne_of_gt hdx) (ne_of_gt hdy), ← determinant_signed w]
  congr 1
  ring

noncomputable def scale (w : Word) (anchor : ℝ) : ℝ :=
  1 / ((mobiusCoeffs w).C+(mobiusCoeffs w).D*anchor)^2

theorem scale_pos (w : Word) {anchor : ℝ} (ha : 0 ≤ anchor) : 0 < scale w anchor := by
  have hC : (0 : ℝ) < (mobiusCoeffs w).C := by exact_mod_cast mobius_C_pos w
  unfold scale
  positivity

/-- The graph's difference formula follows from the actual finite CF map. -/
theorem normalized_difference (w : Word) {anchor x y : ℝ}
    (ha : 0 ≤ anchor) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (tailMap w x-tailMap w y)/scale w anchor =
      (-1 : ℝ)^w.length * (x-y) *
        ratio (denominatorRatio w) anchor x * ratio (denominatorRatio w) anchor y := by
  have hC : (0 : ℝ) < (mobiusCoeffs w).C := by exact_mod_cast mobius_C_pos w
  have hdx : (0 : ℝ) < (mobiusCoeffs w).C+(mobiusCoeffs w).D*x := by positivity
  have hdy : (0 : ℝ) < (mobiusCoeffs w).C+(mobiusCoeffs w).D*y := by positivity
  have hda : (0 : ℝ) < (mobiusCoeffs w).C+(mobiusCoeffs w).D*anchor := by positivity
  have hr : 0 ≤ denominatorRatio w := (denominatorRatio_mem_Icc w).1
  have hrx := ratio_den_pos hr hx
  have hry := ratio_den_pos hr hy
  rw [tailMap_sub w hx hy]
  unfold scale ratio denominatorRatio at *
  field_simp [ne_of_gt hC, ne_of_gt hdx, ne_of_gt hdy, ne_of_gt hda,
    ne_of_gt hrx, ne_of_gt hry]

/-- Multiplying independently proved ratio boxes yields a difference box.
The orientation sign is handled separately by the parity of the prefix. -/
theorem unsigned_difference_enclosure (bx by_ rx ry : QBounds)
    {x y r anchor : ℝ} (hx : bx.mem x) (hy : by_.mem y)
    (hrx : rx.mem (ratio r anchor x)) (hry : ry.mem (ratio r anchor y)) :
    (QBounds.mul (QBounds.sub bx by_) (QBounds.mul rx ry)).mem
      ((x-y)*ratio r anchor x*ratio r anchor y) := by
  simpa [mul_assoc] using QBounds.mul_sound (QBounds.sub bx by_) (QBounds.mul rx ry)
    (x-y) (ratio r anchor x*ratio r anchor y) (QBounds.sub_sound bx by_ x y hx hy)
    (QBounds.mul_sound rx ry _ _ hrx hry)

end Berstein.Normalization
