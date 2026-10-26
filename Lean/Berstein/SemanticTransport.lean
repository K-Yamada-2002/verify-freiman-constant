import Berstein.SemanticCore
import Berstein.Normalization
import Berstein.FractionalLinear
import HallRay.ContinuedFraction.PrefixGrowth

namespace Berstein.GraphMeaning
open HallRay.ContinuedFraction

theorem sign_of_parity (w : Word) (p : Bool) (hp : p = decide (w.length % 2 = 1)) :
    (-1 : ℝ)^w.length = if p then -1 else 1 := by
  rw [neg_one_pow_eq_pow_mod_two]
  by_cases h : w.length % 2 = 1
  · have he : p = true := by simpa [h] using hp
    simp [he,h]
  · have he : p = false := by simpa [h] using hp
    have hz : w.length % 2 = 0 := by omega
    simp [he,hz]

theorem tailMap_le_of_signed_difference (w : Word) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : (-1 : ℝ)^w.length*(x-y) ≤ 0) :
    tailMap w x ≤ tailMap w y := by
  apply sub_nonpos.mp
  rw [Normalization.tailMap_sub w hx hy]
  exact div_nonpos_of_nonpos_of_nonneg h (by positivity)

theorem anchor_order (w : Word) (s : Forbidden31313.State) (p : Bool)
    (hp : p = decide (w.length % 2 = 1)) :
    tailMap w (anchor s.val p).eval ≤ tailMap w (opposite s.val p).eval := by
  apply tailMap_le_of_signed_difference w (anchor_unit s p).1 (opposite_unit s p).1
  rw [sign_of_parity w p hp]
  have h := (Forbidden31313.exactBounds_unit s).2.1
  cases p <;> simp [anchor, opposite, lower_eval, upper_eval] <;> linarith

theorem anchor_min_opposite_max (w : Word) (s : Forbidden31313.State) (p : Bool)
    (hp : p = decide (w.length % 2 = 1)) :
    tailMap w (anchor s.val p).eval =
      min (tailMap w (Forbidden31313.exactLower s)) (tailMap w (Forbidden31313.exactUpper s)) ∧
    tailMap w (opposite s.val p).eval =
      max (tailMap w (Forbidden31313.exactLower s)) (tailMap w (Forbidden31313.exactUpper s)) := by
  have h := anchor_order w s p hp
  cases p
  · simp only [anchor, opposite, Bool.false_eq_true, ↓reduceIte, lower_eval, upper_eval] at h ⊢
    exact ⟨(min_eq_left h).symm, (max_eq_right h).symm⟩
  · simp only [anchor, opposite, ↓reduceIte, lower_eval, upper_eval] at h ⊢
    exact ⟨(min_eq_right h).symm, (max_eq_left h).symm⟩

theorem coeffs_map (w : Word) : coeffs (w.map Subtype.val) =
    ⟨(mobiusCoeffs w).A, (mobiusCoeffs w).B, (mobiusCoeffs w).C, (mobiusCoeffs w).D⟩ := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [List.map_cons, coeffs, ih, mobiusCoeffs]

theorem denominatorRatio_append (u v : Word) : denominatorRatio (u++v) =
    ((mobiusCoeffs v).D+(mobiusCoeffs v).B*denominatorRatio u) /
      ((mobiusCoeffs v).C+(mobiusCoeffs v).A*denominatorRatio u) := by
  have hC : (0 : ℝ) < (mobiusCoeffs u).C := by exact_mod_cast mobius_C_pos u
  have hCv : (0 : ℝ) < (mobiusCoeffs v).C := by exact_mod_cast mobius_C_pos v
  have hnew : (0 : ℝ) < (mobiusCoeffs (u++v)).C := by exact_mod_cast mobius_C_pos (u++v)
  rw [mobiusCoeffs_append] at hnew
  unfold denominatorRatio
  rw [mobiusCoeffs_append]
  push_cast at hnew ⊢
  field_simp [ne_of_gt hC, ne_of_gt hnew]
  <;> ring

theorem shapeImage_cast (v : Word) (r : ℚ) : (shapeImage (v.map Subtype.val) r : ℝ) =
    ((mobiusCoeffs v).D+(mobiusCoeffs v).B*(r : ℝ)) /
      ((mobiusCoeffs v).C+(mobiusCoeffs v).A*(r : ℝ)) := by
  simp only [shapeImage, coeffs_map]
  push_cast
  rfl

theorem shape_transport (u v : Word) (parent child : QBounds)
    (hparent : parent.mem (denominatorRatio u)) (hp : 0 ≤ parent.lo)
    (hl : child.lo ≤ shapeImage (v.map Subtype.val) parent.lo ∧
      shapeImage (v.map Subtype.val) parent.lo ≤ child.hi)
    (hh : child.lo ≤ shapeImage (v.map Subtype.val) parent.hi ∧
      shapeImage (v.map Subtype.val) parent.hi ≤ child.hi) :
    child.mem (denominatorRatio (u++v)) := by
  have hlo : (0 : ℝ) ≤ parent.lo := by exact_mod_cast hp
  have hhi : (0 : ℝ) ≤ parent.hi := hlo.trans (hparent.1.trans hparent.2)
  have hC : (0 : ℝ) < (mobiusCoeffs v).C := by exact_mod_cast mobius_C_pos v
  have hA : (0 : ℝ) ≤ (mobiusCoeffs v).A := by positivity
  have hl' : child.mem (shapeImage (v.map Subtype.val) parent.lo) := by
    unfold QBounds.mem
    exact_mod_cast hl
  have hh' : child.mem (shapeImage (v.map Subtype.val) parent.hi) := by
    unfold QBounds.mem
    exact_mod_cast hh
  rw [shapeImage_cast] at hl' hh'
  rw [denominatorRatio_append]
  exact FractionalLinear.enclosure hparent
    (add_pos_of_pos_of_nonneg hC (mul_nonneg hA hlo))
    (add_pos_of_pos_of_nonneg hC (mul_nonneg hA hhi))
    (add_pos_of_pos_of_nonneg hC (mul_nonneg hA (denominatorRatio_mem_Icc u).1)) hl' hh'

theorem derivativeDen_eval (v : Word) (y : Quadratic462) :
    (derivativeDen (v.map Subtype.val) y).1.eval =
      (mobiusCoeffs v).C+(mobiusCoeffs v).D*y.eval ∧
    (derivativeDen (v.map Subtype.val) y).2.eval =
      (mobiusCoeffs v).A+(mobiusCoeffs v).B*y.eval := by
  simp only [derivativeDen, coeffs_map, Quadratic462.eval_add,
    Quadratic462.eval_mul, Quadratic462.eval_ofRat]
  push_cast
  exact ⟨rfl, rfl⟩

theorem scale_append_ratio (u v : Word) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Normalization.scale (u++v) y / Normalization.scale u x =
      ((1+denominatorRatio u*x) /
        (((mobiusCoeffs v).C+(mobiusCoeffs v).D*y) +
          denominatorRatio u*((mobiusCoeffs v).A+(mobiusCoeffs v).B*y)))^2 := by
  have hC : (0 : ℝ) < (mobiusCoeffs u).C := by exact_mod_cast mobius_C_pos u
  have hCv : (0 : ℝ) < (mobiusCoeffs v).C := by exact_mod_cast mobius_C_pos v
  have hnewC : (0 : ℝ) < (mobiusCoeffs (u++v)).C := by exact_mod_cast mobius_C_pos (u++v)
  have hxden : (0 : ℝ) < (mobiusCoeffs u).C+(mobiusCoeffs u).D*x := by positivity
  have hyden : (0 : ℝ) < (mobiusCoeffs (u++v)).C+(mobiusCoeffs (u++v)).D*y := by positivity
  unfold Normalization.scale denominatorRatio
  rw [mobiusCoeffs_append] at hyden ⊢
  push_cast at hyden ⊢
  field_simp [ne_of_gt hC, ne_of_gt hxden, ne_of_gt hyden]
  <;> ring

/-- Checked derivative values at both shape corners bound the actual
change of anchor scale throughout the whole parameter interval. -/
theorem derivative_transport (u v : Word) (parent out : QBounds)
    (x y dl dh : Quadratic462) (hx : 0 ≤ x.eval) (hy : 0 ≤ y.eval)
    (hparent : parent.mem (denominatorRatio u)) (hp : 0 ≤ parent.lo)
    (hl : derivativeAt (v.map Subtype.val) x y parent.lo = some dl)
    (hh : derivativeAt (v.map Subtype.val) x y parent.hi = some dh)
    (hlo : out.mem dl.eval) (hhi : out.mem dh.eval) :
    out.mem (Normalization.scale (u++v) y.eval / Normalization.scale u x.eval) := by
  have hd := derivativeDen_eval v y
  rw [derivativeAt_sound _ _ _ _ _ hl, hd.1, hd.2] at hlo
  rw [derivativeAt_sound _ _ _ _ _ hh, hd.1, hd.2] at hhi
  rw [scale_append_ratio u v hx hy]
  have hp0 : (0 : ℝ) ≤ parent.lo := by exact_mod_cast hp
  have hp1 : (0 : ℝ) ≤ parent.hi := hp0.trans (hparent.1.trans hparent.2)
  have hr : 0 ≤ denominatorRatio u := (denominatorRatio_mem_Icc u).1
  have hC : (0 : ℝ) < (mobiusCoeffs v).C := by exact_mod_cast mobius_C_pos v
  have hd0 : (0 : ℝ) < (mobiusCoeffs v).C+(mobiusCoeffs v).D*y.eval := by positivity
  have hd1 : (0 : ℝ) ≤ (mobiusCoeffs v).A+(mobiusCoeffs v).B*y.eval := by positivity
  change _ ∈ Set.Icc (out.lo : ℝ) (out.hi : ℝ)
  change _ ∈ Set.Icc (out.lo : ℝ) (out.hi : ℝ) at hlo hhi
  simpa only [mul_comm] using FractionalLinear.square_fractional_enclosure hparent
    (add_pos_of_pos_of_nonneg hd0 (mul_nonneg hd1 hp0))
    (add_pos_of_pos_of_nonneg hd0 (mul_nonneg hd1 hp1))
    (add_pos_of_pos_of_nonneg hd0 (mul_nonneg hd1 hr))
    (show 0 ≤ 1+x.eval*(parent.lo : ℝ) by nlinarith [mul_nonneg hx hp0])
    (show 0 ≤ 1+x.eval*(parent.hi : ℝ) by nlinarith [mul_nonneg hx hp1])
    (by simpa only [mul_comm] using hlo) (by simpa only [mul_comm] using hhi)

/-- A constant tag requires an exact cross-product identity, so equal tags
denote equal actual derivative factors rather than merely overlapping boxes. -/
theorem derivative_constant (u v : Word) (x y k : Quadratic462) (r₀ : ℚ)
    (hx : 0 ≤ x.eval) (hy : 0 ≤ y.eval) (hr₀ : 0 ≤ r₀)
    (hcross : Quadratic462.mul x (derivativeDen (v.map Subtype.val) y).1 =
      (derivativeDen (v.map Subtype.val) y).2)
    (hk : derivativeAt (v.map Subtype.val) x y r₀ = some k) :
    Normalization.scale (u++v) y.eval / Normalization.scale u x.eval = k.eval := by
  let d₀ := (derivativeDen (v.map Subtype.val) y).1.eval
  let d₁ := (derivativeDen (v.map Subtype.val) y).2.eval
  have hd := derivativeDen_eval v y
  have hC : (0 : ℝ) < (mobiusCoeffs v).C := by exact_mod_cast mobius_C_pos v
  have hpos : 0 < d₀ := by dsimp [d₀]; rw [hd.1]; positivity
  have hnonneg : 0 ≤ d₁ := by dsimp [d₁]; rw [hd.2]; positivity
  have hc : x.eval*d₀ = 1*d₁ := by
    have h := congrArg Quadratic462.eval hcross
    simpa only [Quadratic462.eval_mul, one_mul] using h
  have hr : 0 ≤ denominatorRatio u := (denominatorRatio_mem_Icc u).1
  have hz : (0 : ℝ) ≤ r₀ := by exact_mod_cast hr₀
  have hact : (1+denominatorRatio u*x.eval)/(d₀+denominatorRatio u*d₁) = 1/d₀ := by
    simpa only [mul_comm] using FractionalLinear.constant_of_cross_eq (ne_of_gt hpos)
      (ne_of_gt (add_pos_of_pos_of_nonneg hpos (mul_nonneg hnonneg hr))) hc
  have hcorner : (1+(r₀ : ℝ)*x.eval)/(d₀+(r₀ : ℝ)*d₁) = 1/d₀ := by
    simpa only [mul_comm] using FractionalLinear.constant_of_cross_eq (ne_of_gt hpos)
      (ne_of_gt (add_pos_of_pos_of_nonneg hpos (mul_nonneg hnonneg hz))) hc
  rw [scale_append_ratio u v hx hy, ← hd.1, ← hd.2]
  change ((1+denominatorRatio u*x.eval)/(d₀+denominatorRatio u*d₁))^2 = k.eval
  rw [hact]
  have he := derivativeAt_sound _ _ _ _ _ hk
  change k.eval = ((1+(r₀ : ℝ)*x.eval)/(d₀+(r₀ : ℝ)*d₁))^2 at he
  rw [hcorner] at he
  exact he.symm

end Berstein.GraphMeaning
