import HallRay.ContinuedFraction.Basic
import Berstein.Quadratic462

/-!
# Semantic bridge for exact quadratic continued fractions

The executable evaluator accepts natural digits so certificate replay can
avoid importing the continued-fraction development.  This file proves its
meaning for positive `HallRay` digits.
-/

namespace Berstein.Quadratic462

open HallRay.ContinuedFraction

/-- Real finite-tail map for a list of natural partial quotients. -/
private noncomputable def natTailMap (digits : List ℕ) (x : ℝ) : ℝ :=
  digits.foldr (fun (a : ℕ) (y : ℝ) ↦ 1 / ((a : ℝ) + y)) x

private theorem natTailMap_map (digits : Word) (x : ℝ) :
    natTailMap (digits.map Subtype.val) x = tailMap digits x := by
  induction digits generalizing x with
  | nil => rfl
  | cons a digits ih =>
      simp only [List.map_cons, natTailMap, List.foldr_cons, tailMap_cons]
      exact congrArg (fun z : ℝ => 1 / ((a.1 : ℝ) + z)) (ih x)

theorem cfNat_sound (digits : List ℕ) (tail result : Quadratic462)
    (h : cf digits tail = some result) :
    eval result = natTailMap digits (eval tail) := by
  induction digits generalizing result with
  | nil =>
      simp only [cf, List.foldr_nil, Option.some.injEq] at h
      subst result
      rfl
  | cons a digits ih =>
      change cfStep a (cf digits tail) = some result at h
      cases htail : cf digits tail with
      | none => simp [cfStep, htail] at h
      | some inner =>
          simp only [cfStep, htail] at h
          have hinter := ih inner htail
          have hstep := checkedInv_sound
            (add (ofRat a) inner) result h
          rw [eval_add, eval_ofRat, hinter] at hstep
          simpa only [natTailMap, List.foldr_cons, one_div, Rat.cast_natCast] using hstep

/-- A successful exact evaluation agrees with HallRay's real finite-tail map. -/
theorem cf_sound (digits : Word) (tail result : Quadratic462)
    (h : cf (digits.map Subtype.val) tail = some result) :
  eval result = tailMap digits (eval tail) := by
  have hn := cfNat_sound (digits.map Subtype.val) tail result h
  rw [natTailMap_map] at hn
  exact hn

end Berstein.Quadratic462
