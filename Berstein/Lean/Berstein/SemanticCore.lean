import Berstein.SemanticCheck
import Berstein.QuadraticCF
import Berstein.Forbidden31313

/-! Exact certificate labels interpreted as real continued fractions and
forbidden-word automaton states. The numerical label data are untrusted;
these statements use successful executable checks. -/
set_option maxHeartbeats 1000000

namespace Berstein.GraphMeaning
open HallRay.ContinuedFraction

 theorem contains_sound (b : QBounds) (x : Quadratic462) (h : contains b x = true) :
    b.mem x.eval := by
  have hh := Bool.and_eq_true_iff.mp h
  constructor
  · simpa only [Quadratic462.eval_ofRat] using Quadratic462.le_sound _ _ hh.1
  · simpa only [Quadratic462.eval_ofRat] using Quadratic462.le_sound _ _ hh.2

theorem lower_eval (s : Forbidden31313.State) :
    (lower s.val).eval = Forbidden31313.exactLower s := by
  fin_cases s <;> norm_num [lower, Quadratic462.eval, Forbidden31313.exactLower] <;> ring

theorem upper_eval (s : Forbidden31313.State) :
    (upper s.val).eval = Forbidden31313.exactUpper s := by
  fin_cases s <;> norm_num [upper, Quadratic462.eval, Forbidden31313.exactUpper] <;> ring

theorem anchor_unit (s : Forbidden31313.State) (parity : Bool) :
    (anchor s.val parity).eval ∈ Set.Icc (0 : ℝ) 1 := by
  have h := Forbidden31313.exactBounds_unit s
  cases parity <;> simp only [anchor, Bool.false_eq_true, ↓reduceIte, lower_eval, upper_eval]
  · exact ⟨h.1, h.2.1.trans h.2.2⟩
  · exact ⟨h.1.trans h.2.1, h.2.2⟩

theorem opposite_unit (s : Forbidden31313.State) (parity : Bool) :
    (opposite s.val parity).eval ∈ Set.Icc (0 : ℝ) 1 := by
  have h := Forbidden31313.exactBounds_unit s
  cases parity <;> simp only [opposite, Bool.false_eq_true, ↓reduceIte, lower_eval, upper_eval]
  · exact ⟨h.1.trans h.2.1, h.2.2⟩
  · exact ⟨h.1, h.2.1.trans h.2.2⟩

theorem stateStep_eq (s : Forbidden31313.State) (d : ℕ) :
    stateStep s.val d = (Forbidden31313.transitionNat s d).map Fin.val := by
  simp only [stateStep, Forbidden31313.transitionNat]
  split_ifs <;> rfl

theorem after_eq (s : Forbidden31313.State) (w : Word) :
    after s.val (w.map Subtype.val) = (Forbidden31313.afterWord s w).map Fin.val := by
  induction w generalizing s with
  | nil => rfl
  | cons d w ih =>
      simp only [List.map_cons, after, Forbidden31313.afterWord, stateStep_eq]
      cases h : Forbidden31313.transitionNat s d.val with
      | none => rfl
      | some t => simpa only [Option.map_some, Option.bind_eq_bind, Option.pure_def, Option.bind_some] using ih t

theorem after_sound (s t : Forbidden31313.State) (w : Word)
    (h : after s.val (w.map Subtype.val) = some t.val) :
    Forbidden31313.afterWord s w = some t := by
  rw [after_eq] at h
  cases hs : Forbidden31313.afterWord s w with
  | none => simp [hs] at h
  | some u =>
      have heq : u = t := Fin.ext (by simpa [hs] using h)
      simpa only [heq]

/-- Exact quadratic labels of an accepted transition denote the images of
its child interval endpoints under the extension continued fraction. -/
theorem cf_endpoints (w : Word) (s : Forbidden31313.State) (parity : Bool)
    (lo hi : Quadratic462)
    (hl : Quadratic462.cf (w.map Subtype.val) (anchor s.val parity) = some lo)
    (hh : Quadratic462.cf (w.map Subtype.val) (opposite s.val parity) = some hi) :
    lo.eval = tailMap w (anchor s.val parity).eval ∧
    hi.eval = tailMap w (opposite s.val parity).eval :=
  ⟨Quadratic462.cf_sound w _ _ hl, Quadratic462.cf_sound w _ _ hh⟩

/-- The stored derivative evaluation is the squared real fractional-linear
expression at the checked parent shape endpoint. -/
theorem derivativeAt_sound (w : List Nat) (x y z : Quadratic462) (r : ℚ)
    (h : derivativeAt w x y r = some z) :
    z.eval = ((1+(r : ℝ)*x.eval) /
      ((derivativeDen w y).1.eval+(r : ℝ)*(derivativeDen w y).2.eval))^2 := by
  unfold derivativeAt at h
  cases hi : Quadratic462.checkedInv
      (Quadratic462.add (derivativeDen w y).1
        (Quadratic462.mul (Quadratic462.ofRat r) (derivativeDen w y).2)) with
  | none => simp [hi] at h
  | some v =>
      simp only [hi, Option.bind_eq_bind, Option.pure_def, Option.bind_some, Option.some.injEq] at h
      subst z
      have hv := Quadratic462.checkedInv_sound _ _ hi
      simp only [Quadratic462.eval_add, Quadratic462.eval_mul,
        Quadratic462.eval_ofRat] at hv
      simp only [Quadratic462.eval_mul, Quadratic462.eval_add, Quadratic462.eval_one,
        Quadratic462.eval_ofRat, hv, div_eq_mul_inv, pow_two]


end Berstein.GraphMeaning
