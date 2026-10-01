import HallRay.ContinuedFraction.Basic

/-!
# Continued fractions as Möbius transformations

Algebraic facts about adjoining a finite common prefix to a continued
fraction.

Planned contents:

* the map `Φ_w`;
* its expression using consecutive convergents;
* the determinant identity;
* the common-prefix length formula;
* the exact inequalities used in Hall's length condition.
-/

namespace HallRay
namespace ContinuedFraction

/--
Adjoin the finite word `w` before the complete quotient `x`:

`prefixMap w x = [0; w₁, ..., wₙ, x]`.
-/
noncomputable def prefixMap (w : Word) (x : ℝ) : ℝ :=
  w.foldr (fun a y ↦ 1 / ((a.1 : ℝ) + y)) (1 / x)

theorem prefixMap_eq_tailMap (w : Word) (x : ℝ) :
    prefixMap w x = tailMap w (1 / x) := rfl

@[simp]
theorem prefixMap_nil (x : ℝ) : prefixMap [] x = 1 / x := rfl

@[simp]
theorem prefixMap_cons (a : PartialQuotient) (w : Word) (x : ℝ) :
    prefixMap (a :: w) x = 1 / ((a.1 : ℝ) + prefixMap w x) := rfl

theorem prefixMap_append (u v : Word) (x : ℝ) :
    prefixMap (u ++ v) x = tailMap u (prefixMap v x) := by
  rw [prefixMap_eq_tailMap, tailMap_append]
  rfl

theorem prefixMap_append_singleton (w : Word) (a : PartialQuotient) (x : ℝ) :
    prefixMap (w ++ [a]) x = prefixMap w ((a.1 : ℝ) + 1 / x) := by
  rw [prefixMap_append]
  rfl

/-- The four nonnegative coefficients of the Möbius transformation attached
to a finite word. -/
structure MobiusCoeffs where
  A : ℕ
  B : ℕ
  C : ℕ
  D : ℕ
  deriving DecidableEq

/-- Coefficients initialized by `1/x = (0*x+1)/(1*x+0)` and updated when a
digit is prepended. -/
def mobiusCoeffs : Word → MobiusCoeffs
  | [] => ⟨0, 1, 1, 0⟩
  | a :: w =>
      let c := mobiusCoeffs w
      ⟨c.C, c.D, a.1 * c.C + c.A, a.1 * c.D + c.B⟩

theorem mobius_den_pos (w : Word) {x : ℝ} (hx : 0 < x) :
    0 < ((mobiusCoeffs w).C : ℝ) * x + (mobiusCoeffs w).D := by
  induction w with
  | nil => simpa [mobiusCoeffs] using hx
  | cons a w ih =>
      have heq :
          (((a.1 * (mobiusCoeffs w).C + (mobiusCoeffs w).A : ℕ) : ℝ) * x +
              (a.1 * (mobiusCoeffs w).D + (mobiusCoeffs w).B : ℕ)) =
            (a.1 : ℝ) *
                (((mobiusCoeffs w).C : ℝ) * x + (mobiusCoeffs w).D) +
              (((mobiusCoeffs w).A : ℝ) * x + (mobiusCoeffs w).B) := by
        push_cast
        ring
      simp only [mobiusCoeffs]
      rw [heq]
      have ha : (0 : ℝ) < a.1 := by exact_mod_cast a.property
      have hprod :
          0 < (a.1 : ℝ) *
            (((mobiusCoeffs w).C : ℝ) * x + (mobiusCoeffs w).D) :=
        mul_pos ha ih
      have hnum :
          0 ≤ ((mobiusCoeffs w).A : ℝ) * x + (mobiusCoeffs w).B := by positivity
      linarith

/-- Möbius-transform expression for a common continued-fraction prefix. -/
theorem prefixMap_eq_mobius (w : Word) {x : ℝ} (hx : 0 < x) :
    prefixMap w x =
      (((mobiusCoeffs w).A : ℝ) * x + (mobiusCoeffs w).B) /
        (((mobiusCoeffs w).C : ℝ) * x + (mobiusCoeffs w).D) := by
  induction w with
  | nil => simp [mobiusCoeffs, prefixMap]
  | cons a w ih =>
      rw [prefixMap_cons, ih]
      have hden := mobius_den_pos w hx
      simp only [mobiusCoeffs]
      push_cast
      rw [show
        ((a.1 : ℝ) * (mobiusCoeffs w).C + (mobiusCoeffs w).A) * x +
              ((a.1 : ℝ) * (mobiusCoeffs w).D + (mobiusCoeffs w).B) =
            (a.1 : ℝ) *
                (((mobiusCoeffs w).C : ℝ) * x + (mobiusCoeffs w).D) +
              (((mobiusCoeffs w).A : ℝ) * x + (mobiusCoeffs w).B) by ring]
      have hD :
          0 < x * ((mobiusCoeffs w).C : ℝ) + (mobiusCoeffs w).D := by
        nlinarith
      have ha : (0 : ℝ) < a.1 := by exact_mod_cast a.property
      have hN :
          0 ≤ ((mobiusCoeffs w).A : ℝ) * x + (mobiusCoeffs w).B := by positivity
      have hE :
          0 < (a.1 : ℝ) *
                (x * ((mobiusCoeffs w).C : ℝ) + (mobiusCoeffs w).D) +
              (((mobiusCoeffs w).A : ℝ) * x + (mobiusCoeffs w).B) := by
        have := mul_pos ha hD
        linarith
      have hE' :
          0 < (a.1 : ℝ) *
                (((mobiusCoeffs w).C : ℝ) * x + (mobiusCoeffs w).D) +
              (((mobiusCoeffs w).A : ℝ) * x + (mobiusCoeffs w).B) := by
        nlinarith
      have hsum :
          0 < (a.1 : ℝ) +
            (((mobiusCoeffs w).A : ℝ) * x + (mobiusCoeffs w).B) /
              (((mobiusCoeffs w).C : ℝ) * x + (mobiusCoeffs w).D) := by
        have : 0 ≤
            (((mobiusCoeffs w).A : ℝ) * x + (mobiusCoeffs w).B) /
              (((mobiusCoeffs w).C : ℝ) * x + (mobiusCoeffs w).D) :=
          div_nonneg hN hden.le
        linarith
      field_simp [ne_of_gt hden, ne_of_gt hE', ne_of_gt hsum]

/-- Consecutive continuant coefficients have determinant of absolute value
one. -/
theorem abs_mobius_det (w : Word) :
    |((mobiusCoeffs w).A : ℝ) * (mobiusCoeffs w).D -
        ((mobiusCoeffs w).B : ℝ) * (mobiusCoeffs w).C| = 1 := by
  induction w with
  | nil => norm_num [mobiusCoeffs]
  | cons a w ih =>
      simp only [mobiusCoeffs]
      push_cast
      have heq :
          ((mobiusCoeffs w).C : ℝ) *
                ((a.1 : ℝ) * (mobiusCoeffs w).D + (mobiusCoeffs w).B) -
              ((mobiusCoeffs w).D : ℝ) *
                ((a.1 : ℝ) * (mobiusCoeffs w).C + (mobiusCoeffs w).A) =
            -(((mobiusCoeffs w).A : ℝ) * (mobiusCoeffs w).D -
              ((mobiusCoeffs w).B : ℝ) * (mobiusCoeffs w).C) := by
        ring
      rw [heq, abs_neg, ih]

/-- The denominator coefficients satisfy `0 ≤ D ≤ C`; equivalently the
ratio `qₙ₋₁/qₙ` used in Hall's estimates lies in `[0,1]`. -/
theorem mobius_D_le_C (w : Word) :
    (mobiusCoeffs w).D ≤ (mobiusCoeffs w).C := by
  have h :
      ∀ w : Word,
        (mobiusCoeffs w).D ≤ (mobiusCoeffs w).C ∧
          (w ≠ [] → (mobiusCoeffs w).B ≤ (mobiusCoeffs w).A) := by
    intro v
    induction v with
    | nil => simp [mobiusCoeffs]
    | cons a v ih =>
        by_cases hv : v = []
        · subst v
          constructor
          · simpa [mobiusCoeffs] using (Nat.succ_le_iff.mpr a.property)
          · intro
            simp [mobiusCoeffs]
        · have hBA : (mobiusCoeffs v).B ≤ (mobiusCoeffs v).A := ih.2 hv
          constructor
          · simp only [mobiusCoeffs]
            exact Nat.add_le_add (Nat.mul_le_mul_left a.1 ih.1) hBA
          · intro
            simp only [mobiusCoeffs]
            exact ih.1
  exact (h w).1

theorem mobius_C_pos (w : Word) : 0 < (mobiusCoeffs w).C := by
  have hden := mobius_den_pos w (show (0 : ℝ) < 1 by norm_num)
  by_contra h
  have hC : (mobiusCoeffs w).C = 0 := Nat.eq_zero_of_not_pos h
  have hD : (mobiusCoeffs w).D = 0 :=
    Nat.eq_zero_of_le_zero (hC ▸ mobius_D_le_C w)
  simp [hC, hD] at hden

/-- The normalized denominator ratio used in §2.2. -/
noncomputable def denominatorRatio (w : Word) : ℝ :=
  (mobiusCoeffs w).D / (mobiusCoeffs w).C

theorem denominatorRatio_mem_Icc (w : Word) :
    denominatorRatio w ∈ Set.Icc (0 : ℝ) 1 := by
  have hC : (0 : ℝ) < (mobiusCoeffs w).C := by
    exact_mod_cast mobius_C_pos w
  have hDC : ((mobiusCoeffs w).D : ℝ) ≤ (mobiusCoeffs w).C := by
    exact_mod_cast mobius_D_le_C w
  constructor
  · exact div_nonneg (by positivity) hC.le
  · exact (div_le_one hC).2 hDC

/--
Exact common-prefix length formula (Equation (2.1) in `doc/main.tex`).
-/
theorem abs_prefixMap_sub_prefixMap (w : Word) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    |prefixMap w x - prefixMap w y| =
      |x - y| /
        ((((mobiusCoeffs w).C : ℝ) * x + (mobiusCoeffs w).D) *
          (((mobiusCoeffs w).C : ℝ) * y + (mobiusCoeffs w).D)) := by
  rw [prefixMap_eq_mobius w hx, prefixMap_eq_mobius w hy]
  have hdx := mobius_den_pos w hx
  have hdy := mobius_den_pos w hy
  have hdet := abs_mobius_det w
  let A : ℝ := (mobiusCoeffs w).A
  let B : ℝ := (mobiusCoeffs w).B
  let C : ℝ := (mobiusCoeffs w).C
  let D : ℝ := (mobiusCoeffs w).D
  have hdx' : 0 < C * x + D := by simpa [C, D] using hdx
  have hdy' : 0 < C * y + D := by simpa [C, D] using hdy
  change |(A * x + B) / (C * x + D) - (A * y + B) / (C * y + D)| =
    |x - y| / ((C * x + D) * (C * y + D))
  rw [div_sub_div (A * x + B) (A * y + B) (ne_of_gt hdx') (ne_of_gt hdy'),
    abs_div, abs_mul, abs_of_pos hdx', abs_of_pos hdy']
  have hnum :
      (A * x + B) * (C * y + D) - (C * x + D) * (A * y + B) =
        (A * D - B * C) * (x - y) := by ring
  rw [hnum, abs_mul]
  have hdet' : |A * D - B * C| = 1 := by
    simpa [A, B, C, D] using hdet
  rw [hdet', one_mul]

theorem continuousOn_prefixMap_pos (w : Word) :
    ContinuousOn (prefixMap w) (Set.Ioi (0 : ℝ)) := by
  let A : ℝ := (mobiusCoeffs w).A
  let B : ℝ := (mobiusCoeffs w).B
  let C : ℝ := (mobiusCoeffs w).C
  let D : ℝ := (mobiusCoeffs w).D
  have hcont :
      ContinuousOn (fun x : ℝ ↦ (A * x + B) / (C * x + D)) (Set.Ioi 0) := by
    apply ((continuous_const.mul continuous_id).add continuous_const).continuousOn.div
      ((continuous_const.mul continuous_id).add continuous_const).continuousOn
    intro x hx
    have hpos : 0 < C * x + D := by
      dsimp [C, D]
      exact mobius_den_pos w hx
    exact ne_of_gt hpos
  apply hcont.congr
  intro x hx
  dsimp [A, B, C, D]
  exact prefixMap_eq_mobius w hx

theorem injOn_prefixMap_pos (w : Word) :
    Set.InjOn (prefixMap w) (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hlen := abs_prefixMap_sub_prefixMap w hx hy
  rw [hxy, sub_self, abs_zero] at hlen
  have hden :
      (((mobiusCoeffs w).C : ℝ) * x + (mobiusCoeffs w).D) *
          (((mobiusCoeffs w).C : ℝ) * y + (mobiusCoeffs w).D) ≠ 0 := by
    exact mul_ne_zero (ne_of_gt (mobius_den_pos w hx)) (ne_of_gt (mobius_den_pos w hy))
  have hnum : |x - y| = 0 := by
    exact (div_eq_zero_iff.mp hlen.symm).resolve_right hden
  exact sub_eq_zero.mp (abs_eq_zero.mp hnum)

end ContinuedFraction
end HallRay
