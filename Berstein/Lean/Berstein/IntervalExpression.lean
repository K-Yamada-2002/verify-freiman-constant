import Berstein.IntervalArithmetic
import Berstein.FiniteCover

/-!
# A verified rational-expression backend for interval covers

`enclose` computes rational bounds or rejects a denominator whose lower
bound is not positive. Its structural soundness theorem holds for every real
parameter environment inside the supplied boxes. The coverage wrapper uses
this proved comparator directly, requiring no backend-soundness hypothesis.
-/

namespace Berstein.IntervalExpression

/-- Exact rational expressions with numbered real parameters. -/
inductive Expr where
  | const : ℚ → Expr
  | var : ℕ → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | div : Expr → Expr → Expr
  deriving DecidableEq, Repr

/-- The real interpretation of a rational expression. -/
noncomputable def eval (env : ℕ → ℝ) : Expr → ℝ
  | .const q => q
  | .var k => env k
  | .add a b => eval env a + eval env b
  | .sub a b => eval env a - eval env b
  | .mul a b => eval env a * eval env b
  | .div a b => eval env a / eval env b

/-- Executable rational enclosure; all failed denominators propagate `none`. -/
def enclose (boxes : ℕ → QBounds) : Expr → Option QBounds
  | .const q => some (QBounds.point q)
  | .var k => some (boxes k)
  | .add a b => match enclose boxes a, enclose boxes b with
      | some x, some y => some (QBounds.add x y)
      | _, _ => none
  | .sub a b => match enclose boxes a, enclose boxes b with
      | some x, some y => some (QBounds.sub x y)
      | _, _ => none
  | .mul a b => match enclose boxes a, enclose boxes b with
      | some x, some y => some (QBounds.mul x y)
      | _, _ => none
  | .div a b => match enclose boxes a, enclose boxes b with
      | some x, some y => QBounds.checkedDiv x y
      | _, _ => none

/-- Every successful enclosure contains the real evaluation, uniformly
over all environments which satisfy the variable bounds. -/
theorem enclose_sound (boxes : ℕ → QBounds) (env : ℕ → ℝ)
    (henv : ∀ k, (boxes k).mem (env k)) (e : Expr) (bounds : QBounds)
    (h : enclose boxes e = some bounds) : bounds.mem (eval env e) := by
  induction e generalizing bounds with
  | const q =>
      simp only [enclose, Option.some.injEq] at h
      subst bounds
      exact QBounds.point_sound q
  | var k =>
      simp only [enclose, Option.some.injEq] at h
      subst bounds
      exact henv k
  | add a b ihA ihB =>
      cases ha : enclose boxes a <;> cases hb : enclose boxes b <;>
        simp [enclose, ha, hb] at h
      subst bounds
      exact QBounds.add_sound _ _ _ _ (ihA _ ha) (ihB _ hb)
  | sub a b ihA ihB =>
      cases ha : enclose boxes a <;> cases hb : enclose boxes b <;>
        simp [enclose, ha, hb] at h
      subst bounds
      exact QBounds.sub_sound _ _ _ _ (ihA _ ha) (ihB _ hb)
  | mul a b ihA ihB =>
      cases ha : enclose boxes a <;> cases hb : enclose boxes b <;>
        simp [enclose, ha, hb] at h
      subst bounds
      exact QBounds.mul_sound _ _ _ _ (ihA _ ha) (ihB _ hb)
  | div a b ihA ihB =>
      cases ha : enclose boxes a <;> cases hb : enclose boxes b <;>
        simp [enclose, ha, hb] at h
      exact QBounds.checkedDiv_sound _ _ _ _ _ (ihA _ ha) (ihB _ hb) h

/-- Certify `a ≤ b` by enclosing `b-a`. Syntactically identical expressions
are accepted directly, avoiding loss of precision from repeated parameters. -/
def leq (boxes : ℕ → QBounds) (a b : Expr) : Bool :=
  if a = b then true else
    match enclose boxes (.sub b a) with
    | some bounds => bounds.nonnegativeTest
    | none => false

/-- An accepted expression comparison is valid throughout the parameter box. -/
theorem leq_sound (boxes : ℕ → QBounds) (env : ℕ → ℝ)
    (henv : ∀ k, (boxes k).mem (env k)) (a b : Expr)
    (h : leq boxes a b = true) : eval env a ≤ eval env b := by
  by_cases hab : a = b
  · subst b
    exact le_rfl
  · simp only [leq, if_neg hab] at h
    cases he : enclose boxes (.sub b a) with
    | none => simp [he] at h
    | some bounds =>
        have htest : bounds.nonnegativeTest = true := by simpa [he] using h
        have hnonneg := QBounds.nonnegativeTest_sound bounds (eval env (.sub b a))
          (enclose_sound boxes env henv _ bounds he) htest
        change 0 ≤ eval env b - eval env a at hnonneg
        linarith

/-- A finite cover checker using the certified rational-expression comparator. -/
def verifiedCheckCover {Vertex : Type*} (boxes : ℕ → QBounds)
    (interval : Vertex → FiniteCover.Interval Expr) (admitted : Vertex → Bool)
    (left right : Expr) (witness : List Vertex) : Bool :=
  FiniteCover.check interval (leq boxes) admitted left right witness

/-- One successful computation certifies real coverage at every parameter
interpretation inside the boxes. The comparator's soundness is already proved. -/
theorem verifiedCheckCover_sound {Vertex : Type*} (boxes : ℕ → QBounds)
    (interval : Vertex → FiniteCover.Interval Expr) (admitted : Vertex → Bool)
    (left right : Expr) (witness : List Vertex)
    (h : verifiedCheckCover boxes interval admitted left right witness = true) :
    ∀ env : ℕ → ℝ, (∀ k, (boxes k).mem (env k)) →
      ∀ x ∈ Set.Icc (eval env left) (eval env right),
        ∃ v ∈ witness, admitted v = true ∧
          x ∈ Set.Icc (eval env (interval v).lower) (eval env (interval v).upper) := by
  intro env henv
  exact FiniteCover.check_sound interval (leq boxes) admitted (eval env)
    (fun a b hab ↦ leq_sound boxes env henv a b hab) left right witness h

/-- The executable evaluator refuses division by a zero denominator. -/
theorem zero_denominator_rejected :
    enclose (fun _ ↦ QBounds.point 0) (.div (.const 1) (.const 0)) = none := by
  norm_num [enclose, QBounds.checkedDiv, QBounds.point]

/-- It also refuses a denominator box which touches zero. -/
theorem denominator_touching_zero_rejected :
    enclose (fun _ ↦ (⟨0, 1⟩ : QBounds)) (.div (.const 1) (.var 0)) = none := by
  norm_num [enclose, QBounds.checkedDiv, QBounds.point]

private def varyingIntervals : Bool → FiniteCover.Interval Expr
  | false => ⟨.const 0, .add (.var 0) (.const 1)⟩
  | true => ⟨.var 0, .const 2⟩

/-- A single computation validates the moving intervals `[0,p+1]` and
`[p,2]` covering `[0,2]` simultaneously for all `p ∈ [0,1/2]`. -/
theorem parameter_varying_cover_accepted :
    verifiedCheckCover (fun _ ↦ (⟨0, 1/2⟩ : QBounds)) varyingIntervals
      (fun _ ↦ true) (.const 0) (.const 2) [false, true] = true := by
  norm_num [verifiedCheckCover, FiniteCover.check, FiniteCover.checkTail,
    varyingIntervals, leq, enclose, QBounds.point, QBounds.sub, QBounds.add,
    QBounds.neg, QBounds.nonnegativeTest]

end Berstein.IntervalExpression
