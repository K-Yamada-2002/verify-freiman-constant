import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact arithmetic in `ℚ(√462)`

Elements are stored as rational pairs `a + b * √462`.  The executable order
checker compares rational squares only; its correctness is proved below.
-/

namespace Berstein

/-- A rational coefficient pair representing `a + b * √462`. -/
structure Quadratic462 where
  a : ℚ
  b : ℚ
  deriving DecidableEq, Repr, Inhabited

namespace Quadratic462

def zero : Quadratic462 := ⟨0, 0⟩

def one : Quadratic462 := ⟨1, 0⟩

def ofRat (q : ℚ) : Quadratic462 := ⟨q, 0⟩

/-- Real interpretation of a coefficient pair. -/
noncomputable def eval (x : Quadratic462) : ℝ :=
  (x.a : ℝ) + (x.b : ℝ) * Real.sqrt 462

def add (x y : Quadratic462) : Quadratic462 := ⟨x.a + y.a, x.b + y.b⟩

def neg (x : Quadratic462) : Quadratic462 := ⟨-x.a, -x.b⟩

def sub (x y : Quadratic462) : Quadratic462 := add x (neg y)

def mul (x y : Quadratic462) : Quadratic462 :=
  ⟨x.a * y.a + 462 * x.b * y.b, x.a * y.b + x.b * y.a⟩

/-- The field norm `a² - 462 b²`. -/
def norm (x : Quadratic462) : ℚ := x.a ^ 2 - 462 * x.b ^ 2

def conj (x : Quadratic462) : Quadratic462 := ⟨x.a, -x.b⟩

/-- Inversion is only defined with an explicit nonzero norm proof. -/
def inv (x : Quadratic462) (hn : x.norm ≠ 0) : Quadratic462 :=
  ⟨x.a / x.norm, -x.b / x.norm⟩

/-- Checked executable inversion. -/
def checkedInv (x : Quadratic462) : Option Quadratic462 :=
  if hn : x.norm ≠ 0 then some (inv x hn) else none

def div (x y : Quadratic462) (hy : y.norm ≠ 0) : Quadratic462 :=
  mul x (inv y hy)

theorem eval_zero : eval zero = 0 := by simp [eval, zero]

theorem eval_one : eval one = 1 := by simp [eval, one]

theorem eval_ofRat (q : ℚ) : eval (ofRat q) = q := by
  simp [eval, ofRat]

theorem eval_add (x y : Quadratic462) : eval (add x y) = eval x + eval y := by
  simp only [eval, add, Rat.cast_add]
  ring

theorem eval_neg (x : Quadratic462) : eval (neg x) = -eval x := by
  simp only [eval, neg, Rat.cast_neg]
  ring

theorem eval_sub (x y : Quadratic462) : eval (sub x y) = eval x - eval y := by
  simp only [sub, eval_add, eval_neg]
  ring

theorem eval_mul (x y : Quadratic462) : eval (mul x y) = eval x * eval y := by
  simp only [eval, mul, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  have hsqrt : (Real.sqrt (462 : ℝ)) ^ 2 = 462 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 462)]
  ring_nf
  rw [hsqrt]

theorem eval_conj_mul (x : Quadratic462) :
    eval x * eval (conj x) = (x.norm : ℝ) := by
  have hsqrt : (Real.sqrt (462 : ℝ)) ^ 2 = 462 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 462)]
  simp only [eval, conj, Rat.cast_neg]
  ring_nf
  rw [hsqrt]
  unfold norm
  push_cast
  ring

theorem eval_inv (x : Quadratic462) (hn : x.norm ≠ 0) :
    eval (inv x hn) = (eval x)⁻¹ := by
  have hnormR : (x.norm : ℝ) ≠ 0 := by exact_mod_cast hn
  have hprod : eval x * eval (conj x) = (x.norm : ℝ) := eval_conj_mul x
  have hx : eval x ≠ 0 := by
    intro hx
    rw [hx] at hprod
    simp at hprod
    exact hnormR hprod.symm
  have hinv : eval (inv x hn) = eval (conj x) / (x.norm : ℝ) := by
    unfold inv eval conj
    simp only [Rat.cast_div, Rat.cast_neg]
    field_simp [hnormR]
  rw [hinv]
  field_simp [hx, hnormR]
  nlinarith [hprod]

theorem eval_div (x y : Quadratic462) (hy : y.norm ≠ 0) :
    eval (div x y hy) = eval x / eval y := by
  simp only [div, eval_mul, eval_inv]
  exact div_eq_mul_inv _ _

theorem checkedInv_sound (x y : Quadratic462) (h : checkedInv x = some y) :
    eval y = (eval x)⁻¹ := by
  unfold checkedInv at h
  split at h
  · next hn =>
      have hy : inv x hn = y := Option.some.inj h
      subst y
      exact eval_inv x hn
  · contradiction

/-- One partial quotient applied to an optional quadratic tail. -/
def cfStep (a : ℕ) :
    Option Quadratic462 → Option Quadratic462
  | none => none
  | some tail => checkedInv (add (ofRat a) tail)

/-- Exact finite continued fraction map. Failed norm checks propagate as `none`. -/
def cf (digits : List ℕ) (tail : Quadratic462) :
    Option Quadratic462 := digits.foldr cfStep (some tail)

/-- Decidable nonnegativity, using rational square comparison in opposite-sign cases. -/
def nonneg (x : Quadratic462) : Bool :=
  if hb : 0 ≤ x.b then
    if ha : 0 ≤ x.a then true else decide (x.a ^ 2 ≤ 462 * x.b ^ 2)
  else
    if ha : 0 ≤ x.a then decide (462 * x.b ^ 2 ≤ x.a ^ 2) else false

/-- Decidable order comparison, implemented as a sign test on the difference. -/
def le (x y : Quadratic462) : Bool := nonneg (sub y x)

private theorem square_le_iff_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ≤ y ↔ x ^ 2 ≤ y ^ 2 := by
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hxy
    have hxy' : y < x := lt_of_not_ge hxy
    nlinarith [sq_nonneg (x - y)]

private theorem sqrt462_mul_le_iff {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (p : ℝ) ≤ (q : ℝ) * Real.sqrt 462 ↔ p ^ 2 ≤ 462 * q ^ 2 := by
  have hsqrt : 0 ≤ Real.sqrt (462 : ℝ) := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt (462 : ℝ)) ^ 2 = 462 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 462)]
  rw [square_le_iff_of_nonneg (by exact_mod_cast hp)
    (mul_nonneg (by exact_mod_cast hq) hsqrt)]
  push_cast
  rw [mul_pow, hsquare]
  constructor <;> intro h
  · norm_cast at h ⊢
    nlinarith [h]
  · norm_cast at h ⊢
    nlinarith [h]

private theorem sqrt462_mul_le_iff' {p q : ℚ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (q : ℝ) * Real.sqrt 462 ≤ (p : ℝ) ↔ 462 * q ^ 2 ≤ p ^ 2 := by
  have hsqrt : 0 ≤ Real.sqrt (462 : ℝ) := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt (462 : ℝ)) ^ 2 = 462 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 462)]
  rw [square_le_iff_of_nonneg (mul_nonneg (by exact_mod_cast hq) hsqrt)
    (by exact_mod_cast hp)]
  push_cast
  rw [mul_pow, hsquare]
  constructor <;> intro h
  · norm_cast at h ⊢
    nlinarith [h]
  · norm_cast at h ⊢
    nlinarith [h]

theorem nonneg_sound (x : Quadratic462) (h : nonneg x = true) : 0 ≤ eval x := by
  unfold nonneg at h
  split at h
  · rename_i hb
    split at h
    · have ha : 0 ≤ x.a := ‹0 ≤ x.a›
      have hb' : 0 ≤ x.b := hb
      unfold eval
      positivity
    · rename_i ha
      have hsq : x.a ^ 2 ≤ 462 * x.b ^ 2 := of_decide_eq_true h
      have haNeg : x.a < 0 := lt_of_not_ge ha
      have hapos : 0 ≤ -(x.a : ℝ) := by exact_mod_cast (show 0 ≤ -x.a by linarith)
      have hsqQneg : (-x.a) ^ 2 ≤ 462 * x.b ^ 2 := by nlinarith [hsq]
      have hleft : ((-x.a : ℚ) : ℝ) ≤ (x.b : ℝ) * Real.sqrt 462 :=
        (sqrt462_mul_le_iff (by exact_mod_cast hapos) (by exact_mod_cast hb)).2 (by
          exact hsqQneg)
      simp only [Rat.cast_neg] at hleft
      unfold eval
      have ha' : (x.a : ℝ) < 0 := by exact_mod_cast haNeg
      linarith [hleft]
  · rename_i hb
    split at h
    · rename_i ha
      have hsq : 462 * x.b ^ 2 ≤ x.a ^ 2 := of_decide_eq_true h
      have hbNeg : x.b < 0 := lt_of_not_ge hb
      have hbpos : 0 ≤ -x.b := by linarith
      have hright : ((-x.b : ℚ) : ℝ) * Real.sqrt 462 ≤ (x.a : ℝ) :=
        (sqrt462_mul_le_iff' (by exact_mod_cast ha) (by exact_mod_cast hbpos)).2 (by
          have hr : 462 * (x.b : ℝ) ^ 2 ≤ (x.a : ℝ) ^ 2 := by exact_mod_cast hsq
          nlinarith [hr])
      simp only [Rat.cast_neg] at hright
      unfold eval
      nlinarith [hright]
    · cases h

theorem le_sound (x y : Quadratic462) (h : le x y = true) :
    eval x ≤ eval y := by
  have hn := nonneg_sound (sub y x) h
  rw [eval_sub] at hn
  linarith

end Quadratic462
end Berstein
