import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact rational interval arithmetic

Every operation computes solely with arbitrary-precision rational numbers.
The real semantics and the soundness theorems are independent of IO, compiler
evaluation, or any particular table. A failed positive-denominator check is
represented by `none`, rather than admitting an invalid division enclosure.
-/

namespace Berstein

/-- Rational bounds, with possibly empty real interpretation. -/
structure QBounds where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr, Inhabited

namespace QBounds

/-- A real number is enclosed by the two rational endpoints. -/
def mem (b : QBounds) (x : ℝ) : Prop := (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)

def point (q : ℚ) : QBounds := ⟨q, q⟩

def add (a b : QBounds) : QBounds := ⟨a.lo + b.lo, a.hi + b.hi⟩

def neg (a : QBounds) : QBounds := ⟨-a.hi, -a.lo⟩

def sub (a b : QBounds) : QBounds := add a (neg b)

/-- Multiplication uses all four corners and works for arbitrary signs. -/
def mul (a b : QBounds) : QBounds :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
    max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩

/-- Inversion with flipped endpoints; its soundness requires `0 < b.lo`. -/
def invPos (b : QBounds) : QBounds := ⟨1 / b.hi, 1 / b.lo⟩

/-- Division whose denominator is required to have positive lower endpoint. -/
def divPos (a b : QBounds) : QBounds := mul a (invPos b)

def positiveTest (b : QBounds) : Bool := decide (0 < b.lo)

/-- Certifying a nonnegative lower endpoint certifies every enclosed real. -/
def nonnegativeTest (b : QBounds) : Bool := decide (0 ≤ b.lo)

/-- A total executable division API which refuses uncertified denominators. -/
def checkedDiv (a b : QBounds) : Option QBounds :=
  if 0 < b.lo then some (divPos a b) else none

theorem point_sound (q : ℚ) : (point q).mem (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem add_sound (a b : QBounds) (x y : ℝ) (hx : a.mem x) (hy : b.mem y) :
    (add a b).mem (x + y) := by
  simp only [mem, add, Rat.cast_add]
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem neg_sound (a : QBounds) (x : ℝ) (hx : a.mem x) :
    (neg a).mem (-x) := by
  simp only [mem, neg, Rat.cast_neg]
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem sub_sound (a b : QBounds) (x y : ℝ) (hx : a.mem x) (hy : b.mem y) :
    (sub a b).mem (x - y) := by
  simpa only [sub, sub_eq_add_neg] using add_sound a (neg b) x (-y) hx (neg_sound b y hy)

/-- A linear function takes every interval value between its endpoint values. -/
private theorem mul_mem_of_endpoint_bounds {a b x y lo hi : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (ha : lo ≤ a * y ∧ a * y ≤ hi)
    (hb : lo ≤ b * y ∧ b * y ≤ hi) : lo ≤ x * y ∧ x * y ≤ hi := by
  by_cases hy : 0 ≤ y
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans hb.2⟩
  · have hy' : y ≤ 0 := (lt_of_not_ge hy).le
    exact ⟨hb.1.trans (mul_le_mul_of_nonpos_right hx.2 hy'),
      (mul_le_mul_of_nonpos_right hx.1 hy').trans ha.2⟩

private theorem mul_mem_of_corner_bounds {a b c d x y lo hi : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hac : lo ≤ a * c ∧ a * c ≤ hi) (had : lo ≤ a * d ∧ a * d ≤ hi)
    (hbc : lo ≤ b * c ∧ b * c ≤ hi) (hbd : lo ≤ b * d ∧ b * d ≤ hi) :
    lo ≤ x * y ∧ x * y ≤ hi := by
  have ha : lo ≤ a * y ∧ a * y ≤ hi := by
    simpa only [mul_comm] using mul_mem_of_endpoint_bounds (y := a) (lo := lo) (hi := hi) hy
      (by simpa only [mul_comm] using hac) (by simpa only [mul_comm] using had)
  have hb : lo ≤ b * y ∧ b * y ≤ hi := by
    simpa only [mul_comm] using mul_mem_of_endpoint_bounds (y := b) (lo := lo) (hi := hi) hy
      (by simpa only [mul_comm] using hbc) (by simpa only [mul_comm] using hbd)
  exact mul_mem_of_endpoint_bounds hx ha hb

theorem mul_sound (a b : QBounds) (x y : ℝ) (hx : a.mem x) (hy : b.mem y) :
    (mul a b).mem (x * y) := by
  simp only [mem, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  apply mul_mem_of_corner_bounds hx hy
  all_goals constructor <;> simp

theorem invPos_sound (b : QBounds) (y : ℝ) (hy : b.mem y) (hpos : 0 < b.lo) :
    (invPos b).mem (1 / y) := by
  have hlo : (0 : ℝ) < b.lo := by exact_mod_cast hpos
  have hypos : 0 < y := hlo.trans_le hy.1
  simp only [mem, invPos, Rat.cast_div, Rat.cast_one]
  exact ⟨div_le_div_of_nonneg_left (by norm_num) hypos hy.2,
    div_le_div_of_nonneg_left (by norm_num) hlo hy.1⟩

theorem divPos_sound (a b : QBounds) (x y : ℝ) (hx : a.mem x) (hy : b.mem y)
    (hpos : 0 < b.lo) : (divPos a b).mem (x / y) := by
  simpa only [divPos, div_eq_mul_inv, one_div, one_mul] using
    mul_sound a (invPos b) x (1 / y) hx (invPos_sound b y hy hpos)

theorem positiveTest_sound (b : QBounds) (x : ℝ) (hx : b.mem x)
    (htest : positiveTest b = true) : 0 < x := by
  have hpos : 0 < b.lo := of_decide_eq_true htest
  have hlo : (0 : ℝ) < b.lo := by exact_mod_cast hpos
  exact hlo.trans_le hx.1

theorem nonnegativeTest_sound (b : QBounds) (x : ℝ) (hx : b.mem x)
    (htest : nonnegativeTest b = true) : 0 ≤ x := by
  have hnonneg : 0 ≤ b.lo := of_decide_eq_true htest
  have hlo : (0 : ℝ) ≤ b.lo := by exact_mod_cast hnonneg
  exact hlo.trans hx.1

theorem checkedDiv_sound (a b c : QBounds) (x y : ℝ) (hx : a.mem x) (hy : b.mem y)
    (hchecked : checkedDiv a b = some c) : c.mem (x / y) := by
  unfold checkedDiv at hchecked
  split at hchecked
  · next hpos =>
      have hc : divPos a b = c := Option.some.inj hchecked
      rw [← hc]
      exact divPos_sound a b x y hx hy hpos
  · contradiction

end QBounds
end Berstein
