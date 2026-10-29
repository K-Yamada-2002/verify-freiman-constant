import Freiman.Endpoint
import Berstein.IntervalExpression

/-! A sound rational-expression checker for S <-> V_zeta. Narrow rational
bounds for the two radicals avoid extending the exact endpoint field. -/
namespace Freiman.Coordinate
open Berstein HallRay.ContinuedFraction IntervalExpression

def sqrtBox : QBounds := ⟨(107470926301023385196220052877408564979819/5000000000000000000000000000000000000000),(214941852602046770392440105754817129959639/10000000000000000000000000000000000000000)⟩
def zetaBox : QBounds := ⟨(378469547164993308199513292169059966407/1250000000000000000000000000000000000000),(6055512754639892931192212674704959462513/20000000000000000000000000000000000000000)⟩

theorem sqrt_mem : sqrtBox.mem (Real.sqrt 462) := by
  have h := GraphMeaning.contains_sound sqrtBox (⟨0,1⟩ : Quadratic462) (by decide +kernel)
  simpa [Quadratic462.eval] using h

theorem zeta_mem : zetaBox.mem Endpoint.zeta := by
  have hl : zetaBox.lo^2+3*zetaBox.lo-1 ≤ 0 := by decide +kernel
  have hh : 0 ≤ zetaBox.hi^2+3*zetaBox.hi-1 := by decide +kernel
  have hl0 : (0 : ℝ) ≤ zetaBox.lo := by norm_num [zetaBox]
  have hh0 : (0 : ℝ) ≤ zetaBox.hi := by norm_num [zetaBox]
  have hl' : (zetaBox.lo : ℝ)^2+3*(zetaBox.lo : ℝ)-1 ≤ 0 := by exact_mod_cast hl
  have hh' : 0 ≤ (zetaBox.hi : ℝ)^2+3*(zetaBox.hi : ℝ)-1 := by exact_mod_cast hh
  have he := Endpoint.zeta_equation
  have hn := Endpoint.zeta_nonneg
  constructor <;> nlinarith

def quadExpr (x : Quadratic462) : Expr := .add (.const x.a) (.mul (.const x.b) (.var 4))

def expression (x y : Quadratic462) (toZeta : Bool) : Expr :=
  let r := Expr.var 0
  let s := Expr.var 1
  let z := Expr.var 3
  let one (a b : Expr) : Expr := .add (.const 1) (.mul a b)
  let forward := Expr.mul (.div (one r z) (one r (quadExpr x)))
    (.div (one s (quadExpr y)) (one s z))
  let backward := Expr.mul (.div (one r (quadExpr x)) (one r z))
    (.div (one s z) (one s (quadExpr y)))
  let factor := if toZeta then forward else backward
  .mul (.var 2) (.mul factor factor)

def boxes (r s v : QBounds) : Nat → QBounds
  | 0 => r
  | 1 => s
  | 2 => v
  | 3 => zetaBox
  | _ => sqrtBox

noncomputable def environment (r s v : ℝ) : Nat → ℝ
  | 0 => r
  | 1 => s
  | 2 => v
  | 3 => Endpoint.zeta
  | _ => Real.sqrt 462

def check (x y : Quadratic462) (toZeta : Bool) (r s v out : QBounds) : Bool :=
  match IntervalExpression.enclose (boxes r s v) (expression x y toZeta) with
  | none => false
  | some result => decide (out.lo ≤ result.lo ∧ result.hi ≤ out.hi)

noncomputable def conversion (x y r s v : ℝ) (toZeta : Bool) : ℝ :=
  let z := Endpoint.zeta
  let forward := ((1+r*z)/(1+r*x))*((1+s*y)/(1+s*z))
  let backward := ((1+r*x)/(1+r*z))*((1+s*z)/(1+s*y))
  let factor := if toZeta then forward else backward
  v*factor*factor

 theorem check_sound (x y : Quadratic462) (toZeta : Bool) (r s v out : QBounds)
    (hr : ℝ) (hs : ℝ) (hv : ℝ) (hrr : r.mem hr) (hss : s.mem hs) (hvv : v.mem hv)
    (hc : check x y toZeta r s v out = true) :
    out.mem (conversion x.eval y.eval hr hs hv toZeta) := by
  have henv : ∀ k, (boxes r s v k).mem (environment hr hs hv k) := by
    intro k
    rcases k with _ | _ | _ | _ | k <;> first | exact hrr | exact hss | exact hvv | exact zeta_mem | exact sqrt_mem
  unfold check at hc
  cases he : IntervalExpression.enclose (boxes r s v) (expression x y toZeta) with
  | none => simp [he] at hc
  | some result =>
    rw [he] at hc
    have hh := of_decide_eq_true hc
    have h := IntervalExpression.enclose_sound (boxes r s v) (environment hr hs hv) henv
      (expression x y toZeta) result he
    have hvalue : IntervalExpression.eval (environment hr hs hv) (expression x y toZeta) =
        conversion x.eval y.eval hr hs hv toZeta := by
      cases toZeta <;> simp [expression,quadExpr,IntervalExpression.eval,environment,conversion,Quadratic462.eval] <;> ring
    rw [hvalue] at h
    exact ⟨(Rat.cast_mono hh.1).trans h.1,h.2.trans (Rat.cast_mono hh.2)⟩

/-- Change of normalization is an identity of actual continued fractions. -/
theorem ratio_change (a b : Word) {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Normalization.scale b z / Normalization.scale a z =
      (Normalization.scale b y / Normalization.scale a x)*
        (((1+denominatorRatio a*z)/(1+denominatorRatio a*x))*
          ((1+denominatorRatio b*y)/(1+denominatorRatio b*z)))^2 := by
  have ha : (0 : ℝ) < (mobiusCoeffs a).C := by exact_mod_cast mobius_C_pos a
  have hb : (0 : ℝ) < (mobiusCoeffs b).C := by exact_mod_cast mobius_C_pos b
  have hax : (0 : ℝ) < (mobiusCoeffs a).C+(mobiusCoeffs a).D*x := by positivity
  have haz : (0 : ℝ) < (mobiusCoeffs a).C+(mobiusCoeffs a).D*z := by positivity
  have hby : (0 : ℝ) < (mobiusCoeffs b).C+(mobiusCoeffs b).D*y := by positivity
  have hbz : (0 : ℝ) < (mobiusCoeffs b).C+(mobiusCoeffs b).D*z := by positivity
  unfold Normalization.scale denominatorRatio
  field_simp [ne_of_gt ha,ne_of_gt hb,ne_of_gt hax,ne_of_gt haz,ne_of_gt hby,ne_of_gt hbz]
  <;> ring

 theorem ratio_change_back (a b : Word) {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Normalization.scale b y / Normalization.scale a x =
      (Normalization.scale b z / Normalization.scale a z)*
        (((1+denominatorRatio a*x)/(1+denominatorRatio a*z))*
          ((1+denominatorRatio b*z)/(1+denominatorRatio b*y)))^2 := by
  have ha : (0 : ℝ) < (mobiusCoeffs a).C := by exact_mod_cast mobius_C_pos a
  have hb : (0 : ℝ) < (mobiusCoeffs b).C := by exact_mod_cast mobius_C_pos b
  have hax : (0 : ℝ) < (mobiusCoeffs a).C+(mobiusCoeffs a).D*x := by positivity
  have haz : (0 : ℝ) < (mobiusCoeffs a).C+(mobiusCoeffs a).D*z := by positivity
  have hby : (0 : ℝ) < (mobiusCoeffs b).C+(mobiusCoeffs b).D*y := by positivity
  have hbz : (0 : ℝ) < (mobiusCoeffs b).C+(mobiusCoeffs b).D*z := by positivity
  unfold Normalization.scale denominatorRatio
  field_simp [ne_of_gt ha,ne_of_gt hb,ne_of_gt hax,ne_of_gt haz,ne_of_gt hby,ne_of_gt hbz]
  <;> ring

end Freiman.Coordinate

namespace Freiman.Coordinate
open Berstein HallRay.ContinuedFraction

theorem to_zeta (a b : Word) (x y : Quadratic462) (hx : 0 ≤ x.eval) (hy : 0 ≤ y.eval)
    (r s v out : QBounds) (hr : r.mem (denominatorRatio a)) (hs : s.mem (denominatorRatio b))
    (hv : v.mem (Normalization.scale b y.eval/Normalization.scale a x.eval))
    (hc : check x y true r s v out = true) :
    out.mem (Normalization.scale b Endpoint.zeta/Normalization.scale a Endpoint.zeta) := by
  have h := check_sound x y true r s v out _ _ _ hr hs hv hc
  have he : conversion x.eval y.eval (denominatorRatio a) (denominatorRatio b)
      (Normalization.scale b y.eval/Normalization.scale a x.eval) true =
      Normalization.scale b Endpoint.zeta/Normalization.scale a Endpoint.zeta := by
    rw [ratio_change a b hx hy Endpoint.zeta_nonneg]
    simp only [conversion,Bool.false_eq_true,↓reduceIte]
    ring
  rwa [he] at h

theorem from_zeta (a b : Word) (x y : Quadratic462) (hx : 0 ≤ x.eval) (hy : 0 ≤ y.eval)
    (r s v out : QBounds) (hr : r.mem (denominatorRatio a)) (hs : s.mem (denominatorRatio b))
    (hv : v.mem (Normalization.scale b Endpoint.zeta/Normalization.scale a Endpoint.zeta))
    (hc : check x y false r s v out = true) :
    out.mem (Normalization.scale b y.eval/Normalization.scale a x.eval) := by
  have h := check_sound x y false r s v out _ _ _ hr hs hv hc
  have he : conversion x.eval y.eval (denominatorRatio a) (denominatorRatio b)
      (Normalization.scale b Endpoint.zeta/Normalization.scale a Endpoint.zeta) false =
      Normalization.scale b y.eval/Normalization.scale a x.eval := by
    rw [ratio_change_back a b hx hy Endpoint.zeta_nonneg]
    simp only [conversion,Bool.false_eq_true,↓reduceIte]
    ring
  rwa [he] at h

end Freiman.Coordinate
