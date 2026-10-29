import Berstein.SemanticTransport
import Berstein.SemanticSound
import Berstein.Constants

/-! Exact endpoint and scale invariants of the Freiman endpoint construction.
All finite identities below are reduced inside the Lean kernel. -/
namespace Freiman.Endpoint
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction

 def A : Word := asWord [3,2,1,1,3]
 def B : Word := asWord [4,3,2,2]
 def U : Word := asWord [1,3,1,2,1,3]
 def V : Word := asWord [3,1,3,1,2,1]
 def x : Quadratic462 := ⟨-28/19,2/19⟩
 def y : Quadratic462 := ⟨-29/53,2/53⟩
 def gamma : Quadratic462 := ⟨3697,-172⟩
 def leftValue : Quadratic462 := ⟨1006/3557,2/3557⟩
 def rightValue : Quadratic462 := ⟨32174/138317,2/138317⟩

 theorem left_checked : Quadratic462.cf (A.map Subtype.val) x = some leftValue := by
   decide +kernel
 theorem right_checked : Quadratic462.cf (B.map Subtype.val) y = some rightValue := by
   decide +kernel

 /-- The central endpoint is exactly c_F, not a decimal approximation. -/
 theorem central_endpoint : 4+tailMap A x.eval+tailMap B y.eval = freimanConstant := by
   rw [← Quadratic462.cf_sound A x leftValue left_checked,
       ← Quadratic462.cf_sound B y rightValue right_checked]
   norm_num [leftValue,rightValue,Quadratic462.eval,freimanConstant]
   ring

 theorem period_left_fixed : tailMap U x.eval = x.eval :=
   (Quadratic462.cf_sound U x x (by decide +kernel)).symm
 theorem period_right_fixed : tailMap V y.eval = y.eval :=
   (Quadratic462.cf_sound V y y (by decide +kernel)).symm

 theorem x_nonneg : 0 ≤ x.eval := by
   have h := (anchor_unit (1 : Forbidden31313.State) true).1
   simpa [anchor,upper,x,Quadratic462.eval] using h
 theorem y_nonneg : 0 ≤ y.eval := by
   have h := (anchor_unit (0 : Forbidden31313.State) false).1
   simpa [anchor,lower,y,Quadratic462.eval] using h

 /-- The same multiplier works for every actual left prefix. -/
 theorem left_scale_return (a : Word) :
     Normalization.scale (a++U) x.eval / Normalization.scale a x.eval = gamma.eval := by
   apply derivative_constant a U x x gamma 0 x_nonneg x_nonneg (by norm_num)
   · decide +kernel
   · decide +kernel

 theorem right_scale_return (b : Word) :
     Normalization.scale (b++V) y.eval / Normalization.scale b y.eval = gamma.eval := by
   apply derivative_constant b V y y gamma 0 y_nonneg y_nonneg (by norm_num)
   · decide +kernel
   · decide +kernel

 theorem gamma_pos : 0 < gamma.eval := by
   have h := div_pos (Normalization.scale_pos (A++U) x_nonneg)
     (Normalization.scale_pos A x_nonneg)
   rw [left_scale_return] at h
   exact h

 /-- The lower endpoints are preserved after an arbitrary number of returns. -/
 theorem endpoint_return (a b : Word) :
     tailMap (a++U) x.eval+tailMap (b++V) y.eval =
       tailMap a x.eval+tailMap b y.eval := by
   rw [tailMap_append,tailMap_append,period_left_fixed,period_right_fixed]

 /-- The common multiplier cancels exactly, without interval widening. -/
 theorem ratio_return (a b : Word) :
     Normalization.scale (b++V) y.eval / Normalization.scale (a++U) x.eval =
       Normalization.scale b y.eval / Normalization.scale a x.eval := by
   have hl := (div_eq_iff (ne_of_gt (Normalization.scale_pos a x_nonneg))).mp
     (left_scale_return a)
   have hr := (div_eq_iff (ne_of_gt (Normalization.scale_pos b y_nonneg))).mp
     (right_scale_return b)
   rw [hl,hr]
   exact mul_div_mul_left _ _ (ne_of_gt gamma_pos)

 /-- Fixed point of the 33 return, used for the V_zeta coordinate. -/
 noncomputable def zeta : ℝ := (Real.sqrt 13-3)/2
 def loop33 : Word := asWord [3,3]

 theorem zeta_nonneg : 0 ≤ zeta := by
   have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
   have hn := Real.sqrt_nonneg (13 : ℝ)
   dsimp [zeta]
   nlinarith

 theorem zeta_equation : zeta^2+3*zeta-1 = 0 := by
   have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
   dsimp [zeta]
   nlinarith

 theorem loop33_fixed : tailMap loop33 zeta = zeta := by
   change 1/((3 : ℝ)+1/(3+zeta)) = zeta
   have hz := zeta_nonneg
   have h1 : 3+zeta ≠ 0 := by linarith
   have h2 : 3+1/(3+zeta) ≠ 0 := by positivity
   field_simp
   nlinarith [zeta_equation]

end Freiman.Endpoint

namespace Freiman.Endpoint
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction

/-- A fixed point makes the scale factor independent of the preceding word.
This real identity also applies to sqrt(13), outside Q(sqrt(462)). -/
theorem scale_append_fixed (a v : Word) {z : ℝ} (hz : 0 ≤ z)
    (hfixed : tailMap v z = z) :
    Normalization.scale (a++v) z = Normalization.scale a z * Normalization.scale v z := by
  have hv : (0 : ℝ) < (mobiusCoeffs v).C+(mobiusCoeffs v).D*z := by
    have hc : (0 : ℝ) < (mobiusCoeffs v).C := by exact_mod_cast mobius_C_pos v
    positivity
  have hf := tailMap_eq_mobius v z hz
  rw [hfixed] at hf
  have he : (mobiusCoeffs v).A+(mobiusCoeffs v).B*z =
      z*((mobiusCoeffs v).C+(mobiusCoeffs v).D*z) := by
    exact (div_eq_iff (ne_of_gt hv)).mp hf.symm
  have hd : (mobiusCoeffs (a++v)).C+(mobiusCoeffs (a++v)).D*z =
      ((mobiusCoeffs a).C+(mobiusCoeffs a).D*z)*
        ((mobiusCoeffs v).C+(mobiusCoeffs v).D*z) := by
    rw [mobiusCoeffs_append]
    push_cast
    have he' := congrArg (fun t : ℝ => ((mobiusCoeffs a).D : ℝ)*t) he
    nlinarith only [he']
  simp only [Normalization.scale,hd,mul_pow,one_div_mul_one_div]

/-- The 33 loop preserves the zeta derivative ratio for every pair of words. -/
theorem zeta_ratio_return (a b : Word) :
    Normalization.scale (b++loop33) zeta / Normalization.scale (a++loop33) zeta =
      Normalization.scale b zeta / Normalization.scale a zeta := by
  rw [scale_append_fixed b loop33 zeta_nonneg loop33_fixed,
    scale_append_fixed a loop33 zeta_nonneg loop33_fixed]
  exact mul_div_mul_right _ _ (ne_of_gt (Normalization.scale_pos loop33 zeta_nonneg))

end Freiman.Endpoint
