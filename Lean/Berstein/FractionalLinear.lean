import Berstein.IntervalArithmetic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Endpoint checking for the shape and derivative transport functions. -/

namespace Berstein.FractionalLinear

theorem affine_nonneg {a b lo hi x : ℝ} (hx : x ∈ Set.Icc lo hi)
    (hlo : 0 ≤ a+b*lo) (hhi : 0 ≤ a+b*hi) : 0 ≤ a+b*x := by
  by_cases hb : 0 ≤ b
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hx.1)]
  · have hb' : b ≤ 0 := le_of_not_ge hb
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hb' (sub_nonneg.mpr hx.2)]

/-- No assumption on the sign of the determinant is needed: positive
denominators make each proposed bound an affine inequality. -/
theorem enclosure {a b c d lo hi x L H : ℝ} (hx : x ∈ Set.Icc lo hi)
    (hdlo : 0 < c+d*lo) (hdhi : 0 < c+d*hi) (hdx : 0 < c+d*x)
    (hlo : (a+b*lo)/(c+d*lo) ∈ Set.Icc L H)
    (hhi : (a+b*hi)/(c+d*hi) ∈ Set.Icc L H) :
    (a+b*x)/(c+d*x) ∈ Set.Icc L H := by
  have hl₀ := (le_div_iff₀ hdlo).mp hlo.1
  have hl₁ := (le_div_iff₀ hdhi).mp hhi.1
  have hu₀ := (div_le_iff₀ hdlo).mp hlo.2
  have hu₁ := (div_le_iff₀ hdhi).mp hhi.2
  constructor
  · apply (le_div_iff₀ hdx).mpr
    have h := affine_nonneg (a := a-L*c) (b := b-L*d) hx (by nlinarith) (by nlinarith)
    nlinarith
  · apply (div_le_iff₀ hdx).mpr
    have h := affine_nonneg (a := H*c-a) (b := H*d-b) hx (by nlinarith) (by nlinarith)
    nlinarith

theorem square_enclosure {x lo hi : ℝ} (hlo : 0 ≤ lo) (hx : x ∈ Set.Icc lo hi) :
    x^2 ∈ Set.Icc (lo^2) (hi^2) := by
  constructor <;> nlinarith [hx.1, hx.2]

theorem square_fractional_enclosure {a b c d lo hi x L H : ℝ}
    (hx : x ∈ Set.Icc lo hi)
    (hdlo : 0 < c+d*lo) (hdhi : 0 < c+d*hi) (hdx : 0 < c+d*x)
    (hnlo : 0 ≤ a+b*lo) (hnhi : 0 ≤ a+b*hi)
    (hlo : ((a+b*lo)/(c+d*lo))^2 ∈ Set.Icc L H)
    (hhi : ((a+b*hi)/(c+d*hi))^2 ∈ Set.Icc L H) :
    ((a+b*x)/(c+d*x))^2 ∈ Set.Icc L H := by
  rcases le_total ((a+b*lo)/(c+d*lo)) ((a+b*hi)/(c+d*hi)) with h | h
  · have he := enclosure hx hdlo hdhi hdx ⟨le_rfl,h⟩ ⟨h,le_rfl⟩
    have hsq := square_enclosure (div_nonneg hnlo hdlo.le) he
    exact ⟨hlo.1.trans hsq.1, hsq.2.trans hhi.2⟩
  · have he := enclosure hx hdlo hdhi hdx ⟨h,le_rfl⟩ ⟨le_rfl,h⟩
    have hsq := square_enclosure (div_nonneg hnhi hdhi.le) he
    exact ⟨hhi.1.trans hsq.1, hsq.2.trans hlo.2⟩

theorem constant_of_cross_eq {a b c d x : ℝ} (hc : c ≠ 0)
    (hx : c+d*x ≠ 0) (hcross : b*c = a*d) :
    (a+b*x)/(c+d*x) = a/c := by
  apply (div_eq_div_iff hx hc).mpr
  calc
    (a+b*x)*c = a*c+(b*c)*x := by ring
    _ = a*(c+d*x) := by rw [hcross]; ring

end Berstein.FractionalLinear
