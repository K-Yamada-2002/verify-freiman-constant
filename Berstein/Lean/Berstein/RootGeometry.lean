import Berstein.Markov
import HallRay.ContinuedFraction.Mobius

/-! Exact finite-prefix geometry. -/

namespace Berstein
open HallRay.ContinuedFraction

theorem prefix322_coefficients : mobiusCoeffs prefix322 = ⟨5, 2, 17, 7⟩ := rfl

theorem prefix431_coefficients : mobiusCoeffs prefix431 = ⟨4, 3, 17, 13⟩ := rfl

theorem prefix322_shape : denominatorRatio prefix322 = (7/17 : ℝ) := rfl

theorem prefix431_shape : denominatorRatio prefix431 = (13/17 : ℝ) := rfl

end Berstein
