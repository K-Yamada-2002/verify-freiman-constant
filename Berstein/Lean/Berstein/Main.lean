import Berstein.Verified

/-! Public result. The sole premise is acceptance by the executable finite
certificate checker; all analytical implications are proved in `Verified`.
The concrete original table is replayed by `graphReplay` and `scripts/verify.py`.
-/

namespace Berstein
open GraphCertificate

/-- The exact rational interval is contained in the Markov spectrum strictly
below the specified Freiman constant whenever the finite checker accepts. -/
theorem target_interval_subset
    (input : Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (cells : Nat → List Cell) (h : Certificate.check input data alive cells = true) :
    Set.Icc targetLower targetUpper ⊆ markovSpectrum ∩ Set.Iio freimanConstant :=
  Certificate.target_interval_subset_of_check input data alive cells h

/-- Interior in the real line, outside the ray `[freimanConstant,∞)`. -/
theorem open_interval_subset_interior
    (input : Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (cells : Nat → List Cell) (h : Certificate.check input data alive cells = true) :
    Set.Ioo targetLower targetUpper ⊆
      interior (markovSpectrum \ Set.Ici freimanConstant) :=
  Certificate.open_interval_subset_interior_of_check input data alive cells h

theorem interior_below_freiman_nonempty
    (input : Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (cells : Nat → List Cell) (h : Certificate.check input data alive cells = true) :
    (interior (markovSpectrum \ Set.Ici freimanConstant)).Nonempty :=
  Certificate.interior_below_freiman_nonempty_of_check input data alive cells h

theorem target_width : targetUpper - targetLower = (11/6250 : ℝ) := by
  norm_num [targetUpper, targetLower]

theorem target_midpoint : (targetLower + targetUpper) / 2 = (226333/50000 : ℝ) := by
  norm_num [targetUpper, targetLower]

end Berstein
