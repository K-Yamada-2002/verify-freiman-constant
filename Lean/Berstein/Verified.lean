import Berstein.CertificateCheck
import Berstein.GraphSuccessor
import Berstein.RootState
import Berstein.SpectralVerified

/-! End-to-end soundness of the executable certificate checker.

The only certificate premise is Boolean acceptance. The actual continued
fractions, infinite cylinder realization, and domination of every noncentral
position are proved here or in the imported modules. Running the large checker
is deliberately external to kernel reduction; see the verification report.
-/

namespace Berstein.Certificate
open GraphCertificate GraphMeaning

theorem filling_of_accepted (input : Input) (data : Data) (alive : ByteArray)
    (cells : Nat → List Cell) (h : Accepted input data alive cells) :
    SumFilling (filledLower-4) (filledUpper-4) := by
  apply filling_of_checked_roots_and_successors input data alive h.roots
  intro s x hx
  apply verified_successor h.meaning ?_ cells h.geometries s x hx
  intro i hi
  have hs := (check_dimensions input data h.meaning).1
  exact h.prepared _ (Array.mem_of_getElem?
    (lookup_some_getD input.sides i (by omega)))

theorem target_interval_subset_of_accepted
    (input : Input) (data : Data) (alive : ByteArray)
    (cells : Nat → List Cell) (h : Accepted input data alive cells) :
    Set.Icc targetLower targetUpper ⊆ markovSpectrum ∩ Set.Iio freimanConstant := by
  have hf := filling_of_accepted input data alive cells h
  have hb := SpectralVerified.noncentral_bound
  have hd : (SpectralVerified.bound : ℝ) ≤ 4+(filledLower-4) := by
    have hlt := rational_spectral_bound_lt_filledLower
    norm_num [SpectralVerified.bound] at hlt ⊢
    linarith
  have hm := interval_subset_markovSpectrum_of_filling_and_bound
    (filledLower-4) (filledUpper-4) (SpectralVerified.bound : ℝ) hf hb hd
  intro x hx
  refine ⟨hm ?_, target_interval_below_freimanConstant hx⟩
  have hf := target_interval_subset_filled hx
  constructor <;> linarith [hf.1,hf.2]

/-- The main theorem: executable acceptance suffices, with no assumed filling,
spectral bound, semantic interpretation, or successor-cover hypothesis. -/
theorem target_interval_subset_of_check
    (input : Input) (data : Data) (alive : ByteArray)
    (cells : Nat → List Cell) (h : check input data alive cells = true) :
    Set.Icc targetLower targetUpper ⊆ markovSpectrum ∩ Set.Iio freimanConstant :=
  target_interval_subset_of_accepted input data alive cells
    (check_sound input data alive cells h)

theorem open_interval_subset_interior_of_check
    (input : Input) (data : Data) (alive : ByteArray)
    (cells : Nat → List Cell) (h : check input data alive cells = true) :
    Set.Ioo targetLower targetUpper ⊆
      interior (markovSpectrum \ Set.Ici freimanConstant) := by
  apply interior_maximal _ isOpen_Ioo
  intro x hx
  have hm := target_interval_subset_of_check input data alive cells h ⟨hx.1.le,hx.2.le⟩
  refine ⟨hm.1, ?_⟩
  change ¬ freimanConstant ≤ x
  exact not_le.mpr hm.2

theorem interior_below_freiman_nonempty_of_check
    (input : Input) (data : Data) (alive : ByteArray)
    (cells : Nat → List Cell) (h : check input data alive cells = true) :
    (interior (markovSpectrum \ Set.Ici freimanConstant)).Nonempty := by
  refine ⟨(targetLower+targetUpper)/2,
    open_interval_subset_interior_of_check input data alive cells h ?_⟩
  constructor <;> linarith [targetLower_lt_targetUpper]

end Berstein.Certificate
