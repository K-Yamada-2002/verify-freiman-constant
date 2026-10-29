import Freiman.Initial
import Freiman.FiniteRay

/-! End-to-end checker soundness for [c_F,infinity) in the actual Markov
spectrum. All remaining premises are finite executable acceptance predicates. -/
namespace Freiman
open Berstein

structure RayData where
  localConditions : Array Local.Condition
  spectralCertificates : Array Spectral.Certificate
  finiteRows : List FiniteRay.Row
  upperRows : List Root.Row

/-- Full finite acceptance, including the already-proved general table. -/
def rayCheck (input : GraphCertificate.Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell) (ray : RayData) : Bool :=
  Berstein.Certificate.check input data alive cells &&
    Local.allCheck input data alive ray.localConditions && Initial.check ray.localConditions &&
    FiniteRay.check input data alive ray.spectralCertificates Initial.upper (Quadratic462.ofRat (13/2)) ray.finiteRows &&
    Root.coverCheck input data alive (Quadratic462.ofRat (1/2)) (Quadratic462.ofRat (3/2)) ray.upperRows

/-- The Freiman half-line is in M whenever the complete finite checker accepts.
There are no assumed filling, spectral domination or interval-inclusion premises. -/
theorem ray_subset_markov_of_check (input : GraphCertificate.Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell) (ray : RayData)
    (hc : rayCheck input data alive cells ray = true) :
    Set.Ici freimanConstant ⊆ markovSpectrum := by
  simp only [rayCheck,Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨⟨ht,hl⟩,hi⟩,hf⟩,hu⟩
  have htable := Berstein.Certificate.check_sound input data alive cells ht
  have hlocal := Local.allCheck_sound input data alive ray.localConditions hl
  have hfirst := Initial.interval_subset input data alive cells htable ray.localConditions hlocal hi
  have hfinite := FiniteRay.check_sound input data alive cells htable ray.spectralCertificates
    Initial.upper (Quadratic462.ofRat (13/2)) ray.finiteRows hf
  have hupper := Root.upper_ray_of_check input data alive cells htable ray.upperRows hu
  intro t ht'
  by_cases hlow : t ≤ Initial.upper.eval
  · exact hfirst ⟨ht',hlow⟩
  · by_cases hmid : t ≤ 13/2
    · apply hfinite
      constructor
      · exact le_of_lt (lt_of_not_ge hlow)
      · simpa only [Quadratic462.eval_ofRat,Rat.cast_div,Rat.cast_ofNat] using hmid
    · exact hupper (le_of_lt (lt_of_not_ge hmid))

end Freiman
