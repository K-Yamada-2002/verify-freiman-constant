import Berstein.SemanticCheck

namespace Berstein.GraphMeaning

def rootScale : Quadratic462 := ⟨55792801/159491641, 2467176/159491641⟩

def rootRatioBox (input : GraphCertificate.Input) : QBounds :=
  ⟨(51/50 : ℚ)^(input.firstExponent+135),
    (51/50 : ℚ)^(input.firstExponent+136)⟩

/-- Check the actual below-ray root, independently of the older root field
in the reusable graph file. Geometry193 = left8 ×22 + right17, bin135=-20. -/
def checkRoots (input : GraphCertificate.Input) (data : Data) (alive : ByteArray) : Bool :=
  let left := input.sides[8]?.getD default
  let right := input.sides[17]?.getD default
  let ml := data.sides[8]?.getD default
  let mr := data.sides[17]?.getD default
  decide (input.states = 22 ∧ input.bins = 310 ∧ input.types = 32 ∧ input.firstExponent = -155) &&
  decide (17 < input.sides.size ∧ 17 < data.sides.size ∧ 136 < input.grid.size) &&
  (left.parity && right.parity) && decide (ml.state = 0 ∧ mr.state = 2) &&
  decide (ml.shape.lo ≤ 7/17 ∧ 7/17 ≤ ml.shape.hi) &&
  decide (mr.shape.lo ≤ 13/17 ∧ 13/17 ≤ mr.shape.hi) &&
  contains (rootRatioBox input) rootScale &&
  (List.range 25).all (fun j =>
    let t := j+3
    decide (input.bands[t]? = some ⟨((t : ℚ)-1)/32, ((t : ℚ)+1)/32⟩) &&
      GraphCertificate.adopted input alive 193 135 t)

end Berstein.GraphMeaning
