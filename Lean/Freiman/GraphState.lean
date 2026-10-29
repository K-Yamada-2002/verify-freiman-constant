import Freiman.CylinderCover

namespace Freiman.GraphMeaning
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction Forbidden31313
variable [Setup]

structure RealState (input : GraphCertificate.Input) (data : Data) (alive : ByteArray) where
  left : RealSide input data Setup.left
  right : RealSide input data Setup.right
  bin : Nat
  bin_lt : bin < input.bins
  type : Nat
  type_lt : type < input.types
  adopted : GraphCertificate.adopted input alive (left.index*input.states+right.index) bin type = true
  ratio : right.scale/left.scale ∈ Set.Icc (exactCut input bin) (exactCut input (bin+1))
  balance : right.scale/left.scale ∈ Set.Icc (1/10000 : ℝ) 10000
  bandUnit : 0 ≤ (input.bands[type]?.getD default).lo ∧
    (input.bands[type]?.getD default).lo ≤ (input.bands[type]?.getD default).hi ∧
    (input.bands[type]?.getD default).hi ≤ 1

namespace RealState
variable {input : GraphCertificate.Input} {data : Data} {alive : ByteArray}
abbrev band (s : RealState input data alive) : QBounds := input.bands[s.type]?.getD default
abbrev geometry (s : RealState input data alive) : Nat := s.left.index*input.states+s.right.index
theorem geometry_left (s : RealState input data alive) : s.geometry / input.states = s.left.index := by
  have hp : 0 < input.states := Nat.zero_lt_of_lt s.right.index_lt
  change (s.left.index*input.states+s.right.index)/input.states = s.left.index
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt s.right.index_lt]
  simp

theorem geometry_right (s : RealState input data alive) : s.geometry % input.states = s.right.index :=
  Nat.mul_add_mod_of_lt s.right.index_lt

noncomputable def endpoint (s : RealState input data alive) (p : ℝ) : ℝ :=
  Setup.center+s.left.endpoint p+s.right.endpoint p
noncomputable def target (s : RealState input data alive) : Set ℝ :=
  Set.Icc (s.endpoint s.band.lo) (s.endpoint s.band.hi)
noncomputable def pair (s : RealState input data alive) : CylinderCover.LegalPair where
  leftExtension := s.left.extension
  rightExtension := s.right.extension
  leftDigits := s.left.digits
  rightDigits := s.right.digits
  leftState := s.left.state
  rightState := s.right.state
  leftLegal := s.left.legal
  rightLegal := s.right.legal
  leftAnchor := s.left.anchorValue
  rightAnchor := s.right.anchorValue
  leftAnchor_mem := s.left.anchorValue_mem
  rightAnchor_mem := s.right.anchorValue_mem

theorem target_subset_hull (s : RealState input data alive) :
    s.target ⊆ CylinderCover.sumHull s.pair := by
  have hlo : (s.band.lo : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast s.bandUnit.1
    · exact_mod_cast s.bandUnit.2.1.trans s.bandUnit.2.2
  have hhi : (s.band.hi : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast s.bandUnit.1.trans s.bandUnit.2.1
    · exact_mod_cast s.bandUnit.2.2
  have hll := s.left.endpoint_mem hlo
  have hrl := s.right.endpoint_mem hlo
  have hlh := s.left.endpoint_mem hhi
  have hrh := s.right.endpoint_mem hhi
  intro x hx
  change Setup.center+s.left.lowerValue+s.right.lowerValue ≤ x ∧
    x ≤ Setup.center+s.left.upperValue+s.right.upperValue
  change s.endpoint s.band.lo ≤ x ∧ x ≤ s.endpoint s.band.hi at hx
  dsimp only [endpoint] at hx
  constructor <;> linarith [hll.1,hrl.1,hlh.2,hrh.2,hx.1,hx.2]

noncomputable def normalizedEndpoint (s : RealState input data alive)
    (e : GraphCertificate.Endpoint) : ℝ :=
  GraphCertificate.endpointValue s.left.finite s.right.finite
    s.left.normalizedValue s.right.normalizedValue (s.right.scale/s.left.scale) e

theorem parent_endpoint (s : RealState input data alive)
    (hcheck : check input data = true) (p : ℚ) :
    s.normalizedEndpoint (GraphCertificate.parentEndpoint p) =
      (s.endpoint (p : ℝ)-Setup.center)/s.left.scale := by
  dsimp only [normalizedEndpoint,GraphCertificate.endpointValue,GraphCertificate.parentEndpoint]
  rw [s.left.empty_endpoint hcheck p,s.right.empty_endpoint hcheck p]
  unfold endpoint
  field_simp [ne_of_gt s.left.scale_pos,ne_of_gt s.right.scale_pos]
  <;> ring

theorem normalized_target_mem (s : RealState input data alive)
    (hcheck : check input data = true) {x : ℝ} (hx : x ∈ s.target) :
    (x-Setup.center)/s.left.scale ∈ Set.Icc
      (s.normalizedEndpoint (GraphCertificate.parentEndpoint s.band.lo))
      (s.normalizedEndpoint (GraphCertificate.parentEndpoint s.band.hi)) := by
  rw [s.parent_endpoint hcheck,s.parent_endpoint hcheck]
  exact ⟨div_le_div_of_nonneg_right (by linarith [hx.1]) s.left.scale_pos.le,
    div_le_div_of_nonneg_right (by linarith [hx.2]) s.left.scale_pos.le⟩

def Next (s t : RealState input data alive) : Prop := CylinderCover.Extends s.pair t.pair

theorem ratio_eq_denominators (s : RealState input data alive) :
    s.right.scale/s.left.scale =
      (CylinderCover.denominator s.pair.leftWord s.pair.leftAnchor)^2 /
        (CylinderCover.denominator s.pair.rightWord s.pair.rightAnchor)^2 := by
  have hl := CylinderCover.denominator_pos s.left.word s.left.anchorValue_mem.1
  have hr := CylinderCover.denominator_pos s.right.word s.right.anchorValue_mem.1
  change (1/(CylinderCover.denominator s.right.word s.right.anchorValue)^2) /
      (1/(CylinderCover.denominator s.left.word s.left.anchorValue)^2) =
      (CylinderCover.denominator s.left.word s.left.anchorValue)^2 /
        (CylinderCover.denominator s.right.word s.right.anchorValue)^2
  field_simp [ne_of_gt hl, ne_of_gt hr]

noncomputable def system
    (hcovers : ∀ s : RealState input data alive, ∀ x ∈ s.target,
      ∃ t : RealState input data alive, Next s t ∧ x ∈ t.target) :
    ClosedCoverSystem (RealState input data alive)
      (ActualCylinders.Stream × ActualCylinders.Stream) :=
  CylinderCover.closedCover RealState.pair RealState.target Next target_subset_hull
    (fun _ _ h => h) hcovers 100 (by norm_num) (fun s => by
      rw [← ratio_eq_denominators s]
      norm_num
      exact s.balance)

/-- Once the verified finite graph supplies successors, every root target
is a sum of actual admissible continued fractions. -/
theorem realizes
    (hcovers : ∀ s : RealState input data alive, ∀ x ∈ s.target,
      ∃ t : RealState input data alive, Next s t ∧ x ∈ t.target)
    (s : RealState input data alive) {x : ℝ} (hx : x ∈ s.target) :
    ∃ a ∈ admissibleTailSet Setup.left, ∃ b ∈ admissibleTailSet Setup.right, x = Setup.center+a+b := by
  obtain ⟨u,hu,hvalue⟩ := (system hcovers).realizes hx
  obtain ⟨a,ha,b,hb,heq⟩ := CylinderCover.realizes_mem_sum hu
  exact ⟨a,ha,b,hb,hvalue.symm.trans heq⟩

end RealState
end Freiman.GraphMeaning
