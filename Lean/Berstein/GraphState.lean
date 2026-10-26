import Berstein.CylinderCover
import Berstein.SemanticTransport
import Berstein.SemanticSound
import Berstein.GraphNumericSound

/-! Infinite-prefix states carried by the finite graph. The row indices alone
do not determine a real cylinder: these states retain both actual words and
the semantic invariants needed to transport them. -/
namespace Berstein.GraphMeaning
open HallRay.ContinuedFraction Forbidden31313

theorem exact_bounds_strict (s : Forbidden31313.State) : exactLower s < exactUpper s := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 462)
  have hn := Real.sqrt_nonneg (462 : ℝ)
  have hl : (21 : ℝ) < Real.sqrt 462 := by nlinarith
  have hu : Real.sqrt 462 < (22 : ℝ) := by nlinarith
  fin_cases s <;> norm_num [exactLower,exactUpper] <;> nlinarith

structure RealSide (input : GraphCertificate.Input) (data : Data) (root : Word) where
  extension : Word
  digits : ∀ a ∈ extension, a.val ≤ 3
  index : Nat
  index_lt : index < input.states
  state : Forbidden31313.State
  state_eq : (data.sides[index]?.getD default).state = state.val
  legal : afterWord 0 (root ++ extension) = some state
  parity : (input.sides[index]?.getD default).parity = decide ((root ++ extension).length % 2 = 1)
  shape : (data.sides[index]?.getD default).shape.mem (denominatorRatio (root ++ extension))

namespace RealSide
variable {input : GraphCertificate.Input} {data : Data} {root : Word}
abbrev word (s : RealSide input data root) : Word := root ++ s.extension
abbrev finite (s : RealSide input data root) : GraphCertificate.Side := input.sides[s.index]?.getD default
abbrev meaning (s : RealSide input data root) : Side := data.sides[s.index]?.getD default
noncomputable def anchorValue (s : RealSide input data root) : ℝ :=
  (anchor s.state.val s.finite.parity).eval
noncomputable def scale (s : RealSide input data root) : ℝ := Normalization.scale s.word s.anchorValue
noncomputable def lowerValue (s : RealSide input data root) : ℝ := CylinderCover.lowerValue s.word s.state
noncomputable def upperValue (s : RealSide input data root) : ℝ := CylinderCover.upperValue s.word s.state
noncomputable def endpoint (s : RealSide input data root) (p : ℝ) : ℝ :=
  (1-p)*s.lowerValue+p*s.upperValue

theorem anchorValue_mem (s : RealSide input data root) : s.anchorValue ∈ Set.Icc (0 : ℝ) 1 :=
  anchor_unit s.state s.finite.parity

theorem scale_pos (s : RealSide input data root) : 0 < s.scale :=
  Normalization.scale_pos s.word s.anchorValue_mem.1

theorem lower_le_upper (s : RealSide input data root) : s.lowerValue ≤ s.upperValue := min_le_max

theorem lower_lt_upper (s : RealSide input data root) : s.lowerValue < s.upperValue := by
  apply min_lt_max.mpr
  intro h
  have hb := exactBounds_unit s.state
  have he := injOn_tailMap_Icc s.word
    ⟨hb.1,hb.2.1.trans hb.2.2⟩ ⟨hb.1.trans hb.2.1,hb.2.2⟩ h
  exact (ne_of_lt (exact_bounds_strict s.state)) he

theorem endpoint_mem (s : RealSide input data root) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    s.endpoint p ∈ Set.Icc s.lowerValue s.upperValue := by
  have hl := s.lower_le_upper
  unfold endpoint
  constructor
  · nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr hl)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hl)]

noncomputable def rawValue (s : RealSide input data root) (j : Nat) : ℝ :=
  (s.meaning.raw[j]?.getD default).eval
noncomputable def normalizedValue (s : RealSide input data root) (j : Nat) : ℝ :=
  tailMap s.word (s.rawValue j) / s.scale

theorem facts (s : RealSide input data root) (hcheck : check input data = true) :
    ∃ x empty, s.meaning.raw[s.finite.anchor]? = some x ∧
      s.finite.transitions[0]? = some empty ∧
      SideFacts input data s.index s.finite s.meaning x empty := by
  have hsize := check_sizes input data hcheck
  exact checkSide_gets input data s.index s.finite s.meaning
    (lookup_some_getD _ _ (by rw [← hsize.1]; exact s.index_lt))
    (lookup_some_getD _ _ (by rw [← hsize.2.1]; exact s.index_lt))
    (check_sides input data hcheck s.index s.index_lt)

theorem raw_facts (s : RealSide input data root) (hcheck : check input data = true) :
    s.finite.anchor < s.finite.tails.size ∧
    s.rawValue s.finite.anchor = s.anchorValue ∧
    (∀ j < s.finite.tails.size, (s.finite.tails[j]?.getD default).mem (s.rawValue j) ∧
      s.rawValue j ∈ Set.Icc (0 : ℝ) 1) := by
  obtain ⟨x,empty,hx,_,hf⟩ := s.facts hcheck
  have hanchor : s.finite.anchor < s.meaning.raw.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at hx
    contradiction
  refine ⟨hf.rawSize ▸ hanchor, ?_, ?_⟩
  · simp only [rawValue,hx,Option.getD_some,hf.anchorEq,anchorValue]
    rw [s.state_eq]
  · intro j hj
    exact hf.rawBounds j (by rw [hf.rawSize]; exact hj) _ _
      (lookup_some_getD _ _ hj)
      (lookup_some_getD _ _ (by rw [hf.rawSize]; exact hj))

theorem numeric_differences (s : RealSide input data root)
    (hcheck : check input data = true) (hprepared : GraphCertificate.checkPrepared s.finite = true) :
    ∀ i < s.finite.tails.size, ∀ j < s.finite.tails.size,
      (s.finite.delta i j).mem (s.normalizedValue i-s.normalizedValue j) := by
  obtain ⟨x,empty,_,_,hf⟩ := s.facts hcheck
  obtain ⟨ha,heq,hr⟩ := s.raw_facts hcheck
  have hshape : s.finite.shape.mem (denominatorRatio s.word) := by
    have hlo : (s.finite.shape.lo : ℝ) ≤ s.meaning.shape.lo := by exact_mod_cast hf.shapeOuter.1
    have hhi : (s.meaning.shape.hi : ℝ) ≤ s.finite.shape.hi := by exact_mod_cast hf.shapeOuter.2.1
    exact ⟨hlo.trans s.shape.1,s.shape.2.trans hhi⟩
  have h := GraphCertificate.checkPrepared_actual_differences s.finite s.word s.rawValue
    hprepared ha hshape hf.shapeOuter.2.2 (fun i hi => (hr i hi).1)
    (fun i hi => (hr i hi).2.1) (sign_of_parity s.word s.finite.parity s.parity)
  simpa only [normalizedValue,scale,heq] using h

theorem lower_eq_anchor (s : RealSide input data root) :
    s.lowerValue = tailMap s.word s.anchorValue :=
  (anchor_min_opposite_max s.word s.state s.finite.parity s.parity).1.symm

theorem upper_eq_opposite (s : RealSide input data root) :
    s.upperValue = tailMap s.word (opposite s.state.val s.finite.parity).eval :=
  (anchor_min_opposite_max s.word s.state s.finite.parity s.parity).2.symm

/-- A checked extension endpoint is the endpoint of the actual extended
cylinder, expressed in the parent scale. -/
theorem transition_endpoint (s t : RealSide input data root) (e : Nat)
    (tr : GraphCertificate.Transition) (w : List Nat) (lo hi : Quadratic462)
    (htr : s.finite.transitions[e]? = some tr)
    (hlo : s.meaning.raw[tr.lowerId]? = some lo)
    (hhi : s.meaning.raw[tr.upperId]? = some hi)
    (hw : (asWord w).map Subtype.val = w)
    (hext : t.word = s.word ++ asWord w)
    (hf : TransitionFacts s.finite s.meaning tr t.finite t.meaning w lo hi)
    (p : ℚ) :
    GraphCertificate.sideEndpointValue s.finite s.normalizedValue e p =
      t.endpoint (p : ℝ) / s.scale := by
  have hlcf : lo.eval = tailMap (asWord w) (anchor t.state.val t.finite.parity).eval := by
    apply Quadratic462.cf_sound
    rw [hw, ← t.state_eq]
    exact hf.lower
  have hhcf : hi.eval = tailMap (asWord w) (opposite t.state.val t.finite.parity).eval := by
    apply Quadratic462.cf_sound
    rw [hw, ← t.state_eq]
    exact hf.upper
  have hl : tailMap s.word (s.rawValue tr.lowerId) = t.lowerValue := by
    rw [rawValue,hlo,Option.getD_some,hlcf,← tailMap_append,← hext,t.lower_eq_anchor]
    rfl
  have hh : tailMap s.word (s.rawValue tr.upperId) = t.upperValue := by
    rw [rawValue,hhi,Option.getD_some,hhcf,← tailMap_append,← hext,t.upper_eq_opposite]
  simp only [GraphCertificate.sideEndpointValue,htr,Option.getD_some,normalizedValue,hl,hh,endpoint]
  ring

theorem finite_lookup (s : RealSide input data root) (hcheck : check input data = true) :
    input.sides[s.index]? = some s.finite :=
  lookup_some_getD _ _ (by rw [← (check_sizes input data hcheck).1]; exact s.index_lt)

theorem meaning_lookup (s : RealSide input data root) (hcheck : check input data = true) :
    data.sides[s.index]? = some s.meaning :=
  lookup_some_getD _ _ (by rw [← (check_sizes input data hcheck).2.1]; exact s.index_lt)

theorem empty_endpoint (s : RealSide input data root)
    (hcheck : check input data = true) (p : ℚ) :
    GraphCertificate.sideEndpointValue s.finite s.normalizedValue 0 p =
      s.endpoint (p : ℝ) / s.scale := by
  obtain ⟨x,tr,_,htr,hf⟩ := s.facts hcheck
  have hactive : 0 ≤ tr.state := by rw [hf.emptyEq.1]; exact Int.natCast_nonneg _
  have hc : input.sides[tr.state.toNat]? = some s.finite := by
    rw [hf.emptyEq.1]; exact s.finite_lookup hcheck
  have hcm : data.sides[tr.state.toNat]? = some s.meaning := by
    rw [hf.emptyEq.1]; exact s.meaning_lookup hcheck
  have hsize : 0 < s.finite.transitions.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at htr
    contradiction
  have hchecked := hf.transitions 0 (by rw [← hf.transitionSize]; exact hsize)
  obtain ⟨w,lo,hi,hw,hlo,hhi,ht⟩ := checkTransition_gets input data s.index 0
    s.finite s.meaning tr s.finite s.meaning (s.finite_lookup hcheck)
    (s.meaning_lookup hcheck) htr hactive hc hcm hchecked
  have hwzero : w = [] := Option.some.inj (hw.symm.trans (check_empty_extension input data hcheck))
  subst w
  exact s.transition_endpoint s 0 tr [] lo hi htr hlo hhi rfl
    (by simp [asWord]) ht p

end RealSide

noncomputable def exactCut (input : GraphCertificate.Input) (n : Nat) : ℝ :=
  ((51/50 : ℚ) ^ (input.firstExponent+(n : Int)) : ℚ)

structure RealState (input : GraphCertificate.Input) (data : Data) (alive : ByteArray) where
  left : RealSide input data prefix322
  right : RealSide input data prefix431
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
  4+s.left.endpoint p+s.right.endpoint p
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
  change 4+s.left.lowerValue+s.right.lowerValue ≤ x ∧
    x ≤ 4+s.left.upperValue+s.right.upperValue
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
      (s.endpoint (p : ℝ)-4)/s.left.scale := by
  dsimp only [normalizedEndpoint,GraphCertificate.endpointValue,GraphCertificate.parentEndpoint]
  rw [s.left.empty_endpoint hcheck p,s.right.empty_endpoint hcheck p]
  unfold endpoint
  field_simp [ne_of_gt s.left.scale_pos,ne_of_gt s.right.scale_pos]
  <;> ring

theorem normalized_target_mem (s : RealState input data alive)
    (hcheck : check input data = true) {x : ℝ} (hx : x ∈ s.target) :
    (x-4)/s.left.scale ∈ Set.Icc
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
    ∃ a ∈ admissibleTailSet prefix322, ∃ b ∈ admissibleTailSet prefix431, x = 4+a+b := by
  obtain ⟨u,hu,hvalue⟩ := (system hcovers).realizes hx
  obtain ⟨a,ha,b,hb,heq⟩ := CylinderCover.realizes_mem_sum hu
  exact ⟨a,ha,b,hb,hvalue.symm.trans heq⟩

end RealState
end Berstein.GraphMeaning
