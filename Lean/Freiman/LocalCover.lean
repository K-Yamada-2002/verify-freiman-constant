import Freiman.LocalSelf
import Berstein.CertificateCheck

/-! A single closed successor construction joining the four local conditions
and the general finite table. All infinite paths retain their actual words. -/
namespace Freiman.Local
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction
variable [Setup]

structure Tagged (conditions : Array Condition) where
  condition : Condition
  index : Nat
  lookup : conditions[index]? = some condition
  actual : State condition

inductive Combined (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (conditions : Array Condition) where
  | general : Freiman.GraphMeaning.RealState input data alive → Combined input data alive conditions
  | special : Tagged conditions → Combined input data alive conditions

namespace Combined
variable {input : GraphCertificate.Input} {data : Data} {alive : ByteArray} {conditions : Array Condition}

noncomputable def pair : Combined input data alive conditions → CylinderCover.LegalPair
  | .general s => s.pair
  | .special s => s.actual.pair
noncomputable def target : Combined input data alive conditions → Set ℝ
  | .general s => s.target
  | .special s => s.actual.target

def Next (s t : Combined input data alive conditions) : Prop := CylinderCover.Extends s.pair t.pair

end Combined

/-- Exactly the finite acceptances required for all local cases. -/
def allCheck (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (conditions : Array Condition) : Bool :=
  conditions.all (fun c => c.check && coverageCheck input data alive conditions c)

structure Accepted (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (conditions : Array Condition) : Prop where
  valid : ∀ c ∈ conditions, c.check = true
  coverage : ∀ c ∈ conditions, coverageCheck input data alive conditions c = true

 omit [Setup] in
 theorem allCheck_sound (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (conditions : Array Condition) (hc : allCheck input data alive conditions = true) :
    Accepted input data alive conditions := by
  have h := Array.all_eq_true_iff_forall_mem.mp hc
  exact ⟨fun c hm => (Bool.and_eq_true_iff.mp (h c hm)).1,
    fun c hm => (Bool.and_eq_true_iff.mp (h c hm)).2⟩

 theorem local_successor_covered (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (hm : Berstein.GraphMeaning.check input data = true) (conditions : Array Condition)
    (accepted : Accepted input data alive conditions) (tag : Tagged conditions)
    (x : ℝ) (hx : x ∈ tag.actual.target) :
    ∃ t : Combined input data alive conditions,
      CylinderCover.Extends tag.actual.pair t.pair ∧ x ∈ t.target := by
  let c := tag.condition
  let s := tag.actual
  have hmem := Array.mem_of_getElem? tag.lookup
  have hc := accepted.valid c hmem
  have hcover := accepted.coverage c hmem
  have hf := c.facts hc
  have hnorm : (x-Setup.center)/s.left.scale ∈ Set.Icc
      (s.normalizedEndpoint (GraphCertificate.parentEndpoint c.band.lo))
      (s.normalizedEndpoint (GraphCertificate.parentEndpoint c.band.hi)) := by
    rw [s.parent_endpoint hc,s.parent_endpoint hc]
    exact ⟨div_le_div_of_nonneg_right (by linarith [hx.1]) s.left.scale_pos.le,
      div_le_div_of_nonneg_right (by linarith [hx.2]) s.left.scale_pos.le⟩
  obtain ⟨v,_,hv,hcov⟩ := FiniteCover.check_sound (fun v : Vertex => ⟨v.lower,v.upper⟩)
    (GraphCertificate.endpointLeq c.left.numeric c.right.numeric c.scale)
    (vertexCheck input data alive conditions c) s.normalizedEndpoint
    (GraphCertificate.endpointLeq_sound c.left.numeric c.right.numeric c.scale
      (normalized c.left s.left) (normalized c.right s.right) (s.right.scale/s.left.scale)
      (c.left.numeric_differences hf.left s.left) (c.right.numeric_differences hf.right s.right) (s.scale_mem hc))
    (GraphCertificate.parentEndpoint c.band.lo) (GraphCertificate.parentEndpoint c.band.hi)
    c.menu hcover ((x-Setup.center)/s.left.scale) hnorm
  have hvertex := hv
  simp only [vertexCheck,Bool.and_eq_true,decide_eq_true_eq] at hvertex
  rcases hvertex with ⟨⟨⟨⟨hl,hr⟩,hprogress⟩,_⟩,hdest⟩
  obtain ⟨fl⟩ := c.left.step_exists hf.left v.left hl
  obtain ⟨fr⟩ := c.right.step_exists hf.right v.right hr
  have hproper : 0 < fl.word.length+fr.word.length := by
    simpa only [fl.word_eq,fr.word_eq,decide_eq_true_eq] using hprogress
  let l := s.left.extend fl.word fl.transition fl.lower fl.upper hf.left fl.facts
  let r := s.right.extend fr.word fr.transition fr.lower fr.upper hf.right fr.facts
  change s.normalizedEndpoint ⟨v.left,v.right,v.band.lo⟩ ≤ (x-Setup.center)/s.left.scale ∧
    (x-Setup.center)/s.left.scale ≤ s.normalizedEndpoint ⟨v.left,v.right,v.band.hi⟩ at hcov
  rw [s.child_endpoint hc v fl fr v.band.lo,s.child_endpoint hc v fl fr v.band.hi] at hcov
  have hxchild : x ∈ Set.Icc (pairEndpoint l r v.band.lo) (pairEndpoint l r v.band.hi) := by
    have hlo := (div_le_div_iff_of_pos_right s.left.scale_pos).mp hcov.1
    have hhi := (div_le_div_iff_of_pos_right s.left.scale_pos).mp hcov.2
    dsimp only [pairEndpoint]
    exact ⟨by linarith,by linarith⟩
  cases he : v.destination with
  | none =>
    rw [he] at hdest
    obtain ⟨t,ht,hx⟩ := general_successor input data alive hm s hc v fl fr hproper hdest x hxchild
    exact ⟨.general t,ht,hx⟩
  | some j =>
    rw [he] at hdest
    obtain ⟨dest,hd,t,ht,hx⟩ := local_successor conditions accepted.valid s hc v j fl fr hproper hdest x hxchild
    exact ⟨.special ⟨dest,j,hd,t⟩,ht,hx⟩

 theorem Combined.successor (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell)
    (htable : Berstein.Certificate.Accepted input data alive cells) (conditions : Array Condition)
    (hlocal : Accepted input data alive conditions) (s : Combined input data alive conditions)
    (x : ℝ) (hx : x ∈ s.target) :
    ∃ t : Combined input data alive conditions, s.Next t ∧ x ∈ t.target := by
  cases s with
  | general s =>
    have hp : ∀ i < input.states, GraphCertificate.checkPrepared (input.sides[i]?.getD default) = true := by
      intro i hi
      have hs := (check_sizes input data htable.meaning).1
      exact htable.prepared _ (Array.mem_of_getElem? (lookup_some_getD input.sides i (by omega)))
    obtain ⟨t,ht,hx⟩ := Freiman.GraphMeaning.verified_successor htable.meaning hp cells htable.geometries s x hx
    exact ⟨.general t,ht,hx⟩
  | special s => exact local_successor_covered input data alive htable.meaning conditions hlocal s x hx

 theorem Combined.target_subset_hull (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (conditions : Array Condition) (hlocal : Accepted input data alive conditions)
    (s : Combined input data alive conditions) : s.target ⊆ CylinderCover.sumHull s.pair := by
  cases s with
  | general s => exact s.target_subset_hull
  | special s => exact s.actual.target_subset_hull (hlocal.valid _ (Array.mem_of_getElem? s.lookup))

 theorem Combined.balance (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (conditions : Array Condition) (hlocal : Accepted input data alive conditions)
    (s : Combined input data alive conditions) :
    1/(100 : ℝ)^2 ≤ (CylinderCover.denominator s.pair.leftWord s.pair.leftAnchor)^2/
        (CylinderCover.denominator s.pair.rightWord s.pair.rightAnchor)^2 ∧
    (CylinderCover.denominator s.pair.leftWord s.pair.leftAnchor)^2/
        (CylinderCover.denominator s.pair.rightWord s.pair.rightAnchor)^2 ≤ (100 : ℝ)^2 := by
  cases s with
  | general s =>
    dsimp only [pair]
    rw [← s.ratio_eq_denominators]
    norm_num
    exact s.balance
  | special s =>
    have h := s.actual.balance (hlocal.valid _ (Array.mem_of_getElem? s.lookup))
    have he : s.actual.right.scale/s.actual.left.scale =
        (CylinderCover.denominator s.actual.pair.leftWord s.actual.pair.leftAnchor)^2/
          (CylinderCover.denominator s.actual.pair.rightWord s.actual.pair.rightAnchor)^2 := by
      have hl := CylinderCover.denominator_pos s.actual.left.word s.actual.left.anchor_mem.1
      have hr := CylinderCover.denominator_pos s.actual.right.word s.actual.right.anchor_mem.1
      change (1/(CylinderCover.denominator s.actual.right.word s.actual.right.anchorValue)^2)/
          (1/(CylinderCover.denominator s.actual.left.word s.actual.left.anchorValue)^2) =
          (CylinderCover.denominator s.actual.left.word s.actual.left.anchorValue)^2/
            (CylinderCover.denominator s.actual.right.word s.actual.right.anchorValue)^2
      field_simp [ne_of_gt hl,ne_of_gt hr]
    rw [he] at h
    norm_num
    exact h

/-- The combined infinite construction now realizes every accepted local target. -/
theorem realizes (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell)
    (htable : Berstein.Certificate.Accepted input data alive cells) (conditions : Array Condition)
    (hlocal : Accepted input data alive conditions) (s : Combined input data alive conditions)
    {x : ℝ} (hx : x ∈ s.target) :
    ∃ a ∈ admissibleTailSet Setup.left, ∃ b ∈ admissibleTailSet Setup.right, x = Setup.center+a+b := by
  let system := CylinderCover.closedCover (Combined.pair (conditions := conditions)) Combined.target Combined.Next
    (Combined.target_subset_hull input data alive conditions hlocal)
    (fun _ _ h => h) (Combined.successor input data alive cells htable conditions hlocal) 100 (by norm_num)
    (Combined.balance input data alive conditions hlocal)
  obtain ⟨u,hu,he⟩ := system.realizes hx
  obtain ⟨a,ha,b,hb,hvalue⟩ := CylinderCover.realizes_mem_sum hu
  exact ⟨a,ha,b,hb,he.symm.trans hvalue⟩

end Freiman.Local
