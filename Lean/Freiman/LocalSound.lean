import Freiman.LocalCheck
import Freiman.GraphSuccessor

namespace Freiman.Local
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction Forbidden31313

structure ConditionFacts (c : Condition) : Prop where
  left : c.left.check = true
  right : c.right.check = true
  leftEmpty : c.left.checkStep 0 = true
  rightEmpty : c.right.checkStep 0 = true
  leftWord : c.left.extensions[0]? = some []
  rightWord : c.right.extensions[0]? = some []
  leftTarget : c.left.targets[0]? = some c.left.spec
  rightTarget : c.right.targets[0]? = some c.right.spec
  kind : c.kind < 4
  leftState : c.left.spec.state.val = 1
  leftParity : c.left.spec.parity = true
  rightParity : c.right.spec.parity = false
  rightState : c.right.spec.state.val = if c.kind < 2 then 0 else 1
  band : 0 ≤ c.band.lo ∧ c.band.lo ≤ c.band.hi ∧ c.band.hi ≤ 1
  invariantPositive : 0 < c.invariant.lo
  scaleBounds : 1/10000 ≤ c.scale.lo ∧ c.scale.hi ≤ 10000

 theorem Condition.facts (c : Condition) (h : c.check = true) : ConditionFacts c := by
  simp only [Condition.check,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hl,hr⟩,hle⟩,hre⟩,hz⟩,hk⟩,hb⟩,_⟩
  exact ⟨hl,hr,hle,hre,hz.1,hz.2.1,hz.2.2.1,hz.2.2.2,hk.1,hk.2.1,hk.2.2.1,
    hk.2.2.2.1,hk.2.2.2.2,⟨hb.1,hb.2.1,hb.2.2.1⟩,hb.2.2.2.1,hb.2.2.2.2⟩

 theorem ActualSide.endpoint_mem {root : Word} {spec : Spec} (s : ActualSide root spec)
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    s.endpoint p ∈ Set.Icc s.lowerValue s.upperValue := by
  have h := s.lower_le_upper
  unfold ActualSide.endpoint
  constructor <;> nlinarith [mul_nonneg hp.1 (sub_nonneg.mpr h),
    mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr h)]

 theorem RawSide.empty_endpoint (src : RawSide) (hr : src.check = true)
    (he : src.checkStep 0 = true) (hw : src.extensions[0]? = some [])
    (ht : src.targets[0]? = some src.spec) {root : Word} (s : ActualSide root src.spec) (p : ℚ) :
    GraphCertificate.sideEndpointValue src.numeric (normalized src s) 0 p = s.endpoint p/s.scale := by
  obtain ⟨f⟩ := src.step_exists hr 0 he
  have hf := step_endpoint s hr f p
  have hword : f.word = [] := Option.some.inj (f.word_eq.symm.trans hw)
  have htarget : f.target = src.spec := Option.some.inj (f.target_eq.symm.trans ht)
  simpa only [ActualSide.endpoint,ActualSide.lowerValue,ActualSide.upperValue,ActualSide.word,
    ActualSide.extend,hword,htarget,List.append_nil] using hf

 theorem State.parent_endpoint [Setup] {c : Condition} (s : State c)
    (hc : c.check = true) (p : ℚ) :
    s.normalizedEndpoint (GraphCertificate.parentEndpoint p) =
      (s.endpoint p-Setup.center)/s.left.scale := by
  have hf := c.facts hc
  dsimp only [State.normalizedEndpoint,GraphCertificate.endpointValue,GraphCertificate.parentEndpoint]
  rw [c.left.empty_endpoint hf.left hf.leftEmpty hf.leftWord hf.leftTarget s.left p,
    c.right.empty_endpoint hf.right hf.rightEmpty hf.rightWord hf.rightTarget s.right p]
  unfold State.endpoint
  field_simp [ne_of_gt s.left.scale_pos,ne_of_gt s.right.scale_pos]
  <;> ring

 theorem State.target_subset_hull [Setup] {c : Condition} (s : State c)
    (hc : c.check = true) : s.target ⊆ CylinderCover.sumHull s.pair := by
  have hb := (c.facts hc).band
  have hlo : (c.band.lo : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast hb.1
    · exact_mod_cast hb.2.1.trans hb.2.2
  have hhi : (c.band.hi : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact_mod_cast hb.1.trans hb.2.1
    · exact_mod_cast hb.2.2
  have hll := s.left.endpoint_mem hlo
  have hrl := s.right.endpoint_mem hlo
  have hlh := s.left.endpoint_mem hhi
  have hrh := s.right.endpoint_mem hhi
  intro x hx
  change Setup.center+s.left.lowerValue+s.right.lowerValue ≤ x ∧
    x ≤ Setup.center+s.left.upperValue+s.right.upperValue
  change s.endpoint c.band.lo ≤ x ∧ x ≤ s.endpoint c.band.hi at hx
  dsimp only [State.endpoint] at hx
  constructor <;> linarith [hll.1,hrl.1,hlh.2,hrh.2,hx.1,hx.2]

 theorem State.balance [Setup] {c : Condition} (s : State c) (hc : c.check = true) :
    s.right.scale/s.left.scale ∈ Set.Icc (1/10000 : ℝ) 10000 := by
  have h := s.scale_mem hc
  have hf := (c.facts hc).scaleBounds
  have hlo : (1/10000 : ℝ) ≤ c.scale.lo := by
    have hh : (((1/10000 : ℚ) : ℝ)) ≤ (c.scale.lo : ℝ) := Rat.cast_mono hf.1
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
  have hhi : (c.scale.hi : ℝ) ≤ 10000 := by exact_mod_cast hf.2
  exact ⟨hlo.trans h.1,h.2.trans hhi⟩

 theorem State.child_endpoint [Setup] {c : Condition} (s : State c) (hc : c.check = true)
    (v : Vertex) (fl : StepInfo c.left v.left) (fr : StepInfo c.right v.right) (p : ℚ) :
    s.normalizedEndpoint ⟨v.left,v.right,p⟩ =
      (Setup.center+(s.left.extend fl.word fl.transition fl.lower fl.upper (c.facts hc).left fl.facts).endpoint p+
        (s.right.extend fr.word fr.transition fr.lower fr.upper (c.facts hc).right fr.facts).endpoint p-
          Setup.center)/s.left.scale := by
  dsimp only [State.normalizedEndpoint,GraphCertificate.endpointValue]
  rw [step_endpoint s.left (c.facts hc).left fl p,step_endpoint s.right (c.facts hc).right fr p]
  field_simp [ne_of_gt s.left.scale_pos,ne_of_gt s.right.scale_pos]
  <;> ring

 theorem imageBox_sound [Setup] {c : Condition} (s : State c) (hc : c.check = true)
    (v : Vertex) (fl : StepInfo c.left v.left) (fr : StepInfo c.right v.right)
    (box : QBounds) (he : imageBox c v = some box) :
    box.mem ((s.right.extend fr.word fr.transition fr.lower fr.upper (c.facts hc).right fr.facts).scale/
      (s.left.extend fl.word fl.transition fl.lower fl.upper (c.facts hc).left fl.facts).scale) := by
  let l := s.left.extend fl.word fl.transition fl.lower fl.upper (c.facts hc).left fl.facts
  let r := s.right.extend fr.word fr.transition fr.lower fr.upper (c.facts hc).right fr.facts
  have hl := s.left.extend_derivative fl.word fl.transition fl.lower fl.upper (c.facts hc).left fl.facts
  have hr := s.right.extend_derivative fr.word fr.transition fr.lower fr.upper (c.facts hc).right fr.facts
  unfold imageBox at he
  rw [fl.transition_eq,fr.transition_eq] at he
  cases hfactor : QBounds.checkedDiv fr.transition.derivative fl.transition.derivative with
  | none => simp [hfactor] at he
  | some factor =>
    simp [hfactor] at he
    subst box
    have hrat := QBounds.checkedDiv_sound _ _ factor (r.scale/s.right.scale) (l.scale/s.left.scale) hr hl hfactor
    have h := QBounds.mul_sound c.scale factor _ _ (s.scale_mem hc) hrat
    have heq : (s.right.scale/s.left.scale)*((r.scale/s.right.scale)/(l.scale/s.left.scale)) = r.scale/l.scale := by
      field_simp [ne_of_gt s.left.scale_pos,ne_of_gt s.right.scale_pos,ne_of_gt l.scale_pos]
      <;> ring
    rwa [heq] at h

/-- Attach a transported local child to its checked general-table side. -/
def ActualSide.toGeneral {root : Word} {spec : Spec} (s : ActualSide root spec)
    (input : GraphCertificate.Input) (data : Data) (i : Nat)
    (hc : specMatches input data i spec = true) : RealSide input data root where
  extension := s.extension
  digits := s.digits
  index := i
  index_lt := by simp only [specMatches,Bool.and_eq_true,decide_eq_true_eq] at hc; exact hc.1.1
  state := spec.state
  state_eq := by simp only [specMatches,Bool.and_eq_true,decide_eq_true_eq] at hc; exact hc.2.2.1
  legal := s.legal
  parity := by
    have h := hc
    simp only [specMatches,Bool.and_eq_true,decide_eq_true_eq] at h
    rw [h.2.1]
    exact s.parity
  shape := by
    have h := hc
    simp only [specMatches,Bool.and_eq_true,decide_eq_true_eq] at h
    rw [h.2.2.2]
    exact s.shape

 theorem shapeBox_sound {root : Word} {src : RawSide} (s : ActualSide root src.spec)
    (hr : src.check = true) {e : Nat} (f : StepInfo src e)
    (box : QBounds) (hc : shapeBox src e = some box) :
    box.mem (denominatorRatio (s.extend f.word f.transition f.lower f.upper hr f.facts).word) := by
  unfold shapeBox at hc
  simp only [f.word_eq,Option.bind_eq_bind,Option.bind_some,Option.pure_def,Option.some.injEq] at hc
  subst box
  rw [ActualSide.extend_word]
  apply shape_transport s.word f.word src.spec.shape _ s.shape (src.check_sound hr).nonneg
  · exact ⟨min_le_left _ _,le_max_left _ _⟩
  · exact ⟨min_le_right _ _,le_max_right _ _⟩

end Freiman.Local
