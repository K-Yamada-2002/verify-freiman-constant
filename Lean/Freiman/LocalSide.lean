import Freiman.GraphState
import Berstein.GraphNumericSound

/-! Standalone exact semantic checks for local-menu sides. The local menus
share the proved numerical comparator with the general table, but their
admissibility conditions are checked separately. -/
namespace Freiman.Local
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction Forbidden31313

structure Spec where
  state : Forbidden31313.State
  parity : Bool
  shape : QBounds
  deriving DecidableEq, Inhabited

abbrev Spec.meaning (s : Spec) (raw : Array Quadratic462) : Berstein.GraphMeaning.Side :=
  ⟨s.state.val,s.shape,raw⟩

abbrev Spec.numeric (s : Spec) : GraphCertificate.Side :=
  ⟨s.parity,s.shape,0,#[],#[],#[],#[]⟩

structure RawSide where
  spec : Spec
  numeric : GraphCertificate.Side
  raw : Array Quadratic462
  extensions : Array Word
  targets : Array Spec
  deriving Inhabited

abbrev RawSide.meaning (s : RawSide) : Berstein.GraphMeaning.Side := s.spec.meaning s.raw

def RawSide.check (s : RawSide) : Bool :=
  decide (s.numeric.parity = s.spec.parity ∧ s.numeric.shape = s.spec.shape ∧
    0 ≤ s.spec.shape.lo ∧ s.raw.size = s.numeric.tails.size ∧ s.numeric.anchor < s.raw.size) &&
  decide (s.raw[s.numeric.anchor]? = some (anchor s.spec.state.val s.spec.parity)) &&
  (List.range s.raw.size).all (fun i =>
    match s.raw[i]?, s.numeric.tails[i]? with
    | some raw, some box => contains box raw && contains ⟨0,1⟩ raw
    | _, _ => false) && GraphCertificate.checkPrepared s.numeric

structure RawFacts (s : RawSide) : Prop where
  parity : s.numeric.parity = s.spec.parity
  shape : s.numeric.shape = s.spec.shape
  nonneg : 0 ≤ s.spec.shape.lo
  size : s.raw.size = s.numeric.tails.size
  anchor_lt : s.numeric.anchor < s.raw.size
  anchor : s.raw[s.numeric.anchor]? = some (anchor s.spec.state.val s.spec.parity)
  bounds : ∀ i < s.raw.size, (s.numeric.tails[i]?.getD default).mem
    (s.raw[i]?.getD default).eval ∧ (s.raw[i]?.getD default).eval ∈ Set.Icc (0 : ℝ) 1
  prepared : GraphCertificate.checkPrepared s.numeric = true

theorem RawSide.check_sound (s : RawSide) (h : s.check = true) : RawFacts s := by
  simp only [RawSide.check,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hb,ha⟩,hr⟩,hp⟩
  refine ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2,ha,?_,hp⟩
  intro i hi
  have hc := List.all_eq_true.mp hr i (List.mem_range.mpr hi)
  have hl := lookup_some_getD s.raw i hi
  have ht := lookup_some_getD s.numeric.tails i (by rw [← hb.2.2.2.1]; exact hi)
  rw [hl,ht] at hc
  dsimp only at hc
  simp only [Bool.and_eq_true] at hc
  exact ⟨contains_sound _ _ hc.1,by simpa [QBounds.mem] using contains_sound _ _ hc.2⟩

abbrev virtualTransition (tr : GraphCertificate.Transition) : GraphCertificate.Transition :=
  {tr with state := 1, constant := 0}

abbrev virtualInput (src : RawSide) (tr : GraphCertificate.Transition) (dst : Spec) :
    GraphCertificate.Input :=
  ⟨2,1,0,0,0,0,#[],#[],#[],#[{src.numeric with transitions := #[virtualTransition tr]},dst.numeric]⟩

abbrev virtualData (src : RawSide) (w : Word) (dst : Spec) : Data :=
  ⟨#[src.meaning,dst.meaning #[]],#[w.map Subtype.val],#[]⟩

def RawSide.checkStep (src : RawSide) (e : Nat) : Bool :=
  (do
    let w ← src.extensions[e]?
    let dst ← src.targets[e]?
    let tr ← src.numeric.transitions[e]?
    if !(w.all fun d => decide (d.val ≤ 3)) then return false
    return Berstein.GraphMeaning.checkTransition (virtualInput src tr dst)
      (virtualData src w dst) 0 0).getD false

structure TransportFacts (src : RawSide) (w : Word) (dst : Spec)
    (tr : GraphCertificate.Transition) (lo hi : Quadratic462) : Prop where
  legal : after src.spec.state.val (w.map Subtype.val) = some dst.state.val
  parity : dst.parity = (src.spec.parity != decide (w.length % 2 = 1))
  lower : Quadratic462.cf (w.map Subtype.val) (anchor dst.state.val dst.parity) = some lo
  upper : Quadratic462.cf (w.map Subtype.val) (opposite dst.state.val dst.parity) = some hi
  shapeLo : dst.shape.lo ≤ shapeImage (w.map Subtype.val) src.spec.shape.lo ∧
    shapeImage (w.map Subtype.val) src.spec.shape.lo ≤ dst.shape.hi
  shapeHi : dst.shape.lo ≤ shapeImage (w.map Subtype.val) src.spec.shape.hi ∧
    shapeImage (w.map Subtype.val) src.spec.shape.hi ≤ dst.shape.hi
  derivativeLo : ∃ dl, derivativeAt (w.map Subtype.val) (anchor src.spec.state.val src.spec.parity)
    (anchor dst.state.val dst.parity) src.spec.shape.lo = some dl ∧ tr.derivative.mem dl.eval
  derivativeHi : ∃ dh, derivativeAt (w.map Subtype.val) (anchor src.spec.state.val src.spec.parity)
    (anchor dst.state.val dst.parity) src.spec.shape.hi = some dh ∧ tr.derivative.mem dh.eval
  derivativePositive : 0 < tr.derivative.lo
  digits : ∀ a ∈ w, a.val ≤ 3

/-- Reuse the independently proved semantic transition checker on a two-side
virtual input. The virtual array indices have no mathematical interpretation. -/
theorem RawSide.step_facts (src : RawSide) (hr : src.check = true) (e : Nat)
    (w : Word) (dst : Spec) (tr : GraphCertificate.Transition) (lo hi : Quadratic462)
    (hw : src.extensions[e]? = some w) (hd : src.targets[e]? = some dst)
    (ht : src.numeric.transitions[e]? = some tr)
    (hl : src.raw[tr.lowerId]? = some lo) (hh : src.raw[tr.upperId]? = some hi)
    (hc : src.checkStep e = true) : TransportFacts src w dst tr lo hi := by
  have hf := src.check_sound hr
  unfold RawSide.checkStep at hc
  simp only [hw,hd,ht,Option.bind_eq_bind,Option.bind_some,Option.pure_def] at hc
  split at hc
  · simp_all
  · rename_i hdigits
    have hv : Berstein.GraphMeaning.checkTransition (virtualInput src tr dst)
        (virtualData src w dst) 0 0 = true := hc
    have facts := checkTransition_facts (virtualInput src tr dst) (virtualData src w dst) 0 0
      {src.numeric with transitions := #[virtualTransition tr]} src.meaning (virtualTransition tr)
      dst.numeric (dst.meaning #[]) (w.map Subtype.val) lo hi rfl rfl rfl (by change (0 : ℤ) ≤ 1; decide) rfl rfl rfl hl hh hv
    have hdigits' : ∀ a ∈ w, a.val ≤ 3 := by
      have ht' : (w.all fun d => decide (d.val ≤ 3)) = true := by
        cases he : (w.all fun d => decide (d.val ≤ 3)) <;> simp_all
      simpa only [List.all_eq_true,decide_eq_true_eq] using ht'
    refine ⟨facts.legal,?_,facts.lower,facts.upper,facts.shapeLo,facts.shapeHi,
      ?_,?_,facts.derivativePositive,hdigits'⟩
    · simpa only [Spec.numeric,hf.parity,List.length_map] using facts.parity
    · simpa only [Spec.numeric,hf.parity,RawSide.meaning,Spec.meaning] using facts.derivativeLo
    · simpa only [Spec.numeric,hf.parity,RawSide.meaning,Spec.meaning] using facts.derivativeHi

structure ActualSide (root : Word) (spec : Spec) where
  extension : Word
  digits : ∀ a ∈ extension, a.val ≤ 3
  legal : afterWord 0 (root++extension) = some spec.state
  parity : spec.parity = decide ((root++extension).length % 2 = 1)
  shape : spec.shape.mem (denominatorRatio (root++extension))

namespace ActualSide
variable {root : Word} {spec : Spec}
abbrev word (s : ActualSide root spec) : Word := root++s.extension
noncomputable def anchorValue (_s : ActualSide root spec) : ℝ := (anchor spec.state.val spec.parity).eval
noncomputable def scale (s : ActualSide root spec) : ℝ := Normalization.scale s.word s.anchorValue
noncomputable def lowerValue (s : ActualSide root spec) : ℝ := Berstein.CylinderCover.lowerValue s.word spec.state
noncomputable def upperValue (s : ActualSide root spec) : ℝ := Berstein.CylinderCover.upperValue s.word spec.state
noncomputable def endpoint (s : ActualSide root spec) (p : ℝ) : ℝ := (1-p)*s.lowerValue+p*s.upperValue

theorem anchor_mem (s : ActualSide root spec) : s.anchorValue ∈ Set.Icc (0 : ℝ) 1 := anchor_unit _ _
theorem scale_pos (s : ActualSide root spec) : 0 < s.scale := Normalization.scale_pos _ s.anchor_mem.1
theorem lower_le_upper (s : ActualSide root spec) : s.lowerValue ≤ s.upperValue := min_le_max

theorem lower_eq_anchor (s : ActualSide root spec) : s.lowerValue = tailMap s.word s.anchorValue :=
  (anchor_min_opposite_max s.word spec.state spec.parity s.parity).1.symm

theorem upper_eq_opposite (s : ActualSide root spec) :
    s.upperValue = tailMap s.word (opposite spec.state.val spec.parity).eval :=
  (anchor_min_opposite_max s.word spec.state spec.parity s.parity).2.symm

theorem lower_lt_upper (s : ActualSide root spec) : s.lowerValue < s.upperValue := by
  apply min_lt_max.mpr
  intro h
  have hb := exactBounds_unit spec.state
  have he := injOn_tailMap_Icc s.word ⟨hb.1,hb.2.1.trans hb.2.2⟩ ⟨hb.1.trans hb.2.1,hb.2.2⟩ h
  exact (ne_of_lt (Berstein.GraphMeaning.exact_bounds_strict spec.state)) he

/-- The actual extended words retain legality, parity and the shape box. -/
def extend {src : RawSide} {dst : Spec} (s : ActualSide root src.spec)
    (w : Word) (tr : GraphCertificate.Transition) (lo hi : Quadratic462)
    (hr : src.check = true) (f : TransportFacts src w dst tr lo hi) : ActualSide root dst where
  extension := s.extension++w
  digits := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact s.digits a ha
    · exact f.digits a ha
  legal := by
    rw [← List.append_assoc,afterWord_append,s.legal,Option.bind_some]
    exact after_sound src.spec.state dst.state w f.legal
  parity := by
    rw [f.parity,s.parity]
    simp only [List.length_append]
    by_cases ha : (root.length+s.extension.length)%2=1 <;>
      by_cases hb : w.length%2=1 <;> simp [ha,hb] <;> omega
  shape := by
    have h := shape_transport s.word w src.spec.shape dst.shape s.shape
      (src.check_sound hr).nonneg f.shapeLo f.shapeHi
    simpa only [word,List.append_assoc] using h

 theorem extend_word {src : RawSide} {dst : Spec} (s : ActualSide root src.spec)
    (w : Word) (tr : GraphCertificate.Transition) (lo hi : Quadratic462)
    (hr : src.check = true) (f : TransportFacts src w dst tr lo hi) :
    (s.extend w tr lo hi hr f).word = s.word++w := by simp only [word,extend,List.append_assoc]

 theorem extend_derivative {src : RawSide} {dst : Spec} (s : ActualSide root src.spec)
    (w : Word) (tr : GraphCertificate.Transition) (lo hi : Quadratic462)
    (hr : src.check = true) (f : TransportFacts src w dst tr lo hi) :
    tr.derivative.mem ((s.extend w tr lo hi hr f).scale/s.scale) := by
  obtain ⟨dl,hdl,hl⟩ := f.derivativeLo
  obtain ⟨dh,hdh,hh⟩ := f.derivativeHi
  have h := derivative_transport s.word w src.spec.shape tr.derivative
    (anchor src.spec.state.val src.spec.parity) (anchor dst.state.val dst.parity) dl dh
    s.anchor_mem.1 (anchor_unit dst.state dst.parity).1 s.shape (src.check_sound hr).nonneg hdl hdh hl hh
  simpa only [scale,anchorValue,extend_word] using h

end ActualSide
end Freiman.Local

namespace Freiman.Local
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction Forbidden31313

structure StepInfo (src : RawSide) (e : Nat) where
  word : Word
  target : Spec
  transition : GraphCertificate.Transition
  lower : Quadratic462
  upper : Quadratic462
  word_eq : src.extensions[e]? = some word
  target_eq : src.targets[e]? = some target
  transition_eq : src.numeric.transitions[e]? = some transition
  lower_eq : src.raw[transition.lowerId]? = some lower
  upper_eq : src.raw[transition.upperId]? = some upper
  facts : TransportFacts src word target transition lower upper

 theorem RawSide.step_exists (src : RawSide) (hr : src.check = true) (e : Nat)
    (hc : src.checkStep e = true) : Nonempty (StepInfo src e) := by
  have h := hc
  unfold RawSide.checkStep at h
  cases hw : src.extensions[e]? with
  | none => simp [hw] at h
  | some w =>
    cases hd : src.targets[e]? with
    | none => simp [hw,hd] at h
    | some dst =>
      cases ht : src.numeric.transitions[e]? with
      | none => simp [hw,hd,ht] at h
      | some tr =>
        simp only [hw,hd,ht,Option.bind_eq_bind,Option.bind_some,Option.pure_def] at h
        split at h
        · simp_all
        · have hv : Berstein.GraphMeaning.checkTransition (virtualInput src tr dst)
              (virtualData src w dst) 0 0 = true := h
          obtain ⟨wf,lo,hi,hwf,hl,hh,_⟩ := checkTransition_gets
            (virtualInput src tr dst) (virtualData src w dst) 0 0
            {src.numeric with transitions := #[virtualTransition tr]} src.meaning (virtualTransition tr)
            dst.numeric (dst.meaning #[]) rfl rfl rfl (by change (0 : ℤ) ≤ 1; decide) rfl rfl hv
          have he : wf = w.map Subtype.val := (Option.some.inj hwf).symm
          exact ⟨⟨w,dst,tr,lo,hi,hw,hd,ht,hl,hh,src.step_facts hr e w dst tr lo hi hw hd ht hl hh hc⟩⟩

noncomputable def normalized (src : RawSide) {root : Word} (s : ActualSide root src.spec) (i : Nat) : ℝ :=
  tailMap s.word (src.raw[i]?.getD default).eval / s.scale

 theorem RawSide.numeric_differences (src : RawSide) (hc : src.check = true)
    {root : Word} (s : ActualSide root src.spec) :
    ∀ i < src.numeric.tails.size, ∀ j < src.numeric.tails.size,
      (src.numeric.delta i j).mem (normalized src s i-normalized src s j) := by
  have hf := src.check_sound hc
  have ha : src.numeric.anchor < src.numeric.tails.size := by rw [← hf.size]; exact hf.anchor_lt
  have h := GraphCertificate.checkPrepared_actual_differences src.numeric s.word
    (fun i => (src.raw[i]?.getD default).eval) hf.prepared ha
    (by rw [hf.shape]; exact s.shape) (by rw [hf.shape]; exact hf.nonneg)
    (fun i hi => (hf.bounds i (by rw [hf.size]; exact hi)).1)
    (fun i hi => (hf.bounds i (by rw [hf.size]; exact hi)).2.1)
    (by rw [hf.parity]; exact sign_of_parity _ _ s.parity)
  simpa only [normalized,hf.anchor,Option.getD_some,ActualSide.scale,ActualSide.anchorValue] using h

 theorem step_endpoint {src : RawSide} {root : Word} (s : ActualSide root src.spec)
    (hr : src.check = true) {e : Nat} (f : StepInfo src e) (p : ℚ) :
    GraphCertificate.sideEndpointValue src.numeric (normalized src s) e p =
      (s.extend f.word f.transition f.lower f.upper hr f.facts).endpoint p/s.scale := by
  let t := s.extend f.word f.transition f.lower f.upper hr f.facts
  have hl : tailMap s.word (src.raw[f.transition.lowerId]?.getD default).eval = t.lowerValue := by
    rw [f.lower_eq,Option.getD_some,Quadratic462.cf_sound _ _ _ f.facts.lower,
      ← tailMap_append,← ActualSide.extend_word s f.word f.transition f.lower f.upper hr f.facts]
    exact t.lower_eq_anchor.symm
  have hh : tailMap s.word (src.raw[f.transition.upperId]?.getD default).eval = t.upperValue := by
    rw [f.upper_eq,Option.getD_some,Quadratic462.cf_sound _ _ _ f.facts.upper,
      ← tailMap_append,← ActualSide.extend_word s f.word f.transition f.lower f.upper hr f.facts]
    exact t.upper_eq_opposite.symm
  simp only [GraphCertificate.sideEndpointValue,f.transition_eq,Option.getD_some,normalized,hl,hh,
    ActualSide.endpoint]
  ring

end Freiman.Local
