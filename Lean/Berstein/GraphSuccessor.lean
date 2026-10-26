import Berstein.GraphState
import Berstein.GraphCertificateFacts
import Berstein.SemanticTransport
import Berstein.SemanticGlobalFacts

set_option maxHeartbeats 1000000

namespace Berstein.GraphMeaning
open HallRay.ContinuedFraction Forbidden31313

private theorem child_bind_some {α β : Type} (a : α) (f : α → Option β) :
    (some a >>= f) = f a := rfl
private theorem child_bind_none {α β : Type} (f : α → Option β) :
    ((none : Option α) >>= f) = none := rfl

/-- Finite semantic witnesses for an active transition. -/
structure ChildFacts (input : GraphCertificate.Input) (data : Data)
    (i e : Nat) (tr : GraphCertificate.Transition) where
  parent : GraphCertificate.Side
  parentMeaning : Side
  child : GraphCertificate.Side
  childMeaning : Side
  rawWord : List Nat
  lower : Quadratic462
  upper : Quadratic462
  parent_eq : input.sides[i]? = some parent
  parentMeaning_eq : data.sides[i]? = some parentMeaning
  transition_eq : parent.transitions[e]? = some tr
  child_eq : input.sides[tr.state.toNat]? = some child
  childMeaning_eq : data.sides[tr.state.toNat]? = some childMeaning
  word_eq : data.extensions[e]? = some rawWord
  lower_eq : parentMeaning.raw[tr.lowerId]? = some lower
  upper_eq : parentMeaning.raw[tr.upperId]? = some upper
  stateBound : childMeaning.state < 5
  parentShape : 0 ≤ parentMeaning.shape.lo
  active : 0 ≤ tr.state
  checked : checkTransition input data i e = true
  facts : TransitionFacts parent parentMeaning tr child childMeaning rawWord lower upper
  digits : ∀ d ∈ rawWord, 1 ≤ d ∧ d ≤ 3

namespace ChildFacts
variable {input : GraphCertificate.Input} {data : Data} {i e : Nat}
  {tr : GraphCertificate.Transition}
def word (f : ChildFacts input data i e tr) : Word := asWord f.rawWord
theorem word_values (f : ChildFacts input data i e tr) : f.word.map Subtype.val = f.rawWord :=
  asWord_values f.rawWord (fun d hd => (f.digits d hd).1)
theorem word_digits (f : ChildFacts input data i e tr) : ∀ a ∈ f.word, a.val ≤ 3 :=
  asWord_digits f.rawWord f.digits

theorem constant_lookup (f : ChildFacts input data i e tr) (hconstant : tr.constant ≠ 0) :
    ∃ k, data.constants[tr.constant]? = some k := by
  obtain ⟨dl,hdl,_⟩ := f.facts.derivativeLo
  obtain ⟨dh,hdh,_⟩ := f.facts.derivativeHi
  have hn : ¬ tr.state < 0 := not_lt.mpr f.active
  have h := f.checked
  cases hk : data.constants[tr.constant]? with
  | some k => exact ⟨k,rfl⟩
  | none =>
    unfold checkTransition at h
    rw [f.parent_eq,child_bind_some,f.parentMeaning_eq,child_bind_some,
      f.transition_eq,child_bind_some,if_neg hn] at h
    dsimp only at h
    rw [f.child_eq,child_bind_some,f.childMeaning_eq,child_bind_some,
      f.word_eq,child_bind_some,f.lower_eq,child_bind_some,f.upper_eq,child_bind_some,
      f.facts.lower,child_bind_some,f.facts.upper,child_bind_some,hdl,child_bind_some,
      hdh,child_bind_some,if_neg hconstant,hk,child_bind_none] at h
    simp only [Option.getD_none,Bool.false_eq_true] at h
end ChildFacts

theorem checkedChild_exists {input : GraphCertificate.Input} {data : Data} {root : Word}
    (s : RealSide input data root) (e : Nat) (he : e < input.extensions)
    (hcheck : check input data = true)
    (hactive : 0 ≤ (s.finite.transitions[e]?.getD default).state)
    (hindex : (s.finite.transitions[e]?.getD default).state.toNat < input.states) :
    Nonempty (ChildFacts input data s.index e (s.finite.transitions[e]?.getD default)) := by
  obtain ⟨x,empty,_,_,pf⟩ := s.facts hcheck
  let tr := s.finite.transitions[e]?.getD default
  let child := input.sides[tr.state.toNat]?.getD default
  let cm := data.sides[tr.state.toNat]?.getD default
  have hd := check_dimensions input data hcheck
  have htr : s.finite.transitions[e]? = some tr :=
    lookup_some_getD _ _ (by rw [pf.transitionSize]; exact he)
  have hc : input.sides[tr.state.toNat]? = some child :=
    lookup_some_getD _ _ (by rw [← hd.1]; exact hindex)
  have hm : data.sides[tr.state.toNat]? = some cm :=
    lookup_some_getD _ _ (by rw [← hd.2.1]; exact hindex)
  have ht := pf.transitions e he
  obtain ⟨w,lo,hi,hw,hlo,hhi,hf⟩ := checkTransition_gets input data s.index e
    s.finite s.meaning tr child cm (s.finite_lookup hcheck) (s.meaning_lookup hcheck)
    htr hactive hc hm ht
  obtain ⟨cx,ce,_,_,cf⟩ := checkSide_gets input data tr.state.toNat child cm hc hm
    (check_sides input data hcheck tr.state.toNat hindex)
  exact ⟨⟨s.finite,s.meaning,child,cm,w,lo,hi,s.finite_lookup hcheck,
    s.meaning_lookup hcheck,htr,hc,hm,hw,hlo,hhi,cf.stateBound,pf.shape.1,hactive,ht,hf,
    check_extension_digits input data hcheck e w hw⟩⟩

/-- Actual extension of a prefix, carrying the checked automaton, parity, and
shape invariants into the successor side. -/
noncomputable def RealSide.extend {input : GraphCertificate.Input} {data : Data}
    {root : Word} (s : RealSide input data root) {e : Nat}
    {tr : GraphCertificate.Transition} (f : ChildFacts input data s.index e tr)
    (hindex : tr.state.toNat < input.states) : RealSide input data root where
  extension := s.extension ++ f.word
  digits := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact s.digits a ha
    · exact f.word_digits a ha
  index := tr.state.toNat
  index_lt := hindex
  state := ⟨f.childMeaning.state,f.stateBound⟩
  state_eq := by simp only [f.childMeaning_eq, Option.getD_some]
  legal := by
    have hm : f.parentMeaning.state = s.state.val := by
      simpa only [f.parentMeaning_eq, Option.getD_some] using s.state_eq
    have hf := f.facts.legal
    rw [← f.word_values, hm] at hf
    have hlegal := after_sound s.state ⟨f.childMeaning.state,f.stateBound⟩ f.word hf
    rw [← List.append_assoc,afterWord_append,s.legal,Option.bind_some]
    exact hlegal
  parity := by
    have hp := f.facts.parity
    have hs : f.parent.parity = decide ((root++s.extension).length%2=1) := by
      simpa only [f.parent_eq, Option.getD_some] using s.parity
    have hw : f.word.length = f.rawWord.length := by simp [ChildFacts.word, asWord]
    simp only [f.child_eq, Option.getD_some]
    rw [hp, hs, ← hw]
    simp only [List.length_append]
    by_cases ha : (root.length+s.extension.length)%2=1 <;>
      by_cases hb : f.word.length%2=1 <;> simp [ha,hb] <;> omega
  shape := by
    have hm : f.parentMeaning.shape.mem (denominatorRatio s.word) := by
      simpa only [f.parentMeaning_eq, Option.getD_some] using s.shape
    have ht := shape_transport s.word f.word f.parentMeaning.shape f.childMeaning.shape hm
      f.parentShape (by simpa only [f.word_values] using f.facts.shapeLo)
      (by simpa only [f.word_values] using f.facts.shapeHi)
    simpa only [f.childMeaning_eq, Option.getD_some, RealSide.word, List.append_assoc] using ht

theorem RealSide.extend_word {input : GraphCertificate.Input} {data : Data}
    {root : Word} (s : RealSide input data root) {e : Nat}
    {tr : GraphCertificate.Transition} (f : ChildFacts input data s.index e tr)
    (hindex : tr.state.toNat < input.states) :
    (s.extend f hindex).word = s.word ++ f.word := by
  simp only [RealSide.word,RealSide.extend,List.append_assoc]

theorem RealSide.extend_anchor {input : GraphCertificate.Input} {data : Data}
    {root : Word} (s : RealSide input data root) {e : Nat}
    {tr : GraphCertificate.Transition} (f : ChildFacts input data s.index e tr)
    (hindex : tr.state.toNat < input.states) :
    (s.extend f hindex).anchorValue = (anchor f.childMeaning.state f.child.parity).eval := by
  simp only [RealSide.anchorValue,RealSide.extend,RealSide.finite,f.child_eq,Option.getD_some]

theorem RealSide.parent_anchor {input : GraphCertificate.Input} {data : Data}
    {root : Word} (s : RealSide input data root) {e : Nat}
    {tr : GraphCertificate.Transition} (f : ChildFacts input data s.index e tr) :
    s.anchorValue = (anchor f.parentMeaning.state f.parent.parity).eval := by
  have hm : f.parentMeaning.state = s.state.val := by
    simpa only [f.parentMeaning_eq,Option.getD_some] using s.state_eq
  simp only [RealSide.anchorValue,RealSide.finite,f.parent_eq,Option.getD_some,hm]

theorem RealSide.extend_derivative {input : GraphCertificate.Input} {data : Data}
    {root : Word} (s : RealSide input data root) {e : Nat}
    {tr : GraphCertificate.Transition} (f : ChildFacts input data s.index e tr)
    (hindex : tr.state.toNat < input.states) :
    tr.derivative.mem ((s.extend f hindex).scale/s.scale) := by
  obtain ⟨dl,hdl,hlomem⟩ := f.facts.derivativeLo
  obtain ⟨dh,hdh,hhimem⟩ := f.facts.derivativeHi
  have hparent : f.parentMeaning.shape.mem (denominatorRatio s.word) := by
    simpa only [f.parentMeaning_eq,Option.getD_some] using s.shape
  have hx : 0 ≤ (anchor f.parentMeaning.state f.parent.parity).eval := by
    rw [← s.parent_anchor f]
    exact s.anchorValue_mem.1
  have hy : 0 ≤ (anchor f.childMeaning.state f.child.parity).eval :=
    (anchor_unit ⟨f.childMeaning.state,f.stateBound⟩ f.child.parity).1
  have ht := derivative_transport s.word f.word f.parentMeaning.shape tr.derivative
    (anchor f.parentMeaning.state f.parent.parity) (anchor f.childMeaning.state f.child.parity)
    dl dh hx hy hparent f.parentShape (by simpa only [f.word_values] using hdl)
    (by simpa only [f.word_values] using hdh) hlomem hhimem
  simpa only [RealSide.scale,s.extend_word f hindex,s.extend_anchor f hindex,s.parent_anchor f] using ht

theorem RealSide.extend_derivative_pos {input : GraphCertificate.Input} {data : Data}
    {root : Word} (s : RealSide input data root) {e : Nat}
    {tr : GraphCertificate.Transition} (f : ChildFacts input data s.index e tr)
    (hindex : tr.state.toNat < input.states) :
    0 < (s.extend f hindex).scale/s.scale := div_pos (s.extend f hindex).scale_pos s.scale_pos

theorem RealSide.extend_endpoint {input : GraphCertificate.Input} {data : Data}
    {root : Word} (s : RealSide input data root) {e : Nat}
    {tr : GraphCertificate.Transition} (f : ChildFacts input data s.index e tr)
    (hindex : tr.state.toNat < input.states) (p : ℚ) :
    GraphCertificate.sideEndpointValue s.finite s.normalizedValue e p =
      (s.extend f hindex).endpoint (p : ℝ)/s.scale := by
  have hf : TransitionFacts s.finite s.meaning tr (s.extend f hindex).finite
      (s.extend f hindex).meaning f.rawWord f.lower f.upper := by
    simpa only [RealSide.finite,RealSide.meaning,RealSide.extend,f.parent_eq,
      f.parentMeaning_eq,f.child_eq,f.childMeaning_eq,Option.getD_some] using f.facts
  exact s.transition_endpoint (s.extend f hindex) e tr f.rawWord f.lower f.upper
    (by simpa only [RealSide.finite,f.parent_eq,Option.getD_some] using f.transition_eq)
    (by simpa only [RealSide.meaning,f.parentMeaning_eq,Option.getD_some] using f.lower_eq)
    (by simpa only [RealSide.meaning,f.parentMeaning_eq,Option.getD_some] using f.upper_eq)
    f.word_values (s.extend_word f hindex) hf p

theorem RealSide.extend_constant {input : GraphCertificate.Input} {data : Data}
    {root : Word} (s : RealSide input data root) {e : Nat}
    {tr : GraphCertificate.Transition} (f : ChildFacts input data s.index e tr)
    (hindex : tr.state.toNat < input.states) (hconstant : tr.constant ≠ 0)
    (k : Quadratic462) (hk : data.constants[tr.constant]? = some k) :
    (s.extend f hindex).scale/s.scale = k.eval := by
  have hc := checkTransition_constant_facts input data s.index e f.parent f.parentMeaning
    tr f.child f.childMeaning f.rawWord f.lower f.upper k f.parent_eq f.parentMeaning_eq
    f.transition_eq f.active f.child_eq f.childMeaning_eq f.word_eq f.lower_eq f.upper_eq
    f.checked hconstant hk
  have hx : 0 ≤ (anchor f.parentMeaning.state f.parent.parity).eval := by
    rw [← s.parent_anchor f]
    exact s.anchorValue_mem.1
  have hy : 0 ≤ (anchor f.childMeaning.state f.child.parity).eval :=
    (anchor_unit ⟨f.childMeaning.state,f.stateBound⟩ f.child.parity).1
  have he := derivative_constant s.word f.word (anchor f.parentMeaning.state f.parent.parity)
    (anchor f.childMeaning.state f.child.parity) k f.parentMeaning.shape.lo hx hy f.parentShape
    (by simpa only [f.word_values] using hc.1) (by simpa only [f.word_values] using hc.2)
  simpa only [RealSide.scale,s.extend_word f hindex,s.extend_anchor f hindex,s.parent_anchor f] using he

/-- Recover the common band parameter from any point between two positively
oriented affine endpoints. -/
theorem affine_parameter {a width lo hi x : ℝ} (hw : 0 < width)
    (hx : x ∈ Set.Icc (a+lo*width) (a+hi*width)) :
    ∃ p ∈ Set.Icc lo hi, x = a+p*width := by
  refine ⟨(x-a)/width,⟨?_,?_⟩,?_⟩
  · apply (le_div_iff₀ hw).mpr
    linarith [hx.1]
  · apply (div_le_iff₀ hw).mpr
    linarith [hx.2]
  · rw [div_mul_cancel₀ _ (ne_of_gt hw)]
    ring

noncomputable def sumEndpoint {input : GraphCertificate.Input} {data : Data}
    (left : RealSide input data prefix322) (right : RealSide input data prefix431) (p : ℝ) : ℝ :=
  4+left.endpoint p+right.endpoint p

theorem sumEndpoint_affine {input : GraphCertificate.Input} {data : Data}
    (left : RealSide input data prefix322) (right : RealSide input data prefix431) (p : ℝ) :
    sumEndpoint left right p = 4+left.lowerValue+right.lowerValue+
      p*((left.upperValue-left.lowerValue)+(right.upperValue-right.lowerValue)) := by
  unfold sumEndpoint RealSide.endpoint
  ring

theorem sumEndpoint_parameter {input : GraphCertificate.Input} {data : Data}
    (left : RealSide input data prefix322) (right : RealSide input data prefix431)
    {lo hi x : ℝ} (hl : left.lowerValue < left.upperValue)
    (hx : x ∈ Set.Icc (sumEndpoint left right lo) (sumEndpoint left right hi)) :
    ∃ p ∈ Set.Icc lo hi, x = sumEndpoint left right p := by
  simp only [sumEndpoint_affine] at hx ⊢
  exact affine_parameter (by linarith [right.lower_le_upper]) hx

theorem children_endpoint {input : GraphCertificate.Input} {data : Data} {alive : ByteArray}
    (s : RealState input data alive) {el er : Nat}
    {tl tr : GraphCertificate.Transition}
    (fl : ChildFacts input data s.left.index el tl)
    (fr : ChildFacts input data s.right.index er tr)
    (hli : tl.state.toNat < input.states) (hri : tr.state.toNat < input.states) (p : ℚ) :
    s.normalizedEndpoint ⟨el,er,p⟩ =
      (sumEndpoint (s.left.extend fl hli) (s.right.extend fr hri) p-4)/s.left.scale := by
  dsimp only [RealState.normalizedEndpoint,GraphCertificate.endpointValue]
  rw [s.left.extend_endpoint fl hli p,s.right.extend_endpoint fr hri p]
  unfold sumEndpoint
  field_simp [ne_of_gt s.left.scale_pos,ne_of_gt s.right.scale_pos]
  <;> ring

theorem RealState.geometry_lt {input : GraphCertificate.Input} {data : Data} {alive : ByteArray}
    (s : RealState input data alive) : s.geometry < input.states*input.states := by
  change s.left.index*input.states+s.right.index < input.states*input.states
  calc
    _ < s.left.index*input.states+input.states := Nat.add_lt_add_left s.right.index_lt _
    _ = (s.left.index+1)*input.states := by ring
    _ ≤ input.states*input.states := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt s.left.index_lt)

/-- Once a checked record covers the actual point and its two actual child
prefixes have been transported, the checked image bins and merged bands supply
an adopted successor state. -/
theorem adopted_successor {input : GraphCertificate.Input} {data : Data} {alive : ByteArray}
    (s : RealState input data alive) (hcheck : check input data = true)
    (v : GraphCertificate.Vertex)
    (hv : GraphCertificate.checkVertex input alive s.geometry s.bin v = true)
    (left : RealSide input data prefix322) (right : RealSide input data prefix431)
    (hlindex : left.index =
      (s.left.finite.transitions[(input.pairs[v.pair]?.getD default).left]?.getD default).state.toNat)
    (hrindex : right.index =
      (s.right.finite.transitions[(input.pairs[v.pair]?.getD default).right]?.getD default).state.toNat)
    (hl : (s.left.finite.transitions[(input.pairs[v.pair]?.getD default).left]?.getD default).derivative.mem
      (left.scale/s.left.scale))
    (hr : (s.right.finite.transitions[(input.pairs[v.pair]?.getD default).right]?.getD default).derivative.mem
      (right.scale/s.right.scale))
    (hconstant :
      (s.left.finite.transitions[(input.pairs[v.pair]?.getD default).left]?.getD default).constant ≠ 0 →
      (s.left.finite.transitions[(input.pairs[v.pair]?.getD default).left]?.getD default).constant =
        (s.right.finite.transitions[(input.pairs[v.pair]?.getD default).right]?.getD default).constant →
      right.scale/s.right.scale = left.scale/s.left.scale)
    (hnext : CylinderCover.Extends s.pair
      {leftExtension:=left.extension,rightExtension:=right.extension,leftDigits:=left.digits,
       rightDigits:=right.digits,leftState:=left.state,rightState:=right.state,
       leftLegal:=left.legal,rightLegal:=right.legal,leftAnchor:=left.anchorValue,
       rightAnchor:=right.anchorValue,leftAnchor_mem:=left.anchorValue_mem,
       rightAnchor_mem:=right.anchorValue_mem})
    (x : ℝ) (hx : x ∈ Set.Icc (sumEndpoint left right v.band.lo)
      (sumEndpoint left right v.band.hi)) :
    ∃ t : RealState input data alive, s.Next t ∧ x ∈ t.target := by
  have hs := GraphCertificate.checkVertex_structure input alive s.geometry s.bin v hv
  simp only [s.geometry_left,s.geometry_right] at hs
  rcases hs with ⟨hpair,hfirstBound,hlastBound,hele,here,hl0,hllt,hr0,hrlt,hspine,hmapped,hmerged⟩
  obtain ⟨p,hp,hxp⟩ := sumEndpoint_parameter left right left.lower_lt_upper hx
  obtain ⟨type,ht,hselected,hpband⟩ :=
    GraphCertificate.checkMergedBand_sound input v hmerged p hp
  have hg := check_dimensions input data hcheck
  have hcuts : ∀ k ≤ input.bins, (input.grid[k]?.getD default).mem (exactCut input k) := by
    intro k hk
    have hki : k < input.grid.size := by omega
    have hklookup := lookup_some_getD input.grid k hki
    have hh := check_grid_cut input data hcheck k hki _ hklookup
    exact ⟨Rat.cast_mono hh.1,Rat.cast_mono hh.2.1⟩
  obtain ⟨k,hfirst,hlast,hklo,hkhi⟩ := GraphCertificate.mappedBinsCheck_cover input s.bin
    (s.left.finite.transitions[(input.pairs[v.pair]?.getD default).left]?.getD default)
    (s.right.finite.transitions[(input.pairs[v.pair]?.getD default).right]?.getD default)
    v hmapped hfirstBound hlastBound (exactCut input) hcuts
    (s.right.scale/s.left.scale) (left.scale/s.left.scale) (right.scale/s.right.scale)
    s.ratio s.bin_lt hl hr (div_pos left.scale_pos s.left.scale_pos) hconstant
  have hratio : (s.right.scale/s.left.scale)*(right.scale/s.right.scale)/(left.scale/s.left.scale) =
      right.scale/left.scale := by
    field_simp [ne_of_gt s.left.scale_pos,ne_of_gt s.right.scale_pos,ne_of_gt left.scale_pos]
    <;> ring
  rw [hratio] at hklo hkhi
  have hk : k < input.bins := by omega
  have hbalance : right.scale/left.scale ∈ Set.Icc (1/10000 : ℝ) 10000 := by
    have hlo := check_grid_cut input data hcheck k (by omega) _
      (lookup_some_getD input.grid k (by omega))
    have hhi := check_grid_cut input data hcheck (k+1) (by omega) _
      (lookup_some_getD input.grid (k+1) (by omega))
    have hloReal : (1/10000 : ℝ) ≤ exactCut input k := by
      have hc : ((1/10000 : ℚ) : ℝ) ≤ exactCut input k := Rat.cast_mono hlo.2.2.1
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hc
    have hhiReal : exactCut input (k+1) ≤ (10000 : ℝ) := by
      have hc : exactCut input (k+1) ≤ ((10000 : ℚ) : ℝ) := Rat.cast_mono hhi.2.2.2
      simpa only [Rat.cast_ofNat] using hc
    constructor
    · exact hloReal.trans hklo
    · exact hkhi.trans hhiReal
  have hband := check_band_unit input data hcheck type (by omega) _
    (lookup_some_getD input.bands type (by omega))
  have ha := GraphCertificate.checkVertex_destinations input alive s.geometry s.bin v hv
    type ht hselected k hfirst hlast
  simp only [s.geometry_left,s.geometry_right,← hlindex,← hrindex] at ha
  let t : RealState input data alive :=
    ⟨left,right,k,hk,type,ht,ha,⟨hklo,hkhi⟩,hbalance,hband⟩
  refine ⟨t,hnext,?_⟩
  change sumEndpoint left right (input.bands[type]?.getD default).lo ≤ x ∧
    x ≤ sumEndpoint left right (input.bands[type]?.getD default).hi
  rw [hxp]
  simp only [sumEndpoint_affine]
  constructor <;> nlinarith [left.lower_le_upper,right.lower_le_upper,hpband.1,hpband.2]

/-- The actual successor property of the fully checked finite table. All
numerical assumptions are outputs of executable checks with proved semantics. -/
theorem verified_successor {input : GraphCertificate.Input} {data : Data} {alive : ByteArray}
    (hcheck : check input data = true)
    (hprepared : ∀ i < input.states,
      GraphCertificate.checkPrepared (input.sides[i]?.getD default) = true)
    (cells : Nat → List GraphCertificate.Cell)
    (hgeometry : ∀ g < input.states*input.states,
      GraphCertificate.checkGeometry input alive g (cells g) = true)
    (s : RealState input data alive) (x : ℝ) (hx : x ∈ s.target) :
    ∃ t : RealState input data alive, s.Next t ∧ x ∈ t.target := by
  have hsbin := s.bin_lt
  obtain ⟨cell,hcell,hbin,haccepted⟩ := GraphCertificate.checkGeometry_cell input alive s.geometry
    (cells s.geometry) (hgeometry s.geometry s.geometry_lt) s.bin s.type s.bin_lt s.type_lt s.adopted
  have hg := check_dimensions input data hcheck
  have hS : (QBounds.mk (input.grid[cell.bin]?.getD default).lo
      (input.grid[cell.bin+1]?.getD default).hi).mem (s.right.scale/s.left.scale) := by
    rw [hbin]
    have hlo := check_grid_cut input data hcheck s.bin (by omega) _
      (lookup_some_getD input.grid s.bin (by omega))
    have hhi := check_grid_cut input data hcheck (s.bin+1) (by omega) _
      (lookup_some_getD input.grid (s.bin+1) (by omega))
    exact ⟨(Rat.cast_mono hlo.1).trans s.ratio.1,
      s.ratio.2.trans (Rat.cast_mono hhi.2.1)⟩
  have hl := s.left.numeric_differences hcheck (hprepared s.left.index s.left.index_lt)
  have hr := s.right.numeric_differences hcheck (hprepared s.right.index s.right.index_lt)
  obtain ⟨j,hj,hv,hcovered⟩ := GraphCertificate.checkCell_coverage input alive s.geometry cell
    s.left.normalizedValue s.right.normalizedValue (s.right.scale/s.left.scale)
    (by simpa only [s.geometry_left] using hl)
    (by simpa only [s.geometry_right] using hr) hS haccepted s.type s.type_lt
    (by simpa only [hbin] using s.adopted) ((x-4)/s.left.scale)
    (by simpa only [s.geometry_left,s.geometry_right,RealState.normalizedEndpoint]
      using s.normalized_target_mem hcheck hx)
  let v := cell.vertices[j]?.getD default
  change GraphCertificate.checkVertex input alive s.geometry cell.bin v = true at hv
  rw [hbin] at hv
  have hs := GraphCertificate.checkVertex_structure input alive s.geometry s.bin v hv
  simp only [s.geometry_left,s.geometry_right] at hs
  rcases hs with ⟨hpair,hfirst,hlast,hele,here,hl0,hllt,hr0,hrlt,hspine,hmapped,hmerged⟩
  let pair := input.pairs[v.pair]?.getD default
  let tl := s.left.finite.transitions[pair.left]?.getD default
  let tr := s.right.finite.transitions[pair.right]?.getD default
  have hli : tl.state.toNat < input.states := by dsimp only [tl,pair,RealSide.finite]; omega
  have hri : tr.state.toNat < input.states := by dsimp only [tr,pair,RealSide.finite]; omega
  obtain ⟨lx,le,_,_,lf⟩ := s.left.facts hcheck
  obtain ⟨rx,re,_,_,rf⟩ := s.right.facts hcheck
  have hel : pair.left < input.extensions := by rw [← lf.transitionSize]; exact hele
  have her : pair.right < input.extensions := by rw [← rf.transitionSize]; exact here
  obtain ⟨fl⟩ := checkedChild_exists s.left pair.left hel hcheck hl0 hli
  obtain ⟨fr⟩ := checkedChild_exists s.right pair.right her hcheck hr0 hri
  let left := s.left.extend fl hli
  let right := s.right.extend fr hri
  have hc : tl.constant ≠ 0 → tl.constant = tr.constant →
      right.scale/s.right.scale = left.scale/s.left.scale := by
    intro hn heq
    obtain ⟨k,hk⟩ := fl.constant_lookup hn
    have hkr : data.constants[tr.constant]? = some k := by rw [← heq]; exact hk
    have hnr : tr.constant ≠ 0 := by rw [← heq]; exact hn
    rw [s.right.extend_constant fr hri hnr k hkr,s.left.extend_constant fl hli hn k hk]
  have hpairmem : pair ∈ input.pairs := Array.mem_of_getElem?
    (lookup_some_getD input.pairs v.pair hpair)
  obtain ⟨a,b,ha,hb,hprogress⟩ := check_pair_extension input data hcheck pair hpairmem
  have hea : fl.rawWord = a := Option.some.inj (fl.word_eq.symm.trans ha)
  have heb : fr.rawWord = b := Option.some.inj (fr.word_eq.symm.trans hb)
  have hprogress' : 0 < fl.word.length+fr.word.length := by
    simpa only [ChildFacts.word,asWord,List.length_map,hea,heb] using hprogress
  have hnext : CylinderCover.Extends s.pair
      {leftExtension:=left.extension,rightExtension:=right.extension,leftDigits:=left.digits,
       rightDigits:=right.digits,leftState:=left.state,rightState:=right.state,
       leftLegal:=left.legal,rightLegal:=right.legal,leftAnchor:=left.anchorValue,
       rightAnchor:=right.anchorValue,leftAnchor_mem:=left.anchorValue_mem,
       rightAnchor_mem:=right.anchorValue_mem} := ⟨fl.word,fr.word,rfl,rfl,hprogress'⟩
  have hcovered' : (x-4)/s.left.scale ∈ Set.Icc
      (s.normalizedEndpoint ⟨pair.left,pair.right,v.band.lo⟩)
      (s.normalizedEndpoint ⟨pair.left,pair.right,v.band.hi⟩) := by
    simpa only [s.geometry_left,s.geometry_right,GraphCertificate.vertexLower,
      GraphCertificate.vertexUpper,RealState.normalizedEndpoint] using hcovered
  rw [children_endpoint s fl fr hli hri v.band.lo,
      children_endpoint s fl fr hli hri v.band.hi] at hcovered'
  have hxchild : x ∈ Set.Icc (sumEndpoint left right v.band.lo)
      (sumEndpoint left right v.band.hi) := by
    constructor
    · have h := (div_le_div_iff_of_pos_right s.left.scale_pos).mp hcovered'.1
      linarith
    · have h := (div_le_div_iff_of_pos_right s.left.scale_pos).mp hcovered'.2
      linarith
  exact adopted_successor s hcheck v hv left right rfl rfl
    (s.left.extend_derivative fl hli) (s.right.extend_derivative fr hri) hc hnext x hxchild

end Berstein.GraphMeaning
