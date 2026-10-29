import Freiman.GraphState

namespace Freiman.GraphMeaning
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction Forbidden31313
variable [Setup]

noncomputable def sumEndpoint {input : GraphCertificate.Input} {data : Data}
    (left : RealSide input data Setup.left) (right : RealSide input data Setup.right) (p : ℝ) : ℝ :=
  Setup.center+left.endpoint p+right.endpoint p

theorem sumEndpoint_affine {input : GraphCertificate.Input} {data : Data}
    (left : RealSide input data Setup.left) (right : RealSide input data Setup.right) (p : ℝ) :
    sumEndpoint left right p = Setup.center+left.lowerValue+right.lowerValue+
      p*((left.upperValue-left.lowerValue)+(right.upperValue-right.lowerValue)) := by
  unfold sumEndpoint RealSide.endpoint
  ring

theorem sumEndpoint_parameter {input : GraphCertificate.Input} {data : Data}
    (left : RealSide input data Setup.left) (right : RealSide input data Setup.right)
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
      (sumEndpoint (s.left.extend fl hli) (s.right.extend fr hri) p-Setup.center)/s.left.scale := by
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
    (left : RealSide input data Setup.left) (right : RealSide input data Setup.right)
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
    (by simpa only [hbin] using s.adopted) ((x-Setup.center)/s.left.scale)
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
  have hcovered' : (x-Setup.center)/s.left.scale ∈ Set.Icc
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

end Freiman.GraphMeaning
