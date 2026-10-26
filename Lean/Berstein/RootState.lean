import Berstein.GraphState
import Berstein.RootCheck
import Berstein.RootFacts
import Berstein.IntervalCover

set_option maxHeartbeats 2000000

namespace Berstein.GraphMeaning
open HallRay.ContinuedFraction Forbidden31313

structure RootConditions (input : GraphCertificate.Input) (data : Data) (alive : ByteArray) : Prop where
  dimensions : input.states = 22 ∧ input.bins = 310 ∧ input.types = 32 ∧ input.firstExponent = -155
  available : 17 < input.sides.size ∧ 17 < data.sides.size ∧ 136 < input.grid.size
  parities : (input.sides[8]?.getD default).parity = true ∧
    (input.sides[17]?.getD default).parity = true
  states : (data.sides[8]?.getD default).state = 0 ∧ (data.sides[17]?.getD default).state = 2
  leftShape : (data.sides[8]?.getD default).shape.lo ≤ 7/17 ∧
    7/17 ≤ (data.sides[8]?.getD default).shape.hi
  rightShape : (data.sides[17]?.getD default).shape.lo ≤ 13/17 ∧
    13/17 ≤ (data.sides[17]?.getD default).shape.hi
  bands : ∀ j < 25, input.bands[j+3]? =
    some ⟨(((j+3 : Nat) : ℚ)-1)/32, (((j+3 : Nat) : ℚ)+1)/32⟩ ∧
    GraphCertificate.adopted input alive 193 135 (j+3) = true

theorem checkRoots_conditions (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (h : checkRoots input data alive = true) : RootConditions input data alive := by
  simp only [checkRoots, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨ha,hb⟩,hp⟩,hc⟩,hd⟩,he⟩,_⟩,hg⟩
  exact ⟨ha,hb,hp,hc,hd,he,hg⟩

noncomputable def rootLeft (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (h : RootConditions input data alive) : RealSide input data prefix322 where
  extension := []
  digits := by simp
  index := 8
  index_lt := by rw [h.dimensions.1]; decide
  state := 0
  state_eq := h.states.1
  legal := by simpa using afterWord_322
  parity := by simpa [prefix322] using h.parities.1
  shape := by
    simpa only [QBounds.mem, List.append_nil, prefix322_shape] using
      (show ((data.sides[8]?.getD default).shape.lo : ℝ) ≤ 7/17 ∧
        (7/17 : ℝ) ≤ (data.sides[8]?.getD default).shape.hi by
        have hc : ((data.sides[8]?.getD default).shape.lo : ℝ) ≤ ((7/17 : ℚ) : ℝ) ∧
            ((7/17 : ℚ) : ℝ) ≤ (data.sides[8]?.getD default).shape.hi :=
          ⟨Rat.cast_le.mpr h.leftShape.1, Rat.cast_le.mpr h.leftShape.2⟩
        simpa only [Rat.cast_div, Rat.cast_ofNat] using hc)

noncomputable def rootRight (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (h : RootConditions input data alive) : RealSide input data prefix431 where
  extension := []
  digits := by simp
  index := 17
  index_lt := by rw [h.dimensions.1]; decide
  state := 2
  state_eq := h.states.2
  legal := by simpa using afterWord_431
  parity := by simpa [prefix431] using h.parities.2
  shape := by
    simpa only [QBounds.mem, List.append_nil, prefix431_shape] using
      (show ((data.sides[17]?.getD default).shape.lo : ℝ) ≤ 13/17 ∧
        (13/17 : ℝ) ≤ (data.sides[17]?.getD default).shape.hi by
        have hc : ((data.sides[17]?.getD default).shape.lo : ℝ) ≤ ((13/17 : ℚ) : ℝ) ∧
            ((13/17 : ℚ) : ℝ) ≤ (data.sides[17]?.getD default).shape.hi :=
          ⟨Rat.cast_le.mpr h.rightShape.1, Rat.cast_le.mpr h.rightShape.2⟩
        simpa only [Rat.cast_div, Rat.cast_ofNat] using hc)

theorem root_ratio_eq (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (h : RootConditions input data alive) :
    (rootRight input data alive h).scale/(rootLeft input data alive h).scale = S := by
  simp only [RealSide.scale, RealSide.word, RealSide.anchorValue, RealSide.finite,
    rootRight, rootLeft, List.append_nil]
  rw [h.parities.1, h.parities.2]
  simpa only [anchor, ↓reduceIte, upper_eval] using root_scale_ratio

noncomputable def rootState (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (h : RootConditions input data alive) (j : Nat) (hj : j < 25) : RealState input data alive where
  left := rootLeft input data alive h
  right := rootRight input data alive h
  bin := 135
  bin_lt := by rw [h.dimensions.2.1]; decide
  type := j+3
  type_lt := by rw [h.dimensions.2.2.1]; omega
  adopted := by simpa [rootLeft,rootRight,h.dimensions.1] using (h.bands j hj).2
  ratio := by
    rw [root_ratio_eq]
    have hs := S_mem_bin_minus20
    norm_num [exactCut,h.dimensions.2.2.2]
    norm_num at hs
    exact hs
  balance := by
    rw [root_ratio_eq]
    have hl : (1/10000 : ℝ) ≤ (50/51)^20 := by norm_num
    have hh : (50/51 : ℝ)^19 ≤ 10000 := by norm_num
    exact ⟨hl.trans S_mem_bin_minus20.1,S_mem_bin_minus20.2.trans hh⟩
  bandUnit := by
    rw [(h.bands j hj).1]
    simp only [Option.getD_some]
    have hj' : (j : ℚ) ≤ 24 := by exact_mod_cast (show j ≤ 24 by omega)
    have hpos : (0 : ℚ) ≤ j := by positivity
    push_cast
    constructor <;> (try constructor) <;> linarith

theorem root_hull_sums :
    CylinderCover.lowerValue prefix322 0 + CylinderCover.lowerValue prefix431 2 = L ∧
    CylinderCover.upperValue prefix322 0 + CylinderCover.upperValue prefix431 2 = H := by
  have hl := anchor_min_opposite_max prefix322 0 true (by decide)
  have hr := anchor_min_opposite_max prefix431 2 true (by decide)
  have hl₀ : CylinderCover.lowerValue prefix322 0 = tailMap prefix322 (exactUpper 0) := by
    simpa only [CylinderCover.lowerValue, anchor, ↓reduceIte, upper_eval (0 : State)] using hl.1.symm
  have hr₀ : CylinderCover.lowerValue prefix431 2 = tailMap prefix431 (exactUpper 2) := by
    simpa only [CylinderCover.lowerValue, anchor, ↓reduceIte, upper_eval (2 : State)] using hr.1.symm
  have hl₁ : CylinderCover.upperValue prefix322 0 = tailMap prefix322 (exactLower 0) := by
    simpa only [CylinderCover.upperValue, opposite, ↓reduceIte, lower_eval (0 : State)] using hl.2.symm
  have hr₁ : CylinderCover.upperValue prefix431 2 = tailMap prefix431 (exactLower 2) := by
    simpa only [CylinderCover.upperValue, opposite, ↓reduceIte, lower_eval (2 : State)] using hr.2.symm
  rw [hl₀,hr₀,hl₁,hr₁]
  exact ⟨root_lower_sum,root_upper_sum⟩

theorem root_endpoint (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (h : RootConditions input data alive) (j : Nat) (hj : j < 25) (p : ℝ) :
    (rootState input data alive h j hj).endpoint p = 4+L+p*(H-L) := by
  change 4+((1-p)*CylinderCover.lowerValue prefix322 0+p*CylinderCover.upperValue prefix322 0)+
    ((1-p)*CylinderCover.lowerValue prefix431 2+p*CylinderCover.upperValue prefix431 2) = _
  calc
    _ = 4+(1-p)*(CylinderCover.lowerValue prefix322 0+CylinderCover.lowerValue prefix431 2)+
      p*(CylinderCover.upperValue prefix322 0+CylinderCover.upperValue prefix431 2) := by ring
    _ = _ := by rw [root_hull_sums.1,root_hull_sums.2]; ring

theorem roots_cover_filled (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (h : RootConditions input data alive) {x : ℝ} (hx : x ∈ Set.Icc filledLower filledUpper) :
    ∃ j, ∃ hj : j < 25, x ∈ (rootState input data alive h j hj).target := by
  have hx' : x-4 ∈ Set.Icc (L+(H-L)/16) (L+7*(H-L)/8) := by
    dsimp [filledLower,filledUpper] at hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨I,hI,hxI⟩ := IntervalCover.rootBands_affine_cover L H (x-4) L_lt_H hx'
  unfold IntervalCover.rootBands at hI
  have hmem : ∃ j : ℕ, j ∈ List.range 25 ∧
      (⟨((j : ℚ)+2)/32, ((j : ℚ)+4)/32⟩ : IntervalCover.QInterval) = I :=
    List.mem_map.mp hI
  obtain ⟨j,hj,rfl⟩ := hmem
  have hj' : j < 25 := List.mem_range.mp hj
  refine ⟨j,hj',?_⟩
  change (rootState input data alive h j hj').endpoint
      ((input.bands[j+3]?.getD default).lo : ℝ) ≤ x ∧
    x ≤ (rootState input data alive h j hj').endpoint
      ((input.bands[j+3]?.getD default).hi : ℝ)
  rw [(h.bands j hj').1]
  simp only [Option.getD_some,root_endpoint]
  dsimp at hxI
  push_cast at hxI ⊢
  constructor <;> nlinarith [hxI.1,hxI.2]

theorem filling_of_checked_roots_and_successors
    (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (hr : checkRoots input data alive = true)
    (hcovers : ∀ s : RealState input data alive, ∀ x ∈ s.target,
      ∃ t : RealState input data alive, RealState.Next s t ∧ x ∈ t.target) :
    SumFilling (filledLower-4) (filledUpper-4) := by
  intro z hz
  have h := checkRoots_conditions input data alive hr
  have hx : 4+z ∈ Set.Icc filledLower filledUpper := by
    constructor <;> linarith [hz.1,hz.2]
  obtain ⟨j,hj,ht⟩ := roots_cover_filled input data alive h hx
  obtain ⟨a,ha,b,hb,he⟩ := RealState.realizes hcovers (rootState input data alive h j hj) ht
  exact ⟨a,ha,b,hb,by linarith⟩

end Berstein.GraphMeaning
