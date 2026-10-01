import Berstein.SemanticCore

set_option maxHeartbeats 3000000

namespace Berstein.GraphMeaning
open HallRay.ContinuedFraction

private theorem bind_some_direct {α β : Type} (a : α) (f : α → Option β) :
    (some a >>= f) = f a := rfl
private theorem bind_none_direct {α β : Type} (f : α → Option β) :
    ((none : Option α) >>= f) = none := rfl

/-- The locally checked facts, before the fractional-linear interpolation
step extends the two shape-corner bounds to the whole shape interval. -/
structure TransitionFacts (s : GraphCertificate.Side) (m : Side)
    (tr : GraphCertificate.Transition) (c : GraphCertificate.Side) (cm : Side)
    (w : List Nat) (lo hi : Quadratic462) : Prop where
  legal : after m.state w = some cm.state
  parity : c.parity = (s.parity != decide (w.length % 2 = 1))
  lower : Quadratic462.cf w (anchor cm.state c.parity) = some lo
  upper : Quadratic462.cf w (opposite cm.state c.parity) = some hi
  shapeLo : cm.shape.lo ≤ shapeImage w m.shape.lo ∧ shapeImage w m.shape.lo ≤ cm.shape.hi
  shapeHi : cm.shape.lo ≤ shapeImage w m.shape.hi ∧ shapeImage w m.shape.hi ≤ cm.shape.hi
  derivativeLo : ∃ dl, derivativeAt w (anchor m.state s.parity)
    (anchor cm.state c.parity) m.shape.lo = some dl ∧ tr.derivative.mem dl.eval
  derivativeHi : ∃ dh, derivativeAt w (anchor m.state s.parity)
    (anchor cm.state c.parity) m.shape.hi = some dh ∧ tr.derivative.mem dh.eval
  derivativePositive : 0 < tr.derivative.lo

 theorem checkTransition_facts (input : GraphCertificate.Input) (data : Data) (i e : Nat)
    (s : GraphCertificate.Side) (m : Side) (tr : GraphCertificate.Transition)
    (c : GraphCertificate.Side) (cm : Side) (w : List Nat) (lo hi : Quadratic462)
    (hs : input.sides[i]? = some s) (hm : data.sides[i]? = some m)
    (htr : s.transitions[e]? = some tr) (hactive : 0 ≤ tr.state)
    (hc : input.sides[tr.state.toNat]? = some c)
    (hcm : data.sides[tr.state.toNat]? = some cm)
    (hw : data.extensions[e]? = some w)
    (hlo : m.raw[tr.lowerId]? = some lo) (hhi : m.raw[tr.upperId]? = some hi)
    (h : checkTransition input data i e = true) : TransitionFacts s m tr c cm w lo hi := by
  have hnot : ¬ tr.state < 0 := not_lt.mpr hactive
  unfold checkTransition at h
  rw [hs, bind_some_direct, hm, bind_some_direct, htr, bind_some_direct,
    if_neg hnot] at h
  dsimp only at h
  rw [hc, bind_some_direct, hcm, bind_some_direct,
    hw, bind_some_direct, hlo, bind_some_direct, hhi, bind_some_direct] at h
  cases hlv : Quadratic462.cf w (anchor cm.state c.parity) with
  | none => simp [hlv] at h
  | some lv =>
    cases hhv : Quadratic462.cf w (opposite cm.state c.parity) with
    | none => simp [hlv, hhv] at h
    | some hv =>
      cases hdl : derivativeAt w (anchor m.state s.parity) (anchor cm.state c.parity) m.shape.lo with
      | none => simp [hlv, hhv, hdl] at h
      | some dl =>
        cases hdh : derivativeAt w (anchor m.state s.parity) (anchor cm.state c.parity) m.shape.hi with
        | none => simp [hlv, hhv, hdl, hdh] at h
        | some dh =>
          simp only [hlv, hhv, hdl, hdh, Option.pure_def, bind_some_direct] at h
          have hbasic : (decide (after m.state w = some cm.state) &&
              (c.parity == (s.parity != decide (w.length % 2 = 1))) &&
              decide (lv = lo) && decide (hv = hi) &&
              decide (cm.shape.lo ≤ shapeImage w m.shape.lo ∧ shapeImage w m.shape.lo ≤ cm.shape.hi) &&
              decide (cm.shape.lo ≤ shapeImage w m.shape.hi ∧ shapeImage w m.shape.hi ≤ cm.shape.hi) &&
              contains tr.derivative dl && contains tr.derivative dh &&
              decide (0 < tr.derivative.lo)) = true := by
            split at h
            · exact h
            · cases hk : data.constants[tr.constant]? with
              | none => simp [hk] at h
              | some k =>
                simp only [hk, Option.pure_def, bind_some_direct, Option.getD_some, Bool.and_eq_true] at h
                exact by simpa only [Bool.and_eq_true] using h.1.1
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbasic
          rcases hbasic with ⟨⟨⟨⟨⟨⟨⟨⟨hlegal,hparity⟩,heql⟩,heqh⟩,hsl⟩,hsh⟩,hdlmem⟩,hdhmem⟩,hpos⟩
          subst lv; subst hv
          exact ⟨hlegal,hparity,hlv,hhv,hsl,hsh,
            ⟨dl,hdl,contains_sound _ _ hdlmem⟩,
            ⟨dh,hdh,contains_sound _ _ hdhmem⟩,hpos⟩

structure SideFacts (input : GraphCertificate.Input) (data : Data) (i : Nat)
    (s : GraphCertificate.Side) (m : Side) (x : Quadratic462)
    (empty : GraphCertificate.Transition) : Prop where
  stateBound : m.state < 5
  shape : 0 ≤ m.shape.lo ∧ m.shape.lo ≤ m.shape.hi ∧ m.shape.hi ≤ 1
  shapeOuter : s.shape.lo ≤ m.shape.lo ∧ m.shape.hi ≤ s.shape.hi ∧ 0 ≤ s.shape.lo
  rawSize : m.raw.size = s.tails.size
  transitionSize : s.transitions.size = input.extensions
  anchorEq : x = anchor m.state s.parity
  emptyEq : empty.state = (i : Int) ∧ empty.lowerId = s.anchor
  rawBounds : ∀ j < m.raw.size, ∀ box raw,
    s.tails[j]? = some box → m.raw[j]? = some raw →
    box.mem raw.eval ∧ raw.eval ∈ Set.Icc (0 : ℝ) 1
  transitions : ∀ e < input.extensions, checkTransition input data i e = true

theorem checkSide_facts (input : GraphCertificate.Input) (data : Data) (i : Nat)
    (s : GraphCertificate.Side) (m : Side) (x : Quadratic462)
    (empty : GraphCertificate.Transition)
    (hs : input.sides[i]? = some s) (hm : data.sides[i]? = some m)
    (hx : m.raw[s.anchor]? = some x) (he : s.transitions[0]? = some empty)
    (h : checkSide input data i = true) : SideFacts input data i s m x empty := by
  simp only [checkSide, hs, hm, hx, he, Option.pure_def, bind_some_direct, Option.getD_some,
    Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hstate,hshape⟩,houter⟩,hraw⟩,htrans⟩,hanchor⟩,hempty⟩,hbounds⟩,hchecks⟩
  refine ⟨hstate,hshape,houter,hraw,htrans,hanchor,hempty,?_,?_⟩
  · intro j hj box raw hb hr
    have h := List.all_eq_true.mp hbounds j (List.mem_range.mpr hj)
    simp only [hb,hr,Bool.and_eq_true] at h
    exact ⟨contains_sound box raw h.1, by simpa [QBounds.mem] using contains_sound ⟨0,1⟩ raw h.2⟩
  · intro e he
    exact List.all_eq_true.mp hchecks e (List.mem_range.mpr he)

theorem check_sides (input : GraphCertificate.Input) (data : Data)
    (h : check input data = true) (i : Nat) (hi : i < input.states) :
    checkSide input data i = true := by
  unfold check at h
  exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 i (List.mem_range.mpr hi)

theorem check_extension_digits (input : GraphCertificate.Input) (data : Data)
    (h : check input data = true) (e : Nat) (w : List Nat)
    (hw : data.extensions[e]? = some w) : ∀ d ∈ w, 1 ≤ d ∧ d ≤ 3 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  have hall := h.1.1.1.1.2
  have he : w ∈ data.extensions := Array.mem_of_getElem? hw
  have hd := Array.all_eq_true_iff_forall_mem.mp hall w he
  simpa only [List.all_eq_true, decide_eq_true_eq] using hd

/-- Total decoding of natural words; checked digit positivity proves that
this harmless default is never used for certificate data. -/
def asWord (w : List Nat) : Word := w.map (fun d => ⟨max 1 d, by omega⟩)

theorem asWord_values (w : List Nat) (h : ∀ d ∈ w, 1 ≤ d) :
    (asWord w).map Subtype.val = w := by
  induction w with
  | nil => rfl
  | cons d w ih =>
      have hd : 1 ≤ d := h d (by simp)
      have hw : ∀ a ∈ w, 1 ≤ a := fun a ha => h a (List.mem_cons_of_mem d ha)
      simpa only [asWord, List.map_cons, max_eq_right hd] using congrArg (List.cons d) (ih hw)

theorem asWord_digits (w : List Nat) (h : ∀ d ∈ w, 1 ≤ d ∧ d ≤ 3) :
    ∀ a ∈ asWord w, a.val ≤ 3 := by
  intro a ha
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ha
  exact max_le (by decide) (h d hd).2

theorem checkTransition_constant_facts (input : GraphCertificate.Input) (data : Data) (i e : Nat)
    (s : GraphCertificate.Side) (m : Side) (tr : GraphCertificate.Transition)
    (c : GraphCertificate.Side) (cm : Side) (w : List Nat) (lo hi k : Quadratic462)
    (hs : input.sides[i]? = some s) (hm : data.sides[i]? = some m)
    (htr : s.transitions[e]? = some tr) (hactive : 0 ≤ tr.state)
    (hc : input.sides[tr.state.toNat]? = some c)
    (hcm : data.sides[tr.state.toNat]? = some cm)
    (hw : data.extensions[e]? = some w)
    (hlo : m.raw[tr.lowerId]? = some lo) (hhi : m.raw[tr.upperId]? = some hi)
    (h : checkTransition input data i e = true)
    (hconstant : tr.constant ≠ 0) (hk : data.constants[tr.constant]? = some k) :
    Quadratic462.mul (anchor m.state s.parity)
      (derivativeDen w (anchor cm.state c.parity)).1 =
      (derivativeDen w (anchor cm.state c.parity)).2 ∧
    derivativeAt w (anchor m.state s.parity) (anchor cm.state c.parity) m.shape.lo = some k := by
  have hf := checkTransition_facts input data i e s m tr c cm w lo hi
    hs hm htr hactive hc hcm hw hlo hhi h
  obtain ⟨dl,hdl,_⟩ := hf.derivativeLo
  obtain ⟨dh,hdh,_⟩ := hf.derivativeHi
  have hnot : ¬ tr.state < 0 := not_lt.mpr hactive
  unfold checkTransition at h
  rw [hs, bind_some_direct, hm, bind_some_direct, htr, bind_some_direct,
    if_neg hnot] at h
  dsimp only at h
  rw [hc, bind_some_direct, hcm, bind_some_direct,
    hw, bind_some_direct, hlo, bind_some_direct, hhi, bind_some_direct,
    hf.lower, bind_some_direct, hf.upper, bind_some_direct, hdl, bind_some_direct,
    hdh, bind_some_direct, if_neg hconstant, hk, bind_some_direct] at h
  simp only [Option.pure_def, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2 ▸ hdl⟩

theorem check_sizes (input : GraphCertificate.Input) (data : Data)
    (h : check input data = true) :
    input.states = input.sides.size ∧ input.states = data.sides.size ∧
    input.extensions = data.extensions.size ∧ input.grid.size = input.bins+1 ∧
    input.bands.size = input.types := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1

theorem lookup_some_getD {α : Type*} [Inhabited α] (a : Array α) (i : Nat)
    (hi : i < a.size) : a[i]? = some (a[i]?.getD default) := by
  simp only [Array.getElem?_eq_getElem hi, Option.getD_some]

theorem checkSide_gets (input : GraphCertificate.Input) (data : Data) (i : Nat)
    (s : GraphCertificate.Side) (m : Side)
    (hs : input.sides[i]? = some s) (hm : data.sides[i]? = some m)
    (h : checkSide input data i = true) :
    ∃ x empty, m.raw[s.anchor]? = some x ∧ s.transitions[0]? = some empty ∧
      SideFacts input data i s m x empty := by
  cases hx : m.raw[s.anchor]? with
  | none => simp [checkSide,hs,hm,hx] at h
  | some x =>
    cases he : s.transitions[0]? with
    | none => simp [checkSide,hs,hm,hx,he] at h
    | some empty => exact ⟨x,empty,rfl,rfl,checkSide_facts input data i s m x empty hs hm hx he h⟩

theorem checkTransition_gets (input : GraphCertificate.Input) (data : Data) (i e : Nat)
    (s : GraphCertificate.Side) (m : Side) (tr : GraphCertificate.Transition)
    (c : GraphCertificate.Side) (cm : Side)
    (hs : input.sides[i]? = some s) (hm : data.sides[i]? = some m)
    (htr : s.transitions[e]? = some tr) (hactive : 0 ≤ tr.state)
    (hc : input.sides[tr.state.toNat]? = some c)
    (hcm : data.sides[tr.state.toNat]? = some cm)
    (h : checkTransition input data i e = true) :
    ∃ w lo hi, data.extensions[e]? = some w ∧
      m.raw[tr.lowerId]? = some lo ∧ m.raw[tr.upperId]? = some hi ∧
      TransitionFacts s m tr c cm w lo hi := by
  have hnot : ¬ tr.state < 0 := not_lt.mpr hactive
  have h' := h
  unfold checkTransition at h'
  rw [hs, bind_some_direct, hm, bind_some_direct, htr, bind_some_direct,
    if_neg hnot] at h'
  dsimp only at h'
  rw [hc, bind_some_direct, hcm, bind_some_direct] at h'
  cases hw : data.extensions[e]? with
  | none => simp only [hw,bind_none_direct,Option.getD_none,Bool.false_eq_true] at h'
  | some w =>
    rw [hw,bind_some_direct] at h'
    cases hlo : m.raw[tr.lowerId]? with
    | none => simp only [hlo,bind_none_direct,Option.getD_none,Bool.false_eq_true] at h'
    | some lo =>
      rw [hlo,bind_some_direct] at h'
      cases hhi : m.raw[tr.upperId]? with
      | none => simp only [hhi,bind_none_direct,Option.getD_none,Bool.false_eq_true] at h'
      | some hi => exact ⟨w,lo,hi,rfl,rfl,rfl,
          checkTransition_facts input data i e s m tr c cm w lo hi
            hs hm htr hactive hc hcm hw hlo hhi h⟩

theorem check_empty_extension (input : GraphCertificate.Input) (data : Data)
    (h : check input data = true) : data.extensions[0]? = some [] := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.2

end Berstein.GraphMeaning
