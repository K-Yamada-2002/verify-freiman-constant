import Freiman.LocalGeneral

namespace Freiman.Local
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction

/-- Change only the checked finite specification, retaining the actual word. -/
def ActualSide.withSpec {root : Word} {sp : Spec} (s : ActualSide root sp)
    (dest : Spec) (he : sp = dest) : ActualSide root dest where
  extension := s.extension
  digits := s.digits
  legal := by rw [← he]; exact s.legal
  parity := by rw [← he]; exact s.parity
  shape := by rw [← he]; exact s.shape

@[simp] theorem ActualSide.withSpec_word {root : Word} {sp : Spec} (s : ActualSide root sp)
    (dest : Spec) (he : sp = dest) : (s.withSpec dest he).word = s.word := rfl

@[simp] theorem ActualSide.withSpec_endpoint {root : Word} {sp : Spec} (s : ActualSide root sp)
    (dest : Spec) (he : sp = dest) (p : ℝ) : (s.withSpec dest he).endpoint p = s.endpoint p := by
  cases he
  rfl

@[simp] theorem ActualSide.withSpec_scale {root : Word} {sp : Spec} (s : ActualSide root sp)
    (dest : Spec) (he : sp = dest) : (s.withSpec dest he).scale = s.scale := by
  cases he
  rfl

 theorem Condition.period_anchors (c : Condition) (hc : c.check = true) (hk : c.kind < 2) :
    c.leftAnchor = Endpoint.x ∧ c.rightAnchor = Endpoint.y := by
  have hf := c.facts hc
  constructor
  · simp [Condition.leftAnchor,hf.leftState,hf.leftParity,anchor,upper,Endpoint.x]
  · simp [Condition.rightAnchor,hf.rightState,hk,hf.rightParity,anchor,lower,Endpoint.y]

 theorem invariant_enlarge (source dest : QBounds) {x : ℝ} (h : source.mem x)
    (hl : dest.lo ≤ source.lo) (hh : source.hi ≤ dest.hi) : dest.mem x :=
  ⟨(Rat.cast_mono hl).trans h.1,h.2.trans (Rat.cast_mono hh)⟩

/-- All local destinations: exact periodic S-return, exact V_zeta return,
and the two checked transitions from the S coordinate into V_zeta. -/
theorem local_successor [Setup] (conditions : Array Condition)
    (hconditions : ∀ c ∈ conditions, c.check = true) {c : Condition} (s : State c)
    (hc : c.check = true) (v : Vertex) (j : Nat)
    (fl : StepInfo c.left v.left) (fr : StepInfo c.right v.right)
    (hprogress : 0 < fl.word.length+fr.word.length)
    (hg : localCheck conditions c v j = true) (x : ℝ)
    (hx : x ∈ Set.Icc
      (pairEndpoint (s.left.extend fl.word fl.transition fl.lower fl.upper (c.facts hc).left fl.facts)
        (s.right.extend fr.word fr.transition fr.lower fr.upper (c.facts hc).right fr.facts) v.band.lo)
      (pairEndpoint (s.left.extend fl.word fl.transition fl.lower fl.upper (c.facts hc).left fl.facts)
        (s.right.extend fr.word fr.transition fr.lower fr.upper (c.facts hc).right fr.facts) v.band.hi)) :
    ∃ dest, conditions[j]? = some dest ∧ ∃ t : State dest,
      CylinderCover.Extends s.pair t.pair ∧ x ∈ t.target := by
  let l := s.left.extend fl.word fl.transition fl.lower fl.upper (c.facts hc).left fl.facts
  let r := s.right.extend fr.word fr.transition fr.lower fr.upper (c.facts hc).right fr.facts
  unfold localCheck at hg
  cases hd : conditions[j]? with
  | none => simp [hd] at hg
  | some dest =>
    rw [hd,fl.target_eq,fr.target_eq,fl.word_eq,fr.word_eq] at hg
    simp only [Option.bind_eq_bind,Option.bind_some] at hg
    by_cases he : fl.target = dest.left.spec ∧ fr.target = dest.right.spec ∧ v.band = dest.band
    · simp [he] at hg
      have hdc := hconditions dest (Array.mem_of_getElem? hd)
      let ll := l.withSpec dest.left.spec he.1
      let rr := r.withSpec dest.right.spec he.2.1
      have hlword : ll.word = s.left.word++fl.word := by
        simp only [ll,ActualSide.withSpec_word,l,ActualSide.extend_word]
      have hrword : rr.word = s.right.word++fr.word := by
        simp only [rr,ActualSide.withSpec_word,r,ActualSide.extend_word]
      have hInv : dest.invariant.mem (if dest.useZeta then
          Normalization.scale rr.word Endpoint.zeta/Normalization.scale ll.word Endpoint.zeta
          else rr.scale/ll.scale) := by
        by_cases hj : j = 1
        · simp only [hj,if_pos,Option.pure_def,Option.getD_some,Bool.and_eq_true,decide_eq_true_eq] at hg
          rcases hg with ⟨hck,hdk,huw,hvw,hlo,hhi⟩
          have hsrc := c.period_anchors hc (by omega)
          have hdst := dest.period_anchors hdc (by omega)
          have hzsrc : c.useZeta = false := by simp [Condition.useZeta]; omega
          have hzdst : dest.useZeta = false := by simp [Condition.useZeta,hdk]
          have hs := s.ratio
          simp only [hzsrc,Bool.false_eq_true,ite_false] at hs
          have hRatio : rr.scale/ll.scale = s.right.scale/s.left.scale := by
            change Normalization.scale rr.word dest.rightAnchor.eval/Normalization.scale ll.word dest.leftAnchor.eval =
              Normalization.scale s.right.word c.rightAnchor.eval/Normalization.scale s.left.word c.leftAnchor.eval
            rw [hlword,hrword,huw,hvw,hsrc.1,hsrc.2,hdst.1,hdst.2]
            exact Endpoint.ratio_return s.left.word s.right.word
          simp only [hzdst,Bool.false_eq_true,ite_false,hRatio]
          exact invariant_enlarge c.invariant dest.invariant hs hlo hhi
        · simp only [if_neg hj] at hg
          by_cases hk : 2 ≤ c.kind
          · simp only [if_pos hk,Option.pure_def,Option.getD_some,Bool.and_eq_true,decide_eq_true_eq] at hg
            rcases hg with ⟨hdk,huw,hvw,hlo,hhi⟩
            have hzsrc : c.useZeta = true := by simp [Condition.useZeta,hk]
            have hzdst : dest.useZeta = true := by simp [Condition.useZeta,hdk]
            have hs := s.ratio
            simp only [hzsrc,ite_true] at hs
            have hRatio : Normalization.scale rr.word Endpoint.zeta/Normalization.scale ll.word Endpoint.zeta =
                Normalization.scale s.right.word Endpoint.zeta/Normalization.scale s.left.word Endpoint.zeta := by
              rw [hlword,hrword,huw,hvw]
              exact Endpoint.zeta_ratio_return s.left.word s.right.word
            simp only [hzdst,ite_true,hRatio]
            exact invariant_enlarge c.invariant dest.invariant hs hlo hhi
          · simp only [if_neg hk] at hg
            cases hb : imageBox c v with
            | none => simp [hb] at hg
            | some box =>
              cases hlb : shapeBox c.left v.left with
              | none => simp [hb,hlb] at hg
              | some lb =>
                cases hrb : shapeBox c.right v.right with
                | none => simp [hb,hlb,hrb] at hg
                | some rb =>
                  simp only [hb,hlb,hrb,Option.bind_eq_bind,Option.bind_some,Option.pure_def,Option.getD_some,
                    Bool.and_eq_true,decide_eq_true_eq] at hg
                  have hzdst : dest.useZeta = true := by simp [Condition.useZeta,hg.1]
                  simp only [hzdst,ite_true]
                  have hbox := imageBox_sound s hc v fl fr box hb
                  have hbox' : box.mem (rr.scale/ll.scale) := by
                    simpa only [ll,rr,ActualSide.withSpec_scale,l,r] using hbox
                  have hlshape : lb.mem (denominatorRatio ll.word) := by
                    simpa only [ll,ActualSide.withSpec_word,l] using shapeBox_sound s.left (c.facts hc).left fl lb hlb
                  have hrshape : rb.mem (denominatorRatio rr.word) := by
                    simpa only [rr,ActualSide.withSpec_word,r] using shapeBox_sound s.right (c.facts hc).right fr rb hrb
                  exact Coordinate.to_zeta ll.word rr.word dest.leftAnchor dest.rightAnchor ll.anchor_mem.1 rr.anchor_mem.1
                    _ _ _ _ hlshape hrshape hbox' hg.2
      let t : State dest := ⟨ll,rr,hInv⟩
      refine ⟨dest,rfl,t,⟨fl.word,fr.word,rfl,rfl,hprogress⟩,?_⟩
      change pairEndpoint ll rr dest.band.lo ≤ x ∧ x ≤ pairEndpoint ll rr dest.band.hi
      simpa only [pairEndpoint,ll,rr,l,r,ActualSide.withSpec_endpoint,he.2.2,Set.mem_Icc] using hx
    · simp [he] at hg

end Freiman.Local
