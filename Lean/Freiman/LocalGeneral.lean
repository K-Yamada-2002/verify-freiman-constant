import Freiman.LocalSound

namespace Freiman.Local
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction
variable [Setup]

noncomputable def pairEndpoint {ls rs : Spec} (l : ActualSide Setup.left ls)
    (r : ActualSide Setup.right rs) (p : ℝ) : ℝ := Setup.center+l.endpoint p+r.endpoint p

 theorem pairEndpoint_affine {ls rs : Spec} (l : ActualSide Setup.left ls)
    (r : ActualSide Setup.right rs) (p : ℝ) :
    pairEndpoint l r p = Setup.center+l.lowerValue+r.lowerValue+
      p*((l.upperValue-l.lowerValue)+(r.upperValue-r.lowerValue)) := by
  unfold pairEndpoint ActualSide.endpoint
  ring

 theorem pairEndpoint_parameter {ls rs : Spec} (l : ActualSide Setup.left ls)
    (r : ActualSide Setup.right rs) {lo hi x : ℝ}
    (hx : x ∈ Set.Icc (pairEndpoint l r lo) (pairEndpoint l r hi)) :
    ∃ p ∈ Set.Icc lo hi, x = pairEndpoint l r p := by
  simp only [pairEndpoint_affine] at hx ⊢
  exact Berstein.GraphMeaning.affine_parameter (by linarith [l.lower_lt_upper,r.lower_le_upper]) hx

 theorem ActualSide.toGeneral_scale {root : Word} {spec : Spec} (s : ActualSide root spec)
    (input : GraphCertificate.Input) (data : Data) (i : Nat)
    (hc : specMatches input data i spec = true) :
    (s.toGeneral input data i hc).scale = s.scale := by
  have hh := hc
  simp only [specMatches,Bool.and_eq_true,decide_eq_true_eq] at hh
  dsimp only [RealSide.scale,RealSide.anchorValue,RealSide.finite,RealSide.word,
    ActualSide.toGeneral,ActualSide.scale,ActualSide.anchorValue,ActualSide.word]
  rw [hh.2.1]

/-- A local successor certified to enter the general table. -/
theorem general_successor (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (hm : Berstein.GraphMeaning.check input data = true) {c : Condition}
    (s : State c) (hc : c.check = true) (v : Vertex)
    (fl : StepInfo c.left v.left) (fr : StepInfo c.right v.right)
    (hprogress : 0 < fl.word.length+fr.word.length)
    (hg : generalCheck input data alive c v = true) (x : ℝ)
    (hx : x ∈ Set.Icc
      (pairEndpoint (s.left.extend fl.word fl.transition fl.lower fl.upper (c.facts hc).left fl.facts)
        (s.right.extend fr.word fr.transition fr.lower fr.upper (c.facts hc).right fr.facts) v.band.lo)
      (pairEndpoint (s.left.extend fl.word fl.transition fl.lower fl.upper (c.facts hc).left fl.facts)
        (s.right.extend fr.word fr.transition fr.lower fr.upper (c.facts hc).right fr.facts) v.band.hi)) :
    ∃ t : Freiman.GraphMeaning.RealState input data alive,
      CylinderCover.Extends s.pair t.pair ∧ x ∈ t.target := by
  let l := s.left.extend fl.word fl.transition fl.lower fl.upper (c.facts hc).left fl.facts
  let r := s.right.extend fr.word fr.transition fr.lower fr.upper (c.facts hc).right fr.facts
  unfold generalCheck at hg
  rw [fl.target_eq,fr.target_eq] at hg
  cases hb : imageBox c v with
  | none => simp [hb] at hg
  | some box =>
    simp only [hb,Option.bind_eq_bind,Option.bind_some,Option.pure_def,Option.getD_some,
      Bool.and_eq_true,decide_eq_true_eq] at hg
    rcases hg with ⟨⟨⟨⟨⟨hgl,hgr⟩,hindices⟩,himage⟩,hmerged⟩,hadopted⟩
    let left := l.toGeneral input data v.generalLeft hgl
    let right := r.toGeneral input data v.generalRight hgr
    have hlscale : left.scale = l.scale := l.toGeneral_scale input data v.generalLeft hgl
    have hrscale : right.scale = r.scale := r.toGeneral_scale input data v.generalRight hgr
    have hbox := imageBox_sound s hc v fl fr box hb
    have hd := check_dimensions input data hm
    have hcuts : ∀ k ≤ input.bins, (input.grid[k]?.getD default).mem (exactCut input k) := by
      intro k hk
      have hi : k < input.grid.size := by omega
      have h := check_grid_cut input data hm k hi _ (lookup_some_getD input.grid k hi)
      exact ⟨Rat.cast_mono h.1,Rat.cast_mono h.2.1⟩
    have hlo : exactCut input v.first ≤ r.scale/l.scale :=
      ((hcuts v.first (by omega)).2.trans (Rat.cast_mono himage.1)).trans hbox.1
    have hhi : r.scale/l.scale ≤ exactCut input (v.last+1) :=
      (hbox.2.trans (Rat.cast_mono himage.2)).trans (hcuts (v.last+1) (by omega)).1
    obtain ⟨d,hd',hkl,hkr⟩ := RatioGrid.between_cuts
      (fun j => exactCut input (v.first+j)) (v.last-v.first) (r.scale/l.scale) hlo (by
        simpa only [show v.first+(v.last-v.first+1)=v.last+1 by omega] using hhi)
    let k := v.first+d
    have hk : k < input.bins := by dsimp [k]; omega
    have hratio : right.scale/left.scale ∈ Set.Icc (exactCut input k) (exactCut input (k+1)) := by
      rw [hlscale,hrscale]
      exact ⟨hkl,by simpa only [k,Nat.add_assoc] using hkr⟩
    have hbalance : right.scale/left.scale ∈ Set.Icc (1/10000 : ℝ) 10000 := by
      have hl := check_grid_cut input data hm k (by omega) _ (lookup_some_getD input.grid k (by omega))
      have hr := check_grid_cut input data hm (k+1) (by omega) _ (lookup_some_getD input.grid (k+1) (by omega))
      have hlo' : (1/10000 : ℝ) ≤ exactCut input k := by
        have h : (((1/10000 : ℚ) : ℝ)) ≤ exactCut input k := Rat.cast_mono hl.2.2.1
        simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
      have hhi' : exactCut input (k+1) ≤ (10000 : ℝ) := by
        have h : exactCut input (k+1) ≤ ((10000 : ℚ) : ℝ) := Rat.cast_mono hr.2.2.2
        simpa only [Rat.cast_ofNat] using h
      exact ⟨hlo'.trans hratio.1,hratio.2.trans hhi'⟩
    obtain ⟨p,hp,hxp⟩ := pairEndpoint_parameter l r hx
    obtain ⟨type,ht,hselected,hpband⟩ := GraphCertificate.checkMergedBand_sound input v.asGraph hmerged p hp
    have hall := List.all_eq_true.mp hadopted type (List.mem_range.mpr ht)
    have hab : (List.range (v.last-v.first+1)).all (fun d =>
        GraphCertificate.adopted input alive (v.generalLeft*input.states+v.generalRight) (v.first+d) type) = true := by
      simpa only [GraphCertificate.Vertex.typeMask,Vertex.asGraph,hselected,Bool.not_true,Bool.false_or] using hall
    have hadopt := List.all_eq_true.mp hab d (List.mem_range.mpr (by omega))
    have hband := check_band_unit input data hm type (by omega) _
      (lookup_some_getD input.bands type (by omega))
    let t : Freiman.GraphMeaning.RealState input data alive :=
      ⟨left,right,k,hk,type,ht,hadopt,hratio,hbalance,hband⟩
    refine ⟨t,⟨fl.word,fr.word,rfl,rfl,hprogress⟩,?_⟩
    change pairEndpoint l r ((input.bands[type]?.getD default).lo : ℝ) ≤ x ∧
      x ≤ pairEndpoint l r ((input.bands[type]?.getD default).hi : ℝ)
    rw [hxp]
    simp only [pairEndpoint_affine]
    constructor <;> nlinarith [l.lower_le_upper,r.lower_le_upper,hpband.1,hpband.2]

end Freiman.Local
