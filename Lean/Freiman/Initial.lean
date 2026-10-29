import Freiman.LocalCover
import Freiman.RootCover
import Freiman.Spectral

/-! The closed initial interval beginning exactly at the Freiman constant. -/
namespace Freiman.Initial
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction

abbrev endpointSetup : Setup where
  left := Endpoint.A
  right := Endpoint.B
  left_nonempty := by decide +kernel
  right_nonempty := by decide +kernel
  left_bound := by
    have h : Endpoint.A.all (fun d => decide (d.val ≤ 4)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  right_bound := by
    have h : Endpoint.B.all (fun d => decide (d.val ≤ 4)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  center := 4

local instance : Setup := endpointSetup

def lower : Quadratic462 := ⟨2221564096/491993569,283748/491993569⟩
def upper : Quadratic462 := ⟨75920280795833009/16806706462345411,794958599527483/1613443820385159456⟩
def leftUpper : Quadratic462 := ⟨9715/32894,-1/65788⟩
def rightUpper : Quadratic462 := ⟨975/4154,-1/12462⟩

theorem lower_eval : lower.eval = freimanConstant := by
  norm_num [lower,Quadratic462.eval,freimanConstant]
  ring

theorem left_upper_checked : Quadratic462.cf (Endpoint.A.map Subtype.val) (GraphMeaning.lower 1) = some leftUpper := by
  decide +kernel

theorem right_upper_checked : Quadratic462.cf (Endpoint.B.map Subtype.val) (GraphMeaning.upper 0) = some rightUpper := by
  decide +kernel

theorem lower_identity : 4+Endpoint.leftValue.eval+Endpoint.rightValue.eval = freimanConstant := by
  norm_num [Endpoint.leftValue,Endpoint.rightValue,Quadratic462.eval,freimanConstant]
  ring

theorem upper_identity : 4+(1-(1/8 : ℝ))*Endpoint.leftValue.eval+(1/8 : ℝ)*leftUpper.eval+
    (1-(1/8 : ℝ))*Endpoint.rightValue.eval+(1/8 : ℝ)*rightUpper.eval = upper.eval := by
  norm_num [Endpoint.leftValue,Endpoint.rightValue,leftUpper,rightUpper,upper,Quadratic462.eval]
  ring

def spectrum : Spectral.Certificate :=
  ⟨Endpoint.A,Endpoint.B,⟨4,by decide⟩,1,0,Quadratic462.ofRat (452736/100000)⟩

theorem spectrum_bound_le : spectrum.bound.eval ≤ freimanConstant := by
  rw [← lower_eval]
  exact Quadratic462.le_sound _ _ (by decide +kernel)

def sideCheck (w : Word) (s : Local.Spec) : Bool :=
  decide (Forbidden31313.afterWord 0 w = some s.state ∧
    s.parity = decide (w.length % 2 = 1) ∧ s.shape.lo ≤ Root.shape w ∧ Root.shape w ≤ s.shape.hi)

 theorem sideFacts (w : Word) (s : Local.Spec) (h : sideCheck w s = true) :
    Forbidden31313.afterWord 0 w = some s.state ∧
    s.parity = decide (w.length % 2 = 1) ∧ s.shape.lo ≤ Root.shape w ∧ Root.shape w ≤ s.shape.hi :=
  of_decide_eq_true h

 def actualSide (w : Word) (s : Local.Spec) (h : sideCheck w s = true) : Local.ActualSide w s where
  extension := []
  digits := by simp
  legal := by simpa only [List.append_nil] using (sideFacts w s h).1
  parity := by simpa only [List.append_nil] using (sideFacts w s h).2.1
  shape := by
    rw [List.append_nil,← Root.shape_cast]
    change (s.shape.lo : ℝ) ≤ (Root.shape w : ℝ) ∧ (Root.shape w : ℝ) ≤ (s.shape.hi : ℝ)
    exact_mod_cast (sideFacts w s h).2.2

@[simp] theorem actualSide_word (w : Word) (s : Local.Spec) (h : sideCheck w s = true) :
    (actualSide w s h).word = w := by simp only [Local.ActualSide.word,actualSide,List.append_nil]

def ratio (c : Local.Condition) : Option Quadratic462 := Root.ratio Endpoint.A Endpoint.B c.leftAnchor c.rightAnchor

def check (conditions : Array Local.Condition) : Bool :=
  (do
    let c ← conditions[0]?
    let r ← ratio c
    return decide (c.kind = 0 ∧ c.band = (⟨0,1/8⟩ : QBounds)) && sideCheck Endpoint.A c.left.spec &&
      sideCheck Endpoint.B c.right.spec && contains c.invariant r && Spectral.check spectrum).getD false

structure Facts (conditions : Array Local.Condition) where
  condition : Local.Condition
  lookup : conditions[0]? = some condition
  kind : condition.kind = 0
  band : condition.band = ⟨0,1/8⟩
  left : sideCheck Endpoint.A condition.left.spec = true
  right : sideCheck Endpoint.B condition.right.spec = true
  ratioValue : Quadratic462
  ratio_eq : ratio condition = some ratioValue
  ratio_mem : contains condition.invariant ratioValue = true
  spectral : Spectral.check spectrum = true

 theorem check_facts (conditions : Array Local.Condition) (hc : check conditions = true) : Nonempty (Facts conditions) := by
  unfold check at hc
  cases hd : conditions[0]? with
  | none => simp [hd] at hc
  | some c =>
    cases hr : ratio c with
    | none => simp [hd,hr] at hc
    | some value =>
      simp only [hd,hr,Option.bind_eq_bind,Option.bind_some,Option.pure_def,Option.getD_some,
        Bool.and_eq_true,decide_eq_true_eq] at hc
      exact ⟨⟨c,hd,hc.1.1.1.1.1,hc.1.1.1.1.2,hc.1.1.1.2,hc.1.1.2,value,hr,hc.1.2,hc.2⟩⟩

 theorem interval_subset (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell)
    (htable : Berstein.Certificate.Accepted input data alive cells) (conditions : Array Local.Condition)
    (hlocal : Local.Accepted input data alive conditions) (hinit : check conditions = true) :
    Set.Icc freimanConstant upper.eval ⊆ markovSpectrum := by
  obtain ⟨f⟩ := check_facts conditions hinit
  let c := f.condition
  have hc := hlocal.valid c (Array.mem_of_getElem? f.lookup)
  have hkind : c.kind = 0 := f.kind
  let l := actualSide Endpoint.A c.left.spec f.left
  let r := actualSide Endpoint.B c.right.spec f.right
  have hz : c.useZeta = false := by simp [Local.Condition.useZeta,hkind]
  have hratio : c.invariant.mem (r.scale/l.scale) := by
    have h := contains_sound _ _ f.ratio_mem
    have he := Root.ratio_eval Endpoint.A Endpoint.B c.leftAnchor c.rightAnchor f.ratioValue
      l.anchor_mem.1 r.anchor_mem.1 f.ratio_eq
    have he' : f.ratioValue.eval = r.scale/l.scale := by
      simpa only [Local.ActualSide.scale,Local.ActualSide.anchorValue,l,r,actualSide_word] using he
    rwa [he'] at h
  let s : Local.State c := ⟨l,r,by simpa only [hz,Bool.false_eq_true,ite_false] using hratio⟩
  have ha := c.period_anchors hc (by rw [hkind]; decide)
  have hf := c.facts hc
  have hsright : c.right.spec.state.val = 0 := by simpa only [hkind,show 0 < 2 by decide,ite_true] using hf.rightState
  have hll : l.lowerValue = Endpoint.leftValue.eval := by
    rw [l.lower_eq_anchor,actualSide_word]
    change tailMap Endpoint.A c.leftAnchor.eval = _
    rw [ha.1]
    exact (Quadratic462.cf_sound _ _ _ Endpoint.left_checked).symm
  have hrl : r.lowerValue = Endpoint.rightValue.eval := by
    rw [r.lower_eq_anchor,actualSide_word]
    change tailMap Endpoint.B c.rightAnchor.eval = _
    rw [ha.2]
    exact (Quadratic462.cf_sound _ _ _ Endpoint.right_checked).symm
  have hlu : l.upperValue = leftUpper.eval := by
    rw [l.upper_eq_opposite,actualSide_word,hf.leftState,hf.leftParity]
    exact (Quadratic462.cf_sound _ _ _ left_upper_checked).symm
  have hru : r.upperValue = rightUpper.eval := by
    rw [r.upper_eq_opposite,actualSide_word,hsright,hf.rightParity]
    exact (Quadratic462.cf_sound _ _ _ right_upper_checked).symm
  have hlo : s.endpoint c.band.lo = freimanConstant := by
    rw [f.band]
    simp only [Local.State.endpoint,Local.ActualSide.endpoint,s,Setup.center]
    norm_num only [Rat.cast_zero,zero_mul,sub_zero,one_mul,add_zero]
    rw [hll,hrl]
    exact lower_identity
  have hhi : s.endpoint c.band.hi = upper.eval := by
    rw [f.band]
    simp only [Local.State.endpoint,Local.ActualSide.endpoint,s,Setup.center]
    simp only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
    rw [hll,hrl,hlu,hru]
    linarith [upper_identity]
  have hb := Spectral.check_sound spectrum f.spectral
  intro t ht
  have htarget : t ∈ s.target := by
    change s.endpoint c.band.lo ≤ t ∧ t ≤ s.endpoint c.band.hi
    rwa [hlo,hhi]
  obtain ⟨a,⟨left,hl,ha'⟩,b,⟨right,hr,hb'⟩,he⟩ := Local.realizes input data alive cells htable conditions hlocal
    (.special ⟨c,0,f.lookup,s⟩) htarget
  have hcenter : localValue (glueAt spectrum.center left right) 0 = t := by
    rw [localValue_glueAt_zero]
    change 4+value 0 left+value 0 right = t
    rw [ha',hb'] at he
    exact he.symm
  rw [← hcenter]
  apply mem_markovSpectrum_of_dominant
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · rw [hcenter]
    exact (hb left right hl hr n hn).trans (spectrum_bound_le.trans ht.1)

end Freiman.Initial
