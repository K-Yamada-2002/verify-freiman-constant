import Freiman.GraphSuccessor
import Berstein.QuadraticCF
import Berstein.CertificateCheck

/-! A root checker for arbitrary finite words, independent of the specialized
322/431 root in Berstein. Every label is checked against the actual word. -/
namespace Freiman.Root
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction

structure Witness where
  left : Word
  right : Word
  leftIndex : Nat
  rightIndex : Nat
  bin : Nat
  type : Nat
  deriving Inhabited

def wordsCheck (w : Witness) : Bool :=
  decide (w.left ≠ [] ∧ w.right ≠ []) &&
    w.left.all (fun d => decide (d.val ≤ 4)) &&
    w.right.all (fun d => decide (d.val ≤ 4))

abbrev setup (w : Witness) (center : ℝ) (h : wordsCheck w = true) : Setup where
  left := w.left
  right := w.right
  left_nonempty := by
    simp only [wordsCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1.1.1
  right_nonempty := by
    simp only [wordsCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact h.1.1.2
  left_bound := by
    simp only [wordsCheck,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
    exact h.1.2
  right_bound := by
    simp only [wordsCheck,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
    exact h.2
  center := center

def shape (w : Word) : ℚ :=
  let m := coeffs (w.map Subtype.val)
  (m.d : ℚ)/m.c

theorem shape_cast (w : Word) : (shape w : ℝ) = denominatorRatio w := by
  simp only [shape,coeffs_map,denominatorRatio]
  push_cast
  rfl

def sideCheck (input : GraphCertificate.Input) (data : Data) (w : Word) (i : Nat) : Bool :=
  let s := input.sides[i]?.getD default
  let m := data.sides[i]?.getD default
  decide (i < input.states ∧ i < input.sides.size ∧ i < data.sides.size ∧ m.state < 5) &&
    decide (after 0 (w.map Subtype.val) = some m.state) &&
    decide (s.parity = decide (w.length % 2 = 1)) &&
    decide (m.shape.lo ≤ shape w ∧ shape w ≤ m.shape.hi)

theorem sideFacts (input : GraphCertificate.Input) (data : Data) (w : Word) (i : Nat)
    (h : sideCheck input data w i = true) :
    (i < input.states ∧ i < input.sides.size ∧ i < data.sides.size ∧
      (data.sides[i]?.getD default).state < 5) ∧
    after 0 (w.map Subtype.val) = some (data.sides[i]?.getD default).state ∧
    (input.sides[i]?.getD default).parity = decide (w.length % 2 = 1) ∧
    (data.sides[i]?.getD default).shape.lo ≤ shape w ∧
      shape w ≤ (data.sides[i]?.getD default).shape.hi := by
  simp only [sideCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  exact ⟨h.1.1.1,h.1.1.2,h.1.2,h.2⟩

/-- Data fields do not eliminate proof terms, so their projections compute. -/
def realSide (input : GraphCertificate.Input) (data : Data) (w : Word) (i : Nat)
    (h : sideCheck input data w i = true) : RealSide input data w where
  extension := []
  digits := by simp
  index := i
  index_lt := (sideFacts input data w i h).1.1
  state := ⟨(data.sides[i]?.getD default).state,(sideFacts input data w i h).1.2.2.2⟩
  state_eq := rfl
  legal := by
    simpa only [List.append_nil] using after_sound 0
      ⟨(data.sides[i]?.getD default).state,(sideFacts input data w i h).1.2.2.2⟩ w
      (sideFacts input data w i h).2.1
  parity := by simpa only [List.append_nil] using (sideFacts input data w i h).2.2.1
  shape := by
    rw [List.append_nil,← shape_cast]
    change ((data.sides[i]?.getD default).shape.lo : ℝ) ≤ (shape w : ℝ) ∧
      (shape w : ℝ) ≤ ((data.sides[i]?.getD default).shape.hi : ℝ)
    exact_mod_cast (sideFacts input data w i h).2.2.2

def denominator (w : Word) (x : Quadratic462) : Quadratic462 :=
  (derivativeDen (w.map Subtype.val) x).1

theorem denominator_eval (w : Word) (x : Quadratic462) :
    (denominator w x).eval = (mobiusCoeffs w).C+(mobiusCoeffs w).D*x.eval :=
  (derivativeDen_eval w x).1

def ratio (a b : Word) (x y : Quadratic462) : Option Quadratic462 := do
  let inv ← Quadratic462.checkedInv (denominator b y)
  let quotient := Quadratic462.mul (denominator a x) inv
  pure (Quadratic462.mul quotient quotient)

theorem ratio_eval (a b : Word) (x y out : Quadratic462)
    (hx : 0 ≤ x.eval) (hy : 0 ≤ y.eval) (h : ratio a b x y = some out) :
    out.eval = Normalization.scale b y.eval / Normalization.scale a x.eval := by
  unfold ratio at h
  cases hi : Quadratic462.checkedInv (denominator b y) with
  | none => simp [hi] at h
  | some inv =>
    simp [hi] at h
    subst out
    simp only [Quadratic462.eval_mul,
      Quadratic462.checkedInv_sound _ _ hi,denominator_eval]
    have ha : (0 : ℝ) < (mobiusCoeffs a).C+(mobiusCoeffs a).D*x.eval := by
      have hc : (0 : ℝ) < (mobiusCoeffs a).C := by exact_mod_cast mobius_C_pos a
      positivity
    have hb : (0 : ℝ) < (mobiusCoeffs b).C+(mobiusCoeffs b).D*y.eval := by
      have hc : (0 : ℝ) < (mobiusCoeffs b).C := by exact_mod_cast mobius_C_pos b
      positivity
    unfold Normalization.scale
    field_simp [ne_of_gt ha,ne_of_gt hb]
    <;> ring

def rootRatio (input : GraphCertificate.Input) (data : Data) (w : Witness) : Option Quadratic462 :=
  ratio w.left w.right
    (anchor (data.sides[w.leftIndex]?.getD default).state
      (input.sides[w.leftIndex]?.getD default).parity)
    (anchor (data.sides[w.rightIndex]?.getD default).state
      (input.sides[w.rightIndex]?.getD default).parity)

def check (input : GraphCertificate.Input) (data : Data) (alive : ByteArray) (w : Witness) : Bool :=
  wordsCheck w && sideCheck input data w.left w.leftIndex &&
    sideCheck input data w.right w.rightIndex &&
    decide (w.bin < input.bins ∧ w.type < input.types) &&
    GraphCertificate.adopted input alive (w.leftIndex*input.states+w.rightIndex) w.bin w.type &&
    (match rootRatio input data w with
    | none => false
    | some s => contains ⟨(51/50 : ℚ)^(input.firstExponent+(w.bin : Int)),
        (51/50 : ℚ)^(input.firstExponent+(w.bin : Int)+1)⟩ s &&
          contains ⟨1/10000,10000⟩ s)

theorem words_of_check (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (w : Witness) (h : check input data alive w = true) : wordsCheck w = true := by
  simp only [check,Bool.and_eq_true] at h
  exact h.1.1.1.1.1

/-- Construct the actual root carried by an accepted finite witness. -/
noncomputable def realState (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (w : Witness) (center : ℝ) (hc : check input data alive w = true)
    (hm : Berstein.GraphMeaning.check input data = true) :
    letI := setup w center (words_of_check input data alive w hc)
    Freiman.GraphMeaning.RealState input data alive := by
  letI := setup w center (words_of_check input data alive w hc)
  have h := hc
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
  have hw := h.1.1.1.1.1
  have hl := h.1.1.1.1.2
  have hr := h.1.1.1.2
  have hd := h.1.1.2
  have ha := h.1.2
  have hs := h.2
  let l := realSide input data w.left w.leftIndex hl
  let r := realSide input data w.right w.rightIndex hr
  have htype : w.type < input.bands.size := by
    rw [(check_sizes input data hm).2.2.2.2]; exact hd.2
  have hband := check_band_unit input data hm w.type htype _
    (lookup_some_getD input.bands w.type htype)
  have hratio : r.scale/l.scale ∈ Set.Icc
      (Berstein.GraphMeaning.exactCut input w.bin)
      (Berstein.GraphMeaning.exactCut input (w.bin+1)) ∧
      r.scale/l.scale ∈ Set.Icc (1/10000 : ℝ) 10000 := by
    cases he : rootRatio input data w with
    | none => simp [he] at hs
    | some ratioValue =>
      rw [he] at hs
      have hb := Bool.and_eq_true_iff.mp hs
      have hlower := contains_sound _ _ hb.1
      have hbalance := contains_sound _ _ hb.2
      have he' : ratio l.word r.word (anchor l.state.val l.finite.parity)
          (anchor r.state.val r.finite.parity) = some ratioValue := by
        simpa [rootRatio,l,r,realSide,RealSide.word,RealSide.finite] using he
      have hval : ratioValue.eval = r.scale/l.scale :=
        ratio_eval l.word r.word _ _ ratioValue l.anchorValue_mem.1 r.anchorValue_mem.1 he' 
      rw [hval] at hlower hbalance
      refine ⟨?_,by simpa [QBounds.mem] using hbalance⟩
      simpa [Berstein.GraphMeaning.exactCut,QBounds.mem,add_assoc] using hlower
  refine ⟨l,r,w.bin,hd.1,w.type,hd.2,?_,hratio.1,hratio.2,hband⟩
  simpa [l,r,realSide] using ha

/-- Kernel-checked realization for every checked root of the same large table. -/
theorem realizes (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell)
    (htable : Certificate.Accepted input data alive cells)
    (w : Witness) (center : ℝ) (hw : check input data alive w = true)
    {x : ℝ}
    (hx : letI := setup w center (words_of_check input data alive w hw)
      x ∈ (realState input data alive w center hw htable.meaning).target) :
    ∃ a ∈ admissibleTailSet w.left, ∃ b ∈ admissibleTailSet w.right, x = center+a+b := by
  letI := setup w center (words_of_check input data alive w hw)
  apply Freiman.GraphMeaning.RealState.realizes _
    (realState input data alive w center hw htable.meaning) hx
  intro s t ht
  apply Freiman.GraphMeaning.verified_successor htable.meaning _ cells htable.geometries s t ht
  intro i hi
  have hs := (check_sizes input data htable.meaning).1
  exact htable.prepared _ (Array.mem_of_getElem? (lookup_some_getD input.sides i (by omega)))

end Freiman.Root
