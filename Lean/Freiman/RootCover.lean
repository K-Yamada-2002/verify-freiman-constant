import Freiman.Root
import Freiman.Markov
import Berstein.FiniteCover

/-! Exact endpoint semantics and finite covers by checked arbitrary roots. -/
namespace Freiman.Root
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction

def sideEndpoint (word : Word) (state : Nat) (parity : Bool) (p : ℚ) : Option Quadratic462 := do
  let lo ← Quadratic462.cf (word.map Subtype.val) (anchor state parity)
  let hi ← Quadratic462.cf (word.map Subtype.val) (opposite state parity)
  pure (Quadratic462.add (Quadratic462.mul (Quadratic462.ofRat (1-p)) lo)
    (Quadratic462.mul (Quadratic462.ofRat p) hi))

theorem sideEndpoint_eval {input : GraphCertificate.Input} {data : Data} {word : Word}
    (s : RealSide input data word) (p : ℚ) (out : Quadratic462)
    (h : sideEndpoint s.word s.state.val s.finite.parity p = some out) :
    out.eval = s.endpoint p := by
  unfold sideEndpoint at h
  cases hl : Quadratic462.cf (s.word.map Subtype.val) (anchor s.state.val s.finite.parity) with
  | none => simp only [hl,Option.bind_eq_bind,Option.bind_none] at h; cases h
  | some lo =>
    cases hh : Quadratic462.cf (s.word.map Subtype.val) (opposite s.state.val s.finite.parity) with
    | none => simp only [hl,hh,Option.bind_eq_bind,Option.bind_none,Option.bind_some,Option.pure_def] at h; cases h
    | some hi =>
      simp only [hl,hh,Option.bind_eq_bind,Option.bind_none,Option.bind_some,Option.pure_def,Option.some.injEq] at h
      subst out
      simp only [Quadratic462.eval_add,Quadratic462.eval_mul,Quadratic462.eval_ofRat,
        Rat.cast_sub,Rat.cast_one]
      have hlower := s.lower_eq_anchor
      simp only [RealSide.anchorValue] at hlower
      rw [Quadratic462.cf_sound _ _ _ hl,Quadratic462.cf_sound _ _ _ hh,
        ← hlower,← s.upper_eq_opposite]
      rfl

def endpoint (input : GraphCertificate.Input) (data : Data) (w : Witness) (p : ℚ) :
    Option Quadratic462 := do
  let l ← sideEndpoint w.left (data.sides[w.leftIndex]?.getD default).state
    (input.sides[w.leftIndex]?.getD default).parity p
  let r ← sideEndpoint w.right (data.sides[w.rightIndex]?.getD default).state
    (input.sides[w.rightIndex]?.getD default).parity p
  pure (Quadratic462.add l r)

theorem endpoint_eval (input : GraphCertificate.Input) (data : Data) (w : Witness)
    (hl : sideCheck input data w.left w.leftIndex = true)
    (hr : sideCheck input data w.right w.rightIndex = true)
    (p : ℚ) (out : Quadratic462) (h : endpoint input data w p = some out) :
    out.eval = (realSide input data w.left w.leftIndex hl).endpoint p+
      (realSide input data w.right w.rightIndex hr).endpoint p := by
  unfold endpoint at h
  cases hle : sideEndpoint w.left (data.sides[w.leftIndex]?.getD default).state
      (input.sides[w.leftIndex]?.getD default).parity p with
  | none => simp [hle] at h
  | some l =>
    cases hre : sideEndpoint w.right (data.sides[w.rightIndex]?.getD default).state
        (input.sides[w.rightIndex]?.getD default).parity p with
    | none => simp [hle,hre] at h
    | some r =>
      simp [hle,hre] at h
      subst out
      rw [Quadratic462.eval_add]
      exact congrArg₂ (·+·)
        (sideEndpoint_eval (realSide input data w.left w.leftIndex hl) p l (by simpa only [realSide,RealSide.word,RealSide.finite,List.append_nil] using hle))
        (sideEndpoint_eval (realSide input data w.right w.rightIndex hr) p r (by simpa only [realSide,RealSide.word,RealSide.finite,List.append_nil] using hre))

structure Row where
  witness : Witness
  lower : Quadratic462
  upper : Quadratic462
  deriving Inhabited

def Row.check (input : GraphCertificate.Input) (data : Data) (alive : ByteArray) (row : Row) : Bool :=
  Root.check input data alive row.witness &&
    decide (endpoint input data row.witness (input.bands[row.witness.type]?.getD default).lo = some row.lower) &&
    decide (endpoint input data row.witness (input.bands[row.witness.type]?.getD default).hi = some row.upper)

theorem Row.realizes (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell)
    (htable : Certificate.Accepted input data alive cells)
    (row : Row) (hr : row.check input data alive = true) {x : ℝ}
    (hx : x ∈ Set.Icc row.lower.eval row.upper.eval) :
    ∃ a ∈ admissibleTailSet row.witness.left,
      ∃ b ∈ admissibleTailSet row.witness.right, x = a+b := by
  simp only [Row.check,Bool.and_eq_true,decide_eq_true_eq] at hr
  rcases hr with ⟨⟨hw,hlo⟩,hhi⟩
  have hh := hw
  simp only [Root.check,Bool.and_eq_true] at hh
  have hl := hh.1.1.1.1.2
  have hr := hh.1.1.1.2
  have hel := endpoint_eval input data row.witness hl hr _ _ hlo
  have heh := endpoint_eval input data row.witness hl hr _ _ hhi
  obtain ⟨a,ha,b,hb,he⟩ := Root.realizes input data alive cells htable row.witness 0 hw (x := x) (by
    change 0+(realSide input data row.witness.left row.witness.leftIndex hl).endpoint
        (input.bands[row.witness.type]?.getD default).lo+
        (realSide input data row.witness.right row.witness.rightIndex hr).endpoint
          (input.bands[row.witness.type]?.getD default).lo ≤ x ∧
      x ≤ 0+(realSide input data row.witness.left row.witness.leftIndex hl).endpoint
        (input.bands[row.witness.type]?.getD default).hi+
        (realSide input data row.witness.right row.witness.rightIndex hr).endpoint
          (input.bands[row.witness.type]?.getD default).hi
    rw [zero_add,zero_add,← hel,← heh]
    exact hx)
  exact ⟨a,ha,b,hb,by simpa only [zero_add] using he⟩

def coverCheck (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (lo hi : Quadratic462) (rows : List Row) : Bool :=
  FiniteCover.check (fun r : Row => ⟨r.lower,r.upper⟩) Quadratic462.le
    (Row.check input data alive) lo hi rows

/-- A finite exact check yields actual admissible-tail sums at every target. -/
theorem coverCheck_sound (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell)
    (htable : Certificate.Accepted input data alive cells)
    (lo hi : Quadratic462) (rows : List Row)
    (hc : coverCheck input data alive lo hi rows = true) :
    ∀ x ∈ Set.Icc lo.eval hi.eval, ∃ row ∈ rows,
      wordsCheck row.witness = true ∧
      ∃ a ∈ admissibleTailSet row.witness.left,
        ∃ b ∈ admissibleTailSet row.witness.right, x = a+b := by
  intro x hx
  obtain ⟨r,hr,ha,hx⟩ := FiniteCover.check_sound (fun r : Row => ⟨r.lower,r.upper⟩)
    Quadratic462.le (Row.check input data alive) Quadratic462.eval
    Quadratic462.le_sound lo hi rows hc x hx
  refine ⟨r,hr,words_of_check input data alive r.witness ?_,r.realizes input data alive cells htable ha hx⟩
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ha).1).1

/-- Concrete upper-ray certificate, conditional only on finite checker acceptance. -/
theorem upper_ray_of_check (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell)
    (htable : Certificate.Accepted input data alive cells) (rows : List Row)
    (hc : coverCheck input data alive (Quadratic462.ofRat (1/2)) (Quadratic462.ofRat (3/2)) rows = true) :
    Set.Ici (13/2 : ℝ) ⊆ markovSpectrum := by
  apply Freiman.upper_ray_of_filling
  intro z hz
  obtain ⟨row,_,hw,x,⟨l,hl,hx⟩,y,⟨r,hr,hy⟩,he⟩ :=
    coverCheck_sound input data alive cells htable _ _ rows hc z (by simpa [Quadratic462.eval_ofRat] using hz)
  exact ⟨row.witness.left,row.witness.right,(setup row.witness 0 hw).left_bound,
    (setup row.witness 0 hw).right_bound,l,r,hl,hr,by rw [hx,hy] at he; exact he⟩

end Freiman.Root
