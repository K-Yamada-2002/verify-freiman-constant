import Freiman.LocalSide
import Freiman.Coordinate
import Berstein.RatioGrid

/-! Finite local-menu predicates. Every local root carries the actual prefixes;
only the finite shape, ratio and endpoint inequalities are encoded here. -/
namespace Freiman.Local
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction

structure Vertex where
  left : Nat
  right : Nat
  band : QBounds
  destination : Option Nat
  generalLeft : Nat := 0
  generalRight : Nat := 0
  first : Nat := 0
  last : Nat := 0
  typeMask : UInt32 := 0
  deriving Inhabited

abbrev Vertex.lower (v : Vertex) : GraphCertificate.Endpoint := ⟨v.left,v.right,v.band.lo⟩
abbrev Vertex.upper (v : Vertex) : GraphCertificate.Endpoint := ⟨v.left,v.right,v.band.hi⟩
abbrev Vertex.asGraph (v : Vertex) : GraphCertificate.Vertex :=
  ⟨0,v.band,v.first,v.last,v.typeMask,0,0⟩

structure Condition where
  kind : Nat
  left : RawSide
  right : RawSide
  band : QBounds
  invariant : QBounds
  scale : QBounds
  menu : List Vertex
  deriving Inhabited

abbrev Condition.useZeta (c : Condition) : Bool := decide (2 ≤ c.kind)
abbrev Condition.leftAnchor (c : Condition) : Quadratic462 := anchor c.left.spec.state.val c.left.spec.parity
abbrev Condition.rightAnchor (c : Condition) : Quadratic462 := anchor c.right.spec.state.val c.right.spec.parity

def Condition.check (c : Condition) : Bool :=
  c.left.check && c.right.check && c.left.checkStep 0 && c.right.checkStep 0 &&
    decide (c.left.extensions[0]? = some [] ∧ c.right.extensions[0]? = some [] ∧
      c.left.targets[0]? = some c.left.spec ∧ c.right.targets[0]? = some c.right.spec) &&
    decide (c.kind < 4 ∧ c.left.spec.state.val = 1 ∧ c.left.spec.parity = true ∧
      c.right.spec.parity = false ∧ c.right.spec.state.val = (if c.kind < 2 then 0 else 1)) &&
    decide (0 ≤ c.band.lo ∧ c.band.lo ≤ c.band.hi ∧ c.band.hi ≤ 1 ∧
      0 < c.invariant.lo ∧ c.scale.lo ≥ 1/10000 ∧ c.scale.hi ≤ 10000) &&
    (if c.useZeta then Coordinate.check c.leftAnchor c.rightAnchor false
      c.left.spec.shape c.right.spec.shape c.invariant c.scale else decide (c.scale = c.invariant))

/-- Actual local states, including the preserved derivative-ratio invariant. -/
structure State [Setup] (c : Condition) where
  left : ActualSide Setup.left c.left.spec
  right : ActualSide Setup.right c.right.spec
  ratio : c.invariant.mem (if c.useZeta then
    Normalization.scale right.word Endpoint.zeta/Normalization.scale left.word Endpoint.zeta
    else right.scale/left.scale)

namespace State
variable [Setup] {c : Condition}

noncomputable def endpoint (s : State c) (p : ℝ) : ℝ := Setup.center+s.left.endpoint p+s.right.endpoint p
noncomputable def target (s : State c) : Set ℝ := Set.Icc (s.endpoint c.band.lo) (s.endpoint c.band.hi)
noncomputable def pair (s : State c) : CylinderCover.LegalPair where
  leftExtension := s.left.extension
  rightExtension := s.right.extension
  leftDigits := s.left.digits
  rightDigits := s.right.digits
  leftState := c.left.spec.state
  rightState := c.right.spec.state
  leftLegal := s.left.legal
  rightLegal := s.right.legal
  leftAnchor := s.left.anchorValue
  rightAnchor := s.right.anchorValue
  leftAnchor_mem := s.left.anchor_mem
  rightAnchor_mem := s.right.anchor_mem

noncomputable def normalizedEndpoint (s : State c) (e : GraphCertificate.Endpoint) : ℝ :=
  GraphCertificate.endpointValue c.left.numeric c.right.numeric
    (normalized c.left s.left) (normalized c.right s.right) (s.right.scale/s.left.scale) e

end State

/-- The actual ratio belongs to the outer S-box used for uniform comparisons. -/
theorem State.scale_mem [Setup] {c : Condition} (s : State c) (hc : c.check = true) :
    c.scale.mem (s.right.scale/s.left.scale) := by
  have h := hc
  simp only [Condition.check,Bool.and_eq_true] at h
  have hh := h.2
  by_cases hz : c.useZeta = true
  · rw [if_pos hz] at hh
    have hratio := s.ratio
    rw [if_pos hz] at hratio
    exact Coordinate.from_zeta s.left.word s.right.word c.leftAnchor c.rightAnchor
      s.left.anchor_mem.1 s.right.anchor_mem.1 _ _ _ _ s.left.shape s.right.shape hratio hh
  · have hz' : c.useZeta = false := Bool.eq_false_iff.mpr hz
    simp only [hz',Bool.false_eq_true,if_false,decide_eq_true_eq] at hh
    have hratio := s.ratio
    simpa only [hh,hz',Bool.false_eq_true,if_false] using hratio

def imageBox (c : Condition) (v : Vertex) : Option QBounds := do
  let l ← c.left.numeric.transitions[v.left]?
  let r ← c.right.numeric.transitions[v.right]?
  let factor ← QBounds.checkedDiv r.derivative l.derivative
  pure (QBounds.mul c.scale factor)

def shapeBox (src : RawSide) (e : Nat) : Option QBounds := do
  let w ← src.extensions[e]?
  let a := shapeImage (w.map Subtype.val) src.spec.shape.lo
  let b := shapeImage (w.map Subtype.val) src.spec.shape.hi
  pure ⟨min a b,max a b⟩

def specMatches (input : GraphCertificate.Input) (data : Data) (i : Nat) (s : Spec) : Bool :=
  decide (i < input.states ∧ i < input.sides.size ∧ i < data.sides.size) &&
    decide ((input.sides[i]?.getD default).parity = s.parity ∧
      (data.sides[i]?.getD default).state = s.state.val ∧
      (data.sides[i]?.getD default).shape = s.shape)

def generalCheck (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (c : Condition) (v : Vertex) : Bool :=
  (do
    let l ← c.left.targets[v.left]?
    let r ← c.right.targets[v.right]?
    let image ← imageBox c v
    return specMatches input data v.generalLeft l && specMatches input data v.generalRight r &&
      decide (v.first ≤ v.last ∧ v.last < input.bins ∧ v.last+1 < input.grid.size) &&
      decide ((input.grid[v.first]?.getD default).hi ≤ image.lo ∧
        image.hi ≤ (input.grid[v.last+1]?.getD default).lo) &&
      GraphCertificate.checkMergedBand input v.asGraph &&
      (List.range input.types).all (fun t =>
        !GraphCertificate.typeSelected v.typeMask t ||
          (List.range (v.last-v.first+1)).all (fun d =>
            GraphCertificate.adopted input alive (v.generalLeft*input.states+v.generalRight) (v.first+d) t))).getD false

def localCheck (conditions : Array Condition) (c : Condition) (v : Vertex) (j : Nat) : Bool :=
  (do
    let dest ← conditions[j]?
    let l ← c.left.targets[v.left]?
    let r ← c.right.targets[v.right]?
    let u ← c.left.extensions[v.left]?
    let w ← c.right.extensions[v.right]?
    if !(decide (l = dest.left.spec ∧ r = dest.right.spec ∧ v.band = dest.band)) then return false
    if j = 1 then
      return decide (c.kind < 2 ∧ dest.kind = 1 ∧ u = Endpoint.U ∧ w = Endpoint.V ∧
        dest.invariant.lo ≤ c.invariant.lo ∧ c.invariant.hi ≤ dest.invariant.hi)
    else if 2 ≤ c.kind then
      return decide (dest.kind ≥ 2 ∧ u = Endpoint.loop33 ∧ w = Endpoint.loop33 ∧
        dest.invariant.lo ≤ c.invariant.lo ∧ c.invariant.hi ≤ dest.invariant.hi)
    else
      let image ← imageBox c v
      let leftShape ← shapeBox c.left v.left
      let rightShape ← shapeBox c.right v.right
      return decide (2 ≤ dest.kind) && Coordinate.check dest.leftAnchor dest.rightAnchor true
        leftShape rightShape image dest.invariant).getD false

def vertexCheck (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (conditions : Array Condition) (c : Condition) (v : Vertex) : Bool :=
  c.left.checkStep v.left && c.right.checkStep v.right &&
    (match c.left.extensions[v.left]?, c.right.extensions[v.right]? with
    | some u, some w => decide (0 < u.length+w.length)
    | _, _ => false) &&
    decide (0 ≤ v.band.lo ∧ v.band.lo ≤ v.band.hi ∧ v.band.hi ≤ 1) &&
    (match v.destination with
    | none => generalCheck input data alive c v
    | some j => localCheck conditions c v j)

def coverageCheck (input : GraphCertificate.Input) (data : Data) (alive : ByteArray)
    (conditions : Array Condition) (c : Condition) : Bool :=
  FiniteCover.check (fun v : Vertex => ⟨v.lower,v.upper⟩)
    (GraphCertificate.endpointLeq c.left.numeric c.right.numeric c.scale)
    (vertexCheck input data alive conditions c)
    (GraphCertificate.parentEndpoint c.band.lo) (GraphCertificate.parentEndpoint c.band.hi) c.menu

end Freiman.Local
