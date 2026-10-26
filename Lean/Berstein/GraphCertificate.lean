import Berstein.IntervalArithmetic
import Berstein.FiniteCover
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring

namespace Berstein.GraphCertificate

open scoped BigOperators

structure Transition where
  state : Int
  spine : Bool
  constant : Nat
  derivative : QBounds
  lowerId : Nat
  upperId : Nat
  deriving Repr, Inhabited

structure Side where
  parity : Bool
  shape : QBounds
  anchor : Nat
  tails : Array QBounds
  transitions : Array Transition
  ratios : Array QBounds := #[]
  deltas : Array QBounds := #[]
  deriving Repr, Inhabited

structure Successor where
  left : Nat
  right : Nat
  spine : Bool
  deriving Repr, Inhabited

structure Input where
  states : Nat
  extensions : Nat
  bins : Nat
  types : Nat
  firstExponent : Int
  root : Nat
  bands : Array QBounds
  grid : Array QBounds
  pairs : Array Successor
  sides : Array Side
  deriving Repr, Inhabited

def hull (a b : QBounds) : QBounds := ⟨min a.lo b.lo, max a.hi b.hi⟩
def intersect (a b : QBounds) : QBounds := ⟨max a.lo b.lo, min a.hi b.hi⟩

def ratioCorner (r : ℚ) (anchor tail : QBounds) : Option QBounds :=
  QBounds.checkedDiv
    (QBounds.add (QBounds.point 1) (QBounds.mul (QBounds.point r) anchor))
    (QBounds.add (QBounds.point 1) (QBounds.mul (QBounds.point r) tail))

/-- The quotient is monotone in the shape parameter for fixed actual tails;
its rational bounds at both shape endpoints are therefore sufficient. -/
def ratioBounds (shape anchor tail : QBounds) : Option QBounds := do
  let a ← ratioCorner shape.lo anchor tail
  let b ← ratioCorner shape.hi anchor tail
  pure (hull a b)

def deltaBounds (parity : Bool) (a b ra rb : QBounds) (same : Bool) : QBounds :=
  if same then QBounds.point 0 else
    let d := QBounds.mul (QBounds.sub a b) (QBounds.mul ra rb)
    if parity then QBounds.neg d else d

def prepareSide (side : Side) : Option Side := do
  let mut ratios := #[]
  for i in [:side.tails.size] do
    let r ← if i = side.anchor then some (QBounds.point 1)
      else ratioBounds side.shape (side.tails[side.anchor]?.getD default) (side.tails[i]?.getD default)
    ratios := ratios.push r
  let mut deltas := #[]
  for i in [:side.tails.size] do
    for j in [:side.tails.size] do
      deltas := deltas.push (deltaBounds side.parity
        (side.tails[i]?.getD default) (side.tails[j]?.getD default)
        (ratios[i]?.getD default) (ratios[j]?.getD default) (i == j))
  pure {side with ratios, deltas}

def Side.delta (s : Side) (i j : Nat) : QBounds :=
  s.deltas[i*s.tails.size+j]?.getD default

structure Flow where
  source : Nat
  target : Nat
  weight : ℚ
  deriving Repr, Inhabited

abbrev Coefficients := List (Nat × ℚ)

def coefficient (cs : Coefficients) (i : Nat) : ℚ :=
  (cs.map fun t ↦ if t.1 = i then t.2 else 0).sum

def termEval (cs : Coefficients) (z : Nat → ℝ) : ℝ :=
  (cs.map fun t ↦ (t.2 : ℝ) * z t.1).sum

def flowTerms (fs : List Flow) : Coefficients :=
  fs.flatMap fun f ↦ [(f.source,f.weight),(f.target,-f.weight)]

def flowEval (fs : List Flow) (z : Nat → ℝ) : ℝ :=
  (fs.map fun f ↦ (f.weight : ℝ) * (z f.source-z f.target)).sum

def transportSupport (cs : Coefficients) (fs : List Flow) : List Nat :=
  (cs ++ flowTerms fs).map Prod.fst

/-- The proposer is untrusted. Check the exact coefficient identity, all
index bounds, and the sign of every transported mass. -/
def checkTransport (count : Nat) (cs : Coefficients) (fs : List Flow) : Bool :=
  (transportSupport cs fs).all (fun i ↦ decide (i < count)) &&
    (fs.all (fun f ↦ decide (0 ≤ f.weight)) &&
      (transportSupport cs fs).all (fun i ↦ decide (coefficient cs i = coefficient (flowTerms fs) i)))

private theorem coefficient_cons (t : Nat × ℚ) (cs : Coefficients) (i : Nat) :
    coefficient (t::cs) i = (if t.1=i then t.2 else 0) + coefficient cs i := by
  simp [coefficient]

private theorem coefficient_dot (cs : Coefficients) (z : Nat → ℝ) (s : Finset Nat)
    (h : ∀ t ∈ cs, t.1 ∈ s) :
    (∑ i ∈ s, (coefficient cs i : ℝ) * z i) = termEval cs z := by
  induction cs with
  | nil => simp [coefficient, termEval]
  | cons t cs ih =>
      have ht : t.1 ∈ s := h t List.mem_cons_self
      have hc : ∀ u ∈ cs, u.1 ∈ s := fun u hu ↦ h u (List.mem_cons_of_mem t hu)
      have hcast (i : Nat) :
          ((if t.1=i then t.2 else 0 : ℚ) : ℝ) * z i =
            if i=t.1 then (t.2 : ℝ)*z i else 0 := by
        by_cases hi : i=t.1 <;> simp [hi, eq_comm]
      simp only [coefficient_cons, Rat.cast_add, add_mul, Finset.sum_add_distrib]
      simp_rw [hcast]
      rw [Finset.sum_ite_eq', if_pos ht, ih hc]
      rfl

private theorem flowTerms_eval (fs : List Flow) (z : Nat → ℝ) :
    termEval (flowTerms fs) z = flowEval fs z := by
  induction fs with
  | nil => simp [flowTerms, termEval, flowEval]
  | cons f fs ih =>
      simp only [flowTerms, List.flatMap_cons, termEval, List.map_append,
        List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Rat.cast_neg, neg_mul, add_zero, flowEval] at *
      rw [ih]
      ring

/-- Accepted transport coefficients give an exact real algebraic identity. -/
theorem checkTransport_identity (count : Nat) (cs : Coefficients) (fs : List Flow)
    (h : checkTransport count cs fs = true) (z : Nat → ℝ) :
    termEval cs z = flowEval fs z := by
  have hc : ∀ i ∈ transportSupport cs fs,
      coefficient cs i = coefficient (flowTerms fs) i := by
    have hs :
        (transportSupport cs fs).all (fun i ↦ decide (i < count)) = true ∧
          fs.all (fun f ↦ decide (0 ≤ f.weight)) = true ∧
            (transportSupport cs fs).all
              (fun i ↦ decide (coefficient cs i = coefficient (flowTerms fs) i)) = true := by
      simpa only [checkTransport, Bool.and_eq_true] using h
    simpa only [List.all_eq_true, decide_eq_true_eq] using hs.2.2
  let s := (transportSupport cs fs).toFinset
  have hcs : ∀ t ∈ cs, t.1 ∈ s := by
    intro t ht
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,List.mem_append_left _ ht,rfl⟩)
  have hfs : ∀ t ∈ flowTerms fs, t.1 ∈ s := by
    intro t ht
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,List.mem_append_right _ ht,rfl⟩)
  rw [← coefficient_dot cs z s hcs, ← flowTerms_eval fs z,
    ← coefficient_dot (flowTerms fs) z s hfs]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc i (List.mem_toFinset.mp hi)]

def flowBounds (delta : Nat → Nat → QBounds) : List Flow → QBounds
  | [] => QBounds.point 0
  | f::fs =>
      let rest := flowBounds delta fs
      let d := delta f.source f.target
      ⟨f.weight*d.lo+rest.lo, f.weight*d.hi+rest.hi⟩

/-- Soundness of positive-mass transport, using genuine normalized differences. -/
theorem flowBounds_sound (delta : Nat → Nat → QBounds) (fs : List Flow)
    (z : Nat → ℝ) (hd : ∀ f ∈ fs, (delta f.source f.target).mem (z f.source-z f.target))
    (hw : ∀ f ∈ fs, 0 ≤ f.weight) : (flowBounds delta fs).mem (flowEval fs z) := by
  induction fs with
  | nil => simp [flowBounds, flowEval, QBounds.point, QBounds.mem]
  | cons f fs ih =>
      have hdf := hd f List.mem_cons_self
      have hwf : (0 : ℝ) ≤ f.weight := by exact_mod_cast hw f List.mem_cons_self
      have ht := ih (fun g hg ↦ hd g (List.mem_cons_of_mem f hg))
        (fun g hg ↦ hw g (List.mem_cons_of_mem f hg))
      simp only [flowBounds, flowEval, List.map_cons, List.sum_cons,
        QBounds.mem, Rat.cast_add, Rat.cast_mul]
      exact ⟨add_le_add (mul_le_mul_of_nonneg_left hdf.1 hwf) ht.1,
        add_le_add (mul_le_mul_of_nonneg_left hdf.2 hwf) ht.2⟩

/-- Sparse coefficient aggregation is merely a proposal mechanism; the
transport checker subsequently verifies its result against the original list. -/
def insertCoefficient (t : Nat × ℚ) : Coefficients → Coefficients
  | [] => [t]
  | u::us => if t.1=u.1 then (u.1,u.2+t.2)::us else u::insertCoefficient t us

def proposeFlows : Nat → Coefficients → Coefficients → List Flow
  | 0, _, _ => []
  | _+1, [], _ => []
  | _+1, _, [] => []
  | fuel+1, p::ps, n::ns =>
      let mass := min p.2 n.2
      let ps' := if p.2=mass then ps else (p.1,p.2-mass)::ps
      let ns' := if n.2=mass then ns else (n.1,n.2-mass)::ns
      {source:=p.1,target:=n.1,weight:=mass}::proposeFlows fuel ps' ns'

def endpointCoefficients (alo ahi : Nat) (ap : ℚ) (blo bhi : Nat) (bp : ℚ) : Coefficients :=
  [(alo,1-ap),(ahi,ap),(blo,bp-1),(bhi,-bp)]

def differenceFromCoefficients (count : Nat) (delta : Nat → Nat → QBounds) (cs : Coefficients) : Option QBounds :=
  let compact := cs.foldl (fun acc t ↦ insertCoefficient t acc) []
  let ps := compact.filter (fun t ↦ 0 < t.2)
  let ns := (compact.filter (fun t ↦ t.2 < 0)).map fun t ↦ (t.1,-t.2)
  let f := proposeFlows 8 ps ns
  let g := proposeFlows 8 ps ns.reverse
  if checkTransport count cs f && checkTransport count cs g then
    some (intersect (flowBounds delta f) (flowBounds delta g))
  else none

def endpointDifference (side : Side) (ae : Nat) (ap : ℚ) (be : Nat) (bp : ℚ) : Option QBounds :=
  let a := side.transitions[ae]?.getD default
  let b := side.transitions[be]?.getD default
  differenceFromCoefficients side.tails.size side.delta
    (endpointCoefficients a.lowerId a.upperId ap b.lowerId b.upperId bp)

structure Endpoint where
  left : Nat
  right : Nat
  proportion : ℚ
  deriving DecidableEq, Repr, Inhabited

def endpointLeq (left right : Side) (ratio : QBounds) (a b : Endpoint) : Bool :=
  match endpointDifference left b.left b.proportion a.left a.proportion,
      endpointDifference right b.right b.proportion a.right a.proportion with
  | some x, some y => (QBounds.add x (QBounds.mul ratio y)).nonnegativeTest
  | _, _ => false

structure Vertex where
  pair : Nat
  band : QBounds
  first : Nat
  last : Nat
  typeMask : UInt32
  leftKnot : Nat
  rightKnotEncoded : Nat
  deriving Repr, Inhabited

structure Path where
  type : Nat
  vertices : List Nat
  links : List Nat
  deriving Repr, Inhabited

structure Cell where
  bin : Nat
  vertices : Array Vertex
  paths : List Path
  deriving Repr, Inhabited

def adopted (input : Input) (alive : ByteArray) (geometry bin type : Nat) : Bool :=
  alive[(geometry*input.bins+bin)*input.types+type]?.getD 0 == 1

def typeSelected (mask : UInt32) (type : Nat) : Bool :=
  ((mask >>> type.toUInt32) &&& 1) != 0

def parentEndpoint (p : ℚ) : Endpoint := ⟨0,0,p⟩

def vertexLower (input : Input) (v : Vertex) : Endpoint :=
  let pair := input.pairs[v.pair]?.getD default
  ⟨pair.left,pair.right,v.band.lo⟩

def vertexUpper (input : Input) (v : Vertex) : Endpoint :=
  let pair := input.pairs[v.pair]?.getD default
  ⟨pair.left,pair.right,v.band.hi⟩

def knots (input : Input) : Array ℚ :=
  ((input.bands.toList.flatMap fun b ↦ [b.lo,b.hi]).mergeSort (· ≤ ·)).eraseDups.toArray

private def bandLeq (a b : ℚ) : Bool := decide (a ≤ b)

def checkMergedBand (input : Input) (v : Vertex) : Bool :=
  let selected := (List.range input.types).filter (typeSelected v.typeMask)
  let ordered := selected.mergeSort fun a b ↦
    (input.bands[a]?.getD default).lo ≤ (input.bands[b]?.getD default).lo
  FiniteCover.check (fun t ↦ let b := input.bands[t]?.getD default; ⟨b.lo,b.hi⟩)
    bandLeq (typeSelected v.typeMask) v.band.lo v.band.hi ordered

def mappedBinsCheck (input : Input) (bin : Nat) (left right : Transition) (v : Vertex) : Bool :=
  if left.constant != 0 && left.constant == right.constant then
    decide (v.first = bin ∧ v.last = bin)
  else match QBounds.checkedDiv right.derivative left.derivative with
    | none => false
    | some factor =>
        let ratio := QBounds.mk (input.grid[bin]?.getD default).lo (input.grid[bin+1]?.getD default).hi
        let image := QBounds.mul ratio factor
        decide ((input.grid[v.first]?.getD default).hi ≤ image.lo ∧
          image.hi ≤ (input.grid[v.last+1]?.getD default).lo)

def checkVertex (input : Input) (alive : ByteArray) (geometry bin : Nat) (v : Vertex) : Bool := Id.run do
  if !(v.pair < input.pairs.size && v.first ≤ v.last && v.last < input.bins) then return false
  let pair := input.pairs[v.pair]?.getD default
  let leftSide := input.sides[geometry/input.states]?.getD default
  let rightSide := input.sides[geometry%input.states]?.getD default
  if !(pair.left < leftSide.transitions.size && pair.right < rightSide.transitions.size) then return false
  let left := leftSide.transitions[pair.left]?.getD default
  let right := rightSide.transitions[pair.right]?.getD default
  if !(0 ≤ left.state && left.state < input.states && 0 ≤ right.state && right.state < input.states) then return false
  if pair.spine && !(left.spine && right.spine) then return false
  if !(mappedBinsCheck input bin left right v && checkMergedBand input v) then return false
  let childGeometry := left.state.toNat*input.states+right.state.toNat
  return (List.range input.types).all fun type ↦
    !typeSelected v.typeMask type ||
      (List.range (v.last-v.first+1)).all fun d ↦ adopted input alive childGeometry (v.first+d) type

def checkIntersection (leq : Endpoint → Endpoint → Bool) (input : Input)
    (knotValues : Array ℚ) (v w : Vertex) (link : Nat) : Bool :=
  if link = 0 then
    leq (vertexLower input v) (vertexUpper input w) &&
      leq (vertexLower input w) (vertexUpper input v)
  else if link-1 < knotValues.size then
    let point := parentEndpoint (knotValues[link-1]?.getD 0)
    leq (vertexLower input v) point && (leq point (vertexUpper input v) &&
      (leq (vertexLower input w) point && leq point (vertexUpper input w)))
  else false

def checkPathTail (leq : Endpoint → Endpoint → Bool) (input : Input)
    (knotValues : Array ℚ) (vertices : Array Vertex) : List Nat → List Nat → Bool
  | [], _ => false
  | [i], [] => decide (i < vertices.size) &&
      leq (vertexLower input (vertices[i]?.getD default)) (vertexUpper input (vertices[i]?.getD default))
  | i::j::rest, link::links =>
      decide (i < vertices.size ∧ j < vertices.size) &&
        (leq (vertexLower input (vertices[i]?.getD default)) (vertexUpper input (vertices[i]?.getD default)) &&
          (checkIntersection leq input knotValues (vertices[i]?.getD default) (vertices[j]?.getD default) link &&
            checkPathTail leq input knotValues vertices (j::rest) links))
  | _, _ => false

def checkPath (leq : Endpoint → Endpoint → Bool) (input : Input)
    (knotValues : Array ℚ) (vertices : Array Vertex) (path : Path) : Bool :=
  match path.vertices with
  | [] => false
  | first::rest =>
    let last := rest.getLastD first
    let a := vertices[first]?.getD default
    let b := vertices[last]?.getD default
    let band := input.bands[path.type]?.getD default
    let leftPoint := parentEndpoint (knotValues[a.leftKnot]?.getD 0)
    let rightPoint := parentEndpoint (knotValues[b.rightKnotEncoded-1]?.getD 0)
    decide (path.type < input.types ∧ first < vertices.size ∧ last < vertices.size ∧
      a.leftKnot < knotValues.size ∧ 0 < b.rightKnotEncoded ∧ b.rightKnotEncoded ≤ knotValues.size) &&
      (leq (vertexLower input a) leftPoint &&
        (leq leftPoint (parentEndpoint band.lo) &&
          (leq (parentEndpoint band.hi) rightPoint &&
            (leq rightPoint (vertexUpper input b) &&
              checkPathTail leq input knotValues vertices path.vertices path.links))))

def checkCell (input : Input) (alive : ByteArray) (geometry : Nat) (cell : Cell) : Bool :=
  let left := input.sides[geometry/input.states]?.getD default
  let right := input.sides[geometry%input.states]?.getD default
  let ratio := QBounds.mk (input.grid[cell.bin]?.getD default).lo (input.grid[cell.bin+1]?.getD default).hi
  let selected := (List.range input.types).filter (adopted input alive geometry cell.bin)
  decide (cell.bin < input.bins ∧ cell.paths.map Path.type = selected) &&
    (cell.vertices.toList.all (checkVertex input alive geometry cell.bin) &&
      cell.paths.all (checkPath (endpointLeq left right ratio) input (knots input) cell.vertices))

theorem intersect_sound (a b : QBounds) (x : ℝ) (ha : a.mem x) (hb : b.mem x) :
    (intersect a b).mem x := by
  simp only [intersect, QBounds.mem, Rat.cast_max, Rat.cast_min]
  exact ⟨max_le ha.1 hb.1, le_min ha.2 hb.2⟩

theorem checkTransport_flow_facts (count : Nat) (cs : Coefficients) (fs : List Flow)
    (h : checkTransport count cs fs = true) :
    ∀ f ∈ fs, f.source < count ∧ f.target < count ∧ 0 ≤ f.weight := by
  have hs :
      (transportSupport cs fs).all (fun i ↦ decide (i < count)) = true ∧
        fs.all (fun f ↦ decide (0 ≤ f.weight)) = true ∧
          (transportSupport cs fs).all
            (fun i ↦ decide (coefficient cs i = coefficient (flowTerms fs) i)) = true := by
    simpa only [checkTransport, Bool.and_eq_true] using h
  have hi : ∀ i ∈ transportSupport cs fs, i < count := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hs.1
  have hw : ∀ f ∈ fs, 0 ≤ f.weight := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hs.2.1
  intro f hf
  have hsource : (f.source,f.weight) ∈ flowTerms fs :=
    List.mem_flatMap.mpr ⟨f,hf,by simp⟩
  have htarget : (f.target,-f.weight) ∈ flowTerms fs :=
    List.mem_flatMap.mpr ⟨f,hf,by simp⟩
  exact ⟨hi _ (List.mem_map.mpr ⟨_,List.mem_append_right _ hsource,rfl⟩),
    hi _ (List.mem_map.mpr ⟨_,List.mem_append_right _ htarget,rfl⟩),hw f hf⟩

theorem checkedTransport_bounds (count : Nat) (delta : Nat → Nat → QBounds)
    (cs : Coefficients) (fs : List Flow) (z : Nat → ℝ)
    (hd : ∀ i < count, ∀ j < count, (delta i j).mem (z i-z j))
    (h : checkTransport count cs fs = true) : (flowBounds delta fs).mem (termEval cs z) := by
  rw [checkTransport_identity count cs fs h z]
  have hf := checkTransport_flow_facts count cs fs h
  exact flowBounds_sound delta fs z
    (fun f hmem ↦ hd f.source (hf f hmem).1 f.target (hf f hmem).2.1)
    (fun f hmem ↦ (hf f hmem).2.2)

theorem differenceFromCoefficients_sound (count : Nat) (delta : Nat → Nat → QBounds)
    (cs : Coefficients) (z : Nat → ℝ)
    (hd : ∀ i < count, ∀ j < count, (delta i j).mem (z i-z j))
    (bounds : QBounds) (h : differenceFromCoefficients count delta cs = some bounds) :
    bounds.mem (termEval cs z) := by
  let compact := cs.foldl (fun acc t ↦ insertCoefficient t acc) []
  let ps := compact.filter (fun t ↦ 0 < t.2)
  let ns := (compact.filter (fun t ↦ t.2 < 0)).map fun t ↦ (t.1,-t.2)
  let f := proposeFlows 8 ps ns
  let g := proposeFlows 8 ps ns.reverse
  change (if checkTransport count cs f && checkTransport count cs g then
    some (intersect (flowBounds delta f) (flowBounds delta g)) else none) = some bounds at h
  split at h
  · next hchecked =>
      have hs : checkTransport count cs f = true ∧ checkTransport count cs g = true := by
        simpa only [Bool.and_eq_true] using hchecked
      have hb : intersect (flowBounds delta f) (flowBounds delta g) = bounds := Option.some.inj h
      rw [← hb]
      exact intersect_sound _ _ _ (checkedTransport_bounds count delta cs f z hd hs.1)
        (checkedTransport_bounds count delta cs g z hd hs.2)
  · contradiction

noncomputable def sideEndpointValue (side : Side) (z : Nat → ℝ) (e : Nat) (p : ℚ) : ℝ :=
  let t := side.transitions[e]?.getD default
  (1-(p : ℝ))*z t.lowerId+(p : ℝ)*z t.upperId

theorem endpointDifference_sound (side : Side) (z : Nat → ℝ)
    (hd : ∀ i < side.tails.size, ∀ j < side.tails.size, (side.delta i j).mem (z i-z j))
    (ae : Nat) (ap : ℚ) (be : Nat) (bp : ℚ) (bounds : QBounds)
    (h : endpointDifference side ae ap be bp = some bounds) :
    bounds.mem (sideEndpointValue side z ae ap-sideEndpointValue side z be bp) := by
  have hs := differenceFromCoefficients_sound side.tails.size side.delta _ z hd bounds h
  have heq : termEval (endpointCoefficients
      (side.transitions[ae]?.getD default).lowerId (side.transitions[ae]?.getD default).upperId ap
      (side.transitions[be]?.getD default).lowerId (side.transitions[be]?.getD default).upperId bp) z =
      sideEndpointValue side z ae ap-sideEndpointValue side z be bp := by
    simp only [termEval, endpointCoefficients, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Rat.cast_sub, Rat.cast_one, Rat.cast_neg, sideEndpointValue]
    ring
  rw [heq] at hs
  exact hs

noncomputable def endpointValue (left right : Side) (zl zr : Nat → ℝ) (ratio : ℝ) (e : Endpoint) : ℝ :=
  sideEndpointValue left zl e.left e.proportion + ratio*sideEndpointValue right zr e.right e.proportion

/-- The executable transport comparator is sound for actual endpoint values.
Only normalized differences and the actual derivative ratio need interpreting. -/
theorem endpointLeq_sound (left right : Side) (ratio : QBounds) (zl zr : Nat → ℝ) (S : ℝ)
    (hl : ∀ i < left.tails.size, ∀ j < left.tails.size, (left.delta i j).mem (zl i-zl j))
    (hr : ∀ i < right.tails.size, ∀ j < right.tails.size, (right.delta i j).mem (zr i-zr j))
    (hS : ratio.mem S) (a b : Endpoint) (h : endpointLeq left right ratio a b = true) :
    endpointValue left right zl zr S a ≤ endpointValue left right zl zr S b := by
  cases ha : endpointDifference left b.left b.proportion a.left a.proportion <;>
    cases hb : endpointDifference right b.right b.proportion a.right a.proportion <;>
      simp [endpointLeq, ha, hb] at h
  have hleft := endpointDifference_sound left zl hl _ _ _ _ _ ha
  have hright := endpointDifference_sound right zr hr _ _ _ _ _ hb
  have hnonnegative := QBounds.nonnegativeTest_sound _ _
    (QBounds.add_sound _ _ _ _ hleft (QBounds.mul_sound _ _ _ _ hS hright)) h
  dsimp [endpointValue]
  linarith

/-- A small preflight validates the arithmetic caches rather than trusting
an imperative preparation loop or externally supplied cached values. -/
def checkPrepared (side : Side) : Bool :=
  decide (side.ratios.size = side.tails.size ∧ side.deltas.size = side.tails.size*side.tails.size) &&
    ((List.range side.tails.size).all (fun i ↦ decide
      ((if i = side.anchor then some (QBounds.point 1)
        else ratioBounds side.shape (side.tails[side.anchor]?.getD default) (side.tails[i]?.getD default)) =
          some (side.ratios[i]?.getD default))) &&
      (List.range side.tails.size).all (fun i ↦ (List.range side.tails.size).all (fun j ↦
        decide (side.delta i j = deltaBounds side.parity
          (side.tails[i]?.getD default) (side.tails[j]?.getD default)
          (side.ratios[i]?.getD default) (side.ratios[j]?.getD default) (i == j)))))

theorem checkPrepared_sound (side : Side) (h : checkPrepared side = true) :
    (side.ratios.size = side.tails.size ∧ side.deltas.size = side.tails.size*side.tails.size) ∧
      (∀ i < side.tails.size,
        (if i = side.anchor then some (QBounds.point 1)
          else ratioBounds side.shape (side.tails[side.anchor]?.getD default) (side.tails[i]?.getD default)) =
            some (side.ratios[i]?.getD default)) ∧
      (∀ i < side.tails.size, ∀ j < side.tails.size,
        side.delta i j = deltaBounds side.parity (side.tails[i]?.getD default) (side.tails[j]?.getD default)
          (side.ratios[i]?.getD default) (side.ratios[j]?.getD default) (i == j)) := by
  simpa only [checkPrepared, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] using h

theorem checkIntersection_sound (leq : Endpoint → Endpoint → Bool) (input : Input)
    (knotValues : Array ℚ) (ev : Endpoint → ℝ)
    (hleq : ∀ a b, leq a b = true → ev a ≤ ev b) (v w : Vertex) (link : Nat)
    (h : checkIntersection leq input knotValues v w link = true) :
    ev (vertexLower input w) ≤ ev (vertexUpper input v) ∧
      ev (vertexLower input v) ≤ ev (vertexUpper input w) := by
  by_cases hz : link = 0
  · have hs : leq (vertexLower input v) (vertexUpper input w) = true ∧
        leq (vertexLower input w) (vertexUpper input v) = true := by
      simpa only [checkIntersection, if_pos hz, Bool.and_eq_true] using h
    exact ⟨hleq _ _ hs.2,hleq _ _ hs.1⟩
  · by_cases hk : link-1 < knotValues.size
    · let p := parentEndpoint (knotValues[link-1]?.getD 0)
      have hs : leq (vertexLower input v) p = true ∧ leq p (vertexUpper input v) = true ∧
          leq (vertexLower input w) p = true ∧ leq p (vertexUpper input w) = true := by
        simpa only [checkIntersection, if_neg hz, if_pos hk, Bool.and_eq_true] using h
      exact ⟨(hleq _ _ hs.2.2.1).trans (hleq _ _ hs.2.1),
        (hleq _ _ hs.1).trans (hleq _ _ hs.2.2.2)⟩
    · simp [checkIntersection,hz,hk] at h

/-- A checked path covers between its first lower and last upper endpoints;
shared parent knots justify graph edges without losing interval correlations. -/
theorem checkPathTail_sound (leq : Endpoint → Endpoint → Bool) (input : Input)
    (knotValues : Array ℚ) (vertices : Array Vertex) (ev : Endpoint → ℝ)
    (hleq : ∀ a b, leq a b = true → ev a ≤ ev b)
    (first : Nat) (rest links : List Nat)
    (h : checkPathTail leq input knotValues vertices (first::rest) links = true) :
    ∀ x : ℝ, ev (vertexLower input (vertices[first]?.getD default)) ≤ x →
      x ≤ ev (vertexUpper input (vertices[rest.getLastD first]?.getD default)) →
        ∃ i ∈ first::rest, i < vertices.size ∧
          x ∈ Set.Icc (ev (vertexLower input (vertices[i]?.getD default)))
            (ev (vertexUpper input (vertices[i]?.getD default))) := by
  induction rest generalizing first links with
  | nil =>
      cases links with
      | nil =>
          have hi : first < vertices.size := by
            have hs : first < vertices.size ∧
                leq (vertexLower input (vertices[first]?.getD default))
                  (vertexUpper input (vertices[first]?.getD default)) = true := by
              simpa only [checkPathTail, Bool.and_eq_true, decide_eq_true_eq] using h
            exact hs.1
          intro x hx hr
          exact ⟨first,List.mem_cons_self,hi,hx,hr⟩
      | cons link links => simp [checkPathTail] at h
  | cons next rest ih =>
      cases links with
      | nil => simp [checkPathTail] at h
      | cons link links =>
          have hs : (first < vertices.size ∧ next < vertices.size) ∧
              leq (vertexLower input (vertices[first]?.getD default))
                (vertexUpper input (vertices[first]?.getD default)) = true ∧
              checkIntersection leq input knotValues (vertices[first]?.getD default)
                (vertices[next]?.getD default) link = true ∧
              checkPathTail leq input knotValues vertices (next::rest) links = true := by
            simpa only [checkPathTail, Bool.and_eq_true, decide_eq_true_eq] using h
          intro x hx hr
          by_cases hu : x ≤ ev (vertexUpper input (vertices[first]?.getD default))
          · exact ⟨first,List.mem_cons_self,hs.1.1,hx,hu⟩
          · have hedge := (checkIntersection_sound leq input knotValues ev hleq _ _ link hs.2.2.1).1
            have hnext : ev (vertexLower input (vertices[next]?.getD default)) ≤ x :=
              hedge.trans (le_of_not_ge hu)
            obtain ⟨i,hi,hsize,hmem⟩ := ih next links hs.2.2.2 x hnext
              (by simpa only [List.getLastD_cons] using hr)
            exact ⟨i,List.mem_cons_of_mem first hi,hsize,hmem⟩

theorem checkPath_sound (leq : Endpoint → Endpoint → Bool) (input : Input)
    (knotValues : Array ℚ) (vertices : Array Vertex) (ev : Endpoint → ℝ)
    (hleq : ∀ a b, leq a b = true → ev a ≤ ev b) (path : Path)
    (h : checkPath leq input knotValues vertices path = true) :
    ∀ x ∈ Set.Icc (ev (parentEndpoint (input.bands[path.type]?.getD default).lo))
        (ev (parentEndpoint (input.bands[path.type]?.getD default).hi)),
      ∃ i ∈ path.vertices, i < vertices.size ∧
        x ∈ Set.Icc (ev (vertexLower input (vertices[i]?.getD default)))
          (ev (vertexUpper input (vertices[i]?.getD default))) := by
  cases hp : path.vertices with
  | nil => simp [checkPath,hp] at h
  | cons first rest =>
      let a := vertices[first]?.getD default
      let b := vertices[rest.getLastD first]?.getD default
      let band := input.bands[path.type]?.getD default
      let leftPoint := parentEndpoint (knotValues[a.leftKnot]?.getD 0)
      let rightPoint := parentEndpoint (knotValues[b.rightKnotEncoded-1]?.getD 0)
      have hs :
          (path.type < input.types ∧ first < vertices.size ∧ rest.getLastD first < vertices.size ∧
            a.leftKnot < knotValues.size ∧ 0 < b.rightKnotEncoded ∧ b.rightKnotEncoded ≤ knotValues.size) ∧
          leq (vertexLower input a) leftPoint = true ∧
          leq leftPoint (parentEndpoint band.lo) = true ∧
          leq (parentEndpoint band.hi) rightPoint = true ∧
          leq rightPoint (vertexUpper input b) = true ∧
          checkPathTail leq input knotValues vertices (first::rest) path.links = true := by
        simpa only [checkPath,hp,Bool.and_eq_true,decide_eq_true_eq] using h
      intro x hx
      obtain ⟨i,hi,hsize,hmem⟩ := checkPathTail_sound leq input knotValues vertices ev hleq
        first rest path.links hs.2.2.2.2.2 x
        (((hleq _ _ hs.2.1).trans (hleq _ _ hs.2.2.1)).trans hx.1)
        (hx.2.trans ((hleq _ _ hs.2.2.2.1).trans (hleq _ _ hs.2.2.2.2.1)))
      exact ⟨i,by simpa [hp] using hi,hsize,hmem⟩

/-- The actual cell checker yields endpoint coverage throughout the ratio
box; normalized continued-fraction differences supply its only real inputs. -/
theorem checkCell_coverage (input : Input) (alive : ByteArray) (geometry : Nat) (cell : Cell)
    (zl zr : Nat → ℝ) (S : ℝ)
    (hl : ∀ i < (input.sides[geometry/input.states]?.getD default).tails.size,
      ∀ j < (input.sides[geometry/input.states]?.getD default).tails.size,
      ((input.sides[geometry/input.states]?.getD default).delta i j).mem (zl i-zl j))
    (hr : ∀ i < (input.sides[geometry%input.states]?.getD default).tails.size,
      ∀ j < (input.sides[geometry%input.states]?.getD default).tails.size,
      ((input.sides[geometry%input.states]?.getD default).delta i j).mem (zr i-zr j))
    (hS : (QBounds.mk (input.grid[cell.bin]?.getD default).lo
      (input.grid[cell.bin+1]?.getD default).hi).mem S)
    (h : checkCell input alive geometry cell = true) :
    ∀ type < input.types, adopted input alive geometry cell.bin type = true →
      ∀ x ∈ Set.Icc
        (endpointValue (input.sides[geometry/input.states]?.getD default)
          (input.sides[geometry%input.states]?.getD default) zl zr S
          (parentEndpoint (input.bands[type]?.getD default).lo))
        (endpointValue (input.sides[geometry/input.states]?.getD default)
          (input.sides[geometry%input.states]?.getD default) zl zr S
          (parentEndpoint (input.bands[type]?.getD default).hi)),
      ∃ i < cell.vertices.size, checkVertex input alive geometry cell.bin (cell.vertices[i]?.getD default) = true ∧
        x ∈ Set.Icc
          (endpointValue (input.sides[geometry/input.states]?.getD default)
            (input.sides[geometry%input.states]?.getD default) zl zr S
            (vertexLower input (cell.vertices[i]?.getD default)))
          (endpointValue (input.sides[geometry/input.states]?.getD default)
            (input.sides[geometry%input.states]?.getD default) zl zr S
            (vertexUpper input (cell.vertices[i]?.getD default))) := by
  have hs :
      (cell.bin < input.bins ∧ cell.paths.map Path.type =
        (List.range input.types).filter (adopted input alive geometry cell.bin)) ∧
      (∀ v ∈ cell.vertices.toList, checkVertex input alive geometry cell.bin v = true) ∧
      (∀ p ∈ cell.paths, checkPath
        (endpointLeq (input.sides[geometry/input.states]?.getD default)
          (input.sides[geometry%input.states]?.getD default)
          ⟨(input.grid[cell.bin]?.getD default).lo,(input.grid[cell.bin+1]?.getD default).hi⟩)
        input (knots input) cell.vertices p = true) := by
    simpa only [checkCell,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] using h
  intro type htype hadopted x hx
  have ht : type ∈ cell.paths.map Path.type := by
    rw [hs.1.2]
    exact List.mem_filter.mpr ⟨List.mem_range.mpr htype,hadopted⟩
  obtain ⟨path,hpath,hpathtype⟩ := List.mem_map.mp ht
  have hc := checkPath_sound _ input (knots input) cell.vertices
    (endpointValue _ _ zl zr S) (endpointLeq_sound _ _ _ zl zr S hl hr hS) path (hs.2.2 path hpath)
  obtain ⟨i,hi,hsize,hmem⟩ := hc x (by simpa [hpathtype] using hx)
  refine ⟨i,hsize,hs.2.1 _ ?_,hmem⟩
  simp only [Array.getElem?_eq_getElem hsize, Option.getD_some]
  exact Array.getElem_mem_toList hsize

/-- Every point of a merged band belongs to an explicitly selected original
band. This proves that merging never enlarges the adopted union. -/
theorem checkMergedBand_sound (input : Input) (v : Vertex) (h : checkMergedBand input v = true) :
    ∀ x ∈ Set.Icc (v.band.lo : ℝ) (v.band.hi : ℝ),
      ∃ type < input.types, typeSelected v.typeMask type = true ∧
        x ∈ Set.Icc ((input.bands[type]?.getD default).lo : ℝ)
          ((input.bands[type]?.getD default).hi : ℝ) := by
  let selected := (List.range input.types).filter (typeSelected v.typeMask)
  let ordered := selected.mergeSort fun a b ↦
    (input.bands[a]?.getD default).lo ≤ (input.bands[b]?.getD default).lo
  have hleq : ∀ a b : ℚ, bandLeq a b = true → (a : ℝ) ≤ b := by
    intro a b hab
    have hrat : a ≤ b := of_decide_eq_true hab
    exact Rat.cast_mono hrat
  have hc := FiniteCover.check_sound (Endpoint := ℚ) (Vertex := Nat)
    (fun t ↦ let b := input.bands[t]?.getD default; (⟨b.lo,b.hi⟩ : FiniteCover.Interval ℚ))
    bandLeq (typeSelected v.typeMask) (fun q : ℚ ↦ (q : ℝ)) hleq
    v.band.lo v.band.hi ordered h
  intro x hx
  obtain ⟨type,ht,hselected,hmem⟩ := hc x hx
  have htype : type ∈ List.range input.types := by
    have hf : type ∈ selected := List.mem_mergeSort.mp ht
    exact (List.mem_filter.mp hf).1
  exact ⟨type,List.mem_range.mp htype,hselected,hmem⟩

/-- Every selected band is adopted in every destination bin, rather than
only at a representative destination ratio. -/
theorem checkVertex_destinations (input : Input) (alive : ByteArray) (geometry bin : Nat)
    (v : Vertex) (h : checkVertex input alive geometry bin v = true) :
    let pair := input.pairs[v.pair]?.getD default
    let left := (input.sides[geometry/input.states]?.getD default).transitions[pair.left]?.getD default
    let right := (input.sides[geometry%input.states]?.getD default).transitions[pair.right]?.getD default
    ∀ type < input.types, typeSelected v.typeMask type = true →
      ∀ k, v.first ≤ k → k ≤ v.last →
        adopted input alive (left.state.toNat*input.states+right.state.toNat) k type = true := by
  let pair := input.pairs[v.pair]?.getD default
  let left := (input.sides[geometry/input.states]?.getD default).transitions[pair.left]?.getD default
  let right := (input.sides[geometry%input.states]?.getD default).transitions[pair.right]?.getD default
  let childGeometry := left.state.toNat*input.states+right.state.toNat
  change ∀ type < input.types, typeSelected v.typeMask type = true →
    ∀ k, v.first ≤ k → k ≤ v.last → adopted input alive childGeometry k type = true
  unfold checkVertex at h
  dsimp only [Id.run, Pure.pure, Id.instMonad] at h
  repeat' first | split at h | contradiction
  have hall : ∀ type ∈ List.range input.types,
      (!typeSelected v.typeMask type ||
        (List.range (v.last-v.first+1)).all
          (fun d ↦ adopted input alive childGeometry (v.first+d) type)) = true := by
    simpa only [List.all_eq_true] using h
  intro type htype hselected k hfirst hlast
  have hc := hall type (List.mem_range.mpr htype)
  have hd : ∀ d ∈ List.range (v.last-v.first+1),
      adopted input alive childGeometry (v.first+d) type = true := by
    simpa only [hselected, Bool.not_true, Bool.false_or, List.all_eq_true] using hc
  have hk : k-v.first ∈ List.range (v.last-v.first+1) := List.mem_range.mpr (by omega)
  simpa only [Nat.add_sub_of_le hfirst] using hd (k-v.first) hk

end Berstein.GraphCertificate
