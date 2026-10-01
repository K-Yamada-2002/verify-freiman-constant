import Berstein.SemanticData

namespace Berstein.GraphMeaning

def lower (s : Nat) : Quadratic462 :=
  if s = 2 then ⟨-1/2, 1/28⟩
  else if s = 4 then ⟨-24/53, 2/53⟩ else ⟨-29/53, 2/53⟩

def upper (s : Nat) : Quadratic462 :=
  if s = 1 then ⟨-28/19, 2/19⟩
  else if s = 3 then ⟨-29/19, 2/19⟩ else ⟨-1, 1/12⟩

def anchor (s : Nat) (parity : Bool) : Quadratic462 :=
  if parity then upper s else lower s

def opposite (s : Nat) (parity : Bool) : Quadratic462 :=
  if parity then lower s else upper s

def contains (b : QBounds) (x : Quadratic462) : Bool :=
  Quadratic462.le (Quadratic462.ofRat b.lo) x && Quadratic462.le x (Quadratic462.ofRat b.hi)

def stateStep (s d : Nat) : Option Nat :=
  if d = 1 then some (if s = 1 then 2 else if s = 3 then 4 else 0)
  else if d = 3 then (if s = 2 then some 3 else if s = 4 then none else some 1)
  else some 0

def after : Nat → List Nat → Option Nat
  | s, [] => some s
  | s, d::w => (stateStep s d).bind (fun t => after t w)

structure Coeffs where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving Repr, DecidableEq, Inhabited

def coeffs : List Nat → Coeffs
  | [] => ⟨0,1,1,0⟩
  | d::w => let m := coeffs w; ⟨m.c,m.d,d*m.c+m.a,d*m.d+m.b⟩

def shapeImage (w : List Nat) (r : ℚ) : ℚ :=
  let m := coeffs w
  (m.d+m.b*r)/(m.c+m.a*r)

def derivativeDen (w : List Nat) (y : Quadratic462) : Quadratic462 × Quadratic462 :=
  let m := coeffs w
  (Quadratic462.add (Quadratic462.ofRat m.c) (Quadratic462.mul (Quadratic462.ofRat m.d) y),
   Quadratic462.add (Quadratic462.ofRat m.a) (Quadratic462.mul (Quadratic462.ofRat m.b) y))

def derivativeAt (w : List Nat) (x y : Quadratic462) (r : ℚ) : Option Quadratic462 := do
  let (d₀,d₁) := derivativeDen w y
  let inverse ← Quadratic462.checkedInv (Quadratic462.add d₀ (Quadratic462.mul (Quadratic462.ofRat r) d₁))
  let quotient := Quadratic462.mul (Quadratic462.add Quadratic462.one (Quadratic462.mul (Quadratic462.ofRat r) x)) inverse
  pure (Quadratic462.mul quotient quotient)

def checkTransition (input : GraphCertificate.Input) (data : Data) (i e : Nat) : Bool :=
  (do
    let s ← input.sides[i]?
    let m ← data.sides[i]?
    let tr ← s.transitions[e]?
    if tr.state < 0 then return true
    let child := tr.state.toNat
    let c ← input.sides[child]?
    let cm ← data.sides[child]?
    let w ← data.extensions[e]?
    let lo ← m.raw[tr.lowerId]?
    let hi ← m.raw[tr.upperId]?
    let x := anchor m.state s.parity
    let y := anchor cm.state c.parity
    let lowValue ← Quadratic462.cf w y
    let highValue ← Quadratic462.cf w (opposite cm.state c.parity)
    let dl ← derivativeAt w x y m.shape.lo
    let dh ← derivativeAt w x y m.shape.hi
    let shapeLo := shapeImage w m.shape.lo
    let shapeHi := shapeImage w m.shape.hi
    let basic := decide (after m.state w = some cm.state) &&
      (c.parity == (s.parity != decide (w.length % 2 = 1))) &&
      decide (lowValue = lo) && decide (highValue = hi) &&
      decide (cm.shape.lo ≤ shapeLo ∧ shapeLo ≤ cm.shape.hi) &&
      decide (cm.shape.lo ≤ shapeHi ∧ shapeHi ≤ cm.shape.hi) &&
      contains tr.derivative dl && contains tr.derivative dh &&
      decide (0 < tr.derivative.lo)
    if tr.constant = 0 then return basic
    let constant ← data.constants[tr.constant]?
    let (d₀,d₁) := derivativeDen w y
    return basic && decide (Quadratic462.mul x d₀ = d₁) && decide (dl = constant)
  ).getD false

def checkSide (input : GraphCertificate.Input) (data : Data) (i : Nat) : Bool :=
  (do
    let s ← input.sides[i]?
    let m ← data.sides[i]?
    let x ← m.raw[s.anchor]?
    let zeroTransition : GraphCertificate.Transition ← s.transitions[0]?
    return decide (m.state < 5) &&
      decide (0 ≤ m.shape.lo ∧ m.shape.lo ≤ m.shape.hi ∧ m.shape.hi ≤ 1) &&
      decide (s.shape.lo ≤ m.shape.lo ∧ m.shape.hi ≤ s.shape.hi ∧ 0 ≤ s.shape.lo) &&
      decide (m.raw.size = s.tails.size) &&
      decide (s.transitions.size = input.extensions) &&
      decide (x = anchor m.state s.parity) &&
      decide (zeroTransition.state = (i : Int) ∧ zeroTransition.lowerId = s.anchor) &&
      (List.range m.raw.size).all (fun j =>
        match s.tails[j]?, m.raw[j]? with
        | some box, some raw => contains box raw && contains ⟨0,1⟩ raw
        | _, _ => false) &&
      (List.range input.extensions).all (checkTransition input data i)
  ).getD false

/-- Mathematical input checks are independent of the large alive table. -/
def check (input : GraphCertificate.Input) (data : Data) : Bool :=
  decide (input.states = input.sides.size ∧ input.states = data.sides.size ∧
    input.extensions = data.extensions.size ∧ input.grid.size = input.bins+1 ∧
    input.bands.size = input.types) &&
  decide (data.extensions[0]? = some []) &&
  data.extensions.all (fun w => w.all (fun d => decide (1 ≤ d ∧ d ≤ 3))) &&
  input.pairs.all (fun p =>
    match data.extensions[p.left]?, data.extensions[p.right]? with
    | some a, some b => decide (0 < a.length+b.length)
    | _, _ => false) &&
  input.bands.all (fun b => decide (0 ≤ b.lo ∧ b.lo ≤ b.hi ∧ b.hi ≤ 1)) &&
  (List.range input.grid.size).all (fun k =>
    match input.grid[k]? with
    | none => false
    | some b =>
      let cut := (51/50 : ℚ)^(input.firstExponent+(k : Int))
      decide (b.lo ≤ cut ∧ cut ≤ b.hi ∧ 1/10000 ≤ cut ∧ cut ≤ 10000)) &&
  (List.range input.states).all (checkSide input data)

end Berstein.GraphMeaning
