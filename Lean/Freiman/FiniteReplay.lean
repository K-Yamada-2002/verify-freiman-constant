import Freiman.FiniteRay
import Freiman.Initial
import Freiman.ReplaySupport

/-! Execution driver for the finite initial ray, excluding the local endpoint
interval. No IO result is inserted into a mathematical proof. -/
namespace Freiman.FiniteReplay
open Berstein Berstein.GraphReplay Freiman.RootReplay HallRay.ContinuedFraction

structure Parsed where
  spectra : Array Spectral.Certificate
  lower : Quadratic462
  upper : Quadratic462
  rows : List FiniteRay.Row

def state : TextParser Forbidden31313.State := do
  let n ← natural
  if h : n < 5 then pure ⟨n,h⟩ else throw "invalid automaton state"

def spectral : TextParser Spectral.Certificate := do
  let left ← word
  let right ← word
  let c ← natural
  if h : 1 ≤ c then
    let sl ← state
    let sr ← state
    let bound ← quad
    pure ⟨left,right,⟨c,h⟩,sl,sr,bound⟩
  else throw "nonpositive center"

def data : TextParser Parsed := do
  let count ← natural
  if count = 0 || count > 10000 then throw "invalid spectral count"
  let mut spectra := #[]
  for _ in [:count] do spectra := spectra.push (← spectral)
  let lo ← quad
  let hi ← quad
  let nr ← natural
  if nr = 0 || nr > 1000000 then throw "invalid finite cover count"
  let mut rows := []
  for _ in [:nr] do
    let w ← witness
    let rl ← quad
    let rh ← quad
    let i ← natural
    let l ← quad
    let h ← quad
    rows := rows ++ [⟨⟨w,rl,rh⟩,i,l,h⟩]
  let tokens ← get
  if tokens.pos != tokens.words.size then throw "extra finite-ray tokens"
  pure ⟨spectra,lo,hi,rows⟩

def run : IO Unit := do
  let input ← parseText parseInput "../Freiman/certificates/graph_wide.dat"
  let alive ← IO.FS.readBinFile "../Freiman/certificates/graph_wide.alive.bin"
  let d ← parseText data "generated/freiman_finite.txt"
  if !(decide (d.lower = Initial.upper ∧ d.upper = Quadratic462.ofRat (13/2))) then
    throw (IO.userError "finite-ray target endpoints differ from the final theorem")
  if !(GraphMeaning.check input GraphMeaning.originalMeaning) then throw (IO.userError "input semantics rejected")
  let mut i := 0
  for s in d.spectra do
    if !(Spectral.check s) then throw (IO.userError s!"spectral certificate rejected: {i}")
    i := i+1
    if i % 25 = 0 then IO.println s!"spectral_checked={i}/{d.spectra.size}"
  let coverCheck := FiniteCover.check (fun r : FiniteRay.Row => ⟨r.lower,r.upper⟩)
    Quadratic462.le (FiniteRay.Row.check input GraphMeaning.originalMeaning alive d.spectra) d.lower d.upper
  if !(coverCheck d.rows) then
    for r in d.rows do
      if !(r.check input GraphMeaning.originalMeaning alive d.spectra) then
        throw (IO.userError s!"finite root rejected: spectral={r.spectralIndex}")
    throw (IO.userError "finite cover connectivity rejected")
  if Spectral.check {d.spectra[0]! with bound := Quadratic462.zero} then
    throw (IO.userError "zero spectral bound accepted")
  if coverCheck [] then throw (IO.userError "empty finite cover accepted")
  if coverCheck (d.rows.take (d.rows.length-1)) then throw (IO.userError "truncated finite cover accepted")
  IO.println s!"accepted spectral_roots={d.spectra.size} finite_rows={d.rows.length} negative_controls=3"

end Freiman.FiniteReplay

#eval Freiman.FiniteReplay.run
