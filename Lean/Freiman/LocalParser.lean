import Freiman.LocalCheck
import Freiman.ReplaySupport

namespace Freiman.LocalReplay
open Berstein Berstein.GraphReplay Freiman.RootReplay HallRay.ContinuedFraction

 def spec : TextParser Local.Spec := do
  let n ← natural
  let p ← flag
  let b ← do let l ← rat; let h ← rat; pure (⟨l,h⟩ : QBounds)
  if h : n < 5 then pure ⟨⟨n,h⟩,p,b⟩ else throw "invalid local state"

 def box : TextParser QBounds := do
  let l ← rat
  let h ← rat
  if h < l then throw "reversed local box"
  pure ⟨l,h⟩

 def extension : TextParser Word := do
  let n ← natural
  if n > 1000 then throw "local extension too long"
  let mut w := []
  for _ in [:n] do
    let a ← natural
    if h : 1 ≤ a then
      if a > 3 then throw "local extension digit exceeds three"
      w := w ++ [⟨a,h⟩]
    else throw "zero local digit"
  pure w

 def side : TextParser Local.RawSide := do
  let sp ← spec
  let n ← natural
  if n = 0 || n > 1000 then throw "invalid local raw count"
  let mut raw := #[]
  let mut tails := #[]
  for _ in [:n] do
    raw := raw.push (← quad)
    tails := tails.push (← box)
  let m ← natural
  if m = 0 || m > 1000 then throw "invalid local step count"
  let mut transitions := #[]
  let mut extensions := #[]
  let mut targets := #[]
  for _ in [:m] do
    let d ← box
    let lo ← natural
    let hi ← natural
    if lo ≥ n || hi ≥ n then throw "invalid local endpoint index"
    transitions := transitions.push (⟨0,false,0,d,lo,hi⟩ : GraphCertificate.Transition)
    extensions := extensions.push (← extension)
    targets := targets.push (← spec)
  let proposed : GraphCertificate.Side := ⟨sp.parity,sp.shape,0,tails,transitions,#[],#[]⟩
  let some numeric := GraphCertificate.prepareSide proposed | throw "local cache preparation failed"
  pure ⟨sp,numeric,raw,extensions,targets⟩

 def vertex : TextParser Local.Vertex := do
  let l ← natural
  let r ← natural
  let b ← box
  let target ← natural
  if target = 0 then
    let gl ← natural
    let gr ← natural
    let first ← natural
    let last ← natural
    let mask ← natural
    if mask ≥ 2^32 then throw "invalid local type mask"
    pure ⟨l,r,b,none,gl,gr,first,last,mask.toUInt32⟩
  else pure ⟨l,r,b,some (target-1),0,0,0,0,0⟩

 def conditions : TextParser (Array Local.Condition) := do
  let n ← natural
  if n != 4 then throw "expected four local conditions"
  let mut result := #[]
  for _ in [:n] do
    let k ← natural
    let l ← side
    let r ← side
    let band ← box
    let inv ← box
    let scale ← box
    let m ← natural
    if m = 0 || m > 1000 then throw "invalid local menu count"
    let mut menu := []
    for _ in [:m] do menu := menu ++ [← vertex]
    result := result.push ⟨k,l,r,band,inv,scale,menu⟩
  let tokens ← get
  if tokens.pos != tokens.words.size then throw "extra local tokens"
  pure result

end Freiman.LocalReplay
