import Freiman.LocalParser
import Freiman.Initial

namespace Freiman.LocalReplay
open Berstein Berstein.GraphReplay Freiman.RootReplay HallRay.ContinuedFraction

 def run : IO Unit := do
  let input ← parseText parseInput "../Freiman/certificates/graph_wide.dat"
  let alive ← IO.FS.readBinFile "../Freiman/certificates/graph_wide.alive.bin"
  let cs ← parseText conditions "generated/freiman_local.txt"
  if !(GraphMeaning.check input GraphMeaning.originalMeaning) then throw (IO.userError "input semantics rejected")
  for i in [:cs.size] do
    let c := cs[i]!
    if !(c.check) then
      IO.eprintln s!"left={c.left.check} right={c.right.check} leftStep0={c.left.checkStep 0} rightStep0={c.right.checkStep 0}"
      throw (IO.userError s!"local condition rejected: {i}")
    for j in [:c.menu.length] do
      let v := c.menu[j]!
      if !(Local.vertexCheck input GraphMeaning.originalMeaning alive cs c v) then
        IO.eprintln s!"leftstep={c.left.checkStep v.left} rightstep={c.right.checkStep v.right} destination={reprStr v.destination} steps={v.left},{v.right}"
        IO.eprintln s!"general={Local.generalCheck input GraphMeaning.originalMeaning alive c v} image={reprStr (Local.imageBox c v)}"
        match v.destination with
        | none => pure ()
        | some d => IO.eprintln s!"local={Local.localCheck cs c v d}"
        throw (IO.userError s!"local destination rejected: condition={i} vertex={j}")
    if !(Local.coverageCheck input GraphMeaning.originalMeaning alive cs c) then
      throw (IO.userError s!"local uniform cover rejected: {i}")
    IO.println s!"local_condition={i} vertices={c.menu.length} accepted=true"
  if !(Initial.check cs) then throw (IO.userError "initial closed endpoint interval rejected")
  let reject (accepted : Bool) (label : String) : IO Unit := do
    if accepted then throw (IO.userError s!"corruption accepted: {label}")
  let c0 := cs[0]!
  let c2 := cs[2]!
  let c3 := cs[3]!
  let cover (c : Local.Condition) := Local.coverageCheck input GraphMeaning.originalMeaning alive cs c
  reject (cover {c0 with menu := c0.menu.filter (fun v => v.destination != some 1)}) "missing periodic return"
  reject (cover {c3 with menu := c3.menu.filter (fun v => v.destination != some 3)}) "missing 33 return"
  reject ({c0.left with raw := c0.left.raw.set! 0 Quadratic462.zero}.check) "altered exact raw label"
  reject ({c2 with invariant := ⟨0,0⟩}.check) "zero V_zeta invariant"
  let some general := c0.menu.find? (fun v => v.destination.isNone) |
    throw (IO.userError "missing general successor in original menu")
  reject (Local.vertexCheck input GraphMeaning.originalMeaning alive cs c0 {general with typeMask := 0}) "missing general destination mask"
  reject (Local.vertexCheck input GraphMeaning.originalMeaning alive cs c0
    {c0.menu.head! with destination := some cs.size}) "out-of-range local destination"
  reject (Initial.check (cs.set! 0 {c0 with band := ⟨1/32,1/8⟩})) "initial endpoint omitted"
  let badTransition : GraphCertificate.Transition := {c0.left.numeric.transitions[0]! with derivative := ⟨0,0⟩}
  let badNumeric := {c0.left.numeric with transitions := c0.left.numeric.transitions.set! 0 badTransition}
  reject ({c0.left with numeric := badNumeric}.checkStep 0) "zero derivative bound"
  let vertices := cs.foldl (fun n c => n+c.menu.length) 0
  IO.println s!"accepted local_conditions={cs.size} local_vertices={vertices} initial_interval=true negative_controls=8"

end Freiman.LocalReplay

#eval Freiman.LocalReplay.run
