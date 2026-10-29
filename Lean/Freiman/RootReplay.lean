import Freiman.ReplaySupport

namespace Freiman.RootReplay
open Berstein Berstein.GraphReplay

def run : IO Unit := do
  let input ← parseText parseInput "../Freiman/certificates/graph_wide.dat"
  let alive ← IO.FS.readBinFile "../Freiman/certificates/graph_wide.alive.bin"
  let witnesses ← parseText roots "generated/freiman_roots.txt"
  if !(GraphMeaning.check input GraphMeaning.originalMeaning) then
    throw (IO.userError "semantic input rejected")
  for i in [:witnesses.size] do
    if !(Root.check input GraphMeaning.originalMeaning alive witnesses[i]!) then
      throw (IO.userError s!"arbitrary root rejected at index {i}")
  let cover ← parseText upperRows "generated/freiman_upper.txt"
  let coverCheck := Root.coverCheck input GraphMeaning.originalMeaning alive
    (Quadratic462.ofRat (1/2)) (Quadratic462.ofRat (3/2))
  if !(coverCheck cover) then throw (IO.userError "upper-ray sum cover rejected")
  let first := witnesses[0]!
  let reject (accepted : Bool) (label : String) : IO Unit := do
    if accepted then throw (IO.userError s!"corruption accepted: {label}")
  let rootCheck := Root.check input GraphMeaning.originalMeaning alive
  reject (rootCheck {first with left := []}) "empty root word"
  reject (rootCheck {first with leftIndex := input.states}) "wrong state index"
  reject (rootCheck {first with bin := input.bins}) "wrong bin"
  reject (rootCheck {first with type := input.types}) "wrong band"
  reject (coverCheck []) "missing upper cover"
  let firstRow := cover.head!
  reject (coverCheck ({firstRow with lower := Quadratic462.ofRat (-100)}::cover.tail)) "altered exact endpoint"
  reject (coverCheck (cover.take (cover.length-1))) "missing last covering interval"
  IO.println s!"accepted arbitrary_roots={witnesses.size} upper_cover_rows={cover.length} negative_controls=7 whole_freiman_ray=false"

end Freiman.RootReplay

#eval Freiman.RootReplay.run
