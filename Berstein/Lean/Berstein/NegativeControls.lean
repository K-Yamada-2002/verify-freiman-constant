import Berstein.Replay

/-! In-memory mutation checks for the immutable below-ray replay assets. -/

open Berstein.GraphReplay Berstein.GraphCertificate Berstein.GraphMeaning

namespace Berstein.NegativeControls

private def firstUsedConstant (input : Input) : Option Nat :=
  (input.sides.toList.flatMap fun side =>
    side.transitions.toList.map Transition.constant).find? (· != 0)

private def requireRejected (name : String) (accepted : Bool) : IO Unit := do
  if accepted then
    throw <| IO.userError s!"negative control unexpectedly accepted: {name}"
  IO.println s!"PASS rejected corruption: {name}"

def run : IO Unit := do
  let inputText ← IO.FS.readFile "../../Freiman/data/graph_wide.dat"
  let inputWords := (inputText.splitToList Char.isWhitespace).filter (· != "")
  let input ← match (parseInput.run ⟨inputWords.toArray, 0⟩) with
    | .error e => throw <| IO.userError s!"input parse failed: {e}"
    | .ok (input, _) => pure input
  let alive ← IO.FS.readBinFile "../../Freiman/data/graph_wide.json.alive.bin"
  let geometryBytes ← IO.FS.readBinFile "generated/witnesses/geometry_0.bin"
  let cells ← match (parseGeometry 0).run ⟨geometryBytes, 0⟩ with
    | .error e => throw <| IO.userError s!"geometry 0 parse failed: {e}"
    | .ok (cells, _) => pure cells

  if !(GraphMeaning.check input GraphMeaning.originalMeaning) then
    throw <| IO.userError "baseline exact-semantic check rejected"
  if !(GraphMeaning.checkRoots input GraphMeaning.originalMeaning alive) then
    throw <| IO.userError "baseline root check rejected"
  if !(checkGeometry input alive 0 cells) then
    throw <| IO.userError "baseline geometry 0 rejected"
  IO.println "PASS accepted baseline input, root, and geometry 0"

  let rootBit := (193 * input.bins + 135) * input.types + 3
  if rootBit >= alive.size then
    throw <| IO.userError "root corruption index out of range"
  let withoutRootBit := alive.set! rootBit 0
  requireRejected "root 193 / bin 135 / type 3 adoption bit removed"
    (GraphMeaning.checkRoots input GraphMeaning.originalMeaning withoutRootBit)

  let meaningSide := GraphMeaning.originalMeaning.sides[0]!
  let badRawSide := { meaningSide with
    raw := meaningSide.raw.set! 0 Berstein.Quadratic462.zero }
  let badRawMeaning := { GraphMeaning.originalMeaning with
    sides := GraphMeaning.originalMeaning.sides.set! 0 badRawSide }
  requireRejected "exact meaning raw label changed to zero"
    (GraphMeaning.check input badRawMeaning)

  let some constantId := firstUsedConstant input
    | throw <| IO.userError "input has no used nonzero constant"
  let oldConstant := GraphMeaning.originalMeaning.constants[constantId]!
  let changedConstant := { oldConstant with a := oldConstant.a + 1 }
  let badConstantMeaning := { GraphMeaning.originalMeaning with
    constants := GraphMeaning.originalMeaning.constants.set! constantId changedConstant }
  requireRejected "used nonzero exact constant increased by one"
    (GraphMeaning.check input badConstantMeaning)

  match cells with
  | [] => throw <| IO.userError "geometry 0 has no cells"
  | firstCell :: remainingCells =>
      requireRejected "geometry 0 cell removed"
        (checkGeometry input alive 0 remainingCells)
      if firstCell.paths.isEmpty then
        throw <| IO.userError "first geometry 0 cell has no adopted paths"
      let missingPathCell := { firstCell with paths := firstCell.paths.drop 1 }
      requireRejected "first geometry 0 cell adopted path removed"
        (checkGeometry input alive 0 (missingPathCell :: remainingCells))
      let pathVertexIds := firstCell.paths.flatMap Path.vertices
      let some vertexId := (List.range firstCell.vertices.size).find? (fun i =>
          (firstCell.vertices[i]?.getD default).typeMask != 0 && pathVertexIds.contains i)
        | throw <| IO.userError "first geometry 0 cell has no selected vertex"
      let selectedVertex := firstCell.vertices[vertexId]!
      let zeroMaskVertex := { selectedVertex with typeMask := 0 }
      let maskCell := { firstCell with
        vertices := firstCell.vertices.set! vertexId zeroMaskVertex }
      requireRejected "selected vertex destination mask zeroed"
        (checkGeometry input alive 0 (maskCell :: remainingCells))

end Berstein.NegativeControls

#eval Berstein.NegativeControls.run
