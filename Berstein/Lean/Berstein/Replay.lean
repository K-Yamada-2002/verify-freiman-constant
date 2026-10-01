import Berstein.GraphCertificate
import Berstein.GraphCertificateFacts
import Berstein.SemanticCheck
import Berstein.RootCheck
import Berstein.Data.Meaning

/-!
Executable replay of untrusted compact graph witnesses against the immutable
input and adoption bitmap. No subprocess result enters any mathematical check.
-/
namespace Berstein.GraphReplay
open GraphCertificate

private def dyadicUnit : Int := 281474976710656

structure Tokens where
  words : Array String
  pos : Nat := 0
abbrev TextParser := StateT Tokens (Except String)

def token : TextParser String := do
  let s ← get
  let some word := s.words[s.pos]? | throw s!"missing token {s.pos}"
  set {s with pos := s.pos+1}
  pure word

def integer : TextParser Int := do
  let t ← token
  let some v := t.toInt? | throw s!"invalid integer {t}"
  pure v

def natural : TextParser Nat := do
  let v ← integer
  if v < 0 then throw s!"negative natural {v}"
  pure v.toNat

def bounds : TextParser QBounds := do
  let lo ← integer
  let hi ← integer
  if hi < lo then throw "reversed interval"
  pure ⟨(lo : ℚ)/dyadicUnit,(hi : ℚ)/dyadicUnit⟩

def flag : TextParser Bool := do
  match ← natural with
  | 0 => pure false
  | 1 => pure true
  | _ => throw "invalid Boolean flag"

def parseInput : TextParser Input := do
  if (← token) != "FREIMAN_DYADIC_GRAPH_V1" then throw "invalid input magic"
  let states ← natural
  let extensions ← natural
  let firstExponent ← integer
  let lastExponent ← integer
  let types ← natural
  let pairCount ← natural
  let root ← natural
  if states = 0 || extensions = 0 || types = 0 || types > 32 || lastExponent < firstExponent then
    throw "invalid dimensions"
  let bins := (lastExponent-firstExponent+1).toNat
  let mut bands := #[]
  for _ in [:types] do
    let b ← bounds
    if !(0 ≤ b.lo && b.lo < b.hi && b.hi ≤ 1) then throw "invalid band"
    bands := bands.push b
  let mut pairs := #[]
  for _ in [:pairCount] do
    let left ← natural
    let right ← natural
    let spine ← flag
    if left ≥ extensions || right ≥ extensions || (left = 0 && right = 0) then throw "invalid pair"
    pairs := pairs.push ⟨left,right,spine⟩
  let mut grid := #[]
  for _ in [:bins+1] do
    grid := grid.push (← bounds)
  if (grid[0]?.getD default).lo ≤ 0 then throw "nonpositive grid"
  for k in [:bins] do
    if !((grid[k]?.getD default).hi < (grid[k+1]?.getD default).lo) then throw "unordered grid"
  let mut sides := #[]
  for state in [:states] do
    let width ← bounds
    if width.lo ≤ 0 then throw "nonpositive width"
    let parity ← flag
    let shape ← bounds
    if shape.lo < 0 then throw "negative shape"
    let anchor ← natural
    let count ← natural
    if count = 0 || anchor ≥ count then throw "invalid anchor"
    let mut tails := #[]
    for _ in [:count] do
      tails := tails.push (← bounds)
    let mut transitions := #[]
    for _ in [:extensions] do
      let child ← integer
      if child = -1 then transitions := transitions.push ⟨-1,false,0,default,0,0⟩
      else
        if child < 0 || child ≥ states then throw "invalid child state"
        let spine ← flag
        let constant ← natural
        let derivative ← bounds
        if derivative.lo ≤ 0 then throw "nonpositive derivative"
        let _ ← bounds
        let _ ← bounds
        let lowerId ← natural
        let upperId ← natural
        if lowerId ≥ count || upperId ≥ count then throw "invalid raw endpoint"
        transitions := transitions.push ⟨child,spine,constant,derivative,lowerId,upperId⟩
    let empty := transitions[0]?.getD default
    if empty.state != (state : Int) || empty.lowerId != anchor then throw "empty transition mismatch"
    let raw : Side := ⟨parity,shape,anchor,tails,transitions,#[],#[]⟩
    let some side := prepareSide raw | throw "failed side arithmetic"
    if !checkPrepared side then throw "invalid prepared arithmetic cache"
    sides := sides.push side
  let s ← get
  if s.pos != s.words.size then throw "extra input token"
  pure ⟨states,extensions,bins,types,firstExponent,root,bands,grid,pairs,sides⟩

structure Cursor where
  bytes : ByteArray
  pos : Nat := 0
abbrev BinaryParser := StateT Cursor (Except String)

def readUnsigned (length : Nat) : BinaryParser Nat := do
  let s ← get
  if s.pos+length > s.bytes.size then throw "truncated witness"
  let mut result := 0
  for i in [:length] do
    result := result + (s.bytes[s.pos+i]?.getD 0).toNat * 256^i
  set {s with pos := s.pos+length}
  pure result

def u32 : BinaryParser Nat := readUnsigned 4
def u64 : BinaryParser Nat := readUnsigned 8

def parseVertex : BinaryParser Vertex := do
  let pair ← u32
  let lo ← u64
  let hi ← u64
  let first ← u32
  let last ← u32
  let mask ← u32
  let leftKnot ← u32
  let rightKnotEncoded ← u32
  pure ⟨pair,⟨(lo : ℚ)/dyadicUnit,(hi : ℚ)/dyadicUnit⟩,
    first,last,mask.toUInt32,leftKnot,rightKnotEncoded⟩

def parsePath : BinaryParser Path := do
  let type ← u32
  let count ← u32
  if count = 0 || count > 65536 then throw "invalid path size"
  let mut vertices := #[]
  for _ in [:count] do vertices := vertices.push (← u32)
  let mut links := #[]
  for _ in [:count-1] do links := links.push (← u32)
  pure ⟨type,vertices.toList,links.toList⟩

def parseCell (bin : Nat) : BinaryParser Cell := do
  let count ← u32
  if count > 65536 then throw "invalid vertex count"
  let mut vertices := #[]
  for _ in [:count] do vertices := vertices.push (← parseVertex)
  let pathCount ← u32
  if pathCount > 32 then throw "invalid row count"
  let mut paths := #[]
  for _ in [:pathCount] do paths := paths.push (← parsePath)
  pure ⟨bin,vertices,paths.toList⟩

def parseGeometry (geometry : Nat) : BinaryParser (List Cell) := do
  if (← u32) != 0x3143474c then throw "invalid witness magic"
  if (← u32) != geometry then throw "wrong witness geometry"
  let mut cells := #[]
  let mut bin ← u32
  while bin != 0xffffffff do
    cells := cells.push (← parseCell bin)
    bin ← u32
  let s ← get
  if s.pos != s.bytes.size then throw "trailing witness byte"
  pure cells.toList

end Berstein.GraphReplay

open Berstein.GraphReplay Berstein.GraphCertificate

def main (args : List String) : IO UInt32 := do
  try
    if args.length != 3 && args.length != 5 then
      IO.eprintln "usage: graphReplay input.dat alive.bin witnesses_folder [geometry_begin geometry_end]"
      return 2
    let source ← IO.FS.readFile (args[0]!)
    let words := (source.splitToList Char.isWhitespace).filter (· != "")
    let input ← match (parseInput.run ⟨words.toArray,0⟩) with
      | .error e => throw (IO.userError e)
      | .ok (input,_) => pure input
    let alive ← IO.FS.readBinFile (args[1]!)
    if alive.size != input.states*input.states*input.bins*input.types then
      throw (IO.userError "wrong immutable bitmap size")
    if !(alive.data.all fun b ↦ b == 0 || b == 1) then throw (IO.userError "non-Boolean bitmap")
    if !(Berstein.GraphMeaning.check input Berstein.GraphMeaning.originalMeaning) then
      throw (IO.userError "exact continued-fraction input meaning rejected")
    if !(Berstein.GraphMeaning.checkRoots input Berstein.GraphMeaning.originalMeaning alive) then
      throw (IO.userError "initial interval root coverage rejected")
    let begin := if args.length = 5 then (args[3]!).toNat?.getD (input.states*input.states) else 0
    let finish := if args.length = 5 then (args[4]!).toNat?.getD 0 else input.states*input.states
    if !(begin < finish && finish ≤ input.states*input.states) then throw (IO.userError "invalid geometry range")
    let started ← IO.monoMsNow
    let mut rowCount := 0
    let mut cellCount := 0
    let mut vertexCount := 0
    let mut pathNodes := 0
    for geometry in [begin:finish] do
      let bytes ← IO.FS.readBinFile s!"{args[2]!}/geometry_{geometry}.bin"
      let cells ← match parseGeometry geometry |>.run ⟨bytes,0⟩ with
        | .error e => throw (IO.userError s!"geometry {geometry}: {e}")
        | .ok (cells,_) => pure cells
      if !(checkGeometry input alive geometry cells) then
        for cell in cells do
          if !(checkCell input alive geometry cell) then
            throw (IO.userError s!"rejected geometry={geometry} bin={cell.bin}")
        throw (IO.userError s!"missing/extra cell in geometry {geometry}")
      for cell in cells do
        cellCount := cellCount+1
        vertexCount := vertexCount+cell.vertices.size
        rowCount := rowCount+cell.paths.length
        pathNodes := pathNodes+(cell.paths.map (·.vertices.length)).sum
      let elapsed := (← IO.monoMsNow)-started
      IO.println s!"geometry={geometry} rows={rowCount} cells={cellCount} selected_vertices={vertexCount} path_nodes={pathNodes} elapsed_ms={elapsed}"
    IO.println s!"accepted geometries=[{begin},{finish}) adopted_rows={rowCount} adopted_cells={cellCount}"
    return 0
  catch e =>
    IO.eprintln s!"replay error: {e}"
    return 1
