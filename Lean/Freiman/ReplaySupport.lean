import Freiman.RootCover
import Berstein.Replay

/-! Execution of the proved-sound arbitrary-root checker. This is execution
 evidence, not kernel reduction of the large table or a half-line theorem.
 `Berstein.Replay` supplies only parsers; its main function is not invoked. -/
namespace Freiman.RootReplay
open Berstein Berstein.GraphReplay

def word : TextParser HallRay.ContinuedFraction.Word := do
  let count ← natural
  if count = 0 || count > 1024 then throw "invalid word length"
  let mut digits := []
  for _ in [:count] do
    let d ← natural
    if d = 0 || d > 4 then throw "invalid root digit"
    digits := digits ++ [d]
  pure (GraphMeaning.asWord digits)

def witness : TextParser Root.Witness := do
  let left ← word
  let right ← word
  let leftIndex ← natural
  let rightIndex ← natural
  let bin ← natural
  let type ← natural
  pure ⟨left,right,leftIndex,rightIndex,bin,type⟩

def roots : TextParser (Array Root.Witness) := do
  let count ← natural
  if count = 0 || count > 1000000 then throw "invalid root count"
  let mut result := #[]
  for _ in [:count] do result := result.push (← witness)
  let state ← get
  if state.pos != state.words.size then throw "extra root tokens"
  pure result

def rat : TextParser ℚ := do
  let numerator ← integer
  let denominator ← natural
  if denominator = 0 then throw "zero rational denominator"
  pure ((numerator : ℚ)/denominator)

def quad : TextParser Quadratic462 := do
  let a ← rat
  let b ← rat
  pure ⟨a,b⟩

def upperRows : TextParser (List Root.Row) := do
  let count ← natural
  if count = 0 || count > 1000000 then throw "invalid upper-cover count"
  let mut result := []
  for _ in [:count] do
    let w ← witness
    let lo ← quad
    let hi ← quad
    result := result ++ [⟨w,lo,hi⟩]
  let state ← get
  if state.pos != state.words.size then throw "extra upper-cover tokens"
  pure result

def parseText {α : Type} (parser : TextParser α) (path : System.FilePath) : IO α := do
  let raw ← IO.FS.readFile path
  let tokens := (raw.splitOn " ").flatMap (fun s => s.splitOn "\n")
    |>.filter (fun s => !s.isEmpty) |>.toArray
  match parser.run ⟨tokens,0⟩ with
  | .error e => throw (IO.userError e)
  | .ok (result,_) => pure result

end Freiman.RootReplay
