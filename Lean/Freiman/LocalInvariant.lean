import Freiman.Endpoint

/-! Uniform shape preservation for the recurrent local endpoint conditions.
The corner checks are finite kernel reductions; the conclusions hold for every
actual prefix whose denominator ratio lies in the parent box. -/
namespace Freiman.LocalInvariant
open Berstein Berstein.GraphMeaning HallRay.ContinuedFraction Endpoint

def entry_left : QBounds := ⟨8709/31250,278689/1000000⟩
def entry_right : QBounds := ⟨205479/500000,410959/1000000⟩
def period_left : QBounds := ⟨267649/1000000,267651/1000000⟩
def period_right : QBounds := ⟨368091/500000,736231/1000000⟩
def three_a_left : QBounds := ⟨756939/2500000,37847/125000⟩
def three_a_right : QBounds := ⟨756939/2500000,37847/125000⟩
def three_b_left : QBounds := ⟨756939/2500000,15139/50000⟩
def three_b_right : QBounds := ⟨756939/2500000,151403/500000⟩

theorem entry_left_return (a : Word)
    (h : entry_left.mem (denominatorRatio a)) :
    period_left.mem (denominatorRatio (a++U)) := by
  apply shape_transport a U entry_left period_left h
  · decide +kernel
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel

theorem entry_right_return (a : Word)
    (h : entry_right.mem (denominatorRatio a)) :
    period_right.mem (denominatorRatio (a++V)) := by
  apply shape_transport a V entry_right period_right h
  · decide +kernel
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel

theorem period_left_return (a : Word)
    (h : period_left.mem (denominatorRatio a)) :
    period_left.mem (denominatorRatio (a++U)) := by
  apply shape_transport a U period_left period_left h
  · decide +kernel
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel

theorem period_right_return (a : Word)
    (h : period_right.mem (denominatorRatio a)) :
    period_right.mem (denominatorRatio (a++V)) := by
  apply shape_transport a V period_right period_right h
  · decide +kernel
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel

theorem three_a_left_return (a : Word)
    (h : three_a_left.mem (denominatorRatio a)) :
    three_a_left.mem (denominatorRatio (a++loop33)) := by
  apply shape_transport a loop33 three_a_left three_a_left h
  · decide +kernel
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel

theorem three_a_right_return (a : Word)
    (h : three_a_right.mem (denominatorRatio a)) :
    three_a_right.mem (denominatorRatio (a++loop33)) := by
  apply shape_transport a loop33 three_a_right three_a_right h
  · decide +kernel
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel

theorem three_b_left_return (a : Word)
    (h : three_b_left.mem (denominatorRatio a)) :
    three_b_left.mem (denominatorRatio (a++loop33)) := by
  apply shape_transport a loop33 three_b_left three_b_left h
  · decide +kernel
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel

theorem three_b_right_return (a : Word)
    (h : three_b_right.mem (denominatorRatio a)) :
    three_b_right.mem (denominatorRatio (a++loop33)) := by
  apply shape_transport a loop33 three_b_right three_b_right h
  · decide +kernel
  · constructor <;> decide +kernel
  · constructor <;> decide +kernel

theorem period_left_legal (a : Word)
    (h : Forbidden31313.afterWord 0 a = some 1) :
    Forbidden31313.afterWord 0 (a++U) = some 1 := by
  rw [Forbidden31313.afterWord_append,h]
  change Forbidden31313.afterWord _ _ = _
  decide +kernel

theorem period_right_legal (a : Word)
    (h : Forbidden31313.afterWord 0 a = some 0) :
    Forbidden31313.afterWord 0 (a++V) = some 0 := by
  rw [Forbidden31313.afterWord_append,h]
  change Forbidden31313.afterWord _ _ = _
  decide +kernel

theorem loop_legal (a : Word)
    (h : Forbidden31313.afterWord 0 a = some 1) :
    Forbidden31313.afterWord 0 (a++loop33) = some 1 := by
  rw [Forbidden31313.afterWord_append,h]
  change Forbidden31313.afterWord _ _ = _
  decide +kernel

end Freiman.LocalInvariant
