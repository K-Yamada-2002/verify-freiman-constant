import Berstein.GraphCertificate
import Berstein.Quadratic462

/-! Untrusted mathematical labels for the original graph input.
The checker must validate these labels before they acquire any meaning. -/

namespace Berstein.GraphMeaning

structure Side where
  state : Nat
  shape : QBounds
  raw : Array Quadratic462
  deriving Repr, Inhabited

structure Data where
  sides : Array Side
  extensions : Array (List Nat)
  constants : Array Quadratic462
  deriving Repr, Inhabited

end Berstein.GraphMeaning
