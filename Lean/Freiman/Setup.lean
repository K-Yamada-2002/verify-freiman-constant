import Berstein.GraphSuccessor

/-! Parameters of a Freiman cylinder construction. The two fixed words may
contain 4; all added digits are in 1,2,3. The center is independent of them. -/
namespace Freiman
open HallRay.ContinuedFraction

class Setup where
  left : Word
  right : Word
  left_nonempty : left ≠ []
  right_nonempty : right ≠ []
  left_bound : ∀ a ∈ left, a.val ≤ 4
  right_bound : ∀ a ∈ right, a.val ≤ 4
  center : ℝ

end Freiman
