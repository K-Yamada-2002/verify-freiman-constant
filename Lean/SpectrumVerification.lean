import HallRay
import Berstein
import Freiman

/-! Entry point for the repository's shared formal-verification workspace.

Each concrete construction keeps its own namespace and explicit certificate
acceptance conditions. Importing this library does not establish acceptance of
the large concrete table by reduction inside the Lean kernel.
-/
