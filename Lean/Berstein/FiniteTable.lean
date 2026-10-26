import Mathlib

/-!
# Exhaustive fixed-table closure checking

The input table is immutable. Every adopted row must have a successful local
cover check, and every destination row required by its witness must be adopted.
In the actual application `destinations` must include every box in a certified
cover of the child's ratio image, not only a representative sample box. A
shared boundary is assigned to a checked containing box. The local check's numerical and
semantic soundness is an explicit interface, not a trusted Boolean input.
-/

namespace Berstein
namespace FiniteTable

variable {size : ℕ}

/-- Executable exhaustive checker; no deletion or repair of failed rows. -/
def check (active localCheck : (Fin size) → Bool) (destinations : (Fin size) → List (Fin size)) : Bool :=
  (List.finRange size).all fun r =>
    !active r || (localCheck r && (destinations r).all active)

/-- Require the specified initial rows in addition to exhaustive closure. -/
def checkWithRoots (roots : List (Fin size)) (active localCheck : (Fin size) → Bool)
    (destinations : (Fin size) → List (Fin size)) : Bool :=
  check active localCheck destinations && roots.all active

theorem checkWithRoots_sound (roots : List (Fin size)) (active localCheck : (Fin size) → Bool)
    (destinations : (Fin size) → List (Fin size))
    (h : checkWithRoots roots active localCheck destinations = true) :
    check active localCheck destinations = true ∧ ∀ r ∈ roots, active r = true := by
  simpa [checkWithRoots, Bool.and_eq_true, List.all_eq_true] using h

/-- All adopted rows passed; all listed destination boxes are adopted. -/
theorem check_sound (active localCheck : (Fin size) → Bool) (destinations : (Fin size) → List (Fin size))
    (h : check active localCheck destinations = true) (r : (Fin size)) (hr : active r = true) :
    localCheck r = true ∧ ∀ q ∈ destinations r, active q = true := by
  have hall : ∀ r : (Fin size),
      (!active r || (localCheck r && (destinations r).all active)) = true := by
    simpa only [check, List.all_eq_true, List.mem_finRange, forall_const] using h
  simpa [hr, List.all_eq_true] using hall r

/-- Semantic connection: a locally checked witness covers the actual target
by legal children whose row indices belong to its checked destination list.

This theorem isolates the exhaustive-table step. `localSound` must be proved
from the numerical checker and its continued-fraction interpretation before
the concrete external table is certified. -/
theorem closed_cover_of_check {State : Type*}
    (active localCheck : (Fin size) → Bool) (destinations : (Fin size) → List (Fin size))
    (row : State → (Fin size)) (target : State → Set ℝ) (next : State → State → Prop)
    (localSound : ∀ s, localCheck (row s) = true →
      ∀ t ∈ target s, ∃ s', next s s' ∧ row s' ∈ destinations (row s) ∧ t ∈ target s')
    (h : check active localCheck destinations = true) :
    ∀ s, active (row s) = true → ∀ t ∈ target s,
      ∃ s', next s s' ∧ active (row s') = true ∧ t ∈ target s' := by
  intro s hs t ht
  obtain ⟨hloc, hdest⟩ := check_sound active localCheck destinations h (row s) hs
  obtain ⟨s', hnext, hrow, htarget⟩ := localSound s hloc t ht
  exact ⟨s', hnext, hdest _ hrow, htarget⟩

/- Regression controls: checking one representative destination is not enough. -/

private def activeExample (r : Fin 3) : Bool := r.val < 2

private def validDestinations (r : Fin 3) : List (Fin 3) :=
  if r.val = 0 then [1] else [0]

private def missingBoxDestinations (r : Fin 3) : List (Fin 3) :=
  if r.val = 0 then [1, 2] else [0]

theorem positive_control :
    check activeExample (fun _ => true) validDestinations = true := by decide

theorem missing_destination_rejected :
    check activeExample (fun _ => true) missingBoxDestinations = false := by decide

theorem failed_local_cover_rejected :
    check activeExample (fun r => r.val != 1) validDestinations = false := by decide

theorem missing_root_rejected :
    checkWithRoots [0, 2] activeExample (fun _ => true) validDestinations = false := by decide

end FiniteTable
end Berstein
