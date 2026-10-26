import Berstein.IntervalExpression
import Berstein.FiniteTable

/-!
# A composed, executable numerical table checker

This combines exhaustive row checking, rational expression evaluation, uniform
interval coverage, and adoption of all listed destination rows. It certifies
these numerical statements for any supplied certificate; its theorem has no
unproved arithmetic or comparator-soundness premise.

The external `graph_wide` input has not yet been translated to this format.
In particular, matching expressions to true CF endpoints and showing that the
listed destinations cover each child's true state/ratio image remain separate
semantic obligations. Arbitrary intervals are not declared to be CF children.
-/

namespace Berstein.NumericalTable
open IntervalExpression

structure Child (size : ℕ) where
  interval : FiniteCover.Interval Expr
  destinations : List (Fin size)

structure Cell (size : ℕ) where
  boxes : Array QBounds
  parent : FiniteCover.Interval Expr
  chain : List (Child size)

def Cell.bounds {size : ℕ} (cell : Cell size) (k : ℕ) : QBounds :=
  cell.boxes[k]?.getD (QBounds.point 0)

def Cell.destinations {size : ℕ} (cell : Cell size) : List (Fin size) :=
  cell.chain.flatMap Child.destinations

/-- All chain children have a destination and together cover the parent. -/
def checkCell {size : ℕ} (cell : Cell size) : Bool :=
  (cell.chain.all (fun c => !c.destinations.isEmpty)) &&
    verifiedCheckCover cell.bounds Child.interval (fun _ => true)
      cell.parent.lower cell.parent.upper cell.chain

/-- The table is fixed; all active rows and all requested roots are checked. -/
def check {size : ℕ} (active : Fin size → Bool) (cells : Fin size → Cell size)
    (roots : List (Fin size)) : Bool :=
  FiniteTable.checkWithRoots roots active (fun r => checkCell (cells r))
    (fun r => (cells r).destinations)

/-- Acceptance proves coverage for every real environment in every adopted
row's parameter box, with every listed destination row adopted. -/
theorem check_sound {size : ℕ} (active : Fin size → Bool)
    (cells : Fin size → Cell size) (roots : List (Fin size))
    (h : check active cells roots = true) :
    (∀ r ∈ roots, active r = true) ∧
    ∀ r, active r = true → ∀ env : ℕ → ℝ,
      (∀ k, (cells r).bounds k |>.mem (env k)) →
      ∀ x ∈ Set.Icc (eval env (cells r).parent.lower) (eval env (cells r).parent.upper),
        ∃ child ∈ (cells r).chain,
          child.destinations ≠ [] ∧
          (∀ q ∈ child.destinations, active q = true) ∧
          x ∈ Set.Icc (eval env child.interval.lower) (eval env child.interval.upper) := by
  obtain ⟨hclosed, hroots⟩ := FiniteTable.checkWithRoots_sound roots active
    (fun r => checkCell (cells r)) (fun r => (cells r).destinations) h
  refine ⟨hroots, ?_⟩
  intro r hr env henv x hx
  obtain ⟨hcell, hadopted⟩ := FiniteTable.check_sound active
    (fun r => checkCell (cells r)) (fun r => (cells r).destinations) hclosed r hr
  have hc : (cells r).chain.all (fun c => !c.destinations.isEmpty) = true ∧
      verifiedCheckCover (cells r).bounds Child.interval (fun _ => true)
        (cells r).parent.lower (cells r).parent.upper (cells r).chain = true := by
    simpa only [checkCell, Bool.and_eq_true] using hcell
  obtain ⟨child, hchild, _, hmem⟩ := verifiedCheckCover_sound
    (cells r).bounds Child.interval (fun _ => true)
    (cells r).parent.lower (cells r).parent.upper (cells r).chain hc.2 env henv x hx
  refine ⟨child, hchild, ?_, ?_, hmem⟩
  · have hn := List.all_eq_true.mp hc.1 child hchild
    simpa using hn
  · intro q hq
    apply hadopted q
    exact List.mem_flatMap.mpr ⟨child, hchild, hq⟩

end Berstein.NumericalTable
