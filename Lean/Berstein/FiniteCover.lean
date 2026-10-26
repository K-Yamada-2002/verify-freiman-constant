import Mathlib.Data.Real.Basic

/-!
# A verified checker for finite interval-cover witnesses

Endpoints are identifiers, interpreted as real numbers only in the soundness
theorem. An executable comparison backend may use exact rationals, algebraic
numbers, or certified interval bounds. It need only prove that an accepted
comparison is valid; completeness is unnecessary.

The witness is a list of vertices (for instance `Fin n`). The checker verifies
admissibility, nonempty intervals, both inequalities for every overlap, and
coverage of the parent's two endpoints. Its soundness proof does not assume
that lower or upper endpoints increase along the witness.
-/

namespace Berstein.FiniteCover

structure Interval (Endpoint : Type*) where
  lower : Endpoint
  upper : Endpoint
  deriving DecidableEq, Repr

/-- Verify a nonempty chain with an explicit first vertex. Every used vertex
must be admitted by the finite family. -/
def checkTail {Endpoint Vertex : Type*}
    (interval : Vertex → Interval Endpoint) (leq : Endpoint → Endpoint → Bool)
    (admitted : Vertex → Bool) (right : Endpoint) : Vertex → List Vertex → Bool
  | v, [] => admitted v &&
      (leq (interval v).lower (interval v).upper && leq right (interval v).upper)
  | v, w :: rest => admitted v &&
      (leq (interval v).lower (interval v).upper &&
        (leq (interval w).lower (interval v).upper &&
          (leq (interval v).lower (interval w).upper &&
            checkTail interval leq admitted right w rest)))

/-- An empty chain is rejected. For a nonempty chain, check both parent
boundaries and every child/overlap obligation. -/
def check {Endpoint Vertex : Type*}
    (interval : Vertex → Interval Endpoint) (leq : Endpoint → Endpoint → Bool)
    (admitted : Vertex → Bool) (left right : Endpoint) : List Vertex → Bool
  | [] => false
  | v :: rest => leq (interval v).lower left &&
      checkTail interval leq admitted right v rest

theorem checkTail_sound {Endpoint Vertex : Type*}
    (interval : Vertex → Interval Endpoint) (leq : Endpoint → Endpoint → Bool)
    (admitted : Vertex → Bool) (eval : Endpoint → ℝ)
    (hleq : ∀ a b, leq a b = true → eval a ≤ eval b)
    (right : Endpoint) (first : Vertex) (rest : List Vertex)
    (h : checkTail interval leq admitted right first rest = true) :
    ∀ x : ℝ, eval (interval first).lower ≤ x → x ≤ eval right →
      ∃ v ∈ first :: rest, admitted v = true ∧
        x ∈ Set.Icc (eval (interval v).lower) (eval (interval v).upper) := by
  induction rest generalizing first with
  | nil =>
      have hs : admitted first = true ∧
          leq (interval first).lower (interval first).upper = true ∧
          leq right (interval first).upper = true := by
        simpa only [checkTail, Bool.and_eq_true] using h
      intro x hx hr
      exact ⟨first, List.mem_cons_self, hs.1, hx, hr.trans (hleq _ _ hs.2.2)⟩
  | cons next rest ih =>
      have hs : admitted first = true ∧
          leq (interval first).lower (interval first).upper = true ∧
          leq (interval next).lower (interval first).upper = true ∧
          leq (interval first).lower (interval next).upper = true ∧
          checkTail interval leq admitted right next rest = true := by
        simpa only [checkTail, Bool.and_eq_true] using h
      intro x hx hr
      by_cases hupper : x ≤ eval (interval first).upper
      · exact ⟨first, List.mem_cons_self, hs.1, hx, hupper⟩
      · have hnext : eval (interval next).lower ≤ x :=
          (hleq _ _ hs.2.2.1).trans (le_of_not_ge hupper)
        obtain ⟨v, hv, ha, hmem⟩ := ih next hs.2.2.2.2 x hnext hr
        exact ⟨v, List.mem_cons_of_mem first hv, ha, hmem⟩

/-- Every accepted witness covers all real points of the parent interval by
admitted children. This is the single checker soundness theorem to reuse for
all table boxes and all parameter interpretations. -/
theorem check_sound {Endpoint Vertex : Type*}
    (interval : Vertex → Interval Endpoint) (leq : Endpoint → Endpoint → Bool)
    (admitted : Vertex → Bool) (eval : Endpoint → ℝ)
    (hleq : ∀ a b, leq a b = true → eval a ≤ eval b)
    (left right : Endpoint) (witness : List Vertex)
    (h : check interval leq admitted left right witness = true) :
    ∀ x ∈ Set.Icc (eval left) (eval right),
      ∃ v ∈ witness, admitted v = true ∧
        x ∈ Set.Icc (eval (interval v).lower) (eval (interval v).upper) := by
  cases witness with
  | nil => simp [check] at h
  | cons first rest =>
      have hs : leq (interval first).lower left = true ∧
          checkTail interval leq admitted right first rest = true := by
        simpa only [check, Bool.and_eq_true] using h
      intro x hx
      exact checkTail_sound interval leq admitted eval hleq right first rest hs.2
        x ((hleq _ _ hs.1).trans hx.1) hx.2

/-- Box-uniform soundness: the same accepted Boolean witness covers the
parent for every parameter in the box, provided accepted endpoint comparisons
are valid throughout that box. -/
theorem check_sound_uniform {Endpoint Vertex Parameter : Type*}
    (interval : Vertex → Interval Endpoint) (leq : Endpoint → Endpoint → Bool)
    (admitted : Vertex → Bool) (eval : Parameter → Endpoint → ℝ)
    (box : Set Parameter)
    (hleq : ∀ p ∈ box, ∀ a b, leq a b = true → eval p a ≤ eval p b)
    (left right : Endpoint) (witness : List Vertex)
    (h : check interval leq admitted left right witness = true) :
    ∀ p ∈ box, ∀ x ∈ Set.Icc (eval p left) (eval p right),
      ∃ v ∈ witness, admitted v = true ∧
        x ∈ Set.Icc (eval p (interval v).lower) (eval p (interval v).upper) := by
  intro p hp
  exact check_sound interval leq admitted (eval p) (hleq p hp) left right witness h

private def integerLeq (a b : ℤ) : Bool := decide (a ≤ b)

/-- Neither lower nor upper endpoints need increase along a valid chain. -/
theorem nonmonotone_chain_accepted :
    check (id : Interval ℤ → Interval ℤ) integerLeq (fun _ => true) 0 8
      [⟨0, 6⟩, ⟨2, 4⟩, ⟨1, 8⟩] = true := by decide

theorem gap_rejected :
    check (id : Interval ℤ → Interval ℤ) integerLeq (fun _ => true) 0 3
      [⟨0, 1⟩, ⟨2, 3⟩] = false := by decide

/-- The forward overlap inequality alone holds here, but the reverse fails. -/
theorem one_direction_overlap_rejected :
    checkTail (id : Interval ℤ → Interval ℤ) integerLeq (fun _ => true) 1
      ⟨2, 3⟩ [⟨0, 1⟩] = false := by decide

theorem missing_admissibility_rejected :
    check (id : Interval ℤ → Interval ℤ) integerLeq
      (fun I => decide (I.lower ≠ 2)) 0 4 [⟨0, 2⟩, ⟨2, 4⟩] = false := by decide

theorem reversed_child_rejected :
    check (id : Interval ℤ → Interval ℤ) integerLeq (fun _ => true) 0 4
      [⟨0, 2⟩, ⟨2, 1⟩, ⟨1, 4⟩] = false := by decide

end Berstein.FiniteCover
