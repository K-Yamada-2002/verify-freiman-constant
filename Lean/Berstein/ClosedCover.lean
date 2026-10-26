import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Linarith

/-!
# From closed successor covers to realization

This file proves the compactness step of the proposed Berstein argument.
It does not assert that the numerical certificate satisfies its hypotheses.
In particular, `covers`, `nested`, `error_bound`, and `shrinks` must be proved
for actual continued-fraction cylinders before this theorem yields a Cantor sum.

Only the underlying cylinders must be nested. The auxiliary target intervals
need not be nested, an important distinction for the graph certificate.
-/

namespace Berstein

/-- A nested compact family with uniformly vanishing error realizes its target.
No continuity of `value` is required, because the bound holds at every point
of each cylinder, including the eventual intersection point. -/
theorem nested_compact_realizes {X : Type*} [TopologicalSpace X]
    (K : ℕ → Set X) (value : X → ℝ) (t : ℝ)
    (hnested : ∀ n, K (n + 1) ⊆ K n)
    (hne : ∀ n, (K n).Nonempty)
    (hcompact : IsCompact (K 0))
    (hclosed : ∀ n, IsClosed (K n))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x ∈ K n, |value x - t| < ε) :
    ∃ x, (∀ n, x ∈ K n) ∧ value x = t := by
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      K hnested hne hcompact hclosed
  have hx' : ∀ n, x ∈ K n := Set.mem_iInter.mp hx
  refine ⟨x, hx', ?_⟩
  have hz : |value x - t| = 0 := by
    by_contra h
    have hp : 0 < |value x - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h)
    obtain ⟨n, hn⟩ := happrox _ hp
    exact (lt_irrefl _) (hn x (hx' n))
  exact sub_eq_zero.mp (abs_eq_zero.mp hz)

/-- Abstract hypotheses for a closed successor construction.

`State` includes all parameters necessary for the real cylinder, not merely
the finite row index. `next` expresses a legal prefix extension. `target` is
the auxiliary interval that the certificate covers; `cylinder` is the compact
set of admissible realizations. `shrinks` is a separate analytic obligation,
not a consequence of a finite directed graph being closed. -/
structure ClosedCoverSystem (State X : Type*) [TopologicalSpace X] where
  cylinder : State → Set X
  target : State → Set ℝ
  next : State → State → Prop
  value : X → ℝ
  error : State → ℝ
  nonempty : ∀ s, (cylinder s).Nonempty
  compact : ∀ s, IsCompact (cylinder s)
  closed : ∀ s, IsClosed (cylinder s)
  nested : ∀ {s s'}, next s s' → cylinder s' ⊆ cylinder s
  covers : ∀ s t, t ∈ target s → ∃ s', next s s' ∧ t ∈ target s'
  error_bound : ∀ s t, t ∈ target s → ∀ x ∈ cylinder s, |value x - t| ≤ error s
  shrinks : ∀ path : ℕ → State, (∀ n, next (path n) (path (n + 1))) →
    ∀ ε : ℝ, 0 < ε → ∃ n, error (path n) < ε

namespace ClosedCoverSystem

/-- Dependent choice selects a legal successor path that keeps the same target.
This does not require target intervals to decrease. -/
theorem exists_path {State X : Type*} [TopologicalSpace X]
    (C : ClosedCoverSystem State X) {s : State} {t : ℝ} (ht : t ∈ C.target s) :
    ∃ path : ℕ → State, path 0 = s ∧
      (∀ n, C.next (path n) (path (n + 1))) ∧
      (∀ n, t ∈ C.target (path n)) := by
  classical
  let A := {s : State // t ∈ C.target s}
  have step_exists : ∀ a : A, ∃ b : A, C.next a.1 b.1 := by
    intro a
    obtain ⟨b, hab, hb⟩ := C.covers a.1 t a.2
    exact ⟨⟨b, hb⟩, hab⟩
  let step : A → A := fun a => Classical.choose (step_exists a)
  have hstep : ∀ a : A, C.next a.1 (step a).1 :=
    fun a => Classical.choose_spec (step_exists a)
  let path : ℕ → A := fun n => (step^[n]) ⟨s, ht⟩
  refine ⟨fun n => (path n).1, rfl, ?_, fun n => (path n).2⟩
  intro n
  have heq : path (n + 1) = step (path n) := by
    exact Function.iterate_succ_apply' step n ⟨s, ht⟩
  change C.next (path n).1 (path (n + 1)).1
  rw [heq]
  exact hstep (path n)

/-- The closed-cover compactness theorem, with all finite and analytic
obligations exposed as fields of `C`. -/
theorem realizes {State X : Type*} [TopologicalSpace X]
    (C : ClosedCoverSystem State X) {s : State} {t : ℝ} (ht : t ∈ C.target s) :
    ∃ x ∈ C.cylinder s, C.value x = t := by
  obtain ⟨path, hroot, hnext, htarget⟩ := C.exists_path ht
  obtain ⟨x, hx, hvalue⟩ := nested_compact_realizes
    (fun n => C.cylinder (path n)) C.value t
    (fun n => C.nested (hnext n))
    (fun n => C.nonempty (path n)) (C.compact (path 0))
    (fun n => C.closed (path n)) (by
      intro ε hε
      obtain ⟨n, hn⟩ := C.shrinks path hnext ε hε
      exact ⟨n, fun x hx => (C.error_bound _ _ (htarget n) x hx).trans_lt hn⟩)
  exact ⟨x, hroot ▸ hx 0, hvalue⟩

theorem target_subset_image {State X : Type*} [TopologicalSpace X]
    (C : ClosedCoverSystem State X) (s : State) :
    C.target s ⊆ C.value '' C.cylinder s := by
  intro t ht
  obtain ⟨x, hx, hxt⟩ := C.realizes ht
  exact ⟨x, hx, hxt⟩

end ClosedCoverSystem

/-- Every point of a rectangle is close to every point of its sum hull.
This supplies `error_bound` from cylinder widths, without falsely assuming
that the sum of two Cantor sets already equals its interval hull. -/
theorem sum_hull_error_bound {a b c d x y t : ℝ}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d)
    (ht : t ∈ Set.Icc (a + c) (b + d)) :
    |(x + y) - t| ≤ (b - a) + (d - c) := by
  apply abs_le.mpr
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, ht.1, ht.2]

/-- Bounded relative size prevents one coordinate from remaining bounded
while the total escapes to infinity. In the intended application these are
the two convergent denominators; relating them to word lengths is a separate
continued-fraction obligation. -/
theorem balanced_growth {x y : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hxy : ∀ n, x n ≤ C * y n) (hyx : ∀ n, y n ≤ C * x n)
    (hgrowth : Filter.Tendsto (fun n => x n + y n) Filter.atTop Filter.atTop) :
    Filter.Tendsto x Filter.atTop Filter.atTop ∧
      Filter.Tendsto y Filter.atTop Filter.atTop := by
  have hpos : 0 < C + 1 := by linarith
  constructor
  · apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [(Filter.tendsto_atTop.mp hgrowth) ((C + 1) * b)] with n hn
    have h := hyx n
    nlinarith
  · apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [(Filter.tendsto_atTop.mp hgrowth) ((C + 1) * b)] with n hn
    have h := hxy n
    nlinarith

end Berstein
