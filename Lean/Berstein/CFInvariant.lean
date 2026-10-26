import HallRay.ContinuedFraction.Basic

/-!
# Finite-state interval invariants bound actual infinite continued fractions

A local Bellman invariant suffices; no claim about greedy extrema or endpoint
attainment is needed. The proof propagates a finite terminal point backwards,
then uses the proved continued-fraction cylinder estimate to bound the actual
infinite limit.
-/

namespace Berstein.CFInvariant

open HallRay.ContinuedFraction

theorem finite_prefix_mem {State : Type*}
    (lower upper : State → ℝ) (step : State → PartialQuotient → State → Prop)
    (invariant : ∀ s d s', step s d s' → ∀ x ∈ Set.Icc (lower s') (upper s'),
      1 / ((d.val : ℝ) + x) ∈ Set.Icc (lower s) (upper s))
    (states : ℕ → State) (digits : ℕ → PartialQuotient)
    (path : ∀ n, step (states n) (digits n) (states (n + 1)))
    (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (lower (states n)) (upper (states n))) :
    tailMap ((List.range n).map digits) x ∈
      Set.Icc (lower (states 0)) (upper (states 0)) := by
  induction n generalizing x with
  | zero => simpa using hx
  | succ n ih =>
      rw [List.range_succ, List.map_append, tailMap_append]
      simp only [List.map_cons, List.map_nil, tailMap_cons, tailMap_nil]
      exact ih _ (invariant _ _ _ (path n) x hx)

/-- The actual infinite continued fraction is enclosed by a transition
invariant. In particular, the conclusion is about the existing `value`
definition as a limit of convergents, not a newly assumed coinductive value. -/
theorem value_mem {State : Type*}
    (lower upper : State → ℝ) (step : State → PartialQuotient → State → Prop)
    (nonempty : ∀ s, lower s ≤ upper s)
    (lower_nonneg : ∀ s, 0 ≤ lower s) (upper_le_one : ∀ s, upper s ≤ 1)
    (invariant : ∀ s d s', step s d s' → ∀ x ∈ Set.Icc (lower s') (upper s'),
      1 / ((d.val : ℝ) + x) ∈ Set.Icc (lower s) (upper s))
    (states : ℕ → State) (digits : ℕ → PartialQuotient)
    (path : ∀ n, step (states n) (digits n) (states (n + 1))) :
    value 0 digits ∈ Set.Icc (lower (states 0)) (upper (states 0)) := by
  have approx : ∀ ε : ℝ, 0 < ε → ∃ y ∈ Set.Icc (lower (states 0)) (upper (states 0)),
      |value 0 digits - y| < ε := by
    intro ε hε
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 4 : ℝ) < 1)
    let x := lower (states (2 * k))
    have hx : x ∈ Set.Icc (lower (states (2 * k))) (upper (states (2 * k))) :=
      ⟨le_rfl, nonempty _⟩
    have hxunit : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨lower_nonneg _, (nonempty _).trans (upper_le_one _)⟩
    refine ⟨tailMap ((List.range (2 * k)).map digits) x,
      finite_prefix_mem lower upper step invariant states digits path (2 * k) x hx, ?_⟩
    apply (abs_value_zero_sub_tailMap_prefix_le digits (2 * k) hxunit).trans_lt
    simpa only [Nat.mul_div_cancel_left _ (by omega : 0 < 2), one_div_pow] using hk
  constructor
  · by_contra h
    have hpos : 0 < lower (states 0) - value 0 digits := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨y, hy, herr⟩ := approx _ hpos
    have hdist := (abs_lt.mp herr).1
    linarith [hy.1]
  · by_contra h
    have hpos : 0 < value 0 digits - upper (states 0) := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨y, hy, herr⟩ := approx _ hpos
    have hdist := (abs_lt.mp herr).2
    linarith [hy.2]

end Berstein.CFInvariant
