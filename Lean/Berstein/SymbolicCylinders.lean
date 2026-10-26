import HallRay.ContinuedFraction.Basic

/-!
# Compact symbolic cylinders and continued-fraction continuity

Finite alphabet streams use the product of the discrete topologies. Avoiding
a fixed finite word is closed, so an allowed prefix cylinder is compact.
Continued-fraction evaluation is continuous by the proved common-prefix bound.
These lemmas do not assert that the certificate covers any target interval.
-/

namespace Berstein

open scoped Topology
open HallRay.ContinuedFraction

/-- A sequence begins with a finite word. -/
def BeginsWith {A : Type*} (w : List A) (u : ℕ → A) : Prop :=
  ∀ i : Fin w.length, u i = w.get i

theorem beginsWith_iff_map_range {A : Type*} (w : List A) (u : ℕ → A) :
    BeginsWith w u ↔ (List.range w.length).map u = w := by
  constructor
  · intro h
    apply List.ext_getElem (by simp)
    intro i hi₁ hi₂
    simpa using h ⟨i, hi₂⟩
  · intro h i
    have hh := congrArg (fun l : List A => l[(i : ℕ)]?) h
    simpa [List.getElem?_eq_getElem, i.isLt] using hh

/-- No translate of `w` occurs in `u`, including across a chosen prefix. -/
def AvoidsWord {A : Type*} (w : List A) (u : ℕ → A) : Prop :=
  ∀ n : ℕ, ¬ ∀ i : Fin w.length, u (n + i) = w.get i

theorem isClosed_beginsWith {A : Type*} [TopologicalSpace A] [T2Space A]
    (w : List A) : IsClosed {u : ℕ → A | BeginsWith w u} := by
  unfold BeginsWith
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_eq (continuous_apply (i : ℕ)) continuous_const

theorem isClosed_avoidsWord {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (w : List A) : IsClosed {u : ℕ → A | AvoidsWord w u} := by
  have hopen (n : ℕ) : IsOpen {u : ℕ → A | ∀ i : Fin w.length,
      u (n + i) = w.get i} := by
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    change IsOpen ((fun u : ℕ → A => u (n + i)) ⁻¹' {w.get i})
    exact (isOpen_discrete {w.get i}).preimage (continuous_apply (n + (i : ℕ)))
  unfold AvoidsWord
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun n => (hopen n).isClosed_compl

/-- Compactness includes the forbidden-word constraint throughout the stream,
including the boundary of the fixed prefix. -/
theorem isCompact_allowedCylinder {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (pre forbidden : List A) :
    IsCompact {u : ℕ → A | BeginsWith pre u ∧ AvoidsWord forbidden u} := by
  exact ((isClosed_beginsWith pre).inter (isClosed_avoidsWord forbidden)).isCompact

/-- Extending a prefix shrinks its symbolic cylinder. -/
theorem beginsWith_append_subset {A : Type*} (pre suffix : List A) :
    {u : ℕ → A | BeginsWith (pre ++ suffix) u} ⊆
      {u : ℕ → A | BeginsWith pre u} := by
  intro u hu i
  have hi : (i : ℕ) < (pre ++ suffix).length := by
    simp only [List.length_append]
    omega
  have h := hu ⟨i, hi⟩
  simpa using h

/-- Only the digits after the fixed word must belong to `allowed`. In
particular, choosing the alphabet `1,2,3,4` and allowed tail digits `1,2,3`
does not incorrectly rule out the fixed word `431`. -/
def TailIn {A : Type*} (pre : List A) (allowed : Set A) (u : ℕ → A) : Prop :=
  ∀ n, u (pre.length + n) ∈ allowed

theorem isClosed_tailIn {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (pre : List A) (allowed : Set A) : IsClosed {u : ℕ → A | TailIn pre allowed u} := by
  unfold TailIn
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun n =>
    (isClosed_discrete allowed).preimage (continuous_apply (pre.length + n))

theorem isCompact_constrainedCylinder {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (pre forbidden : List A) (allowed : Set A) :
    IsCompact {u : ℕ → A |
      BeginsWith pre u ∧ TailIn pre allowed u ∧ AvoidsWord forbidden u} := by
  exact ((isClosed_beginsWith pre).inter
    ((isClosed_tailIn pre allowed).inter (isClosed_avoidsWord forbidden))).isCompact

/-- Continued-fraction evaluation is continuous on streams over any discrete
alphabet, for any map from that alphabet to positive partial quotients. -/
theorem continuous_cfValue {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (digit : A → PartialQuotient) :
    Continuous (fun u : ℕ → A => value 0 (fun n => digit (u n))) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 4 : ℝ) < 1)
  have hneigh : PiNat.cylinder u (2 * k) ∈ 𝓝 u :=
    (PiNat.isOpen_cylinder (fun _ : ℕ => A) u (2 * k)).mem_nhds
      (PiNat.self_mem_cylinder u (2 * k))
  filter_upwards [hneigh] with v hv
  have hpref : (List.range (2 * k)).map (fun n => digit (v n)) =
      (List.range (2 * k)).map (fun n => digit (u n)) := by
    apply List.map_congr_left
    intro i hi
    rw [hv i (List.mem_range.mp hi)]
  have hbound := abs_value_zero_sub_le_of_common_prefix
    (fun n => digit (v n)) (fun n => digit (u n)) (2 * k) hpref
  rw [Real.dist_eq]
  apply hbound.trans_lt
  simpa only [Nat.mul_div_cancel_left _ (by omega : 0 < 2), one_div_pow] using hk

/-- The true continued-fraction set, not just its interval hull, is compact. -/
theorem isCompact_cfCylinder {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (digit : A → PartialQuotient)
    (pre forbidden : List A) :
    IsCompact ((fun u : ℕ → A => value 0 (fun n => digit (u n))) ''
      {u | BeginsWith pre u ∧ AvoidsWord forbidden u}) := by
  exact (isCompact_allowedCylinder pre forbidden).image (continuous_cfValue digit)

theorem isCompact_constrainedCfCylinder {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (digit : A → PartialQuotient)
    (pre forbidden : List A) (allowed : Set A) :
    IsCompact ((fun u : ℕ → A => value 0 (fun n => digit (u n))) ''
      {u | BeginsWith pre u ∧ TailIn pre allowed u ∧ AvoidsWord forbidden u}) := by
  exact (isCompact_constrainedCylinder pre forbidden allowed).image (continuous_cfValue digit)

end Berstein
