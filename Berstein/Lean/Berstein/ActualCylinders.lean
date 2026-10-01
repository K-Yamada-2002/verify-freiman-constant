import Berstein.AdmissiblePrefixes
import Berstein.ScaleShrink

/-! Actual symbolic cylinders and the quantitative approximation used by the
closed successor argument.  Every point is an infinite continued fraction
with the prescribed word and the actual forbidden-word constraint. -/
namespace Berstein.ActualCylinders
open HallRay.ContinuedFraction Forbidden31313

abbrev Stream := ℕ → PartialQuotient

def cylinder (root word : Word) : Set Stream :=
  {u | AdmissibleTail root u ∧ BeginsWith word u}

theorem closed (root word : Word) : IsClosed (cylinder root word) :=
  (isClosed_admissibleTail root).inter (isClosed_beginsWith word)

theorem compact (root word : Word) (B : ℕ) (hB : 3 ≤ B)
    (hroot : ∀ a ∈ root, a.val ≤ B) : IsCompact (cylinder root word) :=
  (isCompact_admissibleTail root B hB hroot).of_isClosed_subset
    (closed root word) (fun _ h => h.1)

theorem nonempty (root extension : Word)
    (hdigits : ∀ a ∈ extension, a.val ≤ 3)
    (hlegal : afterWord 0 (root ++ extension) ≠ none) :
    (cylinder root (root ++ extension)).Nonempty :=
  nonempty_admissible_extension root extension hdigits hlegal

theorem nested (root word extension : Word) :
    cylinder root (word ++ extension) ⊆ cylinder root word := by
  intro u hu
  exact ⟨hu.1, beginsWith_append_subset word extension hu.2⟩

theorem admissible_of_mem {root word : Word} {u : Stream}
    (hlen : root.length ≤ word.length) (hu : u ∈ cylinder root word) :
    AdmissibleTail word u := by
  refine ⟨(beginsWith_iff_map_range word u).mp hu.2, ?_, hu.1.2.2⟩
  intro n
  have h := hu.1.2.1 (word.length-root.length+n)
  have heq : root.length+(word.length-root.length+n) = word.length+n := by omega
  simpa only [heq] using h

/-- The automaton state attached to a legal finite word bounds the real
infinite tail of every point of the corresponding symbolic cylinder. -/
theorem tail_mem_exact {root word : Word} {u : Stream} {s : State}
    (hlen : root.length ≤ word.length) (hu : u ∈ cylinder root word)
    (hstate : afterWord 0 word = some s) :
    value 0 (fun n => u (word.length+n)) ∈ Set.Icc (exactLower s) (exactUpper s) := by
  have ha := admissible_of_mem hlen hu
  have hs := afterWord_eq_stateAt u ha.2.2 word.length
  rw [ha.1, hstate] at hs
  have heq : s = stateAt u word.length := Option.some.inj hs
  rw [heq]
  exact value_shift_mem_exact u ha.2.2 word.length ha.2.1

noncomputable def hull (word : Word) (s : State) : Set ℝ :=
  Set.uIcc (tailMap word (exactLower s)) (tailMap word (exactUpper s))

theorem value_mem_hull {root word : Word} {u : Stream} {s : State}
    (hlen : root.length ≤ word.length) (hu : u ∈ cylinder root word)
    (hstate : afterWord 0 word = some s) : value 0 u ∈ hull word s := by
  have ht := tail_mem_exact hlen hu hstate
  have hb := exactBounds_unit s
  have ha := admissible_of_mem hlen hu
  rw [value_zero_eq_tailMap_prefix u word.length, ha.1]
  exact tailMap_mem_uIcc hb.1 hb.2.1 hb.2.2 ht

/-- Any point of the full interval enclosure is uniformly close to every
actual cylinder value; no claim that the Cantor set fills that interval is used. -/
theorem approximation {root word : Word} {u : Stream} {s : State} {t anchor : ℝ}
    (hlen : root.length ≤ word.length) (hu : u ∈ cylinder root word)
    (hstate : afterWord 0 word = some s) (ht : t ∈ hull word s)
    (ha : anchor ∈ Set.Icc (0 : ℝ) 1) :
    |value 0 u-t| ≤ 4 * Normalization.scale word anchor := by
  have hv := value_mem_hull hlen hu hstate
  have hb := exactBounds_unit s
  have hwidth := tailMap_width_le_four_scale word ha
    ⟨hb.1, hb.2.1.trans hb.2.2⟩ ⟨hb.1.trans hb.2.1, hb.2.2⟩
  have hh : |value 0 u-t| ≤
      |tailMap word (exactLower s)-tailMap word (exactUpper s)| := by
    rcases le_total (tailMap word (exactLower s)) (tailMap word (exactUpper s)) with h | h
    · rw [hull, Set.uIcc_of_le h] at hv ht
      rw [abs_sub_comm (tailMap word (exactLower s)) (tailMap word (exactUpper s)), abs_of_nonneg (sub_nonneg.mpr h)]
      exact abs_le.mpr ⟨by linarith [hv.1, ht.2], by linarith [hv.2, ht.1]⟩
    · rw [hull, Set.uIcc_of_ge h] at hv ht
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      exact abs_le.mpr ⟨by linarith [hv.1, ht.2], by linarith [hv.2, ht.1]⟩
  exact hh.trans hwidth

end Berstein.ActualCylinders
