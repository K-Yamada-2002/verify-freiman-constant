import Berstein.Forbidden31313
import Berstein.AdmissibleCompact

namespace Berstein
open HallRay.ContinuedFraction Forbidden31313

def twoDigit : PartialQuotient := ⟨2, by decide⟩

def padTwo (w : Word) (n : ℕ) : PartialQuotient :=
  if h : n < w.length then w[n] else twoDigit

theorem prefix_padTwo (w : Word) (n : ℕ) :
    (List.range n).map (padTwo w) = w.take n ++ List.replicate (n-w.length) twoDigit := by
  apply List.ext_getElem (by simp; omega)
  intro i hi hj
  have hin : i < n := by simpa using hi
  by_cases hiw : i < w.length
  · have hit : i < (w.take n).length := by simp; omega
    simp [padTwo, hiw, List.getElem_append_left hit]
  · have hit : (w.take n).length ≤ i := by simp; omega
    simp [padTwo, hiw, List.getElem_append_right hit]

theorem afterWord_take_ne_none (s : State) (w : Word)
    (hw : afterWord s w ≠ none) (n : ℕ) : afterWord s (w.take n) ≠ none := by
  intro h
  apply hw
  rw [← List.take_append_drop n w, afterWord_append, h]
  rfl

theorem afterWord_twos_ne_none (s : State) (n : ℕ) :
    afterWord s (List.replicate n twoDigit) ≠ none := by
  induction n generalizing s with
  | zero => simp [afterWord]
  | succ n ih =>
      have ht : transitionNat s twoDigit.val = some 0 := rfl
      simpa only [List.replicate_succ, afterWord, ht, Option.bind_some] using ih 0

theorem all_prefixes_accepted_avoids (u : ℕ → PartialQuotient)
    (h : ∀ n, afterWord 0 ((List.range n).map u) ≠ none) : Avoids31313 u := by
  have hexact : ∀ n, afterWord 0 ((List.range n).map u) = some (stateAt u n) := by
    intro n
    induction n with
    | zero => simp [afterWord]
    | succ n ih =>
        have hs := h (n+1)
        rw [List.range_succ, List.map_append, afterWord_append, ih] at hs ⊢
        simp only [List.map_cons, List.map_nil, Option.bind_some, afterWord] at hs ⊢
        rw [stateAt, transition_history]
        split
        · rename_i hbad
          rw [stateAt, transition_history, if_pos hbad] at hs
          simp at hs
        · simp only [Option.bind_some]
          congr 1
          simp only [stateAt, pastDigit_succ_zero, pastDigit_succ_succ]
  apply avoids_of_transition_stateAt u
  intro n
  have hn := hexact (n+1)
  rw [List.range_succ, List.map_append, afterWord_append, hexact n] at hn
  simpa [afterWord] using hn

theorem avoids_padTwo (w : Word) (hw : afterWord 0 w ≠ none) : Avoids31313 (padTwo w) := by
  apply all_prefixes_accepted_avoids
  intro n
  rw [prefix_padTwo, afterWord_append]
  cases hs : afterWord 0 (w.take n) with
  | none => exact False.elim (afterWord_take_ne_none 0 w hw n hs)
  | some s => exact afterWord_twos_ne_none s _

theorem admissible_padTwo (w : Word) (hw : afterWord 0 w ≠ none) :
    AdmissibleTail w (padTwo w) := by
  refine ⟨?_, ?_, avoids_padTwo w hw⟩
  · simp [prefix_padTwo]
  · intro n
    have hn : ¬ w.length+n < w.length := by omega
    simp only [padTwo, dif_neg hn]
    change (2 : ℕ) ≤ 3
    decide

theorem admissibleTail_append_subset (w v : Word) (hv : ∀ a ∈ v, a.val ≤ 3)
    {u : ℕ → PartialQuotient} (hu : AdmissibleTail (w++v) u) : AdmissibleTail w u := by
  refine ⟨(beginsWith_iff_map_range w u).mp
    (beginsWith_append_subset w v ((beginsWith_iff_map_range _ u).mpr hu.1)), ?_, hu.2.2⟩
  intro n
  by_cases hn : n < v.length
  · have hi : w.length+n < (w++v).length := by simp; omega
    have h := (beginsWith_iff_map_range _ u).mpr hu.1 ⟨w.length+n, hi⟩
    have h' : u (w.length+n) = v[n] := by simpa using h
    rw [h']
    exact hv _ (List.getElem_mem hn)
  · have h := hu.2.1 (n-v.length)
    have heq : (w++v).length+(n-v.length) = w.length+n := by simp; omega
    simpa only [heq] using h

/-- Every legal extension has an actual admissible infinite continuation. -/
theorem nonempty_admissible_extension (w v : Word) (hv : ∀ a ∈ v, a.val ≤ 3)
    (hlegal : afterWord 0 (w++v) ≠ none) :
    ∃ u, AdmissibleTail w u ∧ BeginsWith (w++v) u := by
  have h := admissible_padTwo (w++v) hlegal
  exact ⟨padTwo (w++v), admissibleTail_append_subset w v hv h,
    (beginsWith_iff_map_range _ _).mpr h.1⟩

end Berstein
