import Berstein.Markov
import Berstein.SymbolicCylinders

/-!
# Compactness of the actual admissible continued-fraction sets

The symbolic sequences used by `admissibleTailSet` are a closed subset of a
product of finite alphabets. This proves compactness for the actual definition
used by the Markov bridge, including its tails-only restriction on digit `4`.
-/

namespace Berstein

open HallRay.ContinuedFraction

theorem isClosed_avoids31313 :
    IsClosed {u : ℕ → PartialQuotient | Avoids31313 u} := by
  have hopen (i d : ℕ) : IsOpen {u : ℕ → PartialQuotient | (u i).1 = d} := by
    have hc : Continuous (fun u : ℕ → PartialQuotient => (u i).1) :=
      continuous_subtype_val.comp (continuous_apply i)
    change IsOpen ((fun u : ℕ → PartialQuotient => (u i).1) ⁻¹' {d})
    exact (isOpen_discrete {d}).preimage hc
  unfold Avoids31313
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun n =>
    ((hopen n 3).inter ((hopen (n + 1) 1).inter
      ((hopen (n + 2) 3).inter ((hopen (n + 3) 1).inter (hopen (n + 4) 3))))).isClosed_compl

theorem isClosed_admissibleTail (word : Word) :
    IsClosed {u : ℕ → PartialQuotient | AdmissibleTail word u} := by
  have heq : {u : ℕ → PartialQuotient | AdmissibleTail word u} =
      {u | BeginsWith word u} ∩
        ({u | TailIn word {a | a.1 ≤ 3} u} ∩ {u | Avoids31313 u}) := by
    ext u
    simp [AdmissibleTail, TailIn, beginsWith_iff_map_range]
  rw [heq]
  exact (isClosed_beginsWith word).inter
    ((isClosed_tailIn word {a | a.1 ≤ 3}).inter isClosed_avoids31313)

theorem finite_boundedDigits (B : ℕ) :
    Set.Finite {a : PartialQuotient | a.1 ≤ B} := by
  exact (Set.finite_Iic B).preimage
    (fun _ _ _ _ h => Subtype.ext h)

/-- Any fixed prefix whose digits are at most `B`, followed by admissible
digits at most `3`, lies in the product of the finite alphabet `1,...,B`. -/
theorem admissibleTail_digit_bound (word : Word) (B : ℕ) (hB : 3 ≤ B)
    (hw : ∀ a ∈ word, a.1 ≤ B) (u : ℕ → PartialQuotient)
    (hu : AdmissibleTail word u) (n : ℕ) : (u n).1 ≤ B := by
  by_cases hn : n < word.length
  · have hp := (beginsWith_iff_map_range word u).mpr hu.1 ⟨n, hn⟩
    rw [hp]
    exact hw _ (List.get_mem _ _)
  · have hn' : word.length ≤ n := by omega
    have ht := hu.2.1 (n - word.length)
    rw [Nat.add_sub_of_le hn'] at ht
    exact ht.trans hB

theorem isCompact_admissibleTail (word : Word) (B : ℕ) (hB : 3 ≤ B)
    (hw : ∀ a ∈ word, a.1 ≤ B) :
    IsCompact {u : ℕ → PartialQuotient | AdmissibleTail word u} := by
  have hproduct : IsCompact {u : ℕ → PartialQuotient | ∀ n, (u n).1 ≤ B} :=
    isCompact_pi_infinite (fun _ => (finite_boundedDigits B).isCompact)
  exact hproduct.of_isClosed_subset (isClosed_admissibleTail word)
    (fun u hu n => admissibleTail_digit_bound word B hB hw u hu n)

/-- Compactness of the exact Cantor-set definition used in the Markov bridge. -/
theorem isCompact_admissibleTailSet (word : Word) (B : ℕ) (hB : 3 ≤ B)
    (hw : ∀ a ∈ word, a.1 ≤ B) : IsCompact (admissibleTailSet word) := by
  have heq : admissibleTailSet word =
      (fun u : ℕ → PartialQuotient => value 0 u) '' {u | AdmissibleTail word u} := by
    ext x
    simp only [admissibleTailSet, Set.mem_setOf_eq, Set.mem_image]
    constructor <;> rintro ⟨u, hu, hx⟩ <;> exact ⟨u, hu, hx.symm⟩
  rw [heq]
  exact (isCompact_admissibleTail word B hB hw).image (continuous_cfValue id)

theorem isCompact_admissible322 : IsCompact (admissibleTailSet prefix322) := by
  apply isCompact_admissibleTailSet prefix322 4 (by decide)
  intro a ha
  simp [prefix322] at ha
  rcases ha with rfl | rfl <;> decide

theorem isCompact_admissible431 : IsCompact (admissibleTailSet prefix431) := by
  apply isCompact_admissibleTailSet prefix431 4 (by decide)
  intro a ha
  simp [prefix431] at ha
  rcases ha with rfl | rfl | rfl <;> decide

/-- A constant `2` continuation witnesses nonemptiness at the left root. -/
theorem nonempty_admissible322 : (admissibleTailSet prefix322).Nonempty := by
  let u : ℕ → PartialQuotient := fun n =>
    ⟨if n = 0 then 3 else 2, by split_ifs <;> decide⟩
  refine ⟨value 0 u, u, ?_, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [prefix322, List.range_succ, u]
  · intro n
    simp [prefix322, u]
  · intro n hn
    have h := hn.2.1
    simp [u] at h

/-- A constant `2` continuation witnesses nonemptiness at the right root,
including its allowed fixed digit `4`. -/
theorem nonempty_admissible431 : (admissibleTailSet prefix431).Nonempty := by
  let u : ℕ → PartialQuotient := fun n =>
    ⟨if n = 0 then 4 else if n = 1 then 3 else if n = 2 then 1 else 2,
      by split_ifs <;> decide⟩
  refine ⟨value 0 u, u, ?_, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [prefix431, List.range_succ, u]
  · intro n
    have h0 : 3 + n ≠ 0 := by omega
    have h1 : 3 + n ≠ 1 := by omega
    have h2 : 3 + n ≠ 2 := by omega
    simp [prefix431, u, h1, h2]
  · intro n hn
    by_cases hsmall : n ≤ 2
    · interval_cases n <;> norm_num [u] at hn
    · have h0 : n ≠ 0 := by omega
      have h1 : n ≠ 1 := by omega
      have h2 : n ≠ 2 := by omega
      simp [u, h0, h1, h2] at hn

end Berstein
