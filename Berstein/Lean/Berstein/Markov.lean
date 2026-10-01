import HallRay.ContinuedFraction.Basic

/-!
# The Markov spectrum and the center-dominance bridge

The spectrum here is defined by actual bi-infinite sequences of positive
integer partial quotients, with the continued fractions evaluated as limits.
The last theorem isolates the two still-required analytic inputs: filling the
sum of the two admissible Cantor sets, and bounding every noncentral value.
Neither input is claimed by this module.
-/

namespace Berstein

open HallRay.ContinuedFraction

/-- An actual bi-infinite sequence of positive integer partial quotients. -/
abbrev BiSequence := ℤ → PartialQuotient

/-- The digits on the left of a position, read outwards. -/
def leftDigits (A : BiSequence) (n : ℤ) : ℕ → PartialQuotient :=
  fun k ↦ A (n - (k : ℤ) - 1)

/-- The digits on the right of a position, read outwards. -/
def rightDigits (A : BiSequence) (n : ℤ) : ℕ → PartialQuotient :=
  fun k ↦ A (n + (k : ℤ) + 1)

/-- The local value `A n + [0; A (n-1), …] + [0; A (n+1), …]`. -/
noncomputable def localValue (A : BiSequence) (n : ℤ) : ℝ :=
  (A n).1 + value 0 (leftDigits A n) + value 0 (rightDigits A n)

theorem digit_le_localValue (A : BiSequence) (n : ℤ) :
    ((A n).1 : ℝ) ≤ localValue A n := by
  have hl := (value_zero_mem_Icc (leftDigits A n)).1
  have hr := (value_zero_mem_Icc (rightDigits A n)).1
  dsimp [localValue]
  linarith

theorem localValue_le_digit_add_two (A : BiSequence) (n : ℤ) :
    localValue A n ≤ (A n).1 + 2 := by
  have hl := (value_zero_mem_Icc (leftDigits A n)).2
  have hr := (value_zero_mem_Icc (rightDigits A n)).2
  dsimp [localValue]
  linarith

/-- The local value also agrees with the conventional expression
`[A n; A (n+1), …] + [0; A (n-1), …]`. -/
theorem localValue_eq_value_add (A : BiSequence) (n : ℤ) :
    localValue A n = value ((A n).1 : ℝ) (rightDigits A n) +
      value 0 (leftDigits A n) := by
  rw [value_eq_head_add]
  dsimp [localValue]
  ring

/-- The Markov value of a sequence; boundedness is required in the spectrum. -/
noncomputable def markovValue (A : BiSequence) : ℝ := ⨆ n, localValue A n

/-- The finite Markov spectrum of positive-integer bi-infinite sequences. -/
def markovSpectrum : Set ℝ :=
  {t | ∃ A : BiSequence, BddAbove (Set.range (localValue A)) ∧ t = markovValue A}

/-- A local maximum which dominates all positions is the Markov value. -/
theorem markovValue_eq_of_dominant (A : BiSequence) (c : ℤ)
    (h : ∀ n, localValue A n ≤ localValue A c) :
    markovValue A = localValue A c := by
  have hb : BddAbove (Set.range (localValue A)) :=
    ⟨localValue A c, by rintro _ ⟨n, rfl⟩; exact h n⟩
  exact le_antisymm (ciSup_le h) (le_ciSup hb c)

/-- Center dominance yields membership in the actual Markov spectrum. -/
theorem mem_markovSpectrum_of_dominant (A : BiSequence) (c : ℤ)
    (h : ∀ n, localValue A n ≤ localValue A c) :
    localValue A c ∈ markovSpectrum := by
  refine ⟨A, ⟨localValue A c, ?_⟩, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact h n
  · exact (markovValue_eq_of_dominant A c h).symm

/-- Avoiding `31313` is checked on the whole one-sided sequence, including
the fixed prefix and its boundary with the infinite tail. -/
def Avoids31313 (digits : ℕ → PartialQuotient) : Prop :=
  ∀ n, ¬ ((digits n).1 = 3 ∧ (digits (n + 1)).1 = 1 ∧
    (digits (n + 2)).1 = 3 ∧ (digits (n + 3)).1 = 1 ∧
    (digits (n + 4)).1 = 3)

/-- A prefix is fixed; only digits added after it are restricted to `1,2,3`.
In particular a `4` inside the fixed prefix `431` is permitted. -/
def AdmissibleTail (word : Word) (digits : ℕ → PartialQuotient) : Prop :=
  (List.range word.length).map digits = word ∧
    (∀ n, (digits (word.length + n)).1 ≤ 3) ∧ Avoids31313 digits

/-- The set `K̃(prefix)` of continued fractions with an admissible tail. -/
def admissibleTailSet (word : Word) : Set ℝ :=
  {x | ∃ digits : ℕ → PartialQuotient,
    AdmissibleTail word digits ∧ x = value 0 digits}

/-- The set definition agrees with applying the finite fixed prefix to the
value of the infinite appended tail. -/
theorem value_zero_eq_tailMap_of_admissible (word : Word)
    (digits : ℕ → PartialQuotient) (h : AdmissibleTail word digits) :
    value 0 digits = tailMap word (value 0 (fun k ↦ digits (word.length + k))) := by
  rw [value_zero_eq_tailMap_prefix digits word.length, h.1]

/-- The fixed left prefix, read from the center outwards. -/
def prefix322 : Word := [⟨3, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩]

/-- The fixed right prefix, whose initial `4` is allowed by the convention. -/
def prefix431 : Word := [⟨4, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩]

theorem admissible322_first_three (digits : ℕ → PartialQuotient)
    (h : AdmissibleTail prefix322 digits) :
    (digits 0).1 = 3 ∧ (digits 1).1 = 2 ∧ (digits 2).1 = 2 := by
  have hp := h.1
  simp [prefix322, List.range_succ] at hp
  rcases hp with ⟨h0, h1, h2⟩
  exact ⟨congrArg Subtype.val h0, congrArg Subtype.val h1, congrArg Subtype.val h2⟩

theorem admissible431_first_three (digits : ℕ → PartialQuotient)
    (h : AdmissibleTail prefix431 digits) :
    (digits 0).1 = 4 ∧ (digits 1).1 = 3 ∧ (digits 2).1 = 1 := by
  have hp := h.1
  simp [prefix431, List.range_succ] at hp
  rcases hp with ⟨h0, h1, h2⟩
  exact ⟨congrArg Subtype.val h0, congrArg Subtype.val h1, congrArg Subtype.val h2⟩

/-- Glue two one-sided positive-integer sequences around the central `4`. -/
def glue (left right : ℕ → PartialQuotient) : BiSequence :=
  fun n ↦ if n = 0 then ⟨4, by decide⟩
    else if n < 0 then left (-n - 1).toNat else right (n - 1).toNat

@[simp] theorem glue_zero (left right : ℕ → PartialQuotient) :
    glue left right 0 = ⟨4, by decide⟩ := by simp [glue]

@[simp] theorem leftDigits_glue (left right : ℕ → PartialQuotient) :
    leftDigits (glue left right) 0 = left := by
  funext k
  simp only [leftDigits, zero_sub]
  change glue left right (-(k : ℤ) - 1) = left k
  have hn : -(k : ℤ) - 1 < 0 := by omega
  rw [glue, if_neg (ne_of_lt hn), if_pos hn]
  congr 1
  omega

@[simp] theorem rightDigits_glue (left right : ℕ → PartialQuotient) :
    rightDigits (glue left right) 0 = right := by
  funext k
  simp only [rightDigits, zero_add]
  have hn : ¬ (k : ℤ) + 1 < 0 := by omega
  have hne : (k : ℤ) + 1 ≠ 0 := by omega
  rw [glue, if_neg hne, if_neg hn]
  congr 1
  omega

/-- The central local value is exactly `4 + x + y` for the two chosen tails. -/
@[simp] theorem localValue_glue_zero (left right : ℕ → PartialQuotient) :
    localValue (glue left right) 0 = 4 + value 0 left + value 0 right := by
  simp only [localValue, glue_zero, leftDigits_glue, rightDigits_glue]
  rfl

/-- The exact sum-filling obligation supplied by the closed covering argument. -/
def SumFilling (lo hi : ℝ) : Prop :=
  ∀ z ∈ Set.Icc lo hi, ∃ x ∈ admissibleTailSet prefix322,
    ∃ y ∈ admissibleTailSet prefix431, z = x + y

/-- The uniform bound must cover every noncentral position of every glued
admissible sequence, including the second fixed `4`. -/
def NoncentralBound (bound : ℝ) : Prop :=
  ∀ left right, AdmissibleTail prefix322 left → AdmissibleTail prefix431 right →
    ∀ n : ℤ, n ≠ 0 → localValue (glue left right) n ≤ bound

/-- The Markov bridge: Cantor-sum filling and a genuine noncentral bound
imply the translated interval lies in the actual Markov spectrum. -/
theorem interval_subset_markovSpectrum_of_filling_and_bound
    (lo hi bound : ℝ) (hfill : SumFilling lo hi)
    (hbound : NoncentralBound bound) (hlower : bound ≤ 4 + lo) :
    Set.Icc (4 + lo) (4 + hi) ⊆ markovSpectrum := by
  intro t ht
  have hz : t - 4 ∈ Set.Icc lo hi := by
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨x, ⟨left, hl, hx⟩, y, ⟨right, hr, hy⟩, hsum⟩ := hfill (t - 4) hz
  have hcenter : localValue (glue left right) 0 = t := by
    rw [localValue_glue_zero]
    rw [hx, hy] at hsum
    linarith
  rw [← hcenter]
  apply mem_markovSpectrum_of_dominant
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · rw [hcenter]
    exact (hbound left right hl hr n hn).trans (hlower.trans ht.1)

end Berstein
