import Freiman.Setup
import Berstein.AdmissibleCompact

/-! Center dominance for arbitrary fixed words and arbitrary positive centers.
These lemmas use the actual continued-fraction definition of the Markov spectrum. -/
namespace Freiman
open Berstein HallRay.ContinuedFraction

/-- Glue two actual tails around an arbitrary positive integer. -/
def glueAt (center : PartialQuotient) (left right : ℕ → PartialQuotient) : BiSequence :=
  fun n => if n = 0 then center
    else if n < 0 then left (-n-1).toNat else right (n-1).toNat

@[simp] theorem glueAt_zero (c : PartialQuotient) (l r : ℕ → PartialQuotient) :
    glueAt c l r 0 = c := by simp [glueAt]

@[simp] theorem leftDigits_glueAt (c : PartialQuotient) (l r : ℕ → PartialQuotient) :
    leftDigits (glueAt c l r) 0 = l := by
  funext k
  have hn : -(k : ℤ)-1 < 0 := by omega
  simp only [leftDigits, zero_sub, glueAt, if_neg (ne_of_lt hn), if_pos hn]
  congr 1
  omega

@[simp] theorem rightDigits_glueAt (c : PartialQuotient) (l r : ℕ → PartialQuotient) :
    rightDigits (glueAt c l r) 0 = r := by
  funext k
  have hn : ¬ (k : ℤ)+1 < 0 := by omega
  have he : (k : ℤ)+1 ≠ 0 := by omega
  simp only [rightDigits, zero_add, glueAt, if_neg he, if_neg hn]
  congr 1
  omega

@[simp] theorem localValue_glueAt_zero (c : PartialQuotient) (l r : ℕ → PartialQuotient) :
    localValue (glueAt c l r) 0 = (c.val : ℝ)+value 0 l+value 0 r := by
  simp only [localValue, glueAt_zero, leftDigits_glueAt, rightDigits_glueAt]

/-- Root-specific filling, without a spectral assumption. -/
def SumFilling (a b : Word) (lo hi : ℝ) : Prop :=
  ∀ z ∈ Set.Icc lo hi, ∃ x ∈ admissibleTailSet a,
    ∃ y ∈ admissibleTailSet b, z = x+y

/-- Every noncentral position, for all allowed infinite extensions. -/
def NoncentralBound (a b : Word) (c : PartialQuotient) (bound : ℝ) : Prop :=
  ∀ l r, AdmissibleTail a l → AdmissibleTail b r →
    ∀ n : ℤ, n ≠ 0 → localValue (glueAt c l r) n ≤ bound

theorem interval_subset_markovSpectrum (a b : Word) (c : PartialQuotient)
    (lo hi bound : ℝ) (hfill : SumFilling a b lo hi)
    (hbound : NoncentralBound a b c bound) (hlower : bound ≤ (c.val : ℝ)+lo) :
    Set.Icc ((c.val : ℝ)+lo) ((c.val : ℝ)+hi) ⊆ markovSpectrum := by
  intro t ht
  have hz : t-(c.val : ℝ) ∈ Set.Icc lo hi := by
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨x,⟨l,hl,hx⟩,y,⟨r,hr,hy⟩,hsum⟩ := hfill _ hz
  have hc : localValue (glueAt c l r) 0 = t := by
    rw [localValue_glueAt_zero]
    rw [hx,hy] at hsum
    linarith
  rw [← hc]
  apply mem_markovSpectrum_of_dominant
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · rw [hc]
    exact (hbound l r hl hr n hn).trans (hlower.trans ht.1)

/-- Only the noncentral digits matter for the elementary bound six. -/
theorem noncentral_le_six (a b : Word) (c : PartialQuotient)
    (ha : ∀ d ∈ a, d.val ≤ 4) (hb : ∀ d ∈ b, d.val ≤ 4) :
    NoncentralBound a b c 6 := by
  intro l r hl hr n hn
  have hd : ((glueAt c l r n).val : ℝ) ≤ 4 := by
    have hd' : (glueAt c l r n).val ≤ 4 := by
      rw [glueAt, if_neg hn]
      split_ifs
      · exact admissibleTail_digit_bound a 4 (by decide) ha l hl _
      · exact admissibleTail_digit_bound b 4 (by decide) hb r hr _
    exact_mod_cast hd'
  have hv := localValue_le_digit_add_two (glueAt c l r) n
  linarith

/-- A family of realized sums covering [1/2,3/2] yields the entire upper ray.
The center is selected for each target using the floor function. -/
theorem upper_ray_of_filling
    (hfill : ∀ z ∈ Set.Icc (1/2 : ℝ) (3/2),
      ∃ a b : Word, (∀ d ∈ a, d.val ≤ 4) ∧ (∀ d ∈ b, d.val ≤ 4) ∧
        ∃ l r, AdmissibleTail a l ∧ AdmissibleTail b r ∧ z = value 0 l+value 0 r) :
    Set.Ici (13/2 : ℝ) ⊆ markovSpectrum := by
  intro t ht
  change (13/2 : ℝ) ≤ t at ht
  let n : ℤ := ⌊t-1/2⌋
  have hlow := Int.floor_le (t-1/2)
  have hhigh := Int.lt_floor_add_one (t-1/2)
  have hn : 6 ≤ n := by
    dsimp only [n]
    exact Int.le_floor.mpr (by norm_num; linarith [ht])
  let c : PartialQuotient := ⟨n.toNat, by omega⟩
  have hcast : (c.val : ℝ) = (n : ℝ) := by
    dsimp only [c]
    have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg (by omega)
    exact_mod_cast he
  have hz : t-(n : ℝ) ∈ Set.Icc (1/2 : ℝ) (3/2) := by
    constructor <;> linarith
  obtain ⟨a,b,ha,hb,l,r,hl,hr,hsum⟩ := hfill _ hz
  have hc : localValue (glueAt c l r) 0 = t := by
    rw [localValue_glueAt_zero,hcast]
    linarith
  rw [← hc]
  apply mem_markovSpectrum_of_dominant
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · rw [hc]
    exact (noncentral_le_six a b c ha hb l r hl hr k hk).trans (by linarith [ht])

/-- Join the finite part and the upper ray at their common closed endpoint. -/
theorem ray_of_finite_and_upper {c : ℝ}
    (hfinite : Set.Icc c (13/2 : ℝ) ⊆ markovSpectrum)
    (hupper : Set.Ici (13/2 : ℝ) ⊆ markovSpectrum) :
    Set.Ici c ⊆ markovSpectrum := by
  intro t ht
  by_cases h : t ≤ 13/2
  · exact hfinite ⟨ht,h⟩
  · exact hupper (le_of_lt (lt_of_not_ge h))

end Freiman
