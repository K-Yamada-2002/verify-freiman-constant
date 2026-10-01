import Berstein.Forbidden31313
import Berstein.CFPrefixBounds
import Berstein.SpectralLocal

/-!
# Finite spectral certificates and their interpretation

The finite Boolean acceptances in this module are reduced inside the Lean
kernel with `decide +kernel`. Both their acceptance and their interpretation
as bounds on actual infinite continued fractions are kernel checked.

The far-field check uses six inward digits and the outward automaton interval.
It directly bounds the original sequence, without a tail replacement argument.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Berstein.SpectralVerified

open HallRay.ContinuedFraction Forbidden31313 CFPrefixBounds

def bound : ℚ := 4525423 / 1000000
def four : PartialQuotient := ⟨4, by decide⟩
def unitBounds : QBounds := ⟨0, 1⟩
def alphabet : Word := [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

def words : ℕ → List Word
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun d => (words n).map (d :: ·)

theorem mem_alphabet (d : PartialQuotient) (hd : d.val ≤ 3) : d ∈ alphabet := by
  rcases d with ⟨n, hn⟩
  change n ≤ 3 at hd
  interval_cases n <;> simp [alphabet, Subtype.ext_iff]

theorem mem_words (w : Word) (hw : ∀ d ∈ w, d.val ≤ 3) : w ∈ words w.length := by
  induction w with
  | nil => simp [words]
  | cons d w ih =>
      simp only [List.length_cons, words, List.mem_flatMap, List.mem_map]
      exact ⟨d, mem_alphabet d (hw d (by simp)), w,
        ih (fun a ha => hw a (List.mem_cons_of_mem d ha)), rfl⟩

def farCheck (pre : Word) (d : PartialQuotient) : Bool :=
  match afterWord 0 (pre ++ [d]) with
  | none => true
  | some s => decide ((d.val : ℚ) + (enclose pre.reverse unitBounds).hi +
      (rationalBounds s).hi ≤ bound)

def nearCheck (fixed other : Word) (otherState : State) (pre : Word)
    (d : PartialQuotient) : Bool :=
  match afterWord 0 (fixed ++ pre ++ [d]) with
  | none => true
  | some s => decide ((d.val : ℚ) +
      (enclose ((fixed ++ pre).reverse ++ [four] ++ other) (rationalBounds otherState)).hi +
      (rationalBounds s).hi ≤ bound)

def checkNear (fixed other : Word) (otherState : State) : Bool :=
  (List.range 6).all fun n => (words n).all fun pre =>
    alphabet.all fun d => nearCheck fixed other otherState pre d

theorem far_checked :
    (words 6).all (fun pre => alphabet.all (farCheck pre)) = true := by decide +kernel

theorem near322_checked : checkNear prefix322 prefix431 2 = true := by decide +kernel
theorem near431_checked : checkNear prefix431 prefix322 0 = true := by decide +kernel

theorem adjacent_four_checked :
    (4 : ℚ) + (enclose ([four] ++ prefix322) (rationalBounds 0)).hi +
      (enclose [⟨3, by decide⟩, ⟨1, by decide⟩] (rationalBounds 2)).hi ≤ bound := by
  decide +kernel

theorem rationalBounds_nonneg (s : State) : 0 ≤ (rationalBounds s).lo := by
  fin_cases s <;> norm_num [rationalBounds]

theorem far_inequality (pre : Word) (d : PartialQuotient) (s : State)
    (hlen : pre.length = 6) (hpre : ∀ a ∈ pre, a.val ≤ 3) (hd : d.val ≤ 3)
    (hstate : afterWord 0 (pre ++ [d]) = some s) :
    (d.val : ℚ) + (enclose pre.reverse unitBounds).hi + (rationalBounds s).hi ≤ bound := by
  have hm : pre ∈ words 6 := hlen ▸ mem_words pre hpre
  have hcheck := List.all_eq_true.mp (List.all_eq_true.mp far_checked pre hm)
    d (mem_alphabet d hd)
  simpa [farCheck, hstate] using hcheck

theorem near_inequality (fixed other : Word) (otherState : State)
    (hchecked : checkNear fixed other otherState = true)
    (pre : Word) (d : PartialQuotient) (s : State) (hlen : pre.length < 6)
    (hpre : ∀ a ∈ pre, a.val ≤ 3) (hd : d.val ≤ 3)
    (hstate : afterWord 0 (fixed ++ pre ++ [d]) = some s) :
    (d.val : ℚ) +
      (enclose ((fixed ++ pre).reverse ++ [four] ++ other) (rationalBounds otherState)).hi +
      (rationalBounds s).hi ≤ bound := by
  have hc := List.all_eq_true.mp hchecked pre.length (List.mem_range.mpr hlen)
  have hp := List.all_eq_true.mp hc pre (mem_words pre hpre)
  have hd' := List.all_eq_true.mp hp d (mem_alphabet d hd)
  unfold nearCheck at hd'
  rw [hstate] at hd'
  exact of_decide_eq_true hd'

/-- Digits viewed from a noncentral position towards the central `4`. -/
def towardDigits (u v : ℕ → PartialQuotient) (k : ℕ) : ℕ → PartialQuotient :=
  fun j => if j < k then u (k - 1 - j) else if j = k then four else v (j - k - 1)

noncomputable def sideValue (u v : ℕ → PartialQuotient) (k : ℕ) : ℝ :=
  (u k).val + value 0 (towardDigits u v k) + value 0 (fun j => u (k + 1 + j))

@[simp] theorem toward_before (u v : ℕ → PartialQuotient) (k j : ℕ) (hj : j < k) :
    towardDigits u v k j = u (k - 1 - j) := by simp [towardDigits, hj]

@[simp] theorem toward_center (u v : ℕ → PartialQuotient) (k : ℕ) :
    towardDigits u v k k = four := by simp [towardDigits]

@[simp] theorem toward_after (u v : ℕ → PartialQuotient) (k j : ℕ) :
    towardDigits u v k (k + 1 + j) = v j := by
  have hlt : ¬ k + 1 + j < k := by omega
  have hne : k + 1 + j ≠ k := by omega
  simp only [towardDigits, hlt, hne, if_false]
  congr 1
  omega

theorem reverse_range_map (u : ℕ → PartialQuotient) (n : ℕ) :
    ((List.range n).map u).reverse = (List.range n).map (fun j => u (n - 1 - j)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

theorem toward_take (u v : ℕ → PartialQuotient) (k m : ℕ) (hm : m ≤ k) :
    (List.range m).map (towardDigits u v k) =
      ((List.range m).map (fun j => u (k - m + j))).reverse := by
  rw [reverse_range_map]
  apply List.map_congr_left
  intro j hj
  have hlt : j < m := List.mem_range.mp hj
  rw [toward_before u v k j (by omega)]
  congr 1
  omega

theorem toward_prefix (u v : ℕ → PartialQuotient) (k : ℕ) (other : Word)
    (hv : (List.range other.length).map v = other) :
    (List.range (k + 1 + other.length)).map (towardDigits u v k) =
      ((List.range k).map u).reverse ++ [four] ++ other := by
  rw [List.range_add, List.map_append, List.range_succ, List.map_append]
  rw [toward_take u v k k le_rfl]
  simp [List.map_map, Function.comp_def, hv]

theorem bounded_after (fixed : Word) (u : ℕ → PartialQuotient)
    (hu : AdmissibleTail fixed u) (n : ℕ) (hn : fixed.length ≤ n) :
    ∀ j, (u (n + j)).val ≤ 3 := by
  intro j
  have h := hu.2.1 (n + j - fixed.length)
  have he : fixed.length + (n + j - fixed.length) = n + j := by omega
  simpa only [he] using h

theorem near_side_bound (fixed other : Word) (otherState : State)
    (hfixed : fixed.length = 3)
    (hchecked : checkNear fixed other otherState = true)
    (u v : ℕ → PartialQuotient) (hu : AdmissibleTail fixed u)
    (hv : AdmissibleTail other v) (hvstate : stateAt v other.length = otherState)
    (n : ℕ) (hn : n < 6) : sideValue u v (3 + n) ≤ (bound : ℝ) := by
  let pre : Word := (List.range n).map (fun j => u (3 + j))
  have hprelen : pre.length = n := by simp [pre]
  have huprefix : (List.range 3).map u = fixed := by simpa [hfixed] using hu.1
  have hprefix : (List.range (3 + n)).map u = fixed ++ pre := by
    rw [List.range_add, List.map_append, huprefix]
    simp [pre, List.map_map, Function.comp_def]
  have hpre : ∀ a ∈ pre, a.val ≤ 3 := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    simpa [hfixed] using hu.2.1 j
  have hd : (u (3 + n)).val ≤ 3 := by simpa [hfixed] using hu.2.1 n
  have hprefix' : (List.range (3 + n + 1)).map u = fixed ++ pre ++ [u (3 + n)] := by
    rw [List.range_succ, List.map_append, hprefix]
    rfl
  have hstate : afterWord 0 (fixed ++ pre ++ [u (3 + n)]) =
      some (stateAt u (3 + n + 1)) := by
    rw [← hprefix']
    exact afterWord_eq_stateAt u hu.2.2 _
  have hnumerical := near_inequality fixed other otherState hchecked pre (u (3 + n))
    (stateAt u (3 + n + 1)) (by simpa [hprelen] using hn) hpre hd hstate
  have hout := value_shift_mem_rational u hu.2.2 (3 + n + 1)
    (bounded_after fixed u hu _ (by omega))
  have hvtail := value_shift_mem_rational v hv.2.2 other.length hv.2.1
  rw [hvstate] at hvtail
  have hshift : (fun j => towardDigits u v (3 + n) (3 + n + 1 + other.length + j)) =
      (fun j => v (other.length + j)) := by
    funext j
    rw [show 3 + n + 1 + other.length + j = 3 + n + 1 + (other.length + j) by omega]
    exact toward_after u v (3 + n) (other.length + j)
  have hin := CFPrefixBounds.value_sound (towardDigits u v (3 + n))
    (3 + n + 1 + other.length) (rationalBounds otherState)
    (rationalBounds_nonneg otherState) (by simpa only [hshift] using hvtail)
  rw [toward_prefix u v (3 + n) other hv.1, hprefix] at hin
  have hnum : (u (3 + n)).val +
      ((enclose ((fixed ++ pre).reverse ++ [four] ++ other) (rationalBounds otherState)).hi : ℝ) +
      ((rationalBounds (stateAt u (3 + n + 1))).hi : ℝ) ≤ (bound : ℝ) := by
    exact_mod_cast hnumerical
  dsimp [sideValue]
  linarith [hin.2, hout.2]

theorem far_side_bound (fixed : Word) (hfixed : fixed.length = 3)
    (u v : ℕ → PartialQuotient) (hu : AdmissibleTail fixed u)
    (k : ℕ) (hk : 9 ≤ k) : sideValue u v k ≤ (bound : ℝ) := by
  let pre : Word := (List.range 6).map (fun j => u (k - 6 + j))
  have hprelen : pre.length = 6 := by simp [pre]
  have hpre : ∀ a ∈ pre, a.val ≤ 3 := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    exact bounded_after fixed u hu (k - 6) (by omega) j
  have hd : (u k).val ≤ 3 := by
    simpa using bounded_after fixed u hu k (by omega) 0
  have hend : k - 6 + 6 = k := by omega
  have hend' : k - 6 + 7 = k + 1 := by omega
  have hprefix : (List.range 7).map (fun j => u (k - 6 + j)) = pre ++ [u k] := by
    rw [show 7 = 6 + 1 by rfl, List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil, hend]
    rfl
  have hstate : afterWord 0 (pre ++ [u k]) = some (stateAt u (k + 1)) := by
    have h := afterWord_eq_stateAt (fun j => u (k - 6 + j))
      (avoids_shift u hu.2.2 (k - 6)) 7
    rw [hprefix, stateAt_shift u (k - 6) 7 (by decide), hend'] at h
    exact h
  have hnumerical := far_inequality pre (u k) (stateAt u (k + 1)) hprelen hpre hd hstate
  have hout := value_shift_mem_rational u hu.2.2 (k + 1)
    (bounded_after fixed u hu _ (by omega))
  have hin := CFPrefixBounds.value_sound (towardDigits u v k) 6 unitBounds
    (by norm_num [unitBounds]) (by
      simpa [unitBounds, QBounds.mem] using
        value_zero_mem_Icc (fun j => towardDigits u v k (6 + j)))
  rw [toward_take u v k 6 (by omega)] at hin
  have hnum : (u k).val + ((enclose pre.reverse unitBounds).hi : ℝ) +
      ((rationalBounds (stateAt u (k + 1))).hi : ℝ) ≤ (bound : ℝ) := by
    exact_mod_cast hnumerical
  change (enclose pre.reverse unitBounds).mem (value 0 (towardDigits u v k)) at hin
  dsimp [sideValue]
  linarith [hin.2, hout.2]

@[simp] theorem glue_pos (left right : ℕ → PartialQuotient) (k : ℕ) :
    glue left right ((k : ℤ) + 1) = right k := by
  have hp : (0 : ℤ) < k + 1 := by omega
  rw [glue, if_neg (ne_of_gt hp), if_neg (not_lt.mpr hp.le)]
  congr 1
  omega

@[simp] theorem glue_neg (left right : ℕ → PartialQuotient) (k : ℕ) :
    glue left right (-(k : ℤ) - 1) = left k := by
  have hn : -(k : ℤ) - 1 < 0 := by omega
  rw [glue, if_neg (ne_of_lt hn), if_pos hn]
  congr 1
  omega

theorem rightDigits_glue_pos (left right : ℕ → PartialQuotient) (k : ℕ) :
    rightDigits (glue left right) ((k : ℤ) + 1) = fun j => right (k + 1 + j) := by
  funext j
  change glue left right ((k : ℤ) + 1 + j + 1) = _
  have he : (k : ℤ) + 1 + j + 1 = ((k + 1 + j : ℕ) : ℤ) + 1 := by omega
  rw [he, glue_pos]

theorem leftDigits_glue_neg (left right : ℕ → PartialQuotient) (k : ℕ) :
    leftDigits (glue left right) (-(k : ℤ) - 1) = fun j => left (k + 1 + j) := by
  funext j
  change glue left right (-(k : ℤ) - 1 - j - 1) = _
  have he : -(k : ℤ) - 1 - j - 1 = -((k + 1 + j : ℕ) : ℤ) - 1 := by omega
  rw [he, glue_neg]

theorem leftDigits_glue_pos (left right : ℕ → PartialQuotient) (k : ℕ) :
    leftDigits (glue left right) ((k : ℤ) + 1) = towardDigits right left k := by
  funext j
  change glue left right ((k : ℤ) + 1 - j - 1) = _
  rw [show (k : ℤ) + 1 - j - 1 = (k : ℤ) - j by ring]
  by_cases hj : j < k
  · have hp : (0 : ℤ) < k - j := by omega
    rw [toward_before right left k j hj, glue, if_neg (ne_of_gt hp),
      if_neg (not_lt.mpr hp.le)]
    congr 1
    omega
  · by_cases he : j = k
    · subst j
      simp [towardDigits, four]
    · have hn : (k : ℤ) - j < 0 := by omega
      rw [glue, if_neg (ne_of_lt hn), if_pos hn]
      simp only [towardDigits, hj, he, if_false]
      congr 1
      omega

theorem rightDigits_glue_neg (left right : ℕ → PartialQuotient) (k : ℕ) :
    rightDigits (glue left right) (-(k : ℤ) - 1) = towardDigits left right k := by
  funext j
  change glue left right (-(k : ℤ) - 1 + j + 1) = _
  rw [show -(k : ℤ) - 1 + j + 1 = (j : ℤ) - k by ring]
  by_cases hj : j < k
  · have hn : (j : ℤ) - k < 0 := by omega
    rw [toward_before left right k j hj, glue, if_neg (ne_of_lt hn), if_pos hn]
    congr 1
    omega
  · by_cases he : j = k
    · subst j
      simp [towardDigits, four]
    · have hp : (0 : ℤ) < j - k := by omega
      rw [glue, if_neg (ne_of_gt hp), if_neg (not_lt.mpr hp.le)]
      simp only [towardDigits, hj, he, if_false]
      congr 1
      omega

theorem localValue_pos (left right : ℕ → PartialQuotient) (k : ℕ) :
    localValue (glue left right) ((k : ℤ) + 1) = sideValue right left k := by
  simp only [localValue, glue_pos, leftDigits_glue_pos, rightDigits_glue_pos, sideValue]

theorem localValue_neg (left right : ℕ → PartialQuotient) (k : ℕ) :
    localValue (glue left right) (-(k : ℤ) - 1) = sideValue left right k := by
  simp only [localValue, glue_neg, leftDigits_glue_neg, rightDigits_glue_neg, sideValue]
  ring

theorem left_side_bound (left right : ℕ → PartialQuotient)
    (hl : AdmissibleTail prefix322 left) (hr : AdmissibleTail prefix431 right)
    (k : ℕ) (hk : 3 ≤ k) : sideValue left right k ≤ (bound : ℝ) := by
  by_cases hfar : 9 ≤ k
  · exact far_side_bound prefix322 rfl left right hl k hfar
  · have hn : k - 3 < 6 := by omega
    have he : 3 + (k - 3) = k := by omega
    have h := near_side_bound prefix322 prefix431 2 rfl near322_checked
      left right hl hr (stateAt_admissible431 right hr) (k - 3) hn
    simpa only [he] using h

theorem right_side_bound (left right : ℕ → PartialQuotient)
    (hl : AdmissibleTail prefix322 left) (hr : AdmissibleTail prefix431 right)
    (k : ℕ) (hk : 3 ≤ k) : sideValue right left k ≤ (bound : ℝ) := by
  by_cases hfar : 9 ≤ k
  · exact far_side_bound prefix431 rfl right left hr k hfar
  · have hn : k - 3 < 6 := by omega
    have he : 3 + (k - 3) = k := by omega
    have h := near_side_bound prefix431 prefix322 0 rfl near431_checked
      right left hr hl (stateAt_admissible322 left hl) (k - 3) hn
    simpa only [he] using h

theorem adjacent_four_bound (left right : ℕ → PartialQuotient)
    (hl : AdmissibleTail prefix322 left) (hr : AdmissibleTail prefix431 right) :
    localValue (glue left right) 1 ≤ (bound : ℝ) := by
  obtain ⟨hr0, hr1, hr2⟩ := admissible431_first_three right hr
  have hlvalue := value_shift_mem_rational left hl.2.2 3 hl.2.1
  have hrvalue := value_shift_mem_rational right hr.2.2 3 hr.2.1
  rw [stateAt_admissible322 left hl] at hlvalue
  rw [stateAt_admissible431 right hr] at hrvalue
  have hin := CFPrefixBounds.value_sound (towardDigits right left 0) 4 (rationalBounds 0)
    (rationalBounds_nonneg 0) (by
      have he : (fun j => towardDigits right left 0 (4 + j)) = fun j => left (3 + j) := by
        funext j
        rw [show 4 + j = 0 + 1 + (3 + j) by omega, toward_after]
      simpa only [he] using hlvalue)
  have hp := toward_prefix right left 0 prefix322 hl.1
  change (List.range 4).map (towardDigits right left 0) = [four] ++ prefix322 at hp
  rw [hp] at hin
  have hout := CFPrefixBounds.value_sound (fun j => right (1 + j)) 2 (rationalBounds 2)
    (rationalBounds_nonneg 2) (by
      have he : (fun j => right (1 + (2 + j))) = fun j => right (3 + j) := by
        funext j
        congr 1
        omega
      simpa only [he] using hrvalue)
  have hq1 : right 1 = ⟨3, by decide⟩ := Subtype.ext hr1
  have hq2 : right 2 = ⟨1, by decide⟩ := Subtype.ext hr2
  have hpout : (List.range 2).map (fun j => right (1 + j)) = [⟨3, by decide⟩, ⟨1, by decide⟩] := by
    simp [List.range_succ, hq1, hq2]
  rw [hpout] at hout
  have hnum : (4 : ℝ) + ((enclose ([four] ++ prefix322) (rationalBounds 0)).hi : ℝ) +
      ((enclose [⟨3, by decide⟩, ⟨1, by decide⟩] (rationalBounds 2)).hi : ℝ) ≤ (bound : ℝ) := by
    exact_mod_cast adjacent_four_checked
  have hv : localValue (glue left right) 1 = sideValue right left 0 := localValue_pos left right 0
  rw [hv]
  dsimp [sideValue]
  rw [hr0]
  norm_num only [Nat.cast_ofNat]
  linarith [hin.2, hout.2]

/-- The complete noncentral bound: every admissible pair of infinite tails
and every nonzero integer position are covered. The four finite acceptance
lemmas above are also checked by reduction inside the Lean kernel. -/
theorem noncentral_bound : NoncentralBound (bound : ℝ) := by
  intro left right hl hr n hn
  by_cases hpos : 4 ≤ n
  · let k : ℕ := (n - 1).toNat
    have hk : 3 ≤ k := by dsimp [k]; omega
    have he : n = (k : ℤ) + 1 := by dsimp [k]; omega
    rw [he, localValue_pos]
    exact right_side_bound left right hl hr k hk
  · by_cases hneg : n ≤ -4
    · let k : ℕ := (-n - 1).toNat
      have hk : 3 ≤ k := by dsimp [k]; omega
      have he : n = -(k : ℤ) - 1 := by dsimp [k]; omega
      rw [he, localValue_neg]
      exact left_side_bound left right hl hr k hk
    · have hlo : -3 ≤ n := by omega
      have hhi : n ≤ 3 := by omega
      obtain ⟨hl0, hl1, hl2⟩ := admissible322_first_three left hl
      obtain ⟨hr0, hr1, hr2⟩ := admissible431_first_three right hr
      have hfour : (4 : ℝ) ≤ (bound : ℝ) := by norm_num [bound]
      have hhalf : (9 / 2 : ℝ) ≤ (bound : ℝ) := by norm_num [bound]
      interval_cases n
      · exact (localValue_le_four_of_digit_le_two (glue left right) (-3)
          (by simp [glue, hl2])).trans hfour
      · exact (localValue_le_four_of_digit_le_two (glue left right) (-2)
          (by simp [glue, hl1])).trans hfour
      · exact (localValue_le_nine_halves_of_adjacent_ge_two (glue left right) (-1)
          (by simp [glue, hl0]) (Or.inr (by change (2 : ℕ) ≤ 4; decide))).trans hhalf
      · exact (hn rfl).elim
      · exact adjacent_four_bound left right hl hr
      · exact (localValue_le_nine_halves_of_adjacent_ge_two (glue left right) 2
          (by simp [glue, hr1]) (Or.inl (by simp [glue, hr0]))).trans hhalf
      · exact (localValue_le_four_of_digit_le_two (glue left right) 3
          (by simp [glue, hr2])).trans hfour

end Berstein.SpectralVerified
