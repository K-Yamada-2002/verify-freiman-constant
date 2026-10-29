import Freiman.Markov
import Berstein.SpectralVerified
import Berstein.Quadratic462

/-! A uniform, executable noncentral-bound checker for arbitrary finite roots.
The near/core checks depend on the supplied positive integer center and exact
quadratic bound; distant positions use the existing six-digit automaton bound. -/
namespace Freiman.Spectral
open Berstein HallRay.ContinuedFraction Forbidden31313 CFPrefixBounds
open Berstein.SpectralVerified (words alphabet mem_words mem_alphabet)


def tailBounds (s : State) : QBounds :=
  if s.val = 0 then ⟨(263931519253/1000000000000),(395591052509/500000000000)⟩
  else if s.val = 1 then ⟨(263931519253/1000000000000),(394430803169/500000000000)⟩
  else if s.val = 2 then ⟨(133824736789/500000000000),(395591052509/500000000000)⟩
  else if s.val = 3 then ⟨(263931519253/1000000000000),(73623002739/100000000000)⟩
  else ⟨(179135570947/500000000000),(395591052509/500000000000)⟩

theorem tailBounds_nonneg (s : State) : 0 ≤ (tailBounds s).lo := by
  fin_cases s <;> norm_num [tailBounds]

theorem value_shift_mem_tail (u : ℕ → PartialQuotient) (h : Avoids31313 u)
    (n : ℕ) (hd : ∀ k, (u (n+k)).val ≤ 3) :
    (tailBounds (stateAt u n)).mem (value 0 (fun k => u (n+k))) := by
  have hv := value_shift_mem_exact u h n hd
  have hl : ∀ s : State, GraphMeaning.contains (tailBounds s) (GraphMeaning.lower s.val) = true := by
    decide +kernel
  have hh : ∀ s : State, GraphMeaning.contains (tailBounds s) (GraphMeaning.upper s.val) = true := by
    decide +kernel
  have hle := GraphMeaning.contains_sound _ _ (hl (stateAt u n))
  have hhe := GraphMeaning.contains_sound _ _ (hh (stateAt u n))
  rw [GraphMeaning.lower_eval] at hle
  rw [GraphMeaning.upper_eval] at hhe
  exact ⟨hle.1.trans hv.1,hv.2.trans hhe.2⟩

class Parameters where
  center : PartialQuotient
  bound : Quadratic462

variable [Parameters]

def nearCheck (fixed other : Word) (otherState : State) (pre : Word)
    (d : PartialQuotient) : Bool :=
  match afterWord 0 (fixed ++ pre ++ [d]) with
  | none => true
  | some s => Quadratic462.le (Quadratic462.ofRat ((d.val : ℚ) +
      (enclose ((fixed ++ pre).reverse ++ [Parameters.center] ++ other) (tailBounds otherState)).hi +
      (tailBounds s).hi)) Parameters.bound

def checkNear (fixed other : Word) (otherState : State) : Bool :=
  (List.range 6).all fun n => (words n).all fun pre =>
    alphabet.all fun d => nearCheck fixed other otherState pre d


theorem near_inequality (fixed other : Word) (otherState : State)
    (hchecked : checkNear fixed other otherState = true)
    (pre : Word) (d : PartialQuotient) (s : State) (hlen : pre.length < 6)
    (hpre : ∀ a ∈ pre, a.val ≤ 3) (hd : d.val ≤ 3)
    (hstate : afterWord 0 (fixed ++ pre ++ [d]) = some s) :
    (((d.val : ℚ) +
      (enclose ((fixed ++ pre).reverse ++ [Parameters.center] ++ other) (tailBounds otherState)).hi +
      (tailBounds s).hi : ℚ) : ℝ) ≤ Parameters.bound.eval := by
  have hc := List.all_eq_true.mp hchecked pre.length (List.mem_range.mpr hlen)
  have hp := List.all_eq_true.mp hc pre (mem_words pre hpre)
  have hd' := List.all_eq_true.mp hp d (mem_alphabet d hd)
  unfold nearCheck at hd'
  rw [hstate] at hd'
  simpa only [Quadratic462.eval_ofRat] using Quadratic462.le_sound _ _ hd'

/-- Digits viewed from a noncentral position towards the central digit. -/
def towardDigits (u v : ℕ → PartialQuotient) (k : ℕ) : ℕ → PartialQuotient :=
  fun j => if j < k then u (k - 1 - j) else if j = k then Parameters.center else v (j - k - 1)

noncomputable def sideValue (u v : ℕ → PartialQuotient) (k : ℕ) : ℝ :=
  (u k).val + value 0 (towardDigits u v k) + value 0 (fun j => u (k + 1 + j))

@[simp] theorem toward_before (u v : ℕ → PartialQuotient) (k j : ℕ) (hj : j < k) :
    towardDigits u v k j = u (k - 1 - j) := by simp [towardDigits, hj]

@[simp] theorem toward_center (u v : ℕ → PartialQuotient) (k : ℕ) :
    towardDigits u v k k = Parameters.center := by simp [towardDigits]

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
      ((List.range k).map u).reverse ++ [Parameters.center] ++ other := by
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
    (hchecked : checkNear fixed other otherState = true)
    (u v : ℕ → PartialQuotient) (hu : AdmissibleTail fixed u)
    (hv : AdmissibleTail other v) (hvstate : stateAt v other.length = otherState)
    (n : ℕ) (hn : n < 6) : sideValue u v (fixed.length + n) ≤ Parameters.bound.eval := by
  let pre : Word := (List.range n).map (fun j => u (fixed.length + j))
  have hprelen : pre.length = n := by simp [pre]
  have huprefix : (List.range fixed.length).map u = fixed := hu.1
  have hprefix : (List.range (fixed.length + n)).map u = fixed ++ pre := by
    rw [List.range_add, List.map_append, huprefix]
    simp [pre, List.map_map, Function.comp_def]
  have hpre : ∀ a ∈ pre, a.val ≤ 3 := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    simpa using hu.2.1 j
  have hd : (u (fixed.length + n)).val ≤ 3 := by simpa using hu.2.1 n
  have hprefix' : (List.range (fixed.length + n + 1)).map u = fixed ++ pre ++ [u (fixed.length + n)] := by
    rw [List.range_succ, List.map_append, hprefix]
    rfl
  have hstate : afterWord 0 (fixed ++ pre ++ [u (fixed.length + n)]) =
      some (stateAt u (fixed.length + n + 1)) := by
    rw [← hprefix']
    exact afterWord_eq_stateAt u hu.2.2 _
  have hnumerical := near_inequality fixed other otherState hchecked pre (u (fixed.length + n))
    (stateAt u (fixed.length + n + 1)) (by simpa [hprelen] using hn) hpre hd hstate
  have hout := value_shift_mem_tail u hu.2.2 (fixed.length + n + 1)
    (bounded_after fixed u hu _ (by omega))
  have hvtail := value_shift_mem_tail v hv.2.2 other.length hv.2.1
  rw [hvstate] at hvtail
  have hshift : (fun j => towardDigits u v (fixed.length + n) (fixed.length + n + 1 + other.length + j)) =
      (fun j => v (other.length + j)) := by
    funext j
    rw [show fixed.length + n + 1 + other.length + j = fixed.length + n + 1 + (other.length + j) by omega]
    exact toward_after u v (fixed.length + n) (other.length + j)
  have hin := CFPrefixBounds.value_sound (towardDigits u v (fixed.length + n))
    (fixed.length + n + 1 + other.length) (tailBounds otherState)
    (tailBounds_nonneg otherState) (by simpa only [hshift] using hvtail)
  rw [toward_prefix u v (fixed.length + n) other hv.1, hprefix] at hin
  have hnum : (u (fixed.length + n)).val +
      ((enclose ((fixed ++ pre).reverse ++ [Parameters.center] ++ other) (tailBounds otherState)).hi : ℝ) +
      ((tailBounds (stateAt u (fixed.length + n + 1))).hi : ℝ) ≤ Parameters.bound.eval := by
    simpa only [Rat.cast_add,Rat.cast_natCast] using hnumerical
  dsimp [sideValue]
  linarith [hin.2, hout.2]

theorem far_side_bound (fixed : Word) 
    (u v : ℕ → PartialQuotient) (hu : AdmissibleTail fixed u)
    (k : ℕ) (hk : fixed.length+6 ≤ k) : sideValue u v k ≤ (Berstein.SpectralVerified.bound : ℝ) := by
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
  have hnumerical := Berstein.SpectralVerified.far_inequality pre (u k) (stateAt u (k + 1)) hprelen hpre hd hstate
  have hout := value_shift_mem_rational u hu.2.2 (k + 1)
    (bounded_after fixed u hu _ (by omega))
  have hin := CFPrefixBounds.value_sound (towardDigits u v k) 6 Berstein.SpectralVerified.unitBounds
    (by norm_num [Berstein.SpectralVerified.unitBounds]) (by
      simpa [Berstein.SpectralVerified.unitBounds, QBounds.mem] using
        value_zero_mem_Icc (fun j => towardDigits u v k (6 + j)))
  rw [toward_take u v k 6 (by omega)] at hin
  have hnum : (u k).val + ((enclose pre.reverse Berstein.SpectralVerified.unitBounds).hi : ℝ) +
      ((rationalBounds (stateAt u (k + 1))).hi : ℝ) ≤ (Berstein.SpectralVerified.bound : ℝ) := by
    exact_mod_cast hnumerical
  change (enclose pre.reverse Berstein.SpectralVerified.unitBounds).mem (value 0 (towardDigits u v k)) at hin
  dsimp [sideValue]
  linarith [hin.2, hout.2]


@[simp] theorem glue_pos (left right : ℕ → PartialQuotient) (k : ℕ) :
    glueAt Parameters.center left right ((k : ℤ) + 1) = right k := by
  have hp : (0 : ℤ) < k + 1 := by omega
  rw [glueAt, if_neg (ne_of_gt hp), if_neg (not_lt.mpr hp.le)]
  congr 1
  omega

@[simp] theorem glue_neg (left right : ℕ → PartialQuotient) (k : ℕ) :
    glueAt Parameters.center left right (-(k : ℤ) - 1) = left k := by
  have hn : -(k : ℤ) - 1 < 0 := by omega
  rw [glueAt, if_neg (ne_of_lt hn), if_pos hn]
  congr 1
  omega

theorem rightDigits_glue_pos (left right : ℕ → PartialQuotient) (k : ℕ) :
    rightDigits (glueAt Parameters.center left right) ((k : ℤ) + 1) = fun j => right (k + 1 + j) := by
  funext j
  change glueAt Parameters.center left right ((k : ℤ) + 1 + j + 1) = _
  have he : (k : ℤ) + 1 + j + 1 = ((k + 1 + j : ℕ) : ℤ) + 1 := by omega
  rw [he, glue_pos]

theorem leftDigits_glue_neg (left right : ℕ → PartialQuotient) (k : ℕ) :
    leftDigits (glueAt Parameters.center left right) (-(k : ℤ) - 1) = fun j => left (k + 1 + j) := by
  funext j
  change glueAt Parameters.center left right (-(k : ℤ) - 1 - j - 1) = _
  have he : -(k : ℤ) - 1 - j - 1 = -((k + 1 + j : ℕ) : ℤ) - 1 := by omega
  rw [he, glue_neg]

theorem leftDigits_glue_pos (left right : ℕ → PartialQuotient) (k : ℕ) :
    leftDigits (glueAt Parameters.center left right) ((k : ℤ) + 1) = towardDigits right left k := by
  funext j
  change glueAt Parameters.center left right ((k : ℤ) + 1 - j - 1) = _
  rw [show (k : ℤ) + 1 - j - 1 = (k : ℤ) - j by ring]
  by_cases hj : j < k
  · have hp : (0 : ℤ) < k - j := by omega
    rw [toward_before right left k j hj, glueAt, if_neg (ne_of_gt hp),
      if_neg (not_lt.mpr hp.le)]
    congr 1
    omega
  · by_cases he : j = k
    · subst j
      simp [towardDigits, glueAt]
    · have hn : (k : ℤ) - j < 0 := by omega
      rw [glueAt, if_neg (ne_of_lt hn), if_pos hn]
      simp only [towardDigits, hj, he, if_false]
      congr 1
      omega

theorem rightDigits_glue_neg (left right : ℕ → PartialQuotient) (k : ℕ) :
    rightDigits (glueAt Parameters.center left right) (-(k : ℤ) - 1) = towardDigits left right k := by
  funext j
  change glueAt Parameters.center left right (-(k : ℤ) - 1 + j + 1) = _
  rw [show -(k : ℤ) - 1 + j + 1 = (j : ℤ) - k by ring]
  by_cases hj : j < k
  · have hn : (j : ℤ) - k < 0 := by omega
    rw [toward_before left right k j hj, glueAt, if_neg (ne_of_lt hn), if_pos hn]
    congr 1
    omega
  · by_cases he : j = k
    · subst j
      simp [towardDigits, glueAt]
    · have hp : (0 : ℤ) < j - k := by omega
      rw [glueAt, if_neg (ne_of_gt hp), if_neg (not_lt.mpr hp.le)]
      simp only [towardDigits, hj, he, if_false]
      congr 1
      omega

theorem localValue_pos (left right : ℕ → PartialQuotient) (k : ℕ) :
    localValue (glueAt Parameters.center left right) ((k : ℤ) + 1) = sideValue right left k := by
  simp only [localValue, glue_pos, leftDigits_glue_pos, rightDigits_glue_pos, sideValue]

theorem localValue_neg (left right : ℕ → PartialQuotient) (k : ℕ) :
    localValue (glueAt Parameters.center left right) (-(k : ℤ) - 1) = sideValue left right k := by
  simp only [localValue, glue_neg, leftDigits_glue_neg, rightDigits_glue_neg, sideValue]
  ring


/-- The actual tail has the state obtained by scanning the fixed root. -/
theorem admissible_state (w : Word) (s : State) (u : ℕ → PartialQuotient)
    (hu : AdmissibleTail w u) (hs : afterWord 0 w = some s) : stateAt u w.length = s := by
  have h := afterWord_eq_stateAt u hu.2.2 w.length
  rw [hu.1,hs] at h
  exact (Option.some.inj h).symm

theorem prefix_take (w : Word) (u : ℕ → PartialQuotient)
    (hu : (List.range w.length).map u = w) (k : ℕ) (hk : k ≤ w.length) :
    (List.range k).map u = w.take k := by
  have h := congrArg (List.take k) hu
  simpa only [← List.map_take,List.take_range,min_eq_left hk] using h

theorem prefix_drop (w : Word) (u : ℕ → PartialQuotient)
    (hu : (List.range w.length).map u = w) (k : ℕ) :
    (List.range (w.length-k)).map (fun j => u (k+j)) = w.drop k := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hki : k+i < w.length := by simp at hi; omega
  have h := (beginsWith_iff_map_range w u).mpr hu ⟨k+i,hki⟩
  simpa using h

def coreCheck (fixed other : Word) (fixedState otherState : State) (k : ℕ) : Bool :=
  match fixed[k]? with
  | none => false
  | some d => Quadratic462.le (Quadratic462.ofRat ((d.val : ℚ)+
      (enclose ((fixed.take k).reverse++[Parameters.center]++other) (tailBounds otherState)).hi+
      (enclose (fixed.drop (k+1)) (tailBounds fixedState)).hi)) Parameters.bound

def checkCore (fixed other : Word) (fixedState otherState : State) : Bool :=
  (List.range fixed.length).all (coreCheck fixed other fixedState otherState)

theorem core_side_bound (fixed other : Word) (fixedState otherState : State)
    (hc : checkCore fixed other fixedState otherState = true)
    (u v : ℕ → PartialQuotient) (hu : AdmissibleTail fixed u)
    (hv : AdmissibleTail other v) (hus : stateAt u fixed.length = fixedState)
    (hvs : stateAt v other.length = otherState) (k : ℕ) (hk : k < fixed.length) :
    sideValue u v k ≤ Parameters.bound.eval := by
  have hcheck := List.all_eq_true.mp hc k (List.mem_range.mpr hk)
  have hlookup : fixed[k]? = some (u k) := by
    rw [List.getElem?_eq_getElem hk]
    exact congrArg some ((beginsWith_iff_map_range fixed u).mpr hu.1 ⟨k,hk⟩).symm
  simp only [coreCheck,hlookup] at hcheck
  have hnum := Quadratic462.le_sound _ _ hcheck
  simp only [Quadratic462.eval_ofRat,Rat.cast_add,Rat.cast_natCast] at hnum
  have hvtail := value_shift_mem_tail v hv.2.2 other.length hv.2.1
  rw [hvs] at hvtail
  have hin := CFPrefixBounds.value_sound (towardDigits u v k) (k+1+other.length)
    (tailBounds otherState) (tailBounds_nonneg otherState) (by
      have he : (fun j => towardDigits u v k (k+1+other.length+j)) =
          (fun j => v (other.length+j)) := by
        funext j
        rw [show k+1+other.length+j = k+1+(other.length+j) by omega,toward_after]
      simpa only [he] using hvtail)
  rw [toward_prefix u v k other hv.1,prefix_take fixed u hu.1 k hk.le] at hin
  have hutail := value_shift_mem_tail u hu.2.2 fixed.length hu.2.1
  rw [hus] at hutail
  have hout := CFPrefixBounds.value_sound (fun j => u (k+1+j)) (fixed.length-(k+1))
    (tailBounds fixedState) (tailBounds_nonneg fixedState) (by
      have he : (fun j => u (k+1+(fixed.length-(k+1)+j))) =
          (fun j => u (fixed.length+j)) := by funext j; congr 1; omega
      simpa only [he] using hutail)
  rw [prefix_drop fixed u hu.1 (k+1)] at hout
  dsimp only [sideValue]
  linarith [hin.2,hout.2]

theorem side_bound (fixed other : Word) (fixedState otherState : State)
    (hcore : checkCore fixed other fixedState otherState = true)
    (hnear : checkNear fixed other otherState = true)
    (hfar : (Berstein.SpectralVerified.bound : ℝ) ≤ Parameters.bound.eval)
    (u v : ℕ → PartialQuotient) (hu : AdmissibleTail fixed u)
    (hv : AdmissibleTail other v) (hus : stateAt u fixed.length = fixedState)
    (hvs : stateAt v other.length = otherState) (k : ℕ) : sideValue u v k ≤ Parameters.bound.eval := by
  by_cases hk : k < fixed.length
  · exact core_side_bound fixed other fixedState otherState hcore u v hu hv hus hvs k hk
  · by_cases hfar' : fixed.length+6 ≤ k
    · exact (far_side_bound fixed u v hu k hfar').trans hfar
    · have h := near_side_bound fixed other otherState hnear u v hu hv hvs (k-fixed.length) (by omega)
      simpa only [Nat.add_sub_of_le (by omega : fixed.length ≤ k)] using h

end Freiman.Spectral

namespace Freiman.Spectral
open Berstein HallRay.ContinuedFraction Forbidden31313

structure Certificate where
  left : Word
  right : Word
  center : PartialQuotient
  leftState : State
  rightState : State
  bound : Quadratic462

instance : Inhabited Certificate := ⟨⟨[],[],⟨1,by decide⟩,0,0,default⟩⟩

abbrev Certificate.parameters (c : Certificate) : Parameters := ⟨c.center,c.bound⟩

def check (c : Certificate) : Bool :=
  letI := c.parameters
  decide (afterWord 0 c.left = some c.leftState) &&
    decide (afterWord 0 c.right = some c.rightState) &&
    Quadratic462.le (Quadratic462.ofRat Berstein.SpectralVerified.bound) c.bound &&
    checkCore c.left c.right c.leftState c.rightState &&
    checkCore c.right c.left c.rightState c.leftState &&
    checkNear c.left c.right c.rightState && checkNear c.right c.left c.leftState

/-- All noncentral positions and all infinite admissible extensions follow
from this finite executable predicate. No spectral conclusion is assumed. -/
theorem check_sound (c : Certificate) (hc : check c = true) :
    Freiman.NoncentralBound c.left c.right c.center c.bound.eval := by
  letI := c.parameters
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨⟨hl,hr⟩,hf⟩,hcl⟩,hcr⟩,hnl⟩,hnr⟩
  have hfar : (Berstein.SpectralVerified.bound : ℝ) ≤ c.bound.eval := by
    simpa only [Quadratic462.eval_ofRat] using Quadratic462.le_sound _ _ hf
  intro l r hal har n hn
  change localValue (glueAt Parameters.center l r) n ≤ Parameters.bound.eval
  have hls := admissible_state c.left c.leftState l hal hl
  have hrs := admissible_state c.right c.rightState r har hr
  by_cases hpos : 0 < n
  · let k := (n-1).toNat
    have he : n = (k : ℤ)+1 := by dsimp [k]; omega
    rw [he,localValue_pos]
    exact side_bound c.right c.left c.rightState c.leftState hcr hnr hfar r l har hal hrs hls k
  · let k := (-n-1).toNat
    have he : n = -(k : ℤ)-1 := by dsimp [k]; omega
    rw [he,localValue_neg]
    exact side_bound c.left c.right c.leftState c.rightState hcl hnl hfar l r hal har hls hrs k

end Freiman.Spectral
