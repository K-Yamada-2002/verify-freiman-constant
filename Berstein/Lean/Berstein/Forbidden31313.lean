import Berstein.Markov
import Berstein.CFInvariant
import Berstein.IntervalArithmetic

/-! The five-state automaton for avoiding `31313`, connected to the actual
one-sided sequences in `AdmissibleTail`. Digits other than `1` and `3`,
including the allowed fixed digit `4`, reset the state. -/

namespace Berstein.Forbidden31313

open HallRay.ContinuedFraction

abbrev State := Fin 5

/-- States `0,1,2,3,4` represent suffixes `[],[3],[3,1],[3,1,3],[3,1,3,1]`. -/
def transitionNat (s : State) (digit : ℕ) : Option State :=
  if digit = 1 then
    if s.val = 1 then some 2 else if s.val = 3 then some 4 else some 0
  else if digit = 3 then
    if s.val = 2 then some 3 else if s.val = 4 then none else some 1
  else some 0

/-- Recognize the longest relevant suffix from four previous digits,
provided newest first. Zero can be used as padding before the sequence. -/
def historyState (a b c d : ℕ) : State :=
  if a = 3 then
    if b = 1 ∧ c = 3 then 3 else 1
  else if a = 1 ∧ b = 3 then
    if c = 1 ∧ d = 3 then 4 else 2
  else 0

theorem transition_history (a b c d z : ℕ) :
    transitionNat (historyState a b c d) z =
      if d = 3 ∧ c = 1 ∧ b = 3 ∧ a = 1 ∧ z = 3 then none
      else some (historyState z a b c) := by
  by_cases ha3 : a = 3 <;> by_cases ha1 : a = 1 <;>
    by_cases hb3 : b = 3 <;> by_cases hb1 : b = 1 <;>
    by_cases hc3 : c = 3 <;> by_cases hc1 : c = 1 <;>
    by_cases hd3 : d = 3 <;> by_cases hz3 : z = 3 <;> by_cases hz1 : z = 1 <;>
    simp_all [transitionNat, historyState]

/-- The `k`th preceding digit at time `n`, or zero if it is before time zero. -/
def pastDigit (u : ℕ → PartialQuotient) (n k : ℕ) : ℕ :=
  if k < n then (u (n - 1 - k)).val else 0

def stateAt (u : ℕ → PartialQuotient) (n : ℕ) : State :=
  historyState (pastDigit u n 0) (pastDigit u n 1)
    (pastDigit u n 2) (pastDigit u n 3)

@[simp] theorem pastDigit_succ_zero (u : ℕ → PartialQuotient) (n : ℕ) :
    pastDigit u (n + 1) 0 = (u n).val := by simp [pastDigit]

@[simp] theorem pastDigit_succ_succ (u : ℕ → PartialQuotient) (n k : ℕ) :
    pastDigit u (n + 1) (k + 1) = pastDigit u n k := by
  by_cases hk : k < n
  · have hk' : k + 1 < n + 1 := by omega
    simp only [pastDigit, hk, hk', if_true]
    congr 2
    omega
  · have hk' : ¬ k + 1 < n + 1 := by omega
    simp [pastDigit, hk, hk']

@[simp] theorem stateAt_zero (u : ℕ → PartialQuotient) : stateAt u 0 = 0 := by
  simp [stateAt, pastDigit, historyState]

theorem pastDigit_shift (u : ℕ → PartialQuotient) (start n k : ℕ) (hk : k < n) :
    pastDigit (fun j => u (start + j)) n k = pastDigit u (start + n) k := by
  have hk' : k < start + n := by omega
  simp only [pastDigit, hk, hk', if_true]
  congr 2
  omega

/-- After four digits, the state is independent of the discarded history. -/
theorem stateAt_shift (u : ℕ → PartialQuotient) (start n : ℕ) (hn : 4 ≤ n) :
    stateAt (fun j => u (start + j)) n = stateAt u (start + n) := by
  unfold stateAt
  rw [pastDigit_shift u start n 0 (by omega), pastDigit_shift u start n 1 (by omega),
    pastDigit_shift u start n 2 (by omega), pastDigit_shift u start n 3 (by omega)]

theorem avoids_shift (u : ℕ → PartialQuotient) (h : Avoids31313 u) (start : ℕ) :
    Avoids31313 (fun k => u (start + k)) := by
  intro n
  simpa [Nat.add_assoc] using h (start + n)

theorem no_bad_history (u : ℕ → PartialQuotient) (h : Avoids31313 u) (n : ℕ) :
    ¬ (pastDigit u n 3 = 3 ∧ pastDigit u n 2 = 1 ∧
      pastDigit u n 1 = 3 ∧ pastDigit u n 0 = 1 ∧ (u n).val = 3) := by
  intro hb
  by_cases hn : 4 ≤ n
  · have h0 : 0 < n := by omega
    have h1 : 1 < n := by omega
    have h2 : 2 < n := by omega
    have h3 : 3 < n := by omega
    simp only [pastDigit, h0, h1, h2, h3, if_true, Nat.sub_sub] at hb
    apply h (n - 4)
    have e1 : n - 4 + 1 = n - 3 := by omega
    have e2 : n - 4 + 2 = n - 2 := by omega
    have e3 : n - 4 + 3 = n - 1 := by omega
    have e4 : n - 4 + 4 = n := by omega
    simpa only [e1, e2, e3, e4, Nat.add_zero] using hb
  · have h3 : ¬ 3 < n := by omega
    simp [pastDigit, h3] at hb

/-- Avoidance of the literal forbidden word guarantees every actual step of
the five-state machine, with no assumption about subsequent digits being ≤3. -/
theorem transition_stateAt (u : ℕ → PartialQuotient) (h : Avoids31313 u) (n : ℕ) :
    transitionNat (stateAt u n) (u n).val = some (stateAt u (n + 1)) := by
  rw [stateAt, transition_history, if_neg (no_bad_history u h n)]
  simp only [stateAt, pastDigit_succ_zero, pastDigit_succ_succ]

theorem avoids_of_transition_stateAt (u : ℕ → PartialQuotient)
    (h : ∀ n, transitionNat (stateAt u n) (u n).val = some (stateAt u (n + 1))) :
    Avoids31313 u := by
  intro n hb
  have hp := h (n + 4)
  have h0 : 0 < n + 4 := by omega
  have h1 : 1 < n + 4 := by omega
  have h2 : 2 < n + 4 := by omega
  have h3 : 3 < n + 4 := by omega
  have e0 : n + 4 - 1 - 0 = n + 3 := by omega
  have e1 : n + 4 - 1 - 1 = n + 2 := by omega
  have e2 : n + 4 - 1 - 2 = n + 1 := by omega
  have e3 : n + 4 - 1 - 3 = n := by omega
  have bad : pastDigit u (n + 4) 3 = 3 ∧ pastDigit u (n + 4) 2 = 1 ∧
      pastDigit u (n + 4) 1 = 3 ∧ pastDigit u (n + 4) 0 = 1 ∧ (u (n + 4)).val = 3 := by
    simpa only [pastDigit, h0, h1, h2, h3, if_true, e0, e1, e2, e3] using hb
  rw [stateAt, transition_history, if_pos bad] at hp
  contradiction

theorem avoids_iff_transition_stateAt (u : ℕ → PartialQuotient) :
    Avoids31313 u ↔
      ∀ n, transitionNat (stateAt u n) (u n).val = some (stateAt u (n + 1)) :=
  ⟨fun h n => transition_stateAt u h n, avoids_of_transition_stateAt u⟩

/-- Executable traversal of a finite word, rejecting the forbidden pattern. -/
def afterWord (s : State) : Word → Option State
  | [] => some s
  | digit :: rest => (transitionNat s digit.val).bind fun s' => afterWord s' rest

theorem afterWord_append (s : State) (a b : Word) :
    afterWord s (a ++ b) = (afterWord s a).bind (fun t => afterWord t b) := by
  induction a generalizing s with
  | nil => rfl
  | cons digit a ih =>
      simp only [List.cons_append, afterWord]
      cases h : transitionNat s digit.val <;> simp [h, ih]

theorem afterWord_eq_stateAt (u : ℕ → PartialQuotient) (h : Avoids31313 u) (n : ℕ) :
    afterWord 0 ((List.range n).map u) = some (stateAt u n) := by
  induction n with
  | zero => simp [afterWord]
  | succ n ih =>
      rw [List.range_succ, List.map_append, afterWord_append, ih]
      simp [afterWord, transition_stateAt u h n]

theorem afterWord_eq_stateAt_from (u : ℕ → PartialQuotient) (h : Avoids31313 u)
    (start length : ℕ) :
    afterWord (stateAt u start) ((List.range length).map (fun k => u (start + k))) =
      some (stateAt u (start + length)) := by
  induction length with
  | zero => simp [afterWord]
  | succ length ih =>
      rw [List.range_succ, List.map_append, afterWord_append, ih]
      simp [afterWord, transition_stateAt u h (start + length), Nat.add_assoc]

theorem afterWord_322 : afterWord 0 prefix322 = some 0 := by decide
theorem afterWord_431 : afterWord 0 prefix431 = some 2 := by decide

theorem stateAt_admissible322 (u : ℕ → PartialQuotient)
    (h : AdmissibleTail prefix322 u) : stateAt u 3 = 0 := by
  obtain ⟨h0, h1, h2⟩ := admissible322_first_three u h
  simp [stateAt, pastDigit, historyState, h0, h1, h2]

theorem stateAt_admissible431 (u : ℕ → PartialQuotient)
    (h : AdmissibleTail prefix431 u) : stateAt u 3 = 2 := by
  obtain ⟨h0, h1, h2⟩ := admissible431_first_three u h
  simp [stateAt, pastDigit, historyState, h0, h1, h2]

/-- Exact Bellman lower bounds. These formulas are proved to be invariant
below; their use does not assume that they are attained extrema. -/
noncomputable def exactLower (s : State) : ℝ :=
  if s.val = 2 then -1 / 2 + Real.sqrt 462 / 28
  else if s.val = 4 then (-24 + 2 * Real.sqrt 462) / 53
  else (-29 + 2 * Real.sqrt 462) / 53

noncomputable def exactUpper (s : State) : ℝ :=
  if s.val = 1 then (-28 + 2 * Real.sqrt 462) / 19
  else if s.val = 3 then (-29 + 2 * Real.sqrt 462) / 19
  else -1 + Real.sqrt 462 / 12

private theorem sqrt462_coarse : (21 : ℝ) < Real.sqrt 462 ∧ Real.sqrt 462 < 22 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 462)
  have hn := Real.sqrt_nonneg (462 : ℝ)
  constructor <;> nlinarith

theorem exactBounds_unit (s : State) :
    0 ≤ exactLower s ∧ exactLower s ≤ exactUpper s ∧ exactUpper s ≤ 1 := by
  obtain ⟨hl, hu⟩ := sqrt462_coarse
  fin_cases s <;> norm_num [exactLower, exactUpper] <;>
    constructor <;> (try constructor) <;> nlinarith

/-- Fourteen local inequalities verify the entire algebraic interval
invariant: the fifteenth digit/state pair would produce `31313`. -/
theorem exact_cross_bounds (s t : State) (digit : ℕ)
    (hd : 1 ≤ digit ∧ digit ≤ 3) (h : transitionNat s digit = some t) :
    exactLower s * ((digit : ℝ) + exactUpper t) ≤ 1 ∧
      1 ≤ exactUpper s * ((digit : ℝ) + exactLower t) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 462)
  obtain ⟨hl, hu⟩ := sqrt462_coarse
  obtain ⟨hd1, hd3⟩ := hd
  interval_cases digit <;> fin_cases s <;> fin_cases t <;>
    norm_num [transitionNat, Fin.ext_iff] at h <;> (try contradiction) <;>
    norm_num [exactLower, exactUpper] <;> constructor <;> nlinarith

theorem exact_invariant (s t : State) (digit : PartialQuotient)
    (hd : digit.val ≤ 3) (h : transitionNat s digit.val = some t)
    (x : ℝ) (hx : x ∈ Set.Icc (exactLower t) (exactUpper t)) :
    1 / ((digit.val : ℝ) + x) ∈ Set.Icc (exactLower s) (exactUpper s) := by
  have hstep := exact_cross_bounds s t digit.val ⟨digit.property, hd⟩ h
  have hs := exactBounds_unit s
  have ht := exactBounds_unit t
  have hx0 : 0 ≤ x := ht.1.trans hx.1
  have hdpos : (0 : ℝ) < digit.val := by exact_mod_cast digit.property
  have hden : 0 < (digit.val : ℝ) + x := by linarith
  have hsupper : 0 ≤ exactUpper s := hs.1.trans hs.2.1
  constructor
  · apply (le_div_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left (add_le_add_left hx.2 (digit.val : ℝ)) hs.1
    linarith [hstep.1]
  · apply (div_le_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left (add_le_add_left hx.1 (digit.val : ℝ)) hsupper
    nlinarith [hstep.2]

/-- A legal stream restricted to digits `1,2,3` after position `n` has its
actual continued-fraction tail enclosed by the exact interval of its state. -/
theorem value_shift_mem_exact (u : ℕ → PartialQuotient) (h : Avoids31313 u)
    (n : ℕ) (hdigits : ∀ k, (u (n + k)).val ≤ 3) :
    value 0 (fun k => u (n + k)) ∈
      Set.Icc (exactLower (stateAt u n)) (exactUpper (stateAt u n)) := by
  let step : State → PartialQuotient → State → Prop :=
    fun s d t => d.val ≤ 3 ∧ transitionNat s d.val = some t
  have hb := CFInvariant.value_mem exactLower exactUpper step
    (fun s => (exactBounds_unit s).2.1) (fun s => (exactBounds_unit s).1)
    (fun s => (exactBounds_unit s).2.2)
    (fun s d t hstep x hx => exact_invariant s t d hstep.1 hstep.2 x hx)
    (fun k => stateAt u (n + k)) (fun k => u (n + k)) (by
      intro k
      exact ⟨hdigits k, by simpa [Nat.add_assoc] using transition_stateAt u h (n + k)⟩)
  simpa using hb

/-- Rational outward bounds for use by an executable spectral checker. -/
def rationalBounds (s : State) : QBounds :=
  ⟨if s.val = 2 then 267649463 / 1000000000
    else if s.val = 4 then 358271131 / 1000000000
    else 263931509 / 1000000000,
   if s.val = 1 then 788861617 / 1000000000
    else if s.val = 3 then 368115019 / 500000000
    else 197795529 / 250000000⟩

private theorem sqrt462_fine :
    (214941852602 / 10000000000 : ℝ) < Real.sqrt 462 ∧
      Real.sqrt 462 < (214941852603 / 10000000000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 462)
  have hn := Real.sqrt_nonneg (462 : ℝ)
  constructor <;> nlinarith

theorem exact_enclosed (s : State) :
    ((rationalBounds s).lo : ℝ) ≤ exactLower s ∧
      exactUpper s ≤ ((rationalBounds s).hi : ℝ) := by
  obtain ⟨hl, hu⟩ := sqrt462_fine
  fin_cases s <;> norm_num [rationalBounds, exactLower, exactUpper] <;>
    constructor <;> linarith

theorem value_shift_mem_rational (u : ℕ → PartialQuotient) (h : Avoids31313 u)
    (n : ℕ) (hdigits : ∀ k, (u (n + k)).val ≤ 3) :
    (rationalBounds (stateAt u n)).mem (value 0 (fun k => u (n + k))) := by
  have hv := value_shift_mem_exact u h n hdigits
  have he := exact_enclosed (stateAt u n)
  exact ⟨he.1.trans hv.1, hv.2.trans he.2⟩

end Berstein.Forbidden31313
