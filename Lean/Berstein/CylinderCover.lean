import Berstein.ActualCylinders
import Berstein.ClosedCover
import HallRay.ContinuedFraction.PrefixGrowth

/-! Closed-cover construction specialized to the two actual Berstein Cantor
sets. This module supplies the compactness, nesting and approximation fields;
the graph replay supplies interval coverage and scale balance. -/
namespace Berstein.CylinderCover
open HallRay.ContinuedFraction Forbidden31313 ActualCylinders

structure LegalPair where
  leftExtension : Word
  rightExtension : Word
  leftDigits : ∀ a ∈ leftExtension, a.val ≤ 3
  rightDigits : ∀ a ∈ rightExtension, a.val ≤ 3
  leftState : State
  rightState : State
  leftLegal : afterWord 0 (prefix322 ++ leftExtension) = some leftState
  rightLegal : afterWord 0 (prefix431 ++ rightExtension) = some rightState
  leftAnchor : ℝ
  rightAnchor : ℝ
  leftAnchor_mem : leftAnchor ∈ Set.Icc (0 : ℝ) 1
  rightAnchor_mem : rightAnchor ∈ Set.Icc (0 : ℝ) 1

abbrev LegalPair.leftWord (s : LegalPair) : Word := prefix322 ++ s.leftExtension
abbrev LegalPair.rightWord (s : LegalPair) : Word := prefix431 ++ s.rightExtension

def space (s : LegalPair) : Set (Stream × Stream) :=
  cylinder prefix322 s.leftWord ×ˢ cylinder prefix431 s.rightWord

noncomputable def totalValue (u : Stream × Stream) : ℝ := 4 + value 0 u.1 + value 0 u.2

noncomputable def lowerValue (w : Word) (s : State) : ℝ :=
  min (tailMap w (exactLower s)) (tailMap w (exactUpper s))
noncomputable def upperValue (w : Word) (s : State) : ℝ :=
  max (tailMap w (exactLower s)) (tailMap w (exactUpper s))
noncomputable def sumHull (s : LegalPair) : Set ℝ :=
  Set.Icc (4 + lowerValue s.leftWord s.leftState + lowerValue s.rightWord s.rightState)
    (4 + upperValue s.leftWord s.leftState + upperValue s.rightWord s.rightState)
noncomputable def error (s : LegalPair) : ℝ :=
  4 * (Normalization.scale s.leftWord s.leftAnchor +
    Normalization.scale s.rightWord s.rightAnchor)

theorem space_nonempty (s : LegalPair) : (space s).Nonempty :=
  Set.Nonempty.prod (nonempty _ _ s.leftDigits (by rw [s.leftLegal]; simp))
    (nonempty _ _ s.rightDigits (by rw [s.rightLegal]; simp))

theorem space_compact (s : LegalPair) : IsCompact (space s) := by
  apply IsCompact.prod (compact _ _ 4 (by decide) ?_) (compact _ _ 4 (by decide) ?_)
  · intro a ha
    simp [prefix322] at ha
    rcases ha with rfl | rfl <;> decide
  · intro a ha
    simp [prefix431] at ha
    rcases ha with rfl | rfl | rfl <;> decide

theorem space_closed (s : LegalPair) : IsClosed (space s) :=
  (closed _ _).prod (closed _ _)

def Extends (s t : LegalPair) : Prop :=
  ∃ l r : Word, t.leftExtension = s.leftExtension ++ l ∧
    t.rightExtension = s.rightExtension ++ r ∧ 0 < l.length + r.length

theorem space_nested {s t : LegalPair} (h : Extends s t) : space t ⊆ space s := by
  obtain ⟨l,r,hl,hr,_⟩ := h
  intro u hu
  have hleft : t.leftWord = s.leftWord ++ l := by simp only [LegalPair.leftWord, hl, List.append_assoc]
  have hright : t.rightWord = s.rightWord ++ r := by simp only [LegalPair.rightWord, hr, List.append_assoc]
  exact ⟨nested _ _ l (hleft ▸ hu.1), nested _ _ r (hright ▸ hu.2)⟩

theorem hull_width (w : Word) (s : State) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    upperValue w s - lowerValue w s ≤ 4 * Normalization.scale w a := by
  have hb := exactBounds_unit s
  have h := tailMap_width_le_four_scale w ha
    ⟨hb.1,hb.2.1.trans hb.2.2⟩ ⟨hb.1.trans hb.2.1,hb.2.2⟩
  simpa only [upperValue, lowerValue, max_sub_min_eq_abs, abs_sub_comm] using h

theorem approximation (s : LegalPair) {t : ℝ} (ht : t ∈ sumHull s)
    {u : Stream × Stream} (hu : u ∈ space s) : |totalValue u-t| ≤ error s := by
  have hl := value_mem_hull (by simp [LegalPair.leftWord]) hu.1 s.leftLegal
  have hr := value_mem_hull (by simp [LegalPair.rightWord]) hu.2 s.rightLegal
  have hl' : value 0 u.1 ∈ Set.Icc (lowerValue s.leftWord s.leftState)
      (upperValue s.leftWord s.leftState) := hl
  have hr' : value 0 u.2 ∈ Set.Icc (lowerValue s.rightWord s.rightState)
      (upperValue s.rightWord s.rightState) := hr
  have ht' : t-4 ∈ Set.Icc
      (lowerValue s.leftWord s.leftState + lowerValue s.rightWord s.rightState)
      (upperValue s.leftWord s.leftState + upperValue s.rightWord s.rightState) := by
    constructor <;> linarith [ht.1,ht.2]
  have h := sum_hull_error_bound hl' hr' ht'
  have hleft := hull_width s.leftWord s.leftState s.leftAnchor_mem
  have hright := hull_width s.rightWord s.rightState s.rightAnchor_mem
  have heq : totalValue u-t = (value 0 u.1+value 0 u.2)-(t-4) := by unfold totalValue; ring
  rw [heq]
  unfold error
  linarith

theorem realizes_mem_sum {s : LegalPair} {u : Stream × Stream} (hu : u ∈ space s) :
    ∃ x ∈ admissibleTailSet prefix322, ∃ y ∈ admissibleTailSet prefix431,
      totalValue u = 4+x+y :=
  ⟨value 0 u.1, ⟨u.1,hu.1.1,rfl⟩, value 0 u.2, ⟨u.2,hu.2.1,rfl⟩, rfl⟩

noncomputable def denominator (w : Word) (a : ℝ) : ℝ :=
  (mobiusCoeffs w).C + (mobiusCoeffs w).D * a

theorem denominator_pos (w : Word) {a : ℝ} (ha : 0 ≤ a) : 0 < denominator w a := by
  have hc : (0 : ℝ) < (mobiusCoeffs w).C := by exact_mod_cast mobius_C_pos w
  have hd : (0 : ℝ) ≤ (mobiusCoeffs w).D := by positivity
  dsimp [denominator]
  positivity

theorem denominator_ge_C (w : Word) {a : ℝ} (ha : 0 ≤ a) :
    ((mobiusCoeffs w).C : ℝ) ≤ denominator w a := by
  have hd : (0 : ℝ) ≤ (mobiusCoeffs w).D := by positivity
  dsimp [denominator]
  nlinarith

theorem path_denominators_grow (path : ℕ → LegalPair)
    (hnext : ∀ n, Extends (path n) (path (n+1))) :
    Filter.Tendsto (fun n => denominator (path n).leftWord (path n).leftAnchor +
      denominator (path n).rightWord (path n).rightAnchor) Filter.atTop Filter.atTop := by
  have hstep (n : ℕ) :
      (mobiusCoeffs (path n).leftWord).C + (mobiusCoeffs (path n).rightWord).C + 1 ≤
      (mobiusCoeffs (path (n+1)).leftWord).C + (mobiusCoeffs (path (n+1)).rightWord).C := by
    obtain ⟨l,r,hl,hr,hproper⟩ := hnext n
    have hleft : (path (n+1)).leftWord = (path n).leftWord ++ l := by
      simp only [LegalPair.leftWord, hl, List.append_assoc]
    have hright : (path (n+1)).rightWord = (path n).rightWord ++ r := by
      simp only [LegalPair.rightWord, hr, List.append_assoc]
    rw [hleft,hright]
    apply mobius_C_pair_append_step
    · simp [LegalPair.leftWord,prefix322]
    · simp [LegalPair.rightWord,prefix431]
    · by_contra h
      push_neg at h
      rcases h with ⟨rfl,rfl⟩
      simp at hproper
  have hn (n : ℕ) : n ≤ (mobiusCoeffs (path n).leftWord).C +
      (mobiusCoeffs (path n).rightWord).C := by
    induction n with
    | zero => omega
    | succ n ih => have h := hstep n; omega
  apply Filter.tendsto_atTop.mpr
  intro b
  obtain ⟨N,hN⟩ := exists_nat_ge b
  filter_upwards [Filter.eventually_ge_atTop N] with n hNn
  have hnc : (n : ℝ) ≤ (mobiusCoeffs (path n).leftWord).C +
      (mobiusCoeffs (path n).rightWord).C := by exact_mod_cast hn n
  have hNn' : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hl := denominator_ge_C (path n).leftWord (path n).leftAnchor_mem.1
  have hr := denominator_ge_C (path n).rightWord (path n).rightAnchor_mem.1
  linarith

/-- Construct all analytic fields of the closed-cover argument from actual
legal prefixes, strict extension, and the graph's fixed scale-ratio range. -/
noncomputable def closedCover {Index : Type*} (pairs : Index → LegalPair)
    (target : Index → Set ℝ) (next : Index → Index → Prop)
    (htarget : ∀ i, target i ⊆ sumHull (pairs i))
    (hextends : ∀ i j, next i j → Extends (pairs i) (pairs j))
    (hcovers : ∀ i t, t ∈ target i → ∃ j, next i j ∧ t ∈ target j)
    (K : ℝ) (hK : 0 < K)
    (hbalance : ∀ i, 1/K^2 ≤
      (denominator (pairs i).leftWord (pairs i).leftAnchor)^2 /
        (denominator (pairs i).rightWord (pairs i).rightAnchor)^2 ∧
      (denominator (pairs i).leftWord (pairs i).leftAnchor)^2 /
        (denominator (pairs i).rightWord (pairs i).rightAnchor)^2 ≤ K^2) :
    ClosedCoverSystem Index (Stream × Stream) where
  cylinder i := space (pairs i)
  target := target
  next := next
  value := totalValue
  error i := error (pairs i)
  nonempty i := space_nonempty (pairs i)
  compact i := space_compact (pairs i)
  closed i := space_closed (pairs i)
  nested h := space_nested (hextends _ _ h)
  covers := hcovers
  error_bound i t ht u hu := approximation (pairs i) (htarget i ht) hu
  shrinks path hpath ε hε := by
    obtain ⟨n,hn⟩ := paired_scales_shrink
      (fun n => denominator (pairs (path n)).leftWord (pairs (path n)).leftAnchor)
      (fun n => denominator (pairs (path n)).rightWord (pairs (path n)).rightAnchor) K
      (fun n => denominator_pos _ (pairs (path n)).leftAnchor_mem.1)
      (fun n => denominator_pos _ (pairs (path n)).rightAnchor_mem.1) hK
      (fun n => (hbalance (path n)).1) (fun n => (hbalance (path n)).2)
      (path_denominators_grow (fun n => pairs (path n))
        (fun n => hextends _ _ (hpath n))) hε
    exact ⟨n,hn⟩

end Berstein.CylinderCover
