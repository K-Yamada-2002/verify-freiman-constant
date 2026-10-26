import HallRay.Basic

/-!
# Continued fractions

Basic continued-fraction API needed throughout the project.

Planned contents:

* finite continued fractions attached to words of positive integers;
* values of infinite continued fractions;
* convergents and their denominator growth;
* convergence for a common prefix and bounds on cylinder diameters.
-/

namespace HallRay
namespace ContinuedFraction

open scoped Topology

/-- A positive integer, used as a partial quotient. -/
abbrev PartialQuotient := {n : ℕ // 0 < n}

/-- A finite word of positive partial quotients. -/
abbrev Word := List PartialQuotient

/-- Apply a finite word of partial quotients to a fractional tail `x`. -/
noncomputable def tailMap (digits : Word) (x : ℝ) : ℝ :=
  digits.foldr (fun a y ↦ 1 / ((a.1 : ℝ) + y)) x

/--
Evaluate the fractional tail

`1 / (a₁ + 1 / (a₂ + ... + 1 / aₙ))`.
-/
noncomputable def finiteTail (digits : Word) : ℝ :=
  tailMap digits 0

/-- The finite continued fraction `[head; digits]`. -/
noncomputable def finiteValue (head : ℝ) (digits : Word) : ℝ :=
  head + finiteTail digits

/-- The convergent obtained from the first `n` partial quotients of `digits`. -/
noncomputable def convergent (head : ℝ) (digits : ℕ → PartialQuotient) (n : ℕ) : ℝ :=
  finiteValue head ((List.range n).map digits)

/--
The value `[head; digits 0, digits 1, ...]` of an infinite continued fraction.

Convergence for positive partial quotients will be proved separately.  Using
`Filter.limUnder` gives a total definition while agreeing with the usual
limit whenever the convergents tend to one.
-/
noncomputable def value (head : ℝ) (digits : ℕ → PartialQuotient) : ℝ :=
  Filter.limUnder Filter.atTop (convergent head digits)

@[simp]
theorem tailMap_nil (x : ℝ) : tailMap [] x = x := rfl

@[simp]
theorem tailMap_cons (a : PartialQuotient) (w : Word) (x : ℝ) :
    tailMap (a :: w) x = 1 / ((a.1 : ℝ) + tailMap w x) := rfl

theorem one_le_partialQuotient (a : PartialQuotient) : (1 : ℝ) ≤ a.1 := by
  exact_mod_cast (Nat.succ_le_iff.mpr a.property)

/-- A positive partial quotient sends the unit interval into itself. -/
theorem tailStep_mem_Icc (a : PartialQuotient) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    1 / ((a.1 : ℝ) + x) ∈ Set.Icc (0 : ℝ) 1 := by
  have hden : 1 ≤ (a.1 : ℝ) + x := by
    simpa using add_le_add (one_le_partialQuotient a) hx.1
  constructor
  · positivity
  · exact (div_le_iff₀ (by linarith)).2 (by linarith)

/-- Every finite continued-fraction tail maps the unit interval into itself. -/
theorem tailMap_mem_Icc (w : Word) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    tailMap w x ∈ Set.Icc (0 : ℝ) 1 := by
  induction w generalizing x with
  | nil => simpa
  | cons a w ih =>
      rw [tailMap_cons]
      exact tailStep_mem_Icc a (ih hx)

/-- A finite continued-fraction prefix is continuous on the unit tail interval. -/
theorem continuousOn_tailMap_Icc (w : Word) :
    ContinuousOn (tailMap w) (Set.Icc (0 : ℝ) 1) := by
  induction w with
  | nil => exact continuousOn_id
  | cons a w ih =>
      have hden :
          ∀ x ∈ Set.Icc (0 : ℝ) 1, (a.1 : ℝ) + tailMap w x ≠ 0 := by
        intro x hx
        have htail := (tailMap_mem_Icc w hx).1
        have ha := one_le_partialQuotient a
        linarith
      change ContinuousOn
        (fun x ↦ 1 / ((a.1 : ℝ) + tailMap w x)) (Set.Icc (0 : ℝ) 1)
      exact continuousOn_const.div (continuousOn_const.add ih) hden

/-- A finite prefix is injective when its tail is restricted to the unit interval. -/
theorem injOn_tailMap_Icc (w : Word) :
    Set.InjOn (tailMap w) (Set.Icc (0 : ℝ) 1) := by
  induction w with
  | nil =>
      intro x _ y _ h
      simpa using h
  | cons a w ih =>
      intro x hx y hy h
      rw [tailMap_cons, tailMap_cons] at h
      have h' :
          (a.1 : ℝ) + tailMap w x = (a.1 : ℝ) + tailMap w y := by
        apply inv_injective
        simpa only [one_div] using h
      apply ih hx hy
      linarith

/-- A finite prefix sends a subinterval of the unit tail interval between
the images of its endpoints (with either possible orientation). -/
theorem tailMap_mem_uIcc {w : Word} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hx : x ∈ Set.Icc a b) :
    tailMap w x ∈ Set.uIcc (tailMap w a) (tailMap w b) := by
  have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 :=
    fun _ hy ↦ ⟨ha.trans hy.1, hy.2.trans hb⟩
  have hcont := (continuousOn_tailMap_Icc w).mono hsub
  have hinj := (injOn_tailMap_Icc w).mono hsub
  have hma := hcont.strictMonoOn_of_injOn_Icc' hab hinj
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  rcases hma with hm | ha'
  · exact Set.mem_uIcc_of_le
      (hm.monotoneOn ha_mem hx hx.1)
      (hm.monotoneOn hx hb_mem hx.2)
  · exact Set.mem_uIcc_of_ge
      (ha'.antitoneOn hx hb_mem hx.2)
      (ha'.antitoneOn ha_mem hx hx.1)

/-- Exact difference formula for one continued-fraction step. -/
theorem abs_tailStep_sub_tailStep (a : PartialQuotient) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |1 / ((a.1 : ℝ) + x) - 1 / ((a.1 : ℝ) + y)| =
      |x - y| / (((a.1 : ℝ) + x) * ((a.1 : ℝ) + y)) := by
  have hax : (0 : ℝ) < (a.1 : ℝ) + x := by
    linarith [one_le_partialQuotient a]
  have hay : (0 : ℝ) < (a.1 : ℝ) + y := by
    linarith [one_le_partialQuotient a]
  rw [one_div, one_div, inv_sub_inv (ne_of_gt hax) (ne_of_gt hay),
    abs_div, abs_mul, abs_of_pos hax, abs_of_pos hay]
  rw [show (a.1 : ℝ) + y - ((a.1 : ℝ) + x) = y - x by ring, abs_sub_comm]

/-- One continued-fraction step is nonexpanding on the unit interval. -/
theorem abs_tailStep_sub_le (a : PartialQuotient) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |1 / ((a.1 : ℝ) + x) - 1 / ((a.1 : ℝ) + y)| ≤ |x - y| := by
  rw [abs_tailStep_sub_tailStep a hx.1 hy.1]
  have h₁ : 1 ≤ (a.1 : ℝ) + x := by
    simpa using add_le_add (one_le_partialQuotient a) hx.1
  have h₂ : 1 ≤ (a.1 : ℝ) + y := by
    simpa using add_le_add (one_le_partialQuotient a) hy.1
  exact div_le_self (abs_nonneg _) (by nlinarith)

/-- Two continued-fraction steps contract distances by a factor at most `1/4`.
This elementary uniform estimate is enough to prove convergence without
developing the full classical theory of continuants first. -/
theorem abs_two_tailSteps_sub_le (a b : PartialQuotient) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |1 / ((a.1 : ℝ) + 1 / ((b.1 : ℝ) + x)) -
        1 / ((a.1 : ℝ) + 1 / ((b.1 : ℝ) + y))| ≤
      |x - y| / 4 := by
  let Bx : ℝ := (b.1 : ℝ) + x
  let By : ℝ := (b.1 : ℝ) + y
  let fx : ℝ := 1 / Bx
  let fy : ℝ := 1 / By
  have hBx : 1 ≤ Bx := by
    dsimp [Bx]
    simpa using add_le_add (one_le_partialQuotient b) hx.1
  have hBy : 1 ≤ By := by
    dsimp [By]
    simpa using add_le_add (one_le_partialQuotient b) hy.1
  have hfx : fx ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [fx, Bx]
    exact tailStep_mem_Icc b hx
  have hfy : fy ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [fy, By]
    exact tailStep_mem_Icc b hy
  let Ax : ℝ := (a.1 : ℝ) + fx
  let Ay : ℝ := (a.1 : ℝ) + fy
  have hAx : 1 ≤ Ax := by
    dsimp [Ax]
    simpa using add_le_add (one_le_partialQuotient a) hfx.1
  have hAy : 1 ≤ Ay := by
    dsimp [Ay]
    simpa using add_le_add (one_le_partialQuotient a) hfy.1
  have hpairx : 2 ≤ Bx * Ax := by
    have hBx0 : Bx ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hBx)
    have heq : Bx * Ax = Bx * (a.1 : ℝ) + 1 := by
      dsimp [Ax, fx]
      field_simp
    rw [heq]
    nlinarith [one_le_partialQuotient a]
  have hpairy : 2 ≤ By * Ay := by
    have hBy0 : By ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hBy)
    have heq : By * Ay = By * (a.1 : ℝ) + 1 := by
      dsimp [Ay, fy]
      field_simp
    rw [heq]
    nlinarith [one_le_partialQuotient a]
  have hden : 4 ≤ (Bx * By) * (Ax * Ay) := by
    calc
      4 ≤ (Bx * Ax) * (By * Ay) := by nlinarith
      _ = (Bx * By) * (Ax * Ay) := by ring
  change |1 / Ax - 1 / Ay| ≤ |x - y| / 4
  rw [abs_tailStep_sub_tailStep a hfx.1 hfy.1]
  change |fx - fy| / (Ax * Ay) ≤ |x - y| / 4
  rw [show |fx - fy| = |x - y| / (Bx * By) by
    dsimp [fx, fy, Bx, By]
    exact abs_tailStep_sub_tailStep b hx.1 hy.1]
  rw [div_div]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hden

theorem tailMap_append (u v : Word) (x : ℝ) :
    tailMap (u ++ v) x = tailMap u (tailMap v x) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      simp only [List.cons_append, tailMap_cons, ih]

/--
A word of length `n` contracts the unit interval to diameter at most
`4 ^ (-⌊n/2⌋)`.  This is the cylinder-diameter estimate used in both the
Cantor construction and the block-sequence argument.
-/
theorem abs_tailMap_sub_le (w : Word) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |tailMap w x - tailMap w y| ≤ |x - y| / 4 ^ (w.length / 2) := by
  induction w using List.twoStepInduction generalizing x y with
  | nil => simp
  | singleton a =>
      simpa using abs_tailStep_sub_le a hx hy
  | cons_cons a b w ih =>
      have htx := tailMap_mem_Icc w hx
      have hty := tailMap_mem_Icc w hy
      calc
        |tailMap (a :: b :: w) x - tailMap (a :: b :: w) y| ≤
            |tailMap w x - tailMap w y| / 4 := by
              simpa only [tailMap_cons] using abs_two_tailSteps_sub_le a b htx hty
        _ ≤ (|x - y| / 4 ^ (w.length / 2)) / 4 :=
          div_le_div_of_nonneg_right (ih hx hy) (by norm_num)
        _ = |x - y| / 4 ^ ((a :: b :: w).length / 2) := by
          have hlen : (a :: b :: w).length / 2 = w.length / 2 + 1 := by
            simp only [List.length_cons]
            omega
          rw [hlen, pow_succ]
          ring

/-- A convenient tail-insensitive version of the cylinder estimate. -/
theorem abs_tailMap_le_cylinder (w : Word) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |tailMap w x - tailMap w y| ≤ 1 / 4 ^ (w.length / 2) := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  refine (abs_tailMap_sub_le w ⟨hx0, hx1⟩ ⟨hy0, hy1⟩).trans ?_
  gcongr
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- The finite convergents of every positive-integer continued fraction form
a Cauchy sequence. -/
theorem cauchySeq_convergent (head : ℝ) (digits : ℕ → PartialQuotient) :
    CauchySeq (convergent head digits) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hpow : Filter.Tendsto (fun k : ℕ ↦ ((1 / 4 : ℝ) ^ k)) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hev : ∀ᶠ k : ℕ in Filter.atTop, (1 / 4 : ℝ) ^ k < ε :=
    hpow.eventually (Iio_mem_nhds hε)
  rcases Filter.eventually_atTop.1 hev with ⟨k, hk⟩
  refine ⟨2 * k, fun m hm ↦ ?_⟩
  have hrange : List.range m = List.range (2 * k) ++ List.Ico (2 * k) m := by
    rw [← List.Ico.zero_bot, ← List.Ico.append_consecutive (Nat.zero_le _) hm,
      List.Ico.zero_bot]
  have hsplit :
      (List.range m).map digits =
        (List.range (2 * k)).map digits ++ (List.Ico (2 * k) m).map digits := by
    rw [hrange, List.map_append]
  let w : Word := (List.range (2 * k)).map digits
  let t : Word := (List.Ico (2 * k) m).map digits
  have ht : tailMap t 0 ∈ Set.Icc (0 : ℝ) 1 :=
    tailMap_mem_Icc t (by norm_num)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hcyl :
      |tailMap w (tailMap t 0) - tailMap w 0| ≤
        1 / 4 ^ (w.length / 2) :=
    abs_tailMap_le_cylinder w ht h0
  have hwlen : w.length / 2 = k := by
    dsimp [w]
    simp
  have hbound : 1 / (4 : ℝ) ^ (w.length / 2) < ε := by
    rw [hwlen, ← one_div_pow]
    exact hk k le_rfl
  rw [convergent, convergent, finiteValue, finiteTail, hsplit, tailMap_append,
    Real.dist_eq]
  simpa [w, t, finiteValue, finiteTail] using hcyl.trans_lt hbound

/-- The declared infinite value is indeed the limit of the convergents. -/
theorem tendsto_convergent (head : ℝ) (digits : ℕ → PartialQuotient) :
    Filter.Tendsto (convergent head digits) Filter.atTop (𝓝 (value head digits)) := by
  exact (cauchySeq_convergent head digits).tendsto_limUnder

/-- A fractional infinite continued fraction with positive digits lies in
the closed unit interval. -/
theorem value_zero_mem_Icc (digits : ℕ → PartialQuotient) :
    value 0 digits ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply ge_of_tendsto' (tendsto_convergent 0 digits)
    intro n
    simpa [convergent, finiteValue, finiteTail] using
      (tailMap_mem_Icc ((List.range n).map digits) (by norm_num)).1
  · apply le_of_tendsto' (tendsto_convergent 0 digits)
    intro n
    simpa [convergent, finiteValue, finiteTail] using
      (tailMap_mem_Icc ((List.range n).map digits) (by norm_num)).2

/-- Separating off the real head agrees with the usual continued-fraction
notation `[a; …] = a + [0; …]`. -/
theorem value_eq_head_add (head : ℝ) (digits : ℕ → PartialQuotient) :
    value head digits = head + value 0 digits := by
  apply tendsto_nhds_unique (tendsto_convergent head digits)
  apply (tendsto_const_nhds.add (tendsto_convergent 0 digits)).congr'
  filter_upwards with n
  simp [convergent, finiteValue]

/--
Infinite continued fractions with the same first `n` digits differ by at
most the diameter of their common cylinder.
-/
theorem abs_value_zero_sub_le_of_common_prefix
    (digits₁ digits₂ : ℕ → PartialQuotient) (n : ℕ)
    (hpref : (List.range n).map digits₁ = (List.range n).map digits₂) :
    |value 0 digits₁ - value 0 digits₂| ≤ 1 / 4 ^ (n / 2) := by
  have htend :
      Filter.Tendsto
        (fun m ↦ |convergent 0 digits₁ m - convergent 0 digits₂ m|)
        Filter.atTop (𝓝 |value 0 digits₁ - value 0 digits₂|) :=
    ((tendsto_convergent 0 digits₁).sub (tendsto_convergent 0 digits₂)).abs
  apply le_of_tendsto htend
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  have hrange : List.range m = List.range n ++ List.Ico n m := by
    rw [← List.Ico.zero_bot, ← List.Ico.append_consecutive (Nat.zero_le _) hm,
      List.Ico.zero_bot]
  let w : Word := (List.range n).map digits₁
  let t₁ : Word := (List.Ico n m).map digits₁
  let t₂ : Word := (List.Ico n m).map digits₂
  have ht₁ : tailMap t₁ 0 ∈ Set.Icc (0 : ℝ) 1 :=
    tailMap_mem_Icc t₁ (by norm_num)
  have ht₂ : tailMap t₂ 0 ∈ Set.Icc (0 : ℝ) 1 :=
    tailMap_mem_Icc t₂ (by norm_num)
  have hcyl := abs_tailMap_le_cylinder w ht₁ ht₂
  have hwlen : w.length = n := by simp [w]
  simp only [convergent, finiteValue, finiteTail, hrange, List.map_append, tailMap_append]
  rw [← hpref]
  simpa [w, t₁, t₂, hwlen] using hcyl

/--
An infinite continued fraction is within the diameter of its length-`n`
cylinder of every point obtained by inserting an arbitrary unit-interval
tail after the same prefix.
-/
theorem abs_value_zero_sub_tailMap_prefix_le
    (digits : ℕ → PartialQuotient) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |value 0 digits - tailMap ((List.range n).map digits) t| ≤
      1 / 4 ^ (n / 2) := by
  let w : Word := (List.range n).map digits
  have htend :
      Filter.Tendsto
        (fun m ↦ |convergent 0 digits m - tailMap w t|)
        Filter.atTop (𝓝 |value 0 digits - tailMap w t|) :=
    (tendsto_convergent 0 digits).sub tendsto_const_nhds |>.abs
  apply le_of_tendsto htend
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  have hrange : List.range m = List.range n ++ List.Ico n m := by
    rw [← List.Ico.zero_bot, ← List.Ico.append_consecutive (Nat.zero_le _) hm,
      List.Ico.zero_bot]
  let suffix : Word := (List.Ico n m).map digits
  have hsuffix : tailMap suffix 0 ∈ Set.Icc (0 : ℝ) 1 :=
    tailMap_mem_Icc suffix (by norm_num)
  have hcyl := abs_tailMap_le_cylinder w hsuffix ht
  have hwlen : w.length = n := by simp [w]
  simp only [convergent, finiteValue, finiteTail, hrange, List.map_append,
    tailMap_append]
  simpa [w, suffix, hwlen] using hcyl

/--
Separating a finite prefix from an infinite continued fraction agrees with
applying `tailMap` to the value of the shifted infinite tail.
-/
theorem value_zero_eq_tailMap_prefix (digits : ℕ → PartialQuotient) (n : ℕ) :
    value 0 digits =
      tailMap ((List.range n).map digits)
        (value 0 (fun k ↦ digits (n + k))) := by
  let shifted : ℕ → PartialQuotient := fun k ↦ digits (n + k)
  let w : Word := (List.range n).map digits
  have htail_mem : value 0 shifted ∈ Set.Icc (0 : ℝ) 1 :=
    value_zero_mem_Icc shifted
  have hconv_mem :
      ∀ m, convergent 0 shifted m ∈ Set.Icc (0 : ℝ) 1 := by
    intro m
    simpa [convergent, finiteValue, finiteTail] using
      tailMap_mem_Icc ((List.range m).map shifted) (by norm_num)
  have htwithin :
      Filter.Tendsto (convergent 0 shifted) Filter.atTop
        (𝓝[Set.Icc (0 : ℝ) 1] (value 0 shifted)) :=
    tendsto_nhdsWithin_iff.2
      ⟨tendsto_convergent 0 shifted, Filter.Eventually.of_forall hconv_mem⟩
  have hright :
      Filter.Tendsto (fun m ↦ tailMap w (convergent 0 shifted m))
        Filter.atTop (𝓝 (tailMap w (value 0 shifted))) :=
    Filter.Tendsto.comp
      ((continuousOn_tailMap_Icc w) (value 0 shifted) htail_mem) htwithin
  have hadd : Filter.Tendsto (fun m : ℕ ↦ n + m) Filter.atTop Filter.atTop :=
    by simpa [Nat.add_comm] using Filter.tendsto_add_atTop_nat n
  have hleft :
      Filter.Tendsto (fun m ↦ convergent 0 digits (n + m))
        Filter.atTop (𝓝 (value 0 digits)) :=
    (tendsto_convergent 0 digits).comp hadd
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards with m
  have hrange :
      List.range (n + m) =
        List.range n ++ List.Ico n (n + m) := by
    rw [← List.Ico.zero_bot, ← List.Ico.append_consecutive (Nat.zero_le n)
      (Nat.le_add_right n m), List.Ico.zero_bot]
  have hsuffix :
      (List.Ico n (n + m)).map digits =
        (List.range m).map shifted := by
    rw [show List.Ico n (n + m) =
        (List.range m).map (n + ·) by
          rw [← List.Ico.zero_bot, List.Ico.map_add]
          simp [add_comm]]
    simp [shifted, Function.comp_def]
  simp [convergent, finiteValue, finiteTail, hrange, hsuffix,
    tailMap_append, w]

end ContinuedFraction
end HallRay
