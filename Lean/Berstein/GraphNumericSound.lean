import Berstein.GraphCertificate
import Berstein.Normalization

namespace Berstein.GraphCertificate
open HallRay.ContinuedFraction

theorem hull_left (a b : QBounds) {x : ℝ} (hx : a.mem x) : (hull a b).mem x := by
  exact ⟨(by simpa [hull] using (min_le_left (a.lo : ℝ) b.lo).trans hx.1),
    (by simpa [hull] using hx.2.trans (le_max_left (a.hi : ℝ) b.hi))⟩

theorem hull_right (a b : QBounds) {x : ℝ} (hx : b.mem x) : (hull a b).mem x := by
  exact ⟨(by simpa [hull] using (min_le_right (a.lo : ℝ) b.lo).trans hx.1),
    (by simpa [hull] using hx.2.trans (le_max_right (a.hi : ℝ) b.hi))⟩

theorem ratioCorner_sound (r : ℚ) (anchor tail out : QBounds) {a x : ℝ}
    (ha : anchor.mem a) (hx : tail.mem x) (h : ratioCorner r anchor tail = some out) :
    out.mem (Normalization.ratio r a x) := by
  exact QBounds.checkedDiv_sound _ _ out _ _
    (QBounds.add_sound _ _ _ _ (by simpa using QBounds.point_sound 1)
      (QBounds.mul_sound _ _ _ _ (QBounds.point_sound r) ha))
    (QBounds.add_sound _ _ _ _ (by simpa using QBounds.point_sound 1)
      (QBounds.mul_sound _ _ _ _ (QBounds.point_sound r) hx)) h

theorem ratioBounds_sound (shape anchor tail out : QBounds) {r a x : ℝ}
    (hs : shape.mem r) (hs0 : 0 ≤ shape.lo) (ha : anchor.mem a)
    (hx : tail.mem x) (hx0 : 0 ≤ x) (h : ratioBounds shape anchor tail = some out) :
    out.mem (Normalization.ratio r a x) := by
  cases hl : ratioCorner shape.lo anchor tail with
  | none => simp [ratioBounds, hl] at h
  | some bl =>
      cases hh : ratioCorner shape.hi anchor tail with
      | none => simp [ratioBounds, hl, hh] at h
      | some bh =>
          have he : hull bl bh = out := by simpa [ratioBounds, hl, hh] using h
          rw [← he]
          exact Normalization.ratio_enclosure (by exact_mod_cast hs0) hs hx0 _
            (hull_left _ _ (ratioCorner_sound _ _ _ _ ha hx hl))
            (hull_right _ _ (ratioCorner_sound _ _ _ _ ha hx hh))

/-- Soundness for the cached numerical differences of an actual CF prefix.
Every cache entry is checked by `checkPrepared`; endpoint identities and
enclosures are separate semantic-input facts. -/
theorem checkPrepared_actual_differences (side : Side) (w : Word) (raw : Nat → ℝ)
    (hcheck : checkPrepared side = true)
    (hanchor : side.anchor < side.tails.size)
    (hshape : side.shape.mem (denominatorRatio w)) (hshape0 : 0 ≤ side.shape.lo)
    (htails : ∀ i < side.tails.size, (side.tails[i]?.getD default).mem (raw i))
    (hnonneg : ∀ i < side.tails.size, 0 ≤ raw i)
    (hparity : (-1 : ℝ)^w.length = if side.parity then -1 else 1) :
    ∀ i < side.tails.size, ∀ j < side.tails.size,
      (side.delta i j).mem
        (tailMap w (raw i)/Normalization.scale w (raw side.anchor) -
         tailMap w (raw j)/Normalization.scale w (raw side.anchor)) := by
  obtain ⟨_, hr, hd⟩ := checkPrepared_sound side hcheck
  have hrat : ∀ i < side.tails.size, (side.ratios[i]?.getD default).mem
      (Normalization.ratio (denominatorRatio w) (raw side.anchor) (raw i)) := by
    intro i hi
    have hri := hr i hi
    by_cases he : i = side.anchor
    · rw [if_pos he] at hri
      rw [← Option.some.inj hri, he,
        Normalization.ratio_self (denominatorRatio_mem_Icc w).1 (hnonneg _ hanchor)]
      simpa using QBounds.point_sound 1
    · rw [if_neg he] at hri
      exact ratioBounds_sound _ _ _ _ hshape hshape0 (htails _ hanchor)
        (htails i hi) (hnonneg i hi) hri
  intro i hi j hj
  rw [hd i hi j hj]
  have heq : tailMap w (raw i)/Normalization.scale w (raw side.anchor) -
      tailMap w (raw j)/Normalization.scale w (raw side.anchor) =
      (tailMap w (raw i)-tailMap w (raw j))/Normalization.scale w (raw side.anchor) := by ring
  rw [heq, Normalization.normalized_difference w (hnonneg _ hanchor)
    (hnonneg i hi) (hnonneg j hj), hparity]
  by_cases hij : i = j
  · subst j
    simp [deltaBounds, QBounds.point, QBounds.mem]
  · have hdif := Normalization.unsigned_difference_enclosure _ _ _ _
        (htails i hi) (htails j hj) (hrat i hi) (hrat j hj)
    cases hp : side.parity
    · simpa [deltaBounds, hij, hp] using hdif
    · convert QBounds.neg_sound _ _ hdif using 1 <;>
        simp [deltaBounds, hij, hp] <;> ring

end Berstein.GraphCertificate
