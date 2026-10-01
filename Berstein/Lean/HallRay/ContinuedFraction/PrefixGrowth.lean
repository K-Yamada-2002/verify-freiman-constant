import HallRay.ContinuedFraction.Mobius

/-!
# Growth of continued-fraction continuants under extension

Appending a word composes the associated Möbius matrices.  The lower-left
coefficient therefore cannot decrease, and it increases strictly when both
the old prefix and the extension are nonempty.
-/

namespace HallRay
namespace ContinuedFraction

private theorem mobiusCoeffs_ext {x y : MobiusCoeffs}
    (hA : x.A = y.A) (hB : x.B = y.B)
    (hC : x.C = y.C) (hD : x.D = y.D) : x = y := by
  cases x with
  | mk A B C D =>
      cases y with
      | mk A' B' C' D' => simp_all

theorem mobiusCoeffs_append (u v : Word) :
    mobiusCoeffs (u ++ v) =
      ⟨(mobiusCoeffs u).A * (mobiusCoeffs v).C +
          (mobiusCoeffs u).B * (mobiusCoeffs v).A,
        (mobiusCoeffs u).A * (mobiusCoeffs v).D +
          (mobiusCoeffs u).B * (mobiusCoeffs v).B,
        (mobiusCoeffs u).C * (mobiusCoeffs v).C +
          (mobiusCoeffs u).D * (mobiusCoeffs v).A,
        (mobiusCoeffs u).C * (mobiusCoeffs v).D +
          (mobiusCoeffs u).D * (mobiusCoeffs v).B⟩ := by
  induction u with
  | nil => simp [mobiusCoeffs]
  | cons a u ih =>
      apply mobiusCoeffs_ext
      · simp [List.cons_append, mobiusCoeffs, ih]
      · simp [List.cons_append, mobiusCoeffs, ih]
      · simp only [List.cons_append, mobiusCoeffs, ih]
        ring
      · simp only [List.cons_append, mobiusCoeffs, ih]
        ring

theorem mobius_A_pos_of_nonempty {w : Word} (hw : w ≠ []) :
    0 < (mobiusCoeffs w).A := by
  cases w with
  | nil => contradiction
  | cons a w =>
      simp only [mobiusCoeffs]
      exact mobius_C_pos w

theorem mobius_D_pos_of_nonempty {w : Word} (hw : w ≠ []) :
    0 < (mobiusCoeffs w).D := by
  induction w with
  | nil => contradiction
  | cons a w ih =>
      cases w with
      | nil => simp [mobiusCoeffs]
      | cons b w =>
          simp only [mobiusCoeffs]
          have htail : (b :: w : Word) ≠ [] := by simp
          have hD := ih htail
          have ha : 0 < a.1 := a.property
          exact Nat.lt_of_lt_of_le (Nat.mul_pos ha hD) (Nat.le_add_right _ _)

theorem mobius_C_append_mono (u v : Word) :
    (mobiusCoeffs u).C ≤ (mobiusCoeffs (u ++ v)).C := by
  rw [mobiusCoeffs_append]
  have hC : 1 ≤ (mobiusCoeffs v).C := mobius_C_pos v
  have hprod : (mobiusCoeffs u).C ≤
      (mobiusCoeffs u).C * (mobiusCoeffs v).C := by
    simpa using Nat.mul_le_mul_left (mobiusCoeffs u).C hC
  exact Nat.le_trans hprod (Nat.le_add_right _ _)

theorem mobius_C_append_strict {u v : Word}
    (hu : u ≠ []) (hv : v ≠ []) :
    (mobiusCoeffs u).C + 1 ≤ (mobiusCoeffs (u ++ v)).C := by
  rw [mobiusCoeffs_append]
  have hCv : 1 ≤ (mobiusCoeffs v).C := mobius_C_pos v
  have hDu : 1 ≤ (mobiusCoeffs u).D := mobius_D_pos_of_nonempty hu
  have hAv : 1 ≤ (mobiusCoeffs v).A := mobius_A_pos_of_nonempty hv
  have hprod : (mobiusCoeffs u).C ≤
      (mobiusCoeffs u).C * (mobiusCoeffs v).C := by
    simpa using Nat.mul_le_mul_left (mobiusCoeffs u).C hCv
  have hcross : 1 ≤ (mobiusCoeffs u).D * (mobiusCoeffs v).A := by
    simpa using Nat.mul_le_mul hDu hAv
  exact Nat.add_le_add hprod hcross

theorem mobius_D_pos {w : Word} (hw : w ≠ []) :
    0 < (mobiusCoeffs w).D := mobius_D_pos_of_nonempty hw

theorem mobius_C_pair_append_step {u u' v v' : Word}
    (hu : u ≠ []) (hu' : u' ≠ [])
    (hext : v ≠ [] ∨ v' ≠ []) :
    (mobiusCoeffs u).C + (mobiusCoeffs u').C + 1 ≤
      (mobiusCoeffs (u ++ v)).C + (mobiusCoeffs (u' ++ v')).C := by
  have hmono := mobius_C_append_mono u v
  have hmono' := mobius_C_append_mono u' v'
  rcases hext with hv | hv'
  · have hstrict := mobius_C_append_strict hu hv
    omega
  · have hstrict := mobius_C_append_strict hu' hv'
    omega

end ContinuedFraction
end HallRay
