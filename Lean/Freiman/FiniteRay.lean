import Freiman.RootCover
import Freiman.Spectral

/-! Finite initial-ray intervals, with separate checks of actual filling,
uniform noncentral domination, exact endpoints, and interval connectivity. -/
namespace Freiman.FiniteRay
open Berstein HallRay.ContinuedFraction

structure Row where
  root : Root.Row
  spectralIndex : Nat
  lower : Quadratic462
  upper : Quadratic462
  deriving Inhabited

def center (s : Spectral.Certificate) : Quadratic462 := Quadratic462.ofRat s.center.val

def Row.check (input : GraphCertificate.Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (spectra : Array Spectral.Certificate) (r : Row) : Bool :=
  (do
    let s ← spectra[r.spectralIndex]?
    return r.root.check input data alive &&
      decide (s.left = r.root.witness.left ∧ s.right = r.root.witness.right) &&
      Quadratic462.le s.bound r.lower &&
      Quadratic462.le (Quadratic462.add (center s) r.root.lower) r.lower &&
      Quadratic462.le r.upper (Quadratic462.add (center s) r.root.upper)).getD false

 theorem Row.mem_markov (input : GraphCertificate.Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell)
    (htable : Berstein.Certificate.Accepted input data alive cells)
    (spectra : Array Spectral.Certificate)
    (hs : ∀ s ∈ spectra, Spectral.check s = true) (r : Row)
    (hr : r.check input data alive spectra = true) {t : ℝ}
    (ht : t ∈ Set.Icc r.lower.eval r.upper.eval) : t ∈ markovSpectrum := by
  unfold Row.check at hr
  cases he : spectra[r.spectralIndex]? with
  | none => simp [he] at hr
  | some s =>
    simp only [he,Option.bind_eq_bind,Option.bind_some,Option.pure_def,Option.getD_some,
      Bool.and_eq_true,decide_eq_true_eq] at hr
    rcases hr with ⟨⟨⟨⟨hroot,hwords⟩,hb⟩,hl⟩,hu⟩
    have hbound := Spectral.check_sound s (hs s (Array.mem_of_getElem? he))
    rw [hwords.1,hwords.2] at hbound
    have hbound' := Quadratic462.le_sound _ _ hb
    have hlo := Quadratic462.le_sound _ _ hl
    have hhi := Quadratic462.le_sound _ _ hu
    simp only [Quadratic462.eval_add,center,Quadratic462.eval_ofRat,Rat.cast_natCast] at hlo hhi
    have hz : t-(s.center.val : ℝ) ∈ Set.Icc r.root.lower.eval r.root.upper.eval := by
      constructor <;> linarith [ht.1,ht.2]
    obtain ⟨x,⟨l,hal,hx⟩,y,⟨rr,har,hy⟩,hm⟩ := r.root.realizes input data alive cells htable hroot hz
    have hc : localValue (glueAt s.center l rr) 0 = t := by
      rw [localValue_glueAt_zero]
      rw [hx,hy] at hm
      linarith
    rw [← hc]
    apply mem_markovSpectrum_of_dominant
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · rw [hc]
      exact (hbound l rr hal har n hn).trans (hbound'.trans ht.1)

def check (input : GraphCertificate.Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (spectra : Array Spectral.Certificate) (lo hi : Quadratic462) (rows : List Row) : Bool :=
  spectra.all Spectral.check &&
    FiniteCover.check (fun r : Row => ⟨r.lower,r.upper⟩) Quadratic462.le
      (Row.check input data alive spectra) lo hi rows

/-- The finite-chain conclusion has only executable acceptance premises. -/
theorem check_sound (input : GraphCertificate.Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (cells : Nat → List GraphCertificate.Cell)
    (htable : Berstein.Certificate.Accepted input data alive cells)
    (spectra : Array Spectral.Certificate) (lo hi : Quadratic462) (rows : List Row)
    (hc : check input data alive spectra lo hi rows = true) :
    Set.Icc lo.eval hi.eval ⊆ markovSpectrum := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hs := Array.all_eq_true_iff_forall_mem.mp hh.1
  intro t ht
  obtain ⟨r,_,hr,hm⟩ := FiniteCover.check_sound (fun r : Row => ⟨r.lower,r.upper⟩)
    Quadratic462.le (Row.check input data alive spectra) Quadratic462.eval
    Quadratic462.le_sound lo hi rows hh.2 t ht
  exact r.mem_markov input data alive cells htable spectra hs hr hm

end Freiman.FiniteRay
