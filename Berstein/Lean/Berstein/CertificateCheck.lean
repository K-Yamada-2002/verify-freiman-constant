import Berstein.RootCheck
import Berstein.GraphCertificateFacts

/-! The entire finite acceptance condition. IO and certificate generation
are outside this predicate; all mathematics is conditional only on these
executable checks, never on an assumed Cantor-sum or spectral inclusion. -/

namespace Berstein.Certificate
open GraphCertificate

def check (input : Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (cells : Nat → List Cell) : Bool :=
  GraphMeaning.check input data && GraphMeaning.checkRoots input data alive &&
    input.sides.all checkPrepared &&
    (List.range (input.states*input.states)).all
      (fun geometry => checkGeometry input alive geometry (cells geometry))

structure Accepted (input : Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (cells : Nat → List Cell) : Prop where
  meaning : GraphMeaning.check input data = true
  roots : GraphMeaning.checkRoots input data alive = true
  prepared : ∀ side ∈ input.sides, checkPrepared side = true
  geometries : ∀ geometry < input.states*input.states,
    checkGeometry input alive geometry (cells geometry) = true

theorem check_sound (input : Input) (data : GraphMeaning.Data) (alive : ByteArray)
    (cells : Nat → List Cell) (h : check input data alive cells = true) :
    Accepted input data alive cells := by
  simp only [check, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1,h.1.1.2,h.1.2,h.2⟩

end Berstein.Certificate
