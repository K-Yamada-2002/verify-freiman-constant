import Berstein.SemanticCheck

/-! Global, data-independent consequences of a successful semantic check. -/

namespace Berstein.GraphMeaning

private theorem check_components (input : GraphCertificate.Input) (data : Data)
    (h : check input data = true) :
    input.states = input.sides.size ∧ input.states = data.sides.size ∧
    input.extensions = data.extensions.size ∧ input.grid.size = input.bins+1 ∧
    input.bands.size = input.types ∧
    data.extensions[0]? = some [] ∧
    data.extensions.all (fun w => w.all (fun d => decide (1 ≤ d ∧ d ≤ 3))) = true ∧
    input.pairs.all (fun p =>
      match data.extensions[p.left]?, data.extensions[p.right]? with
      | some a, some b => decide (0 < a.length+b.length)
      | _, _ => false) = true ∧
    input.bands.all (fun b => decide (0 ≤ b.lo ∧ b.lo ≤ b.hi ∧ b.hi ≤ 1)) = true ∧
    (List.range input.grid.size).all (fun k =>
      match input.grid[k]? with
      | none => false
      | some b =>
        let cut := (51/50 : ℚ)^(input.firstExponent+(k : Int))
        decide (b.lo ≤ cut ∧ cut ≤ b.hi ∧ 1/10000 ≤ cut ∧ cut ≤ 10000)) = true ∧
    (List.range input.states).all (checkSide input data) = true := by
  unfold check at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨hdim, hzero⟩, hdigits⟩, hpairs⟩, hbands⟩, hgrid⟩, hsides⟩
  have hdim' := of_decide_eq_true hdim
  have hzero' := of_decide_eq_true hzero
  refine ⟨hdim'.1, ?_⟩
  refine ⟨hdim'.2.1, ?_⟩
  refine ⟨hdim'.2.2.1, ?_⟩
  refine ⟨hdim'.2.2.2.1, ?_⟩
  refine ⟨hdim'.2.2.2.2, ?_⟩
  refine ⟨hzero', ?_⟩
  refine ⟨hdigits, ?_⟩
  refine ⟨hpairs, ?_⟩
  refine ⟨hbands, ?_⟩
  refine ⟨hgrid, ?_⟩
  exact hsides

theorem check_dimensions (input : GraphCertificate.Input) (data : Data)
    (h : check input data = true) :
    input.states = input.sides.size ∧ input.states = data.sides.size ∧
      input.extensions = data.extensions.size ∧ input.grid.size = input.bins+1 ∧
      input.bands.size = input.types :=
  let hc := check_components input data h
  ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1⟩

theorem check_extension_zero (input : GraphCertificate.Input) (data : Data)
    (h : check input data = true) : data.extensions[0]? = some [] := by
  exact (check_components input data h).2.2.2.2.2.1

theorem check_pair_extension (input : GraphCertificate.Input) (data : Data)
    (h : check input data = true) (p : GraphCertificate.Successor)
    (hp : p ∈ input.pairs) :
    ∃ a b, data.extensions[p.left]? = some a ∧
      data.extensions[p.right]? = some b ∧ 0 < a.length+b.length := by
  have hall := Array.all_eq_true_iff_forall_mem.mp
    (check_components input data h).2.2.2.2.2.2.2.1 p hp
  cases ha : data.extensions[p.left]? with
  | none => simp [ha] at hall
  | some a =>
    cases hb : data.extensions[p.right]? with
    | none => simp [ha, hb] at hall
    | some b =>
      rw [ha, hb] at hall
      exact ⟨a,b,rfl,rfl,of_decide_eq_true hall⟩

theorem check_band_unit (input : GraphCertificate.Input) (data : Data)
    (h : check input data = true) (i : Nat) (_hi : i < input.bands.size)
    (b : QBounds) (hb : input.bands[i]? = some b) :
    0 ≤ b.lo ∧ b.lo ≤ b.hi ∧ b.hi ≤ 1 := by
  have hall := Array.all_eq_true_iff_forall_mem.mp
    (check_components input data h).2.2.2.2.2.2.2.2.1 b (Array.mem_of_getElem? hb)
  simpa only [decide_eq_true_eq] using hall

theorem check_grid_cut (input : GraphCertificate.Input) (data : Data)
    (h : check input data = true) (k : Nat) (hk : k < input.grid.size)
    (b : QBounds) (hb : input.grid[k]? = some b) :
    let cut := (51/50 : ℚ)^(input.firstExponent+(k : Int))
    b.lo ≤ cut ∧ cut ≤ b.hi ∧ 1/10000 ≤ cut ∧ cut ≤ 10000 := by
  have hall := List.all_eq_true.mp (check_components input data h).2.2.2.2.2.2.2.2.2.1
    k (List.mem_range.mpr hk)
  simp only [hb] at hall
  simpa only [decide_eq_true_eq] using hall

end Berstein.GraphMeaning
