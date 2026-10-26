import Berstein.GraphCertificate
import Berstein.RatioGrid

namespace Berstein.GraphCertificate

/-- Every active parent bin occurs exactly once, in order, and every supplied
cell passes the proved graph checker. -/
def checkGeometry (input : Input) (alive : ByteArray) (geometry : Nat)
    (cells : List Cell) : Bool :=
  decide (cells.map Cell.bin = (List.range input.bins).filter
    (fun bin => (List.range input.types).any (adopted input alive geometry bin))) &&
  cells.all (checkCell input alive geometry)

theorem checkGeometry_cell (input : Input) (alive : ByteArray) (geometry : Nat)
    (cells : List Cell) (h : checkGeometry input alive geometry cells = true)
    (bin type : Nat) (hb : bin < input.bins) (ht : type < input.types)
    (ha : adopted input alive geometry bin type = true) :
    ∃ cell ∈ cells, cell.bin = bin ∧ checkCell input alive geometry cell = true := by
  have heq : cells.map Cell.bin = (List.range input.bins).filter
      (fun bin => (List.range input.types).any (adopted input alive geometry bin)) :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  have hactive : (List.range input.types).any (adopted input alive geometry bin) = true :=
    List.any_eq_true.mpr ⟨type,List.mem_range.mpr ht,ha⟩
  have hmem : bin ∈ cells.map Cell.bin := by
    rw [heq]
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hb,hactive⟩
  obtain ⟨cell,hcell,hbin⟩ := List.mem_map.mp hmem
  exact ⟨cell,hcell,hbin,List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 cell hcell⟩

/-- Extract every finite index, legality, mapping, and merging check from an
accepted child record. -/
theorem checkVertex_structure (input : Input) (alive : ByteArray) (geometry bin : Nat)
    (v : Vertex) (h : checkVertex input alive geometry bin v = true) :
    let pair := input.pairs[v.pair]?.getD default
    let leftSide := input.sides[geometry/input.states]?.getD default
    let rightSide := input.sides[geometry%input.states]?.getD default
    let left := leftSide.transitions[pair.left]?.getD default
    let right := rightSide.transitions[pair.right]?.getD default
    v.pair < input.pairs.size ∧ v.first ≤ v.last ∧ v.last < input.bins ∧
      pair.left < leftSide.transitions.size ∧ pair.right < rightSide.transitions.size ∧
      0 ≤ left.state ∧ left.state < input.states ∧ 0 ≤ right.state ∧ right.state < input.states ∧
      (pair.spine = true → left.spine = true ∧ right.spine = true) ∧
      mappedBinsCheck input bin left right v = true ∧ checkMergedBand input v = true := by
  dsimp only
  unfold checkVertex at h
  dsimp only [Id.run, Pure.pure, Id.instMonad] at h
  repeat' first | split at h | contradiction
  simp_all [Bool.and_eq_true]

/-- A checked child ratio image is covered by a consecutive range of bins.
The constant-ID shortcut needs its semantic equality, checked separately by
input validation; all other cases use the proved rational division enclosure. -/
theorem mappedBinsCheck_cover (input : Input) (bin : Nat) (left right : Transition)
    (v : Vertex) (hcheck : mappedBinsCheck input bin left right v = true)
    (hfirst : v.first ≤ v.last) (hlast : v.last < input.bins)
    (cut : Nat → ℝ) (hcut : ∀ k ≤ input.bins, (input.grid[k]?.getD default).mem (cut k))
    (S dl dr : ℝ) (hparent : cut bin ≤ S ∧ S ≤ cut (bin+1)) (hbin : bin < input.bins)
    (hdl : left.derivative.mem dl) (hdr : right.derivative.mem dr) (hdlpos : 0 < dl)
    (hconstant : left.constant ≠ 0 → left.constant = right.constant → dr = dl) :
    ∃ k, v.first ≤ k ∧ k ≤ v.last ∧ cut k ≤ S*dr/dl ∧ S*dr/dl ≤ cut (k+1) := by
  have hS : (QBounds.mk (input.grid[bin]?.getD default).lo
      (input.grid[bin+1]?.getD default).hi).mem S :=
    ⟨(hcut bin (by omega)).1.trans hparent.1,
      hparent.2.trans (hcut (bin+1) (by omega)).2⟩
  unfold mappedBinsCheck at hcheck
  split at hcheck
  · next hconst =>
      have hc : left.constant ≠ 0 ∧ left.constant = right.constant := by
        simpa only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hconst
      have hv : v.first = bin ∧ v.last = bin := of_decide_eq_true hcheck
      have heq : S*dr/dl = S := by rw [hconstant hc.1 hc.2]; exact mul_div_cancel_right₀ S (ne_of_gt hdlpos)
      exact ⟨bin,by omega,by omega,by simpa [heq] using hparent.1,by simpa [heq] using hparent.2⟩
  · cases hf : QBounds.checkedDiv right.derivative left.derivative with
    | none => simp only [hf, Bool.false_eq_true] at hcheck
    | some factor =>
        simp only [hf] at hcheck
        let ratio := QBounds.mk (input.grid[bin]?.getD default).lo (input.grid[bin+1]?.getD default).hi
        let image := QBounds.mul ratio factor
        have hm : (input.grid[v.first]?.getD default).hi ≤ image.lo ∧
            image.hi ≤ (input.grid[v.last+1]?.getD default).lo := of_decide_eq_true hcheck
        have hfactor := QBounds.checkedDiv_sound _ _ factor dr dl hdr hdl hf
        have hx : image.mem (S*dr/dl) := by
          have hh := QBounds.mul_sound ratio factor S (dr/dl) hS hfactor
          simpa only [mul_div_assoc] using hh
        have hlo : cut v.first ≤ S*dr/dl :=
          ((hcut v.first (by omega)).2.trans (Rat.cast_mono hm.1)).trans hx.1
        have hhi : S*dr/dl ≤ cut (v.last+1) :=
          (hx.2.trans (Rat.cast_mono hm.2)).trans (hcut (v.last+1) (by omega)).1
        obtain ⟨d,hd,hdl,hdr⟩ := RatioGrid.between_cuts (fun j ↦ cut (v.first+j))
          (v.last-v.first) (S*dr/dl) (by simpa using hlo) (by
            have he : v.first+(v.last-v.first+1)=v.last+1 := by omega
            simpa only [he] using hhi)
        exact ⟨v.first+d,by omega,by omega,hdl,by simpa only [Nat.add_assoc] using hdr⟩

end Berstein.GraphCertificate
