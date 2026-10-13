import HolomorphicAnosov.Topology.AttachedCellPolyhedralData
import HolomorphicAnosov.Topology.CWComplex.AttachmentOldSpaceBoundary
import HolomorphicAnosov.Topology.CWComplex.AttachmentPuncturedQuotient
import HolomorphicAnosov.Topology.CWComplex.AttachmentCharacteristicFibres
import HolomorphicAnosov.Topology.CWComplex.QuotientProductHomotopyDescent

namespace HolomorphicAnosov.HatcherAttachedCell

/-- Boundary-fixed homotopies on the punctured characteristic disk descend
to the punctured attachment, fixing the old space. Source: Hatcher
Theorem 4.8, p.349, and Appendix A.17, pp.532–533. The result keeps both
puncture avoidance and the old-space endpoint conclusion.

Proof: use the old-space constant homotopy on the left summand and the
given homotopy on the punctured disk. The sum/product homeomorphism gives
joint continuity. Mixed characteristic fibres lie on the boundary; two
disk representatives are equal or both boundary points. Thus boundary
fixedness gives equality on every fibre. Locally compact interval-product
quotient descent produces the map. Each endpoint and range condition is
checked on representatives, and the old-space summand gives fixedness.
-/
theorem attachment_punctured_homotopy_descent
    {Z : Type*} [TopologicalSpace Z] [T1Space Z] {k : ℕ}
    (cell : Attachment Z k) (p : Z) (hp : p ∉ cell.oldSpace)
    (H : C(unitInterval × {d : CellDisk k // cell.characteristic d ≠ p}, Z))
    (hzero : ∀ d, H (0, d) = cell.characteristic d.val)
    (hboundary : ∀ t d, ‖d.val.val‖ = 1 → H (t, d) = cell.characteristic d.val)
    (hone : ∀ d, H (1, d) ∈ cell.oldSpace)
    (havoid : ∀ t d, H (t, d) ≠ p) :
    ∃ K : C(unitInterval × {z : Z // z ≠ p}, Z),
      (∀ z, K (0, z) = z.val) ∧
      (∀ z, K (1, z) ∈ cell.oldSpace) ∧
      (∀ t z, K (t, z) ≠ p) ∧
      (∀ t z, z.val ∈ cell.oldSpace → K (t, z) = z.val) ∧
      (∀ t d, K (t, ⟨cell.characteristic d.val, d.property⟩) = H (t, d)) := by
  let D := {d : CellDisk k // cell.characteristic d ≠ p}
  let q : cell.oldSpace ⊕ D → {z : Z // z ≠ p} := Sum.elim
    (fun x ↦ ⟨x.val, fun he ↦ hp (he ▸ x.property)⟩)
    (fun x ↦ ⟨cell.characteristic x.val, x.property⟩)
  have hq : Topology.IsQuotientMap q := attachment_punctured_quotient cell p hp
  let E : unitInterval × (cell.oldSpace ⊕ D) → Z :=
    fun s ↦ Sum.elim (fun x ↦ x.val) (fun d ↦ H (s.1, d)) s.2
  have hE : Continuous E := by
    have hc := ((continuous_subtype_val.comp continuous_snd :
        Continuous (fun s : unitInterval × cell.oldSpace ↦ s.2.val)).sumElim H.continuous).comp
      (Homeomorph.prodSumDistrib (X := unitInterval) (Y := cell.oldSpace) (Z := D)).continuous
    convert hc using 1
    funext s
    rcases s with ⟨t, x | d⟩ <;> rfl
  have hcompat : ∀ t x y, q x = q y → E (t, x) = E (t, y) := by
    intro t x y he
    have heval := congrArg Subtype.val he
    cases x with
    | inl x =>
      cases y with
      | inl y => exact heval
      | inr d =>
        change x.val = cell.characteristic d.val at heval
        change x.val = H (t, d)
        have hd : ‖d.val.val‖ = 1 := (attachment_characteristic_mem_old_iff cell d.val).mp
          (by rw [← heval]; exact x.property)
        exact heval.trans (hboundary t d hd).symm
    | inr d =>
      cases y with
      | inl x =>
        change cell.characteristic d.val = x.val at heval
        change H (t, d) = x.val
        have hd : ‖d.val.val‖ = 1 := (attachment_characteristic_mem_old_iff cell d.val).mp
          (by rw [heval]; exact x.property)
        exact (hboundary t d hd).trans heval
      | inr e =>
        change H (t, d) = H (t, e)
        rcases attachment_characteristic_fibres cell d.val e.val heval with heq | ⟨hd, he⟩
        · exact congrArg (fun x : D ↦ H (t, x)) (Subtype.ext heq)
        · exact (hboundary t d hd).trans (heval.trans (hboundary t e he).symm)
  obtain ⟨K, hK, hKeq⟩ := CWCharacteristic.exists_continuous_product_quotient_lift q hq E hE hcompat
  refine ⟨⟨K, hK⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨x, rfl⟩ := hq.surjective z
    simp only [ContinuousMap.coe_mk]
    rw [hKeq]
    cases x with
    | inl x => rfl
    | inr d => exact hzero d
  · intro z
    obtain ⟨x, rfl⟩ := hq.surjective z
    simp only [ContinuousMap.coe_mk]
    rw [hKeq]
    cases x with
    | inl x => exact x.property
    | inr d => exact hone d
  · intro t z
    obtain ⟨x, rfl⟩ := hq.surjective z
    simp only [ContinuousMap.coe_mk]
    rw [hKeq]
    cases x with
    | inl x => exact fun he ↦ hp (he ▸ x.property)
    | inr d => exact havoid t d
  · intro t z hz
    exact hKeq t (Sum.inl ⟨z.val, hz⟩)
  · intro t d
    exact hKeq t (Sum.inr d)

end HolomorphicAnosov.HatcherAttachedCell
