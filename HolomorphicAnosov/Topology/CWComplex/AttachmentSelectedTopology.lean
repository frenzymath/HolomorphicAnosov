import HolomorphicAnosov.Topology.CWComplex.AttachmentCellCoverage
import HolomorphicAnosov.Topology.CWComplex.AttachmentCellsFinite
import HolomorphicAnosov.Topology.CWComplex.AttachmentCharacteristicClosed
import HolomorphicAnosov.Topology.CWComplex.AttachmentTowerSeparation

/-! Induced topology on selected finite attachment cells.
Source: Hatcher, Algebraic Topology, Appendix p.520. -/
open Set TopCat Topology _root_.Topology
open scoped TopCat
universe u
namespace HolomorphicAnosov.FiniteCellAdjunction

/-- A boundary-closed selection of original cells is closed, and its induced
topology is detected by selected characteristic maps. Boundary closure makes
the selected open-cell union equal the selected closed-disk-image union.
These are finitely many compact sets in a Hausdorff tower. Likewise a subset
whose selected characteristic preimages are closed is a finite union of
compact images of these preimages, hence closed in the ambient space. This
proves the induced-topology criterion. Hatcher Appendix p.520. -/
theorem tower_selected_topology {d : ℕ} {X : TopCat.{u}} (T : Tower d X)
    (S : (n : ℕ) → Set (Cell T n)) :
    let L : Set X := ⋃ (n : ℕ) (c : S n), openCell c.val
    (∀ (n : ℕ) (c : Cell T n), c ∈ S n → boundaryImage c ⊆ L) →
    IsClosed L ∧ (∀ A : Set X, A ⊆ L →
      (IsClosed (Subtype.val ⁻¹' A : Set L) ↔
        ∀ (n : ℕ) (c : Cell T n), c ∈ S n → IsClosed (characteristic c ⁻¹' A))) := by
  intro L hboundary
  let := tower_t2Space T
  let := tower_finite_cells T
  let I := {c : Σ n, Cell T n // c.2 ∈ S c.1}
  have hfull (n : ℕ) (c : Cell T n) (hc : c ∈ S n) : Set.range (characteristic c) ⊆ L := by
    rintro x ⟨z, rfl⟩
    rcases disk_point_interior_or_boundary n z with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨⟨c, hc⟩, b, rfl⟩⟩
    · exact hboundary n c hc ⟨b, rfl⟩
  have hLunion : L = ⋃ c : I, Set.range (characteristic c.val.2) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hx⟩ := mem_iUnion.mp hx
      obtain ⟨c, b, hb⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨⟨⟨n, c.val⟩, c.property⟩, ballInclusion n b, hb⟩
    · intro hx
      obtain ⟨c, hc⟩ := mem_iUnion.mp hx
      exact hfull c.val.1 c.val.2 c.property hc
  have hL : IsClosed L := by
    rw [hLunion]
    exact isClosed_iUnion_of_finite fun c ↦
      (isCompact_range (continuous_characteristic c.val.2)).isClosed
  refine ⟨hL, ?_⟩
  intro A hA
  have hsub : IsClosed (Subtype.val ⁻¹' A : Set L) ↔ IsClosed A := by
    have heq : Subtype.val '' (Subtype.val ⁻¹' A : Set L) = A := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hA hx⟩, hx, rfl⟩
    exact hL.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.trans (by rw [heq])
  rw [hsub]
  constructor
  · intro ha n c hc
    exact ha.preimage (continuous_characteristic c)
  · intro ha
    have hAunion : A = ⋃ c : I, characteristic c.val.2 '' (characteristic c.val.2 ⁻¹' A) := by
      ext x
      constructor
      · intro hx
        have hxL := hA hx
        rw [hLunion] at hxL
        obtain ⟨c, z, hz⟩ := mem_iUnion.mp hxL
        exact mem_iUnion.mpr ⟨c, z, by simpa only [mem_preimage, hz] using hx, hz⟩
      · intro hx
        obtain ⟨c, z, hz, rfl⟩ := mem_iUnion.mp hx
        exact hz
    rw [hAunion]
    apply isClosed_iUnion_of_finite
    intro c
    exact ((ha c.val.1 c.val.2 c.property).isCompact.image
      (continuous_characteristic c.val.2)).isClosed

end HolomorphicAnosov.FiniteCellAdjunction
