import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import HolomorphicAnosov.Topology.Holonomy.UnitDiskEmbedding

noncomputable section
open scoped ContDiff Manifold Topology
open Set Filter _root_.Topology

universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- A product chart can be restricted and rescaled to a product box of unit disks containing a
prescribed point. (Hirsch–Pugh–Shub, p.115) -/
theorem fixed_unit_product_box_g10 {s t : ℕ} {M : Type u} [TopologicalSpace M]
    (Ds : TopologicalSpace.Opens (Fin s → ℝ))
    (Du : TopologicalSpace.Opens (Fin t → ℝ)) (O : TopologicalSpace.Opens M)
    (e : (Ds × Du) ≃ₜ O) (p : O) :
    ∃ js : FoliationCoordinateDisk s → Ds, ∃ ju : FoliationCoordinateDisk t → Du,
      IsOpenEmbedding js ∧ IsOpenEmbedding ju ∧
      ∃ B : TransverseFoliationBox s t M, p.val ∈ B.image ∧
        ∀ zw, (B.chart zw).val = (e (js zw.1, ju zw.2)).val := by
  obtain ⟨js, hjs, zs, hzs⟩ := unit_disk_embedding_in_domain Ds (e.symm p).1
  obtain ⟨ju, hju, zu, hzu⟩ := unit_disk_embedding_in_domain Du (e.symm p).2
  let v : (FoliationCoordinateDisk s × FoliationCoordinateDisk t) → M :=
    fun zw ↦ (e (js zw.1, ju zw.2)).val
  have hv : IsOpenEmbedding v :=
    O.isOpen.isOpenEmbedding_subtypeVal.comp (e.isOpenEmbedding.comp (hjs.prodMap hju))
  let B : TransverseFoliationBox s t M :=
    { image := Set.range v
      isOpen_image := hv.isOpen_range
      chart := hv.isEmbedding.toHomeomorph }
  refine ⟨js, ju, hjs, hju, B, ?_, fun _ ↦ rfl⟩
  refine ⟨(zs, zu), ?_⟩
  change (e (js zs, ju zu)).val = p.val
  rw [hzs, hzu, Prod.mk.eta, e.apply_symm_apply]



end HolomorphicAnosov
