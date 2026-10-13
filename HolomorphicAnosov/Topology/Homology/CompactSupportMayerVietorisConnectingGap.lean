import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietorisData
import HolomorphicAnosov.Topology.Homology.CompactSupportMVAssembly

noncomputable section
namespace HolomorphicAnosov.Topology
open CategoryTheory
universe u

/-- The connecting family for compact-support relative Mayer–Vietoris. -/
theorem compact_support_mayer_vietoris_connecting_gap :
      ∃ δ : ∀ (D : CompactSupportMVData.{u}) (k : ℕ),
          supportSingularHomology D.space (D.left ∩ D.right) D.coefficients (k + 1) →+
            supportSingularHomology D.space (D.left ∪ D.right) D.coefficients k,
        (∀ D : CompactSupportMVData.{u},
          (∀ k : ℕ,
            Function.Exact (δ D k)
              (supportMayerVietorisPhi D.space D.coefficients D.left D.right k) ∧
            Function.Exact
              (supportMayerVietorisPhi D.space D.coefficients D.left D.right k)
              (supportMayerVietorisPsi D.space D.coefficients D.left D.right k) ∧
            Function.Exact
              (supportMayerVietorisPsi D.space D.coefficients D.left D.right (k + 1))
              (δ D k))) ∧
        (∀ (D E : CompactSupportMVData.{u}) (F : CompactSupportMVMap D E) (k : ℕ),
          (F.unionMap k).comp (δ D k) = (δ E k).comp (F.interMap (k + 1)))
    := by
  let δ : ∀ (D : CompactSupportMVData.{u}) (k : ℕ),
      supportSingularHomology D.space (D.left ∩ D.right) D.coefficients (k + 1) →+
        supportSingularHomology D.space (D.left ∪ D.right) D.coefficients k :=
    fun D k ↦ CompactSupportMVData.connecting D k
  refine ⟨δ, ?_, ?_⟩
  · intro D k
    simpa [δ] using CompactSupportMVData.connecting_exact D k
  · intro D E F k
    simpa [δ] using CompactSupportMVMap.connecting_naturality F k

end HolomorphicAnosov.Topology
