import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.FixedUnitProductBoxG10
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation

noncomputable section
open scoped ContDiff Manifold Topology
open Set Filter _root_.Topology

universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- A fixed-unit product box obtained from a paired chart has stable and unstable slices that are
open embeddings into the corresponding intrinsic leaves. (Hirsch–Pugh–Shub, p.115) -/
theorem fixed_unit_product_box_native_plaques_g10 {s t : ℕ}
    {M : Type u} [TopologicalSpace M] {ιs ιu : Type u}
    {Ls : ιs → Type u} {Lu : ιu → Type u}
    [∀ i, TopologicalSpace (Ls i)] [∀ i, TopologicalSpace (Lu i)]
    [∀ i, ChartedSpace (Fin s → ℝ) (Ls i)]
    [∀ i, ChartedSpace (Fin t → ℝ) (Lu i)]
    (is : ∀ i, Ls i → M) (iu : ∀ i, Lu i → M)
    (Ds : TopologicalSpace.Opens (Fin s → ℝ))
    (Du : TopologicalSpace.Opens (Fin t → ℝ)) (O : TopologicalSpace.Opens M)
    (e : (Ds × Du) ≃ₜ O) (p : O)
    (hs : ∀ w : Du, ∃ i : ιs, ∃ V : TopologicalSpace.Opens (Ls i),
      ∃ c : Ds ≃ₜ V,
        ∀ z : Ds, (e (z, w)).val = is i (c z))
    (hu : ∀ z : Ds, ∃ i : ιu, ∃ V : TopologicalSpace.Opens (Lu i),
      ∃ c : Du ≃ₜ V,
        ∀ w : Du, (e (z, w)).val = iu i (c w)) :
    ∃ B : TransverseFoliationBox s t M, p.val ∈ B.image ∧
      (∀ w : FoliationCoordinateDisk t, ∃ i : ιs,
        ∃ j : FoliationCoordinateDisk s → Ls i, IsOpenEmbedding j ∧
          ∀ z, (B.chart (z, w)).val = is i (j z)) ∧
      (∀ z : FoliationCoordinateDisk s, ∃ i : ιu,
        ∃ j : FoliationCoordinateDisk t → Lu i, IsOpenEmbedding j ∧
          ∀ w, (B.chart (z, w)).val = iu i (j w)) := by
  obtain ⟨js, ju, hjs, hju, B, hp, hB⟩ := fixed_unit_product_box_g10 Ds Du O e p
  refine ⟨B, hp, ?_, ?_⟩
  · intro w
    obtain ⟨i, V, c, hc⟩ := hs (ju w)
    let j : FoliationCoordinateDisk s → Ls i := fun z ↦ (c (js z)).val
    have hj : IsOpenEmbedding j :=
      V.isOpen.isOpenEmbedding_subtypeVal.comp (c.isOpenEmbedding.comp hjs)
    refine ⟨i, j, hj, ?_⟩
    intro z
    exact (hB (z, w)).trans (hc (js z))
  · intro z
    obtain ⟨i, V, c, hc⟩ := hu (js z)
    let j : FoliationCoordinateDisk t → Lu i := fun w ↦ (c (ju w)).val
    have hj : IsOpenEmbedding j :=
      V.isOpen.isOpenEmbedding_subtypeVal.comp (c.isOpenEmbedding.comp hju)
    refine ⟨i, j, hj, ?_⟩
    intro w
    exact (hB (z, w)).trans (hc (ju w))



end HolomorphicAnosov
