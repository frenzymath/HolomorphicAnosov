import HolomorphicAnosov.Topology.Homology.CompactSupportClassOfLocalCompatibility
import HolomorphicAnosov.Topology.Homology.EuclideanCompactConvexHomologyProfile
import HolomorphicAnosov.Topology.Homology.CompactSupportBallHomologyLift
import HolomorphicAnosov.Topology.Homology.FiniteCompactChartCover
import HolomorphicAnosov.Topology.Homology.IntegralChartSupportTransport



noncomputable section
namespace HolomorphicAnosov

open Set
open HolomorphicAnosov.Topology _root_.Topology

universe u

/-- For a positive-dimensional chart support, point restrictions detect top-dimensional integral compact-support homology and all higher degrees vanish.  -/
theorem positive_dimensional_chart_support_detection
    (n : ℕ) (_hn : n ≠ 0) (M : Type u) [TopologicalSpace M] [T2Space M]
    (_hM : ∀ x : M, ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      x ∈ e.source)
    (A : Set M) (hA : IsCompact A)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hAe : A ⊆ e.source) :
    (∀ aA : supportSingularHomology (TopCat.of M) A
        (ModuleCat.of ℤ (ULift.{u} ℤ)) n,
      (∀ (x : M) (hx : x ∈ A),
        supportSingularHomologyRestrict (TopCat.of M)
          (ModuleCat.of ℤ (ULift.{u} ℤ))
          (Set.singleton_subset_iff.mpr hx) n aA = 0) → aA = 0) ∧
    (∀ q : ℕ, n < q →
      Subsingleton
        (supportSingularHomology (TopCat.of M) A
          (ModuleCat.of ℤ (ULift.{u} ℤ)) q : Type u)) := by
  exact integral_partial_chart_support_transport n M A hA e hAe

end HolomorphicAnosov
