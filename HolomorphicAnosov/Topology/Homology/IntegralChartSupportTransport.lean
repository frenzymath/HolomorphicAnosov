import HolomorphicAnosov.Topology.Homology.IntegralCompactSupportOrientationTools
import HolomorphicAnosov.Topology.Homology.IntegralPartialChartExcisionComposition
import HolomorphicAnosov.Topology.Homology.IntegralPartialChartExcisionComposition
import HolomorphicAnosov.Topology.Homology.EuclideanCompactConvexHomologyProfile
import HolomorphicAnosov.Topology.Homology.CompactSupportBallHomologyLift
import HolomorphicAnosov.Topology.Homology.FiniteCompactConvexUnionInduction

/-!
Integral chart-support transport boundary.
-/
noncomputable section
namespace HolomorphicAnosov
open Set HolomorphicAnosov.Topology _root_.Topology
universe u

/-- Transport the integral point-detection and above-dimension profile from a Euclidean finite-ball enlargement through a partial chart to an ambient compact support. (Hatcher, Lemma 3.27) -/
theorem integral_partial_chart_support_transport
    (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
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
  exact Classical.choice (integral_partial_chart_excision_composition n M A hA e hAe)

end HolomorphicAnosov
