import HolomorphicAnosov.Topology.Homology.ConvexSupportModTwoLocalHomology
import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietoris
import HolomorphicAnosov.Topology.Homology.ModTwoSupportHomologyEmpty
import HolomorphicAnosov.Topology.Homology.ModTwoLocalHomologyCompatibleFamily
import HolomorphicAnosov.Topology.Homology.FiniteCompactConvexUnionInduction
import HolomorphicAnosov.Topology.Homology.CompactSupportBallEnlargement
import HolomorphicAnosov.Topology.Homology.CompactSupportBallHomologyLiftCoefficients
import HolomorphicAnosov.Topology.Homology.ModTwoSupportUnionDetection
import HolomorphicAnosov.Topology.Homology.ModTwoSupportHomeomorphism
import HolomorphicAnosov.Topology.Homology.HatcherCompactSupportDetectionMod2Helpers

noncomputable section
namespace HolomorphicAnosov.HatcherCompactSupport
universe u
open Set

/-- Point restrictions detect top-degree classes on a nonempty compact support, and supported homology vanishes above the manifold dimension. (Hatcher) -/
theorem hatcher_compact_support_section_mod2_nonempty_data
    (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (A : Set M) (hA : IsCompact A) (hAne : A.Nonempty) :
    (∀ a : SupportHomology A n, (∀ x : A, supportToPoint A n x a = 0) → a = 0) ∧
    (∀ i : ℕ, n < i → Subsingleton (SupportHomology A i)) := by
  exact ⟨
    hatcher_compact_support_section_mod2_nonempty_detection n M A hA hAne,
    hatcher_compact_support_section_mod2_nonempty_vanishing n M A hA hAne
  ⟩

end HolomorphicAnosov.HatcherCompactSupport
