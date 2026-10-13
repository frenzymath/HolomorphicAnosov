import HolomorphicAnosov.Topology.Homology.EuclideanCompactConvexHomologyProfile
import HolomorphicAnosov.Topology.Homology.ConvexSupportRestrictionIso
noncomputable section
namespace HolomorphicAnosov
open Set CategoryTheory CategoryTheory.Limits HolomorphicAnosov.Topology _root_.Topology
set_option maxHeartbeats 4000000 in
 theorem ball_restriction_injective (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : Convex ℝ K) (hcK : IsCompact K) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K) :
    Function.Injective (supportSingularHomologyRestrict
      (TopCat.of (EuclideanSpace ℝ (Fin n))) (ModuleCat.of ℤ (ULift.{0} ℤ))
      (Set.singleton_subset_iff.mpr hx) n) := by
  exact convex_compact_support_restriction_bijective K hK hcK x hx n |>.1
end HolomorphicAnosov
