import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import Mathlib.LinearAlgebra.Projectivization.Action
import HolomorphicAnosov.Analysis.Complex.ProjectiveDeveloping.Helpers.ProjectiveFiniteNeInfinity
import HolomorphicAnosov.Analysis.Complex.ProjectiveDeveloping.Helpers.ProjectiveInfinityOfNotFiniteSource

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys

/-- The finite projective chart has exactly the complement of infinity as range.
Source: Ghys §5 p.597. -/
theorem developing_finite_range :
    Set.range complexProjectiveLineFinite = {complexProjectiveLineInfinity}ᶜ := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact developing_finite_ne_infinity z
  · intro hp
    have hs : p ∈ complexProjectiveLineChartSource 1 := by
      by_contra hn
      exact hp (developing_eq_infinity_of_not_finite_source p hn)
    refine ⟨complexProjectiveLineChartFun 1 p 0, ?_⟩
    change complexProjectiveLineChartInv 1 _ = p
    convert (complexProjectiveLineChart_properties 1).2.2.2.2.1 p hs using 1
    apply congrArg (complexProjectiveLineChartInv 1)
    funext i
    exact congrArg (complexProjectiveLineChartFun 1 p) (Subsingleton.elim 0 i)

end HolomorphicAnosov.Ghys
