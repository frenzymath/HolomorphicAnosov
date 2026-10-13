import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace HolomorphicAnosov

open Set

/-- A stereographic puncture is simply connected. Source: Hatcher
Proposition 1.14, p.35. Its chart is a homeomorphism onto the entire Euclidean
model, which is contractible by straight-line contraction. -/
theorem sphere_puncture_simply_connected (n : ℕ)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    IsSimplyConnected ({p}ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  let e := stereographic' n p
  have : SimplyConnectedSpace e.target := by
    change SimplyConnectedSpace (stereographic' n p).target
    rw [stereographic'_target]
    exact (Homeomorph.Set.univ _).toHomotopyEquiv.simplyConnectedSpace
  have hs : SimplyConnectedSpace e.source :=
    e.toHomeomorphSourceTarget.toHomotopyEquiv.simplyConnectedSpace
  rw [← stereographic'_source (n := n) p]
  exact hs

end HolomorphicAnosov

