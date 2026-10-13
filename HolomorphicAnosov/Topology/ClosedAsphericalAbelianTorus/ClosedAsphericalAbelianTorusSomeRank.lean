import HolomorphicAnosov.Topology.AsphericalTorusRecognition
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.FiniteAbelianTorsionfreeCoordinates
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.CoveringLocalLoopsNull
import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus.ClosedManifoldCWModelAndPi1FG
import Mathlib.Geometry.Manifold.Instances.Real

/-!
Public reusable helper extracted from `HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus`.
Source: Ghys, *Holomorphic Anosov systems* (1995), proof of Theorem B, p.598;
expanded with the cited Hatcher results recorded in the parent module.
-/

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

/-- Steps 2–7 of the source proof establish a torus homotopy type of some
finite rank. The rank is derived from the original fundamental group; its
equality with the manifold dimension is the remaining top-homology step. -/
theorem closed_aspherical_abelian_torus_some_rank (n : ℕ) (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M]
    {U : Type v} [TopologicalSpace U] [ContractibleSpace U]
    (p : U → M) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (x₀ : M)
    (habelian : ∀ a b : FundamentalGroup M x₀, a * b = b * a)
    (htorsion : ∀ a : FundamentalGroup M x₀, ∀ k : ℕ, 0 < k → a ^ k = 1 → a = 1) :
    ∃ r : ℕ, Nonempty (ContinuousMap.HomotopyEquiv M (UnitAddTorus (Fin r))) := by
  obtain ⟨hfg, K, t, hT2, _hconnected, ⟨cw⟩, hmodel⟩ :=
    closed_manifold_cw_model_and_pi1_fg n M
  let := t
  let := cw
  have : T2Space K := hT2
  have : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨r, hpi⟩ := finite_abelian_torsionfree_coordinates
    (FundamentalGroup M x₀) (hfg x₀) habelian htorsion
  exact ⟨r, Topology.aspherical_torus_recognition M (covering_local_loops_null p hp hsurj)
    K hmodel U p hp hsurj x₀ r hpi⟩

end HolomorphicAnosov
