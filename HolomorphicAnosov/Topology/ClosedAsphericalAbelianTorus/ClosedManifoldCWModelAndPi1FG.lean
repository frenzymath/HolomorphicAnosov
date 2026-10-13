import HolomorphicAnosov.Topology.ClosedManifoldFiniteSimplicialRetractPi1FG
import HolomorphicAnosov.Topology.CWDominationHomotopyModel
import Mathlib.Geometry.Manifold.Instances.Real

/-!
Public reusable helper extracted from `HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus`.
Source: Ghys, *Holomorphic Anosov systems* (1995), proof of Theorem B, p.598;
expanded with the cited Hatcher results recorded in the parent module.
-/

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

/-- Hatcher's finite-retract and CW-domination inputs supply a genuine CW
homotopy model and finite generation on the original manifold carrier. -/
theorem closed_manifold_cw_model_and_pi1_fg (n : ℕ) (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M] :
    (∀ x₀ : M, Group.FG (FundamentalGroup M x₀)) ∧
      ∃ (K : Type u) (t : TopologicalSpace K),
        letI := t
        T2Space K ∧ ConnectedSpace K ∧
          Nonempty (_root_.Topology.CWComplex (Set.univ : Set K)) ∧
          Nonempty (ContinuousMap.HomotopyEquiv M K) := by
  obtain ⟨N, P, _hfinite, hconnected, cw, hcwfinite, j, q, hqj, hfg⟩ :=
    closed_manifold_finite_simplicial_retract_pi1_fg n M
  let K₀ := {x : EuclideanSpace ℝ (Fin N) // x ∈ P.space}
  let : _root_.Topology.CWComplex (Set.univ : Set K₀) := cw
  have : ConnectedSpace K₀ := isConnected_iff_connectedSpace.mp hconnected
  have heq : q.comp j = ContinuousMap.id M := by ext x; exact hqj x
  let H : ContinuousMap.Homotopy (q.comp j) (ContinuousMap.id M) :=
    (ContinuousMap.Homotopy.refl (q.comp j)).cast rfl heq
  exact ⟨hfg, cw_domination_homotopy_model n M K₀ j q H⟩

end HolomorphicAnosov
