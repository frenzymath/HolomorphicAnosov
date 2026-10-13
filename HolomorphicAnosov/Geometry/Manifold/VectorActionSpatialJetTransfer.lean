import HolomorphicAnosov.Analysis.Regularity.MontgomeryParameterDerivativeDenseJointContinuity
import HolomorphicAnosov.Geometry.Manifold.VectorActionSpatialJetTransferProviderG12
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Source: Montgomery, *Topological Groups of Differentiable Transformations*, Annals of Mathematics 46 (1945), Corollary 1, pp.386–387. -/

namespace HolomorphicAnosov.VectorActionSpatialSupport

open scoped ContDiff


theorem action_coordinate_spatial_jet_transfer
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    [AddAction V M] [ContinuousVAdd V M]
    (hsmooth : ∀ v : V, ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞ (fun x : M ↦ v +ᵥ x))
    (e f : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (hf : f ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (k : ℕ) (s : Set (V × E)) (hs : IsOpen s)
    (hdom : ∀ p ∈ s, p.2 ∈ e.target ∧ (p.1 +ᵥ e.symm p.2) ∈ f.source) :
    ContinuousOn
      (fun p : V × E ↦ iteratedFDeriv ℝ (Nat.succ (Nat.succ k))
        (fun y : E ↦ f (p.1 +ᵥ e.symm y)) p.2) s := by
  exact action_coordinate_spatial_jet_transfer_provider hsmooth e f he hf k s hs hdom

end HolomorphicAnosov.VectorActionSpatialSupport

