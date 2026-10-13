import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_quotientDerivative_surjective
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (U : (x : M) → Submodule ℂ (TangentSpace (complexModel d) x))
    (f : Biholomorph d d M M) (hU : ∀ x (v : TangentSpace (complexModel d) x),
      v ∈ U x → mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x)) (x : M) :
    Function.Surjective (QuotientLineConnection.quotientDerivative f hU x) := by
  intro q
  obtain ⟨v, rfl⟩ := (U (f x)).mkQ_surjective q
  obtain ⟨w, hw⟩ := (f.mfderivToContinuousLinearEquiv (by simp) x).surjective v
  refine ⟨(U x).mkQ w, ?_⟩
  change (U (f x)).mkQ (mfderiv (complexModel d) (complexModel d) f x w) =
    (U (f x)).mkQ v
  exact congrArg (U (f x)).mkQ hw


end
end HolomorphicAnosov.Paper.Zhang
