import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine
import HolomorphicAnosov.Paper.Zhang.InvariantConnection
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import HolomorphicAnosov.Paper.Zhang.UniformLocalStableCoordinates
import HolomorphicAnosov.Paper.Zhang.TranslationInvariantComplexTorusDescent
import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinate
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Submersion
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_complex_stable_derivative_image
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (hS : ∀ x, ((S.toDistribution x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.stable.toDistribution x) (x : M) :
    (S.toDistribution x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap =
      S.toDistribution (f x) := by
  apply Submodule.restrictScalars_injective ℝ ℂ _
  apply Submodule.map_injective_of_injective (complexTangentToReal d (f x)).injective
  rw [Submodule.restrictScalars_map, ← Submodule.map_comp]
  have hd : (complexTangentToReal d (f x)).toLinearEquiv.toLinearMap.comp
      ((mfderiv (complexModel d) (complexModel d) f x).toLinearMap.restrictScalars ℝ) =
      (mfderiv (realModel d) (realModel d) f.toReal x).toLinearMap.comp
        (complexTangentToReal d x).toLinearEquiv.toLinearMap := by
    ext v
    exact (TranslationInvariantDescent.holomorphic_mfderiv_realification
      (f.contMDiff.mdifferentiable (by simp) x) v).symm
  rw [hd]
  erw [Submodule.map_comp]
  rw [hS x, hS (f x)]
  exact a.splitting.stable_map x



end
end HolomorphicAnosov.Paper.Zhang
