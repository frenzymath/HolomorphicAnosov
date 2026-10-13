import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate
import HolomorphicAnosov.Paper.Zhang.StableFoliationsDerivativeScalarRestriction

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- The real derivative of a holomorphic iterate commutes with the transported complex structure on
tangent fibres. (Ghys, Lemma 2.1, p.589) -/
theorem original_iterate_derivative_commutes_J
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (n : ℕ) (x : M)
    (v : TangentSpace (realModel d) x) :
    mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x
      (complexTangentToReal d x (Complex.I • (complexTangentToReal d x).symm v)) =
    complexTangentToReal d ((f : M → M)^[n] x)
      (Complex.I • (complexTangentToReal d ((f : M → M)^[n] x)).symm
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal n) x v)) := by
  have hc := (f.contMDiff.iterate n).mdifferentiable (by simp) x
  have hr := (realIterate (realModel d) f.toReal n).contMDiff.mdifferentiable (by simp) x
  have hd := derivative_scalar_restriction ((f : M → M)^[n]) x hc hr
  change mfderiv (realModel d) (realModel d) ((f : M → M)^[n]) x _ =
    complexTangentToReal d ((f : M → M)^[n] x)
      (Complex.I • (complexTangentToReal d ((f : M → M)^[n] x)).symm
        (mfderiv (realModel d) (realModel d) ((f : M → M)^[n]) x v))
  rw [hd]
  exact (mfderiv (complexModel d) (complexModel d) ((f : M → M)^[n]) x).map_smul
    Complex.I ((complexTangentToReal d x).symm v)

end StableFoliationsSupport
end HolomorphicAnosov
