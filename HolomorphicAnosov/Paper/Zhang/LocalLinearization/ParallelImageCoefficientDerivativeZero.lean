import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.InvariantParallelScaleDerivativeZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ImageFrameCoefficientNeZero

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_parallel_image_coefficient_derivative_zero
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (U : (x : M) → Submodule ℂ (TangentSpace (complexModel d) x))
    (f : Biholomorph d d M M) (hU : ∀ x (v : TangentSpace (complexModel d) x),
      v ∈ U x → mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (nabla : QuotientLineConnection.Connection U)
    (hinvariant : QuotientLineConnection.IsInvariant nabla f hU)
    {V W : TopologicalSpace.Opens M} (e : QuotientLineConnection.HolomorphicFrame U V)
    (e' : QuotientLineConnection.HolomorphicFrame U W) (x : M)
    (hx : x ∈ V) (hfx : f x ∈ W)
    (hsrc : nabla.form V e x = 0) (htgt : nabla.form W e' (f x) = 0) :
    QuotientLineConnection.realDifferential (d := d)
      (QuotientLineConnection.imageFrameCoefficient f hU e e') x = 0 :=
  localLinearization_invariant_parallel_scale_derivative_zero U f hU nabla hinvariant
    e e' x hx hfx hsrc htgt
    (localLinearization_imageFrameCoefficient_ne_zero U f hU e e' x hx hfx)


end
end HolomorphicAnosov.Paper.Zhang
