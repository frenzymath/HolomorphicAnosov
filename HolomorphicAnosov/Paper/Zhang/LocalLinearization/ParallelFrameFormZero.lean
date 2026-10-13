import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.FrameSelfCoefficientDerivativeZero

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_parallel_frame_form_zero
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (nabla : QuotientLineConnection.Connection U)
    (V : TopologicalSpace.Opens M) (e : QuotientLineConnection.HolomorphicFrame U V)
    (he : QuotientLineConnection.IsParallelOn nabla V e.sectionValue)
    (x : M) (hx : x ∈ V) : nabla.form V e x = 0 := by
  ext v
  have hz := he V e x hx hx v
  apply_fun e.coordinate x hx at hz
  simp only [QuotientLineConnection.covariantDerivative, LinearEquiv.apply_symm_apply,
    map_zero, QuotientLineConnection.HolomorphicFrame.coefficient, dite_eq_left hx,
    e.normalized x hx, one_mul] at hz
  rw [localLinearization_frame_self_coefficient_derivative_zero U V e x hx] at hz
  simpa using hz


end
end HolomorphicAnosov.Paper.Zhang
