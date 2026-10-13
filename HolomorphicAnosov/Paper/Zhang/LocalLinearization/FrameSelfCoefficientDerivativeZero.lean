import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_frame_self_coefficient_derivative_zero
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (V : TopologicalSpace.Opens M) (e : QuotientLineConnection.HolomorphicFrame U V)
    (x : M) (hx : x ∈ V) :
    QuotientLineConnection.realDifferential (d := d) (e.coefficient e.sectionValue) x = 0 := by
  have heq : e.coefficient e.sectionValue =ᶠ[nhds x] (fun _ : M ↦ (1 : ℂ)) := by
    filter_upwards [V.isOpen.mem_nhds hx] with y hy
    change y ∈ V at hy
    unfold QuotientLineConnection.HolomorphicFrame.coefficient
    rw [dite_eq_left hy, e.normalized y hy]
  have hd := heq.mfderiv_eq (I := realModel d) (I' := 𝓘(ℝ, ℂ))
  unfold QuotientLineConnection.realDifferential
  rw [hd]
  simp


end
end HolomorphicAnosov.Paper.Zhang
