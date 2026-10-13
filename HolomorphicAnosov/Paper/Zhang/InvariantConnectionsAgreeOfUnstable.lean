import HolomorphicAnosov.Paper.Zhang.InvariantScalarFormZero
import HolomorphicAnosov.Paper.Zhang.ScalarDifferenceContinuous
import HolomorphicAnosov.Paper.Zhang.ContinuousScalarTangentEvaluation
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.ScalarDifferenceExistsUnique
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.PullbackScalarDifference

open Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection

/-- Continuous invariant quotient-line connections that agree in unstable directions agree everywhere. -/
theorem invariant_connections_agree_of_unstable
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧ Nonempty (HolomorphicFrame U V))
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (D D' : Connection U) (hc : IsContinuous D) (hc' : IsContinuous D')
    (hi : IsInvariant D f hU) (hi' : IsInvariant D' f hU)
    (hu : ∀ (V : Opens X) (e : HolomorphicFrame U V) (x : X), x ∈ V →
      ∀ v : TangentSpace (realModel d) x, v ∈ a.splitting.unstable.toDistribution x →
        D'.form V e x v = D.form V e x v) : Agrees D' D := by
  obtain ⟨α, hα, -⟩ := ConnectionCalculus.scalar_difference_exists_unique hcover D D'
  have hcontinuous := continuous_scalar_tangent_evaluation α
    (scalar_difference_continuous hcover D D' hc hc' α hα)
  have hinvariant : ∀ x, α x = (α (f x)).comp
      (mfderiv (realModel d) (realModel d) f x) := by
    intro x
    obtain ⟨V, hx, ⟨e⟩⟩ := hcover x
    have hp := ConnectionCalculus.pullback_scalar_difference hcover f hU
      D D' D D' α hi hi' hα V e x hx
    exact add_left_cancel ((hα V e x hx).symm.trans hp)
  have hzero := invariant_scalar_form_zero f a α hcontinuous hinvariant (by
    intro x v hv
    obtain ⟨V, hx, ⟨e⟩⟩ := hcover x
    have he := congrArg (fun A ↦ A v) (hα V e x hx)
    simp only [add_apply] at he
    have hu' := hu V e x hx v hv
    exact add_left_cancel (show D.form V e x v + α x v = D.form V e x v + 0 by
      simpa only [add_zero] using he.symm.trans hu'))
  intro V e x hx
  simpa only [hzero x, add_zero] using hα V e x hx

end HolomorphicAnosov
