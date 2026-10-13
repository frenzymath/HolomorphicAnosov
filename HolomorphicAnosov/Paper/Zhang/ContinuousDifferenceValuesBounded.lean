import HolomorphicAnosov.Paper.Zhang.ScalarDifferenceContinuous
import HolomorphicAnosov.Paper.Zhang.ContinuousScalarTangentEvaluation
import HolomorphicAnosov.Paper.Zhang.UniformOriginalScalarBound
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.ScalarDifferenceExistsUnique
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.QuotientLineConnectionC0

/-! Uniform bounds for scalar differences of continuous connections on metric unit tangent balls
over a compact base. (Zhang, Lemma 2.2, eq. (6), p. 5) -/

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection

/-- The scalar difference of two continuous connections is uniformly bounded on metric unit tangent
balls over a compact complex manifold with local holomorphic quotient frames. (Zhang, Lemma 2.2,
eq. (6), p. 5) -/
theorem continuous_difference_values_bounded
    {d : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [CompactSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧ Nonempty (HolomorphicFrame U V))
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x))
    (D D' : Connection U) (hD : IsContinuous D) (hD' : IsContinuous D') :
    BddAbove (differenceValues g D D') := by
  obtain ⟨α, hα, -⟩ := ConnectionCalculus.scalar_difference_exists_unique hcover D' D
  have hc := continuous_scalar_tangent_evaluation α
    (scalar_difference_continuous hcover D' D hD' hD α hα)
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨B, hB, hb⟩ := uniform_original_scalar_bound g α hc
  refine ⟨B, ?_⟩
  rintro r ⟨V, e, x, hx, v, hv, rfl⟩
  have hnorm : ‖v‖ ≤ 1 := by
    change Real.sqrt (g.inner x v v) ≤ 1
    exact (Real.sqrt_le_one).mpr hv
  have heval := congrArg (fun L ↦ L v) (hα V e x hx)
  have heq : D.form V e x v - D'.form V e x v = α x v := by
    simpa only [add_apply, add_sub_cancel_left] using
      congrArg (fun z ↦ z - D'.form V e x v) heval
  rw [heq]
  exact (hb x v).trans ((mul_le_mul_of_nonneg_left hnorm (by linarith)).trans_eq (mul_one B))

end HolomorphicAnosov
