import HolomorphicAnosov.Paper.Zhang.ScalarPullbackGeometricBound
import HolomorphicAnosov.Paper.Zhang.PullbackSequenceDifference
import HolomorphicAnosov.Paper.Zhang.ConnectionLimitOfGeometricBound
import HolomorphicAnosov.Paper.Zhang.CompatibleDifferenceOnSubbundle
import HolomorphicAnosov.Paper.Zhang.IsContinuousOfC0Limit
import HolomorphicAnosov.Paper.Zhang.IsCompatibleOfC0Limit
import HolomorphicAnosov.Paper.Zhang.IsInvariantOfC0Limit
import HolomorphicAnosov.Paper.Zhang.ScalarDifferenceContinuous
import HolomorphicAnosov.Paper.Zhang.ContinuousScalarTangentEvaluation
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.ScalarDifferenceExistsUnique

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Bundle
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection

/-- Every continuous compatible sequence of pullback connections converges globally in C⁰ to a
continuous compatible invariant connection, with a geometric tail bound. (Zhang, Lemma 2.2, eq.
(6)) -/
theorem compatible_pullback_sequence_c0_limit
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    {r : ℕ} (hUhol : IsHolomorphicTangentSubbundle r U)
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hUreal : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧ Nonempty (HolomorphicFrame U V))
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (Ds : ℕ → Connection U)
    (hc : ∀ n, IsContinuous (Ds n)) (hcomp : ∀ n, IsCompatible (Ds n))
    (hp : ∀ n (V W : Opens X) (e : HolomorphicFrame U V)
      (e' : HolomorphicFrame U W) (x : X), x ∈ V → f x ∈ W →
        (Ds (n + 1)).form V e x =
          (imageFrameCoefficient f hU e e' x)⁻¹ •
            realDifferential (imageFrameCoefficient f hU e e') x +
          ((Ds n).form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x))
    : ∃ D : Connection U, IsContinuous D ∧ IsCompatible D ∧ IsInvariant D f hU ∧
      (∀ n, BddAbove (differenceValues a.metric (Ds n) D)) ∧
      Tendsto (fun n ↦ c0Distance a.metric (Ds n) D) atTop (𝓝 0) := by
  obtain ⟨α, hα, -⟩ := ConnectionCalculus.scalar_difference_exists_unique hcover (Ds 0) (Ds 1)
  have hcontinuous := continuous_scalar_tangent_evaluation α
    (scalar_difference_continuous hcover (Ds 0) (Ds 1) (hc 0) (hc 1) α hα)
  have hu : ∀ x v, v ∈ a.splitting.unstable.toDistribution x → α x v = 0 := by
    intro x v hv
    obtain ⟨V, hx, ⟨e⟩⟩ := hcover x
    rw [← hUreal x] at hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    have heq := compatible_difference_on_subbundle hUhol (Ds 0) (Ds 1)
      (hcomp 0) (hcomp 1) V e x hx w hw
    have he := congrArg (fun A ↦ A (complexTangentToReal d x w)) (hα V e x hx)
    simp only [add_apply] at he
    exact add_left_cancel (show (Ds 0).form V e x (complexTangentToReal d x w) +
        α x (complexTangentToReal d x w) =
        (Ds 0).form V e x (complexTangentToReal d x w) + 0 by
      simpa only [add_zero] using he.symm.trans heq)
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨C, τ, hC, hτ, hτ1, hbound⟩ := scalar_pullback_geometric_bound f a α hcontinuous hu
  have hdiff := pullback_sequence_difference hcover f hU Ds hp α hα
  obtain ⟨D, -, -, hb, hlim⟩ := connection_limit_of_geometric_bound a.metric Ds
    hC.le hτ.le hτ1 (by
      intro n V e x hx v
      rw [hdiff n V e x hx]
      simp only [add_apply, ContinuousLinearMap.comp_apply, sub_add_cancel_left, norm_neg]
      change ‖α (((f : X → X)^[n]) x)
        (mfderiv (realModel d) (realModel d) ((f : X → X)^[n]) x v)‖ ≤ C * τ ^ n * ‖v‖
      exact hbound n x v)
  exact ⟨D, isContinuous_of_c0_limit a.metric Ds D hb hlim hc,
    isCompatible_of_c0_limit a.metric Ds D hb hlim hcomp,
    isInvariant_of_c0_limit a.metric f hU Ds D hb hlim hp, hb, hlim⟩

end HolomorphicAnosov
