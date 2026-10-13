import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds
import HolomorphicAnosov.Geometry.ContinuousOriginalNorm

open scoped Manifold ContDiff Topology _root_.Topology Bundle
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov

/-- On a compact complex manifold, the projection associated with a continuous real tangent
splitting is uniformly bounded in any fixed smooth tangent metric. (Zhang, Lemma 2.2, p.5,
preceding equation (6)) -/
theorem uniform_real_projection_bound
    {d : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (S U : ContinuousRealTangentSubbundle (realModel d) X)
    (hsplit : ∀ x, IsCompl (S.toDistribution x) (U.toDistribution x))
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x)) :
    letI : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨g.toRiemannianMetric⟩
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x (v : TangentSpace (realModel d) x),
      ‖(S.toDistribution x).projection (U.toDistribution x) (hsplit x) v‖ ≤ B * ‖v‖ := by
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  let P x := (S.toDistribution x).projection (U.toDistribution x) (hsplit x)
  let q (x : X) : Seminorm ℝ (TangentSpace (complexModel d) x) :=
    (normSeminorm ℝ (TangentSpace (realModel d) x)).comp
      (complexTangentToReal d x).toLinearEquiv.toLinearMap
  let p (x : X) : Seminorm ℝ (TangentSpace (complexModel d) x) :=
    (normSeminorm ℝ (TangentSpace (realModel d) x)).comp
      ((P x).comp (complexTangentToReal d x).toLinearEquiv.toLinearMap)
  have hP := NativeSplittingPreparation.continuous_native_projection (realModel d) S U hsplit
  have hp : Continuous (fun z : TangentBundle (complexModel d) X ↦ p z.proj z.snd) :=
    FixedBlockEstimates.Native.continuous_original_norm g _ _
      (hP.comp continuous_complexTangentToReal)
  have hq : Continuous (fun z : TangentBundle (complexModel d) X ↦ q z.proj z.snd) :=
    FixedBlockEstimates.Native.continuous_original_norm g _ _ continuous_complexTangentToReal
  have hqpos : ∀ x v, v ≠ 0 → 0 < q x v := by
    intro x v hv
    exact norm_pos_iff.mpr (fun hz ↦ hv ((complexTangentToReal d x).map_eq_zero_iff.mp hz))
  obtain ⟨B, hB, hb⟩ := Preparation.uniform_tangent_seminorm_upper_bound p q hp hq hqpos
  refine ⟨B, hB, fun x v ↦ ?_⟩
  have h := hb x ((complexTangentToReal d x).symm v)
  change ‖P x (complexTangentToReal d x ((complexTangentToReal d x).symm v))‖ ≤
    B * ‖complexTangentToReal d x ((complexTangentToReal d x).symm v)‖ at h
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

end HolomorphicAnosov
