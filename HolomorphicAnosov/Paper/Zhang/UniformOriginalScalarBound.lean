import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne

open scoped Manifold ContDiff Topology _root_.Topology Bundle
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov

/-- A continuous family of real-linear scalar functionals on the tangent bundle of a compact complex
manifold is uniformly bounded by a fixed multiple of a smooth tangent metric norm. (Zhang, Lemma
2.2) -/
theorem uniform_original_scalar_bound
    {d : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x))
    (α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hα : Continuous (fun z : TangentBundle (realModel d) X ↦ α z.proj z.snd)) :
    letI : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨g.toRiemannianMetric⟩
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x v, ‖α x v‖ ≤ B * ‖v‖ := by
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  let q (x : X) : Seminorm ℝ (TangentSpace (complexModel d) x) :=
    (normSeminorm ℝ (TangentSpace (realModel d) x)).comp
      (complexTangentToReal d x).toLinearEquiv.toLinearMap
  let p (x : X) : Seminorm ℝ (TangentSpace (complexModel d) x) :=
    (normSeminorm ℝ ℂ).comp
      ((α x).toLinearMap.comp (complexTangentToReal d x).toLinearEquiv.toLinearMap)
  have hp : Continuous (fun z : TangentBundle (complexModel d) X ↦ p z.proj z.snd) :=
    (hα.comp continuous_complexTangentToReal).norm
  have hq : Continuous (fun z : TangentBundle (complexModel d) X ↦ q z.proj z.snd) := by
    let : IsContinuousRiemannianBundle (ComplexModel d)
        (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    have hi : Continuous (fun z : TangentBundle (complexModel d) X ↦
        g.inner z.proj (complexTangentToReal d z.proj z.snd)
          (complexTangentToReal d z.proj z.snd)) :=
      (continuous_complexTangentToReal (d := d) (X := X)).inner_bundle
        (continuous_complexTangentToReal (d := d) (X := X))
    exact hi.sqrt
  have hqpos : ∀ x v, v ≠ 0 → 0 < q x v := by
    intro x v hv
    exact norm_pos_iff.mpr (fun hz ↦ hv ((complexTangentToReal d x).map_eq_zero_iff.mp hz))
  obtain ⟨B, hB, hbound⟩ := Preparation.uniform_tangent_seminorm_upper_bound p q hp hq hqpos
  refine ⟨B, hB, ?_⟩
  intro x v
  have hb := hbound x ((complexTangentToReal d x).symm v)
  change ‖α x (complexTangentToReal d x ((complexTangentToReal d x).symm v))‖ ≤
    B * ‖complexTangentToReal d x ((complexTangentToReal d x).symm v)‖ at hb
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hb

end HolomorphicAnosov
