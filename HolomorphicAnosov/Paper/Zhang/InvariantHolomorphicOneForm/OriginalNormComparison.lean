import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.OneFormBundle

attribute [local instance] complex_isManifold_real
universe u

/-- The Anosov tangent norm and any smooth Hermitian tangent norm are uniformly comparable by
positive constants on a compact complex manifold, using `complexTangentToReal`. -/
theorem original_norm_comparison {d : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] [T2Space M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h) :
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ 1 ≤ C ∧ ∀ x v,
      c * Real.sqrt (((h x).inner v v).re) ≤ ‖complexTangentToReal d x v‖ ∧
      ‖complexTangentToReal d x v‖ ≤ C * Real.sqrt (((h x).inner v v).re) := by
  let : IsManifold (realModel d) ∞ M := complex_isManifold_real d M
  let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.inner, a.metric.contMDiff, fun _ _ _ ↦ rfl⟩
  let : IsContinuousRiemannianBundle (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨⟨a.metric.inner, a.metric.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let g (x : M) : Seminorm ℝ (TangentSpace (complexModel d) x) :=
    (normSeminorm ℝ (TangentSpace (realModel d) x)).comp
      (complexTangentToReal d x).toLinearMap
  have gc : Continuous (fun z : TangentBundle (complexModel d) M ↦ g z.proj z.snd) := by
    have hreal : Continuous (fun z : TangentBundle (realModel d) M ↦ ‖z.snd‖) := by
      have hi : Continuous (fun z : TangentBundle (realModel d) M ↦
          @inner ℝ (TangentSpace (realModel d) z.proj) _ z.snd z.snd) :=
        continuous_id.inner_bundle continuous_id
      simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] using hi.sqrt
    exact hreal.comp continuous_complexTangentToReal
  have gp (x : M) (v : TangentSpace (complexModel d) x) (hv : v ≠ 0) : 0 < g x v := by
    exact norm_pos_iff.mpr (fun hz ↦ hv ((complexTangentToReal d x).injective
      (hz.trans (map_zero _).symm)))
  exact Preparation.uniform_hermitian_tangent_norm_comparison g gc gp h hh


end HolomorphicAnosov.OneFormBundle
