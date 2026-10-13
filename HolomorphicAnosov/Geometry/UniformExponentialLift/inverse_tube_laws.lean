import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Geometry.UniformExponentialLift.local_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.compact_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuous_metricNorm
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_normalTube
import HolomorphicAnosov.Geometry.UniformExponentialLift.uniform_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.glue_inverse_tube

noncomputable section

namespace HolomorphicAnosov
namespace ExponentialLift

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- The inverse of the moving exponential diffeomorphism defines a moving-base inverse
with both inverse identities on their domains. (Hirsch–Pugh–Shub, p. 62) -/
theorem inverse_tube_laws
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (O : Opens (TangentBundle 𝓘(ℝ, E) M)) (B : Opens (M × M))
    (Φ : Diffeomorph (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) O B ∞)
    (hΦ : ∀ z : O, (Φ z : M × M) = riemannianExponentialAddition g z) :
    ∃ L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q,
      (∀ y : B, ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M) =
        ⟨y.val.1, L y.val.1 y.val.2⟩) ∧
      (∀ q w : M, (q, w) ∈ B → riemannianExp g q (L q w) = w) ∧
      ∀ (q : M) (v : TangentSpace 𝓘(ℝ, E) q),
        (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ O → L q (riemannianExp g q v) = v := by
  classical
  have hbase (y : B) : ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M).proj = y.val.1 := by
    have h := congrArg Prod.fst (hΦ (Φ.symm y))
    rw [Φ.apply_symm_apply] at h
    exact h.symm
  have hvector (y : B) : ∃ v : TangentSpace 𝓘(ℝ, E) y.val.1,
      ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M) = ⟨y.val.1, v⟩ := by
    have hq := hbase y
    generalize hz : ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M) = z at *
    obtain ⟨q, v⟩ := z
    change q = y.val.1 at hq
    subst q
    exact ⟨v, rfl⟩
  let L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q := fun q w ↦
    if h : (q, w) ∈ B then Classical.choose (hvector ⟨(q, w), h⟩) else 0
  have hinv (y : B) : ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M) =
      ⟨y.val.1, L y.val.1 y.val.2⟩ := by
    simpa only [L, dite_eq_left y.property] using Classical.choose_spec (hvector y)
  refine ⟨L, hinv, ?_, ?_⟩
  · intro q w hqw
    have h := congrArg Prod.snd (hΦ (Φ.symm ⟨(q, w), hqw⟩))
    rw [Φ.apply_symm_apply] at h
    rw [hinv] at h
    exact h.symm
  · intro q v hv
    have hy : (q, riemannianExp g q v) ∈ B := by
      simpa only [hΦ, riemannianExponentialAddition, riemannianExp] using
        (Φ ⟨⟨q, v⟩, hv⟩).property
    have hφ : Φ ⟨⟨q, v⟩, hv⟩ = ⟨(q, riemannianExp g q v), hy⟩ :=
      Subtype.ext (hΦ _)
    have h := hinv ⟨(q, riemannianExp g q v), hy⟩
    rw [← hφ, Φ.symm_apply_apply] at h
    rw [hφ] at h
    exact (TotalSpace.mk_inj.mp h).symm


end ExponentialLift
end HolomorphicAnosov
