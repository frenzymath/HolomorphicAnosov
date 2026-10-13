import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateDerivative
import HolomorphicAnosov.Analysis.MovingOperatorNormStrictLocalBound
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeForwardInverse
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeInverseForward
import HolomorphicAnosov.Geometry.DiffeomorphInverseIterateBasepoint
import HolomorphicAnosov.Geometry.DiffeomorphForwardInverseIterateBasepoint
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Tactic
import HolomorphicAnosov.Geometry.ContinuousOriginalNorm

noncomputable section
open Bundle Set Filter
open scoped ContDiff Manifold Topology _root_.Topology Bundle
namespace HolomorphicAnosov.FixedBlockEstimates.Native
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Ambient derivative operator norms have the same local upper-bound property. -/
theorem ambient_opNorm_eventually_lt [FiniteDimensional ℝ E]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (F : M → M) (hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ F) (x : M) {c : ℝ} :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) :=
      ⟨g.toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F x‖ < c →
    ∀ᶠ y in 𝓝 x, ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F y‖ < c := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) :=
    ⟨g.toRiemannianMetric⟩
  intro hc
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let frame (y : e.baseSet) : E ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, E) y.val :=
    (e.linearEquivAt ℝ y.val y.prop).symm
  have hv : Continuous (fun p : e.baseSet × E ↦
      (⟨p.1.val, frame p.1 p.2⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    have h := e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd)
      (fun p : e.baseSet × E ↦ e.mem_target.mpr p.1.prop)
    convert h using 1
    funext p
    exact e.toPretrivialization.mk_symm p.1.prop p.2
  have hs := continuous_original_norm g (fun p : e.baseSet × E ↦ p.1.val)
    (fun p ↦ frame p.1 p.2) hv
  have ht := continuous_original_norm g (fun p : e.baseSet × E ↦ F p.1.val)
    (fun p ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F p.1.val (frame p.1 p.2))
    ((hF.continuous_tangentMap (by simp)).comp hv)
  have hlocal := HolomorphicAnosov.moving_operator_norm_eventually_lt frame
    (fun y : e.baseSet ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F y.val) hs ht
    (⟨x, hx⟩ : e.baseSet) hc
  rw [← map_nhds_subtype_coe_eq_nhds hx (e.open_baseSet.mem_nhds hx)]
  exact hlocal

end HolomorphicAnosov.FixedBlockEstimates.Native
