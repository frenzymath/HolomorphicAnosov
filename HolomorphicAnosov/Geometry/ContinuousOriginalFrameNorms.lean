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
import HolomorphicAnosov.Geometry.ContinuousFrameTotalSpace

noncomputable section
open Bundle Set Filter
open scoped ContDiff Manifold Topology _root_.Topology Bundle
namespace HolomorphicAnosov.FixedBlockEstimates.Native
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- In local subbundle frame coordinates, both the original Riemannian norm of a vector and that of
its image under a smooth map’s derivative are continuous. (Zhang, p.1) -/
theorem continuous_original_frame_norms {r : ℕ}
    (P : RealTangentDistribution 𝓘(ℝ, E) M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (F : M → M) (hF : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ F) :
    letI : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x))) :=
      TopologicalSpace.induced
        (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance
    ∀ e : Trivialization (Fin r → ℝ)
        (TotalSpace.proj (F := Fin r → ℝ) (E := fun x : M ↦ ↥(P x))),
    ∀ he : e.IsLinear ℝ,
    letI := he
    letI : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨g.toRiemannianMetric⟩
    Continuous (fun p : e.baseSet × (Fin r → ℝ) ↦
      ‖((e.linearEquivAt ℝ p.1.val p.1.prop).symm p.2).val‖) ∧
    Continuous (fun p : e.baseSet × (Fin r → ℝ) ↦
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F p.1.val
        ((e.linearEquivAt ℝ p.1.val p.1.prop).symm p.2).val‖) := by
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance
  intro e he
  let := he
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  have hv := (continuous_induced_dom :
    Continuous (fun z : TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x)) ↦
      (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M))).comp
      (continuous_frame_totalSpace P e)
  refine ⟨continuous_original_norm g (fun p : e.baseSet × (Fin r → ℝ) ↦ p.1.val)
    (fun p ↦ ((e.linearEquivAt ℝ p.1.val p.1.prop).symm p.2).val) hv, ?_⟩
  exact continuous_original_norm g (fun p : e.baseSet × (Fin r → ℝ) ↦ F p.1.val)
    (fun p ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F p.1.val
      ((e.linearEquivAt ℝ p.1.val p.1.prop).symm p.2).val)
    ((hF.continuous_tangentMap (by simp)).comp hv)

end HolomorphicAnosov.FixedBlockEstimates.Native
