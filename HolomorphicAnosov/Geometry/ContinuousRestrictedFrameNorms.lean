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
import HolomorphicAnosov.Geometry.ContinuousOriginalFrameNorms

noncomputable section
open Bundle Set Filter
open scoped ContDiff Manifold Topology _root_.Topology Bundle
namespace HolomorphicAnosov.FixedBlockEstimates.Native
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original Riemannian norms of vectors in local subbundle frames and of their images under the
restricted derivative of an iterate are continuous. (Zhang, p.1) -/
theorem continuous_restricted_frame_norms {r : ℕ}
    (P : RealTangentDistribution 𝓘(ℝ, E) M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hP : ∀ x, (P x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F x).toLinearMap = P (F x))
    (k : ℕ) :
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
      ‖(e.linearEquivAt ℝ p.1.val p.1.prop).symm p.2‖) ∧
    Continuous (fun p : e.baseSet × (Fin r → ℝ) ↦
      ‖restrictedIterateDerivative F P hP k p.1.val
        ((e.linearEquivAt ℝ p.1.val p.1.prop).symm p.2)‖) := by
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance
  intro e he
  let := he
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  have h := continuous_original_frame_norms P g (realIterate 𝓘(ℝ, E) F k)
    (realIterate 𝓘(ℝ, E) F k).contMDiff e he
  have hn (x : M) (v : P x) :
      ‖restrictedIterateDerivative F P hP k x v‖ =
        ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (realIterate 𝓘(ℝ, E) F k) x v.val‖ := by
    rfl
  simpa only [hn, Submodule.norm_coe] using h

end HolomorphicAnosov.FixedBlockEstimates.Native
