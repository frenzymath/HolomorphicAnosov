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
import HolomorphicAnosov.Geometry.ContinuousRestrictedFrameNorms

noncomputable section
open Bundle Set Filter
open scoped ContDiff Manifold Topology _root_.Topology Bundle
namespace HolomorphicAnosov.FixedBlockEstimates.Native
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A strict bound on the operator norm of a restricted iterate derivative persists in a
neighborhood of the basepoint. (Zhang, p.1) -/
theorem restricted_opNorm_eventually_lt
    (P : ContinuousRealTangentSubbundle 𝓘(ℝ, E) M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hP : ∀ x, (P.toDistribution x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F x).toLinearMap =
      P.toDistribution (F x)) (k : ℕ) (x : M) {c : ℝ} :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) :=
      ⟨g.toRiemannianMetric⟩
    ‖(restrictedIterateDerivative F P.toDistribution hP k x).toContinuousLinearMap‖ < c →
    ∀ᶠ y in 𝓝 x,
      ‖(restrictedIterateDerivative F P.toDistribution hP k y).toContinuousLinearMap‖ < c := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ, E) y) :=
    ⟨g.toRiemannianMetric⟩
  intro hc
  obtain ⟨r, e, hx, he⟩ := P.locally_trivial x
  let : TopologicalSpace (TotalSpace (Fin r → ℝ) (fun y : M ↦ ↥(P.toDistribution y))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance
  let := he
  have hs := continuous_restricted_frame_norms P.toDistribution g F hP k e he
  have hlocal := HolomorphicAnosov.moving_operator_norm_eventually_lt
    (fun y : e.baseSet ↦ (e.linearEquivAt ℝ y.val y.prop).symm)
    (fun y : e.baseSet ↦
      (restrictedIterateDerivative F P.toDistribution hP k y.val).toContinuousLinearMap)
    hs.1 hs.2 (⟨x, hx⟩ : e.baseSet) hc
  have hnhds : Filter.map (Subtype.val : e.baseSet → M) (𝓝 (⟨x, hx⟩ : e.baseSet)) =
      𝓝 x := map_nhds_subtype_coe_eq_nhds hx (e.open_baseSet.mem_nhds hx)
  rw [← hnhds]
  exact hlocal

end HolomorphicAnosov.FixedBlockEstimates.Native
