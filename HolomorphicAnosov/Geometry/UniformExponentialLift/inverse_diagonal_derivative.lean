import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Geometry.UniformExponentialLift.local_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.compact_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuous_metricNorm
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_normalTube
import HolomorphicAnosov.Geometry.UniformExponentialLift.uniform_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.glue_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.inverse_tube_laws
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_inverse_totalSpace
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_centered_totalSpace
import HolomorphicAnosov.Geometry.UniformExponentialLift.contMDiffOn_centered_frame
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_centered_frame_domain
import HolomorphicAnosov.Geometry.UniformExponentialLift.centered_radius
import HolomorphicAnosov.Geometry.UniformExponentialLift.vertical_jet_restriction
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuousOn_vertical_jets
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuousOn_manifold_vertical_jets
import HolomorphicAnosov.Geometry.UniformExponentialLift.tangent_frame_self
import HolomorphicAnosov.Geometry.UniformExponentialLift.centered_vertical_jets
import HolomorphicAnosov.Geometry.UniformExponentialLift.fixed_fibre_contMDiff
import HolomorphicAnosov.Geometry.UniformExponentialLift.inverse_fibre_contMDiffOn

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

/-- The differential of the inverse exponential map at the diagonal is the identity
under the tangent-space identifications. -/
theorem inverse_diagonal_derivative
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (O : Opens (TangentBundle 𝓘(ℝ, E) M)) (B : Opens (M × M))
    (Φ : Diffeomorph (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) O B ∞)
    (L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q)
    (hinv : ∀ y : B, ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M) =
      ⟨y.val.1, L y.val.1 y.val.2⟩)
    (hLexp : ∀ (q : M) (v : TangentSpace 𝓘(ℝ, E) q),
      (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ O → L q (riemannianExp g q v) = v)
    (q : M) (hzeroO : (⟨q, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ O)
    (hdiag : (q, q) ∈ B) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun w ↦ tangentSpaceCastModel 𝓘(ℝ, E) q (L q w)) q =
      (NormedSpace.fromTangentSpace
        (tangentSpaceCastModel 𝓘(ℝ, E) q (L q q))).symm.toContinuousLinearMap ∘L
        (tangentSpaceCastModel 𝓘(ℝ, E) q).toContinuousLinearMap := by
  let c := tangentSpaceCastModel 𝓘(ℝ, E) q
  let ep : E → M := fun v ↦ riemannianExp g q (c.symm v)
  let lq : M → E := fun w ↦ c (L q w)
  have hexp := riemannian_exponential_local_addition g
  have hep0 : ep 0 = q := by simpa [ep, riemannianExp] using hexp.2.2.2.1 q
  have hi := (fixed_fibre_contMDiff q).contMDiffAt (x := (0 : E))
  have he : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 :=
    ((hexp.2.2.1.contMDiffAt (hexp.1.mem_nhds (by
      simpa only [map_zero] using hexp.2.1 q))).comp 0 hi).mdifferentiableAt (by simp)
  have hl : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) lq q :=
    ((inverse_fibre_contMDiffOn O B Φ L hinv q).contMDiffAt
      ((B.isOpen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hdiag)).mdifferentiableAt
      (by simp)
  have heq : lq ∘ ep =ᶠ[𝓝 (0 : E)] id := by
    have hzO : (⟨q, (tangentSpaceCastModel 𝓘(ℝ, E) q).symm (0 : E)⟩ :
        TangentBundle 𝓘(ℝ, E) M) ∈ O := by simpa only [map_zero] using hzeroO
    have hn := hi.continuousAt.preimage_mem_nhds (O.isOpen.mem_nhds hzO)
    filter_upwards [hn] with v hv
    simp only [Function.comp_def, ep, lq]
    rw [hLexp q (c.symm v) hv, c.apply_symm_apply]
    rfl
  have hcomp := mfderiv_comp_of_eq (x := (0 : E)) hl he hep0
  have hder : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (lq ∘ ep) 0 =
      ContinuousLinearMap.id ℝ E := by
    rw [heq.mfderiv_eq, mfderiv_id]
    rfl
  ext v
  have hv := congrArg (fun k ↦ k (c v)) (hcomp.symm.trans hder)
  have hevert := hexp.2.2.2.2.1 q (c v)
  have hev : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 (c v) = v := by
    apply c.injective
    rw [hexp.2.2.2.1 q] at hevert
    change c (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 (c v)) = c v at hevert
    exact hevert
  rw [hep0] at hv
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) lq q
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 (c v)) = c v at hv
  rw [hev] at hv
  exact hv


end ExponentialLift
end HolomorphicAnosov
