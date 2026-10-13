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
import HolomorphicAnosov.Geometry.UniformExponentialLift.inverse_diagonal_derivative

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

/-- The fiber differential of the centered lift at zero equals the derivative of `f`.
(Hirsch–Pugh–Shub, p. 62) -/
theorem centered_derivative_zero
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : M → M) (r : ℕ∞) (hr : 1 ≤ r) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r f)
    (O : Opens (TangentBundle 𝓘(ℝ, E) M)) (B : Opens (M × M))
    (Φ : Diffeomorph (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) O B ∞)
    (L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q)
    (hinv : ∀ y : B, ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M) =
      ⟨y.val.1, L y.val.1 y.val.2⟩)
    (hLexp : ∀ (q : M) (v : TangentSpace 𝓘(ℝ, E) q),
      (⟨q, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ O → L q (riemannianExp g q v) = v)
    (p : M) (hzeroO : (⟨f p, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ O)
    (hdiag : (f p, f p) ∈ B) :
    HasFDerivAt
      (fun u : E ↦ tangentSpaceCastModel 𝓘(ℝ, E) (f p)
        (centeredLift g f L p ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm u)))
      ((tangentSpaceCastModel 𝓘(ℝ, E) (f p)).toContinuousLinearMap ∘L
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p ∘L
        (tangentSpaceCastModel 𝓘(ℝ, E) p).symm.toContinuousLinearMap) 0 := by
  let c := tangentSpaceCastModel 𝓘(ℝ, E) p
  let d := tangentSpaceCastModel 𝓘(ℝ, E) (f p)
  let ep : E → M := fun v ↦ riemannianExp g p (c.symm v)
  let lq : M → E := fun w ↦ d (L (f p) w)
  have hexp := riemannian_exponential_local_addition g
  have hep0 : ep 0 = p := by simpa [ep, riemannianExp] using hexp.2.2.2.1 p
  have hi := (fixed_fibre_contMDiff p).contMDiffAt (x := (0 : E))
  have he : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 :=
    ((hexp.2.2.1.contMDiffAt (hexp.1.mem_nhds (by
      simpa only [map_zero] using hexp.2.1 p))).comp 0 hi).mdifferentiableAt (by simp)
  have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ∞) < 1) hr)
  have hfp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) f p :=
    hf.mdifferentiable (WithTop.coe_ne_zero.mpr hr0) p
  have hl : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) lq (f p) :=
    ((inverse_fibre_contMDiffOn O B Φ L hinv (f p)).contMDiffAt
      ((B.isOpen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hdiag)).mdifferentiableAt
      (by simp)
  have hfe : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (f ∘ ep) 0 :=
    hfp.comp_of_eq 0 he hep0
  have hfe0 : (f ∘ ep) 0 = f p := congrArg f hep0
  have hH := hl.comp_of_eq 0 hfe hfe0
  apply hH.hasMFDerivAt.hasFDerivAt.congr_fderiv
  rw [mfderiv_comp_of_eq (x := (0 : E)) hl hfe hfe0,
    mfderiv_comp_of_eq (x := (0 : E)) hfp he hep0]
  rw [hfe0, hep0]
  have hd := inverse_diagonal_derivative g O B Φ L hinv hLexp (f p) hzeroO hdiag
  ext v
  have hev := hexp.2.2.2.2.1 p v
  rw [hexp.2.2.2.1 p] at hev
  have hevv : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 v = c.symm v := by
    apply c.injective
    change c (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 v) = v at hev
    simpa only [c.apply_symm_apply] using (hev.trans (c.apply_symm_apply v).symm)
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) lq (f p)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ep 0 v)) =
      d (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p (c.symm v))
  rw [hevv]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
    (fun w ↦ tangentSpaceCastModel 𝓘(ℝ, E) (f p) (L (f p) w)) (f p) _ = _
  rw [hd]
  rfl


end ExponentialLift
end HolomorphicAnosov
