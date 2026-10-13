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

/-- The centered lift is `C^r` in tangent-frame coordinates on its domain.
(Hirsch–Pugh–Shub, p. 62) -/
theorem contMDiffOn_centered_frame
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (f : M → M) (r : ℕ∞) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r f)
    (O : Opens (TangentBundle 𝓘(ℝ, E) M)) (B : Opens (M × M))
    (Φ : Diffeomorph (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) O B ∞)
    (L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q)
    (hinv : ∀ y : B, ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M) =
      ⟨y.val.1, L y.val.1 y.val.2⟩) (s t : M) :
    let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
    let e' := trivializationAt E (TangentSpace 𝓘(ℝ, E)) t
    let Z : M × E → TangentBundle 𝓘(ℝ, E) M :=
      fun z ↦ ⟨z.1, e.symmL ℝ z.1 z.2⟩
    let D : Set (M × E) := {z | z.1 ∈ e.baseSet ∧ f z.1 ∈ e'.baseSet ∧
      Z z ∈ riemannianExpDomain g ∧
        (f z.1, f (riemannianExp g z.1 (e.symmL ℝ z.1 z.2))) ∈ B}
    ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) r
      (fun z : M × E ↦ e'.continuousLinearMapAt ℝ (f z.1)
        (centeredLift g f L z.1 (e.symmL ℝ z.1 z.2))) D := by
  dsimp only
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
  let e' := trivializationAt E (TangentSpace 𝓘(ℝ, E)) t
  let Z : M × E → TangentBundle 𝓘(ℝ, E) M := fun z ↦ ⟨z.1, e.symmL ℝ z.1 z.2⟩
  let D : Set (M × E) := {z | z.1 ∈ e.baseSet ∧ f z.1 ∈ e'.baseSet ∧
    Z z ∈ riemannianExpDomain g ∧
      (f z.1, f (riemannianExp g z.1 (e.symmL ℝ z.1 z.2))) ∈ B}
  have horder : (r : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hZ : ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent r Z D := by
    refine (e.contMDiffOn_symm.of_le horder).comp contMDiffOn_id ?_ |>.congr ?_
    · intro z hz
      exact e.mem_target.mpr hz.1
    · intro z hz
      change Z z = e.toOpenPartialHomeomorph.symm (z.1, z.2)
      rw [e.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) z.1 hz.1]
      simp only [Z, Trivialization.symmL_apply, hz.1,
        Trivialization.continuousLinearEquivAt_symm_apply]
  let H : TangentBundle 𝓘(ℝ, E) M → TangentBundle 𝓘(ℝ, E) M :=
    fun z ↦ ⟨f z.proj, centeredLift g f L z.proj z.snd⟩
  have hH : ContMDiffOn (𝓘(ℝ, E)).tangent (𝓘(ℝ, E)).tangent r H
      (riemannianExpDomain g ∩ (fun z : TangentBundle 𝓘(ℝ, E) M ↦
        (f z.proj, f (riemannianExp g z.proj z.snd))) ⁻¹' (B : Set _)) :=
    contMDiffOn_centered_totalSpace g f r hf O B Φ L hinv
  have hHZ : ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent r
      (H ∘ Z) D := hH.comp hZ (fun z hz ↦ ⟨hz.2.2.1, hz.2.2.2⟩)
  have hcoord := (e'.contMDiffOn_iff (fun z hz ↦ e'.mem_source.mpr hz.2.1)).mp hHZ
  exact hcoord.2.congr (fun z hz ↦ by
    change e'.continuousLinearMapAt ℝ (f z.1)
      (centeredLift g f L z.1 (e.symmL ℝ z.1 z.2)) =
        (e' ⟨f z.1, centeredLift g f L z.1 (e.symmL ℝ z.1 z.2)⟩).2
    simp only [Trivialization.continuousLinearMapAt_apply]
    simp [Trivialization.linearMapAt_apply, hz.2.1])


end ExponentialLift
end HolomorphicAnosov
