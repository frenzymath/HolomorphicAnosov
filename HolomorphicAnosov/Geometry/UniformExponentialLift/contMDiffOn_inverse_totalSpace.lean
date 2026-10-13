import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Geometry.UniformExponentialLift.local_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.compact_metric_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.continuous_metricNorm
import HolomorphicAnosov.Geometry.UniformExponentialLift.isOpen_normalTube
import HolomorphicAnosov.Geometry.UniformExponentialLift.uniform_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.glue_inverse_tube
import HolomorphicAnosov.Geometry.UniformExponentialLift.inverse_tube_laws

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

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The moving-base inverse is smooth on its domain as a map to the tangent bundle.
(Hirsch–Pugh–Shub, p. 62) -/
theorem contMDiffOn_inverse_totalSpace
    (O : Opens (TangentBundle 𝓘(ℝ, E) M)) (B : Opens (M × M))
    (Φ : Diffeomorph (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) O B ∞)
    (L : (q : M) → M → TangentSpace 𝓘(ℝ, E) q)
    (hinv : ∀ y : B, ((Φ.symm y : O) : TangentBundle 𝓘(ℝ, E) M) =
      ⟨y.val.1, L y.val.1 y.val.2⟩) :
    ContMDiffOn ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun y : M × M ↦ (⟨y.1, L y.1 y.2⟩ : TangentBundle 𝓘(ℝ, E) M)) B := by
  have h : ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun y : B ↦ (⟨y.val.1, L y.val.1 y.val.2⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    ((contMDiff_subtype_val (U := O)).comp Φ.symm.contMDiff).congr (fun y ↦ (hinv y).symm)
  intro y hy
  exact ((contMDiffAt_subtype_iff (f := fun y : M × M ↦
    (⟨y.1, L y.1 y.2⟩ : TangentBundle 𝓘(ℝ, E) M))).mp (h ⟨y, hy⟩)).contMDiffWithinAt


end ExponentialLift
end HolomorphicAnosov
