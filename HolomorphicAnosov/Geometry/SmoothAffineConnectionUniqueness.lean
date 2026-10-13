import HolomorphicAnosov.Geometry.SmoothAffineConnection
import HolomorphicAnosov.Geometry.SmoothAffineConnectionKoszul
import HolomorphicAnosov.Geometry.SmoothOpenInclusionDifferentialInjective
import HolomorphicAnosov.Geometry.SmoothVectorFieldValue
import Mathlib.Tactic.LinearCombination

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- Two genuine smooth torsion-free compatible connections are equal on every open set. Source: Andrews, Lecture10, Proposition10.3.1, p.97. -/
theorem SmoothAffineConnection.eq_of_torsionFree_metricCompatible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (nabla other : SmoothAffineConnection E M)
    (ht : nabla.IsTorsionFree) (hg : nabla.IsMetricCompatible g)
    (ht' : other.IsTorsionFree) (hg' : other.IsMetricCompatible g) : other = nabla := by
  have hcov : other.cov = nabla.cov := by
    funext U
    apply LinearMap.ext
    intro X
    apply LinearMap.ext
    intro Y
    apply ContMDiffSection.ext
    intro p
    let v := other.cov U X Y p - nabla.cov U X Y p
    obtain ⟨Z, hZ⟩ := exists_smooth_vectorField_value (M := U) p v
    have h1 := nabla.koszul_of_torsionFree_metricCompatible g ht hg U X Y Z p
    have h2 := other.koszul_of_torsionFree_metricCompatible g ht' hg' U X Y Z p
    dsimp only at h1 h2
    have hp := h2.trans h1.symm
    have hpair := (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hp)
    let d := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun q : U ↦ (q : M)) p
    have hvzero : g.inner p.1 (d v) (d v) = 0 := by
      have hpair' : g.inner p.1 (d (other.cov U X Y p)) (d (Z p)) =
          g.inner p.1 (d (nabla.cov U X Y p)) (d (Z p)) := hpair
      rw [hZ] at hpair'
      dsimp [v] at *
      simp only [map_sub, sub_apply] at *
      linear_combination hpair'
    have hv : v = 0 := by
      by_contra hv
      have hpos := g.pos p.1 (d v) (fun hd ↦ hv
        ((smooth_open_inclusion_mfderiv_injective U p) (hd.trans (map_zero d).symm)))
      exact (ne_of_gt hpos) hvzero
    exact sub_eq_zero.mp hv
  cases other
  cases nabla
  congr


end
end HolomorphicAnosov
