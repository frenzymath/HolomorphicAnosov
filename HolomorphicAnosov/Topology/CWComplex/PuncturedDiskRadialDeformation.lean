import HolomorphicAnosov.Topology.CWComplex.RadialRaySphere
import HolomorphicAnosov.Topology.CWComplex.RadialRayBoundary
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.Normed.Module.Convex
import HolomorphicAnosov.Topology.CWComplex.ContinuousRadialRayParameter

namespace HolomorphicAnosov

/-- The arbitrary-pole punctured-disk deformation used to remove a missed
point from a highest-dimensional cell in Hatcher Theorem 4.8, p.349.
It is jointly continuous, stays in the punctured closed unit disk, ends
on the sphere, and fixes that sphere throughout.

Proof: the radial parameter l is continuous off p by its explicit positive
quadratic-root formula and nonzero denominator. Interpolate between z and
the radial sphere point p+l(z-p). Convexity keeps this in the closed disk.
Its displacement from p is (1-t+t*l)(z-p), whose coefficient is at least
one; thus it never hits p. The radial parameter is one on the boundary,
so the interpolation fixes every boundary point. -/
theorem punctured_disk_radial_deformation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : E) (hp : ‖p‖ < 1) :
    ∃ H : C(unitInterval × {z : E // ‖z‖ ≤ 1 ∧ z ≠ p}, E),
      (∀ z, H (0, z) = z.val) ∧
      (∀ z, ‖H (1, z)‖ = 1) ∧
      (∀ t z, ‖H (t, z)‖ ≤ 1 ∧ H (t, z) ≠ p) ∧
      (∀ t z, ‖z.val‖ = 1 → H (t, z) = z.val) := by
  let D := {z : E // ‖z‖ ≤ 1 ∧ z ≠ p}
  let l (z : D) : ℝ := (-inner ℝ p (z.val-p) +
    Real.sqrt ((inner ℝ p (z.val-p)) ^ 2 +
      (1 - ‖p‖ ^ 2) * ‖z.val-p‖ ^ 2)) / ‖z.val-p‖ ^ 2
  have hl (z : D) : 1 ≤ l z ∧ ‖p + l z • (z.val-p)‖ = 1 :=
    radial_ray_sphere_parameter p z.val hp z.property.1 z.property.2
  have hlcont : Continuous l := (continuous_radial_ray_parameter p).comp
    (continuous_subtype_val.subtype_mk (fun z : D ↦ z.property.2))
  let H : C(unitInterval × D, E) :=
    ⟨fun q ↦ (1 - (q.1 : ℝ)) • q.2.val +
      (q.1 : ℝ) • (p + l q.2 • (q.2.val-p)), by
      have ht : Continuous (fun q : unitInterval × D ↦ (q.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
      have hz : Continuous (fun q : unitInterval × D ↦ q.2.val) := continuous_subtype_val.comp continuous_snd
      exact ((continuous_const.sub ht).smul hz).add
        (ht.smul (continuous_const.add ((hlcont.comp continuous_snd).smul
          (hz.sub continuous_const))))⟩
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro z
    simp [H]
  · intro z
    simpa [H] using (hl z).2
  · intro t z
    change ‖(1 - (t : ℝ)) • z.val + (t : ℝ) • (p + l z • (z.val-p))‖ ≤ 1 ∧ _
    constructor
    · have hz : z.val ∈ Metric.closedBall (0 : E) 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property.1
      have hr : p + l z • (z.val-p) ∈ Metric.closedBall (0 : E) 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right, (hl z).2] using (le_refl (1 : ℝ))
      have hm := (convex_closedBall (0 : E) 1) hz hr
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
      simpa only [Metric.mem_closedBall, dist_zero_right] using hm
    · intro he
      have he' : ((1 - (t : ℝ)) + (t : ℝ) * l z) • (z.val-p) = 0 := by
        change (1 - (t : ℝ)) • z.val + (t : ℝ) • (p + l z • (z.val-p)) = p at he
        calc
          _ = ((1 - (t : ℝ)) • z.val + (t : ℝ) • (p + l z • (z.val-p))) - p := by module
          _ = 0 := sub_eq_zero.mpr he
      have hc : 0 < (1 - (t : ℝ)) + (t : ℝ) * l z := by
        have := mul_nonneg t.property.1 (sub_nonneg.mpr (hl z).1)
        nlinarith
      exact (smul_ne_zero hc.ne' (sub_ne_zero.mpr z.property.2)) he'
  · intro t z hz
    have he : l z = 1 := radial_ray_sphere_parameter_boundary p z.val hp hz
    change (1 - (t : ℝ)) • z.val + (t : ℝ) • (p + l z • (z.val-p)) = z.val
    rw [he]
    module

end HolomorphicAnosov
