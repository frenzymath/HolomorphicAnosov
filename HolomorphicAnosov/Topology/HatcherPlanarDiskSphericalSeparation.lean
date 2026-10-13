import HolomorphicAnosov.Topology.CompactRetractComplementConnected
import HolomorphicAnosov.Topology.EmbeddedUnitDiskBoundarySphericalSeparation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Tietze

namespace HolomorphicAnosov


/-- Transport of the embedded-disk boundary separation to a positive-radius
Euclidean disk by translation, dilation, and orthonormal complex coordinates. -/
theorem embedded_euclidean_disk_boundary_sphere_not_preconnected
    (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r)
    (gc : Metric.closedBall x r → ℂ)
    (hgc : Continuous gc) (hinj : Function.Injective gc) :
    let B : Set (Metric.closedBall x r) := {z | z.val ∈ Metric.ball x r}
    ¬ IsPreconnected (OnePoint.some '' (gc '' Bᶜ))ᶜ := by
  intro B
  let e := Complex.orthonormalBasisOneI.repr
  let d := (DilationEquiv.smulTorsor x (k := r) hr.ne').toHomeomorph
  let h : Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall x r :=
    (e.toHomeomorph.trans d).sets (by
      ext z
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
      change ‖z‖ ≤ 1 ↔ dist (r • e z + x) x ≤ r
      rw [dist_add_self_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr, e.norm_map]
      exact (mul_le_iff_le_one_right hr).symm)
  have hboundary : h '' {z | ‖z.val‖ = 1} = Bᶜ := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      change ¬ dist (r • e z.val + x) x < r
      rw [dist_add_self_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr, e.norm_map]
      change ‖z.val‖ = 1 at hz
      rw [hz, mul_one]
      exact lt_irrefl r
    · intro z hz
      refine ⟨h.symm z, ?_, h.apply_symm_apply z⟩
      have hclosed := (h.symm z).property
      have hnorm : ‖(h.symm z).val‖ ≤ 1 := by
        change dist (h.symm z).val 0 ≤ 1 at hclosed
        simpa only [dist_zero_right] using hclosed
      have hout : ¬ r * ‖(h.symm z).val‖ < r := by
        have hz' : ¬ dist (h (h.symm z)).val x < r := by
          change ¬ dist z.val x < r at hz
          simpa only [h.apply_symm_apply] using hz
        change ¬ dist (r • e (h.symm z).val + x) x < r at hz'
        simpa only [dist_add_self_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
          e.norm_map] using hz'
      change ‖(h.symm z).val‖ = 1
      nlinarith
  have hs := embedded_unit_disk_boundary_sphere_not_preconnected
    (fun z ↦ gc (h z)) (hgc.comp h.continuous) (hinj.comp h.injective)
  have heq : (fun z ↦ gc (h z)) '' {z | ‖z.val‖ = 1} = gc '' Bᶜ := by
    rw [← Set.image_image, hboundary]
  rwa [heq] at hs

namespace Topology

/-- Hatcher's planar disk separation theorem in the one-point compactification.

Source statement: Hatcher, Algebraic Topology, Proposition 2B.1(a,b), pp.169–170.
The following alternative planar proof is agent-written. The compact injective
disk image is a retract of the plane: Tietze extension into the source closed
ball extends the inverse of the embedding. Its sphere complement is preconnected
by the compact-retract theorem, which excludes bounded complementary components
using bounded Euclidean fixed-point existence. For the boundary, scale and
translate the source disk to the complex unit disk. The boundary loop's winding
about the center image is nonzero by the odd-loop radial homotopy. Its winding
about a point outside the full image is zero by contraction through the disk.
A preconnected spherical complement would give an omitted-value plane path
between these two points, contradicting constancy of winding. -/
theorem hatcher_planar_disk_spherical_separation
    (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r)
    (gc : Metric.closedBall x r → ℂ)
    (hgc : Continuous gc) (hinj : Function.Injective gc) :
    let B : Set (Metric.closedBall x r) := {z | z.val ∈ Metric.ball x r}
    IsPreconnected (OnePoint.some '' Set.range gc)ᶜ ∧
      ¬ IsPreconnected (OnePoint.some '' (gc '' Bᶜ))ᶜ := by
  intro B
  refine ⟨?_, embedded_euclidean_disk_boundary_sphere_not_preconnected x r hr gc hgc hinj⟩
  have : TietzeExtension (Metric.closedBall x r) :=
    Metric.instTietzeExtensionClosedBall ℝ x hr
  obtain ⟨q, hq⟩ := (ContinuousMap.id (Metric.closedBall x r)).exists_extension
    (hgc.isClosedEmbedding hinj)
  let R : C(ℂ, ℂ) := ⟨fun z ↦ gc (q z), hgc.comp q.continuous⟩
  apply compact_retract_sphere_complement_preconnected (Set.range gc)
    (isCompact_range hgc) R
  · rintro z ⟨w, rfl⟩
    exact ⟨q w, rfl⟩
  · rintro z ⟨w, rfl⟩
    have heq : q (gc w) = w := congrArg (fun f ↦ f w) hq
    change gc (q (gc w)) = gc w
    rw [heq]


end Topology

end HolomorphicAnosov
