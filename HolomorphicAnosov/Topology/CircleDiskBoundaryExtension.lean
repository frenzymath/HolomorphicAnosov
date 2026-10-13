import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Extending circle homeomorphisms over the disk

The explicit radial construction from Hirsch, *Differential Topology* (1976),
printed p.155, supplies the normalized boundary-extension step of Cairns (1951),
§2(A), printed p.860. DAG node: `topo.circle_disk_boundary_extension_g6`.
-/

noncomputable section
open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- A circle homeomorphism extends to a homeomorphism of the closed unit disk.

Source: Hirsch, *Differential Topology* (1976), printed p.155, the displayed
radial-extension formula in the proof ending there; Cairns (1951), §2(A), p.860.
Define the extension at zero to be zero and at a nonzero point `z` to be
`‖z‖ • b (‖z‖⁻¹ • z)`. It preserves the radius. The same formula with `b.symm`
is its inverse. Away from zero continuity follows by normalization, continuity
of `b`, and scalar multiplication; at zero radius preservation proves continuity.
Restricting to radius at most one gives the disk homeomorphism, and radius one
gives the prescribed boundary values. No orientation assumption is needed.
-/
theorem circle_disk_boundary_extension (b : Circle ≃ₜ Circle) :
    ∃ F : Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall (0 : ℂ) 1,
      ∀ z : Circle, (F ⟨z, by simp⟩ : ℂ) = b z := by
  classical
  let direction (z : ℂ) (hz : z ≠ 0) : Circle :=
    ⟨‖z‖⁻¹ • z, by
      change ‖z‖⁻¹ • z ∈ Metric.sphere (0 : ℂ) 1
      rw [Metric.mem_sphere, dist_zero_right]
      simp [norm_ne_zero_iff.mpr hz]⟩
  let radial (a : Circle ≃ₜ Circle) (z : ℂ) : ℂ :=
    if hz : z = 0 then 0 else ‖z‖ • (a (direction z hz) : ℂ)
  have hnorm (a : Circle ≃ₜ Circle) (z : ℂ) : ‖radial a z‖ = ‖z‖ := by
    by_cases hz : z = 0
    · simp [radial, hz]
    · simp [radial, hz]
  have hzero (a : Circle ≃ₜ Circle) : radial a 0 = 0 := by simp [radial]
  have hboundary (a : Circle ≃ₜ Circle) (z : Circle) : radial a z = a z := by
    have hz : (z : ℂ) ≠ 0 := by
      intro h
      have := z.norm_coe
      simp [h] at this
    have hd : direction z hz = z := by
      apply Subtype.ext
      simp [direction]
    simp [radial, hz, hd]
  have hinverse (a : Circle ≃ₜ Circle) (z : ℂ) : radial a.symm (radial a z) = z := by
    by_cases hz : z = 0
    · simp [hz, hzero]
    have hr : radial a z ≠ 0 := by
      intro h
      have := hnorm a z
      exact (norm_ne_zero_iff.mpr hz) (by simpa [h] using this.symm)
    have hd : direction (radial a z) hr = a (direction z hz) := by
      apply Subtype.ext
      change ‖radial a z‖⁻¹ • radial a z = _
      rw [hnorm]
      change ‖z‖⁻¹ • (if h : z = 0 then 0 else ‖z‖ • (a (direction z h) : ℂ)) = _
      rw [dite_eq_right hz]
      exact inv_smul_smul₀ (norm_ne_zero_iff.mpr hz) _
    change (if h : radial a z = 0 then 0 else
      ‖radial a z‖ • (a.symm (direction (radial a z) h) : ℂ)) = z
    rw [dite_eq_right hr, hd, a.symm_apply_apply, hnorm]
    exact smul_inv_smul₀ (norm_ne_zero_iff.mpr hz) z
  have hcont (a : Circle ≃ₜ Circle) : Continuous (radial a) := by
    have hdir : Continuous (fun z : {z : ℂ // z ≠ 0} ↦ direction z z.property) := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.norm.inv₀ (fun z ↦ norm_ne_zero_iff.mpr z.property)).smul
        continuous_subtype_val
    have hnz : ContinuousOn (radial a) {z : ℂ | z ≠ 0} := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun z : {z : ℂ // z ≠ 0} ↦
          ‖(z : ℂ)‖ • (a (direction z z.property) : ℂ)) :=
        continuous_subtype_val.norm.smul (a.continuous.comp hdir).subtype_val
      apply hc.congr
      intro z
      simp [Set.domRestrict, radial, z.property]
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z
      change Tendsto (radial a) (𝓝 0) (𝓝 (radial a 0))
      rw [hzero]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [hnorm, norm_zero] using (continuous_norm.tendsto (0 : ℂ))
    · exact hnz.continuousAt ((isClosed_singleton.isOpen_compl).mem_nhds hz)
  let F : Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall (0 : ℂ) 1 :=
    { toFun := fun z ↦ ⟨radial b z, by simpa only [Metric.mem_closedBall, dist_zero_right, hnorm] using z.property⟩
      invFun := fun z ↦ ⟨radial b.symm z, by simpa only [Metric.mem_closedBall, dist_zero_right, hnorm] using z.property⟩
      left_inv := fun z ↦ Subtype.ext (hinverse b z)
      right_inv := fun z ↦ Subtype.ext (hinverse b.symm z)
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (hcont b).comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (hcont b.symm).comp continuous_subtype_val }
  exact ⟨F, fun z ↦ hboundary b z⟩

end HolomorphicAnosov
