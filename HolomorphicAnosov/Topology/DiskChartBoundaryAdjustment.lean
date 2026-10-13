import HolomorphicAnosov.Topology.CircleDiskBoundaryExtension
import HolomorphicAnosov.Topology.ClosedBallHomeoImageBallBoundary

open Set Metric

namespace HolomorphicAnosov

/-- A disk chart can be adjusted to any prescribed boundary correspondence while
preserving the subset it maps to the open disk.

Source: Hirsch, Differential Topology (1976), printed p.155, radial extension,
as used in Cairns (1951), §4(D), equation (4.5), pp.865–866. Restrict the given
chart to the boundary, conjugate the prescribed map by this restriction, and
extend that circle homeomorphism radially. Postcompose the original chart.
The extension preserves the boundary and hence its complement, the open disk. -/
theorem disk_chart_boundary_adjustment
    (K C R : Set ℂ) (hCK : C ⊆ K)
    (H₀ : K ≃ₜ closedBall (0 : ℂ) 1)
    (hR : H₀ '' {z : K | (z : ℂ) ∈ R} =
      {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ ball (0 : ℂ) 1})
    (hC : H₀ '' {z : K | (z : ℂ) ∈ C} =
      {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ sphere (0 : ℂ) 1})
    (h : C ≃ₜ sphere (0 : ℂ) 1) :
    ∃ H : K ≃ₜ closedBall (0 : ℂ) 1,
      H '' {z : K | (z : ℂ) ∈ R} =
        {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ ball (0 : ℂ) 1} ∧
      ∀ z : K, ∀ hz : (z : ℂ) ∈ C,
        (H z : ℂ) = (h ⟨(z : ℂ), hz⟩ : ℂ) := by
  have hforward (z : K) (hz : (z : ℂ) ∈ C) :
      (H₀ z : ℂ) ∈ sphere (0 : ℂ) 1 := by
    have hi : H₀ z ∈ H₀ '' {z : K | (z : ℂ) ∈ C} := ⟨z, hz, rfl⟩
    rw [hC] at hi
    exact hi
  have hback (w : sphere (0 : ℂ) 1) :
      (H₀.symm ⟨w, sphere_subset_closedBall w.property⟩ : ℂ) ∈ C := by
    have hi : (⟨w, sphere_subset_closedBall w.property⟩ : closedBall (0 : ℂ) 1) ∈
        H₀ '' {z : K | (z : ℂ) ∈ C} := by
      rw [hC]
      exact w.property
    rcases hi with ⟨z, hz, heq⟩
    rw [← heq, H₀.symm_apply_apply]
    exact hz
  let b : C ≃ₜ sphere (0 : ℂ) 1 :=
    { toFun := fun z ↦ ⟨H₀ ⟨z, hCK z.property⟩, hforward _ z.property⟩
      invFun := fun w ↦ ⟨H₀.symm ⟨w, sphere_subset_closedBall w.property⟩, hback w⟩
      left_inv := by
        intro z
        apply Subtype.ext
        exact congrArg (fun t : K ↦ (t : ℂ)) (H₀.symm_apply_apply ⟨z, hCK z.property⟩)
      right_inv := by
        intro w
        apply Subtype.ext
        exact congrArg (fun t : closedBall (0 : ℂ) 1 ↦ (t : ℂ))
          (H₀.apply_symm_apply ⟨w, sphere_subset_closedBall w.property⟩)
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  let k : Circle ≃ₜ Circle := b.symm.trans h
  obtain ⟨E, hE⟩ := circle_disk_boundary_extension k
  have hEB : E '' {z : closedBall (0 : ℂ) 1 | (z : ℂ) ∈ sphere (0 : ℂ) 1} =
      {z : closedBall (0 : ℂ) 1 | (z : ℂ) ∈ sphere (0 : ℂ) 1} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (E z : ℂ) ∈ sphere (0 : ℂ) 1
      have heq := hE (⟨z, hz⟩ : Circle)
      change (E z : ℂ) = _ at heq
      rw [heq]
      exact (k ⟨z, hz⟩).property
    · intro hw
      obtain ⟨z, hz⟩ := k.surjective (⟨w, hw⟩ : Circle)
      refine ⟨⟨z, sphere_subset_closedBall z.property⟩, z.property, ?_⟩
      apply Subtype.ext
      exact (hE z).trans (congrArg Subtype.val hz)
  refine ⟨H₀.trans E, ?_, ?_⟩
  · change (fun z : K ↦ E (H₀ z)) '' _ = _
    rw [← Set.image_image E H₀, hR]
    exact closedBall_homeo_image_ball_of_boundary E hEB
  · intro z hz
    change (E (H₀ z) : ℂ) = (h ⟨z, hz⟩ : ℂ)
    have hval := hE (b ⟨z, hz⟩)
    change (E (H₀ z) : ℂ) = _ at hval
    change (E (H₀ z) : ℂ) = (h (b.symm (b ⟨z, hz⟩)) : ℂ) at hval
    simpa only [b.symm_apply_apply] using hval

end HolomorphicAnosov
