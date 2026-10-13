import HolomorphicAnosov.Topology.AnnulusBoundaryExtension
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Prescribed inner boundary correction on a closed annulus

Source: Hirsch, Differential Topology (1976), p.155, radial extension formula,
as used in Cairns (1951), preliminary 2(B), p.860. This packages the final
boundary-correction step of the polygonal-annulus parameterization.
DAG node: `topo.cairns_annulus_boundary_correction_g6`.
-/

open Set
namespace HolomorphicAnosov.Topology

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- Given any annulus parameterization whose inner boundary is a homeomorphism
`γ` onto the unit circle, postcompose with the radial extension carrying `γ` to
a prescribed boundary homeomorphism `β`. The outer boundary remains the radius
2 circle as a set.

Source: Hirsch p.155 radial formula, through the existing public
`annulus_boundary_extension`. The correction is `F ∘ Ψ`, where `F` preserves
radius and restricts on the unit circle to `β ∘ γ⁻¹`; norm preservation gives the
outer-circle image and the boundary equations. No isotopy or outer pointwise map
is assumed.
-/
theorem cairns_annulus_boundary_correction
    {D R : Set Plane}
    {γ : frontier D ≃ₜ Metric.sphere (0 : Plane) 1}
    {Ψ : ↥(R \ interior D) ≃ₜ {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}}
    (hinner : ∀ x : frontier D, ∃ y : ↥(R \ interior D),
      (y : Plane) = (x : Plane) ∧ (Ψ y : Plane) = (γ x : Plane))
    (houter : (fun x : ↥(R \ interior D) ↦ (Ψ x : Plane)) ''
      {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
        Metric.sphere (0 : Plane) 2)
    (β : frontier D ≃ₜ Metric.sphere (0 : Plane) 1) :
    ∃ Φ : ↥(R \ interior D) ≃ₜ {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
      (∀ x : frontier D, ∃ y : ↥(R \ interior D),
        (y : Plane) = (x : Plane) ∧ (Φ y : Plane) = (β x : Plane)) ∧
      (fun x : ↥(R \ interior D) ↦ (Φ x : Plane)) ''
        {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} = Metric.sphere (0 : Plane) 2 := by
  obtain ⟨F, hnorm, hboundary⟩ := annulus_boundary_extension (γ.symm.trans β)
  refine ⟨Ψ.trans F, ?_, ?_⟩
  · intro x
    obtain ⟨y, hy, hΨy⟩ := hinner x
    refine ⟨y, hy, ?_⟩
    have hγ : 1 ≤ ‖(γ x : Plane)‖ ∧ ‖(γ x : Plane)‖ ≤ 2 := by
      rw [mem_sphere_zero_iff_norm.mp (γ x).property]
      norm_num
    have hΨ : Ψ y = ⟨γ x, hγ⟩ := Subtype.ext hΨy
    change (F (Ψ y) : Plane) = _
    rw [hΨ, hboundary]
    simp
  · apply Set.ext
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hz : (Ψ x : Plane) ∈ Metric.sphere (0 : Plane) 2 := by
        rw [← houter]
        exact ⟨x, hx, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hz ⊢
      exact (hnorm (Ψ x)).trans hz
    · intro hz
      have hz2 : ‖z‖ = 2 := mem_sphere_zero_iff_norm.mp hz
      let w : {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := ⟨z, by simp [hz2]⟩
      have hw : (F.symm w : Plane) ∈ Metric.sphere (0 : Plane) 2 := by
        rw [mem_sphere_zero_iff_norm]
        have hn := hnorm (F.symm w)
        rw [F.apply_symm_apply] at hn
        exact hn.symm.trans hz2
      rw [← houter] at hw
      obtain ⟨x, hx, he⟩ := hw
      refine ⟨x, hx, ?_⟩
      have he' : Ψ x = F.symm w := Subtype.ext he
      change (F (Ψ x) : Plane) = z
      rw [he', F.apply_symm_apply]

end HolomorphicAnosov.Topology

