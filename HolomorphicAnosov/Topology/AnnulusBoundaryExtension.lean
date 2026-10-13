import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Extending a sphere homeomorphism over a closed annulus

The radial formula is the annular version of Hirsch, Differential Topology (1976),
p.155, used for the prescribed boundary in Cairns (1951), preliminary 2(B), p.860.
-/

namespace HolomorphicAnosov
open Set

/-- Every homeomorphism of the unit sphere of a real normed space extends over
its closed annulus of radii one and two, preserving the norm at every point.

Source: Hirsch, Differential Topology (1976), p.155, radial extension formula.
Use polar coordinates on the punctured space, apply the sphere homeomorphism to
its first factor and leave the positive radius fixed, and return to Cartesian
coordinates. This is a homeomorphism with inverse given by the inverse sphere
map. Since the norm is unchanged, both maps restrict to the closed annulus.
On the unit sphere normalization and multiplication by the radius are identities.
The argument includes empty spheres and makes no finite-dimensional assumption. -/
theorem annulus_boundary_extension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1) :
    ∃ F : {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} ≃ₜ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
      (∀ x, ‖(F x : E)‖ = ‖(x : E)‖) ∧
      ∀ z : Metric.sphere (0 : E) 1,
        ∀ hz : 1 ≤ ‖(z : E)‖ ∧ ‖(z : E)‖ ≤ 2,
          (F ⟨z, hz⟩ : E) = (b z : E) := by
  let e := homeomorphUnitSphereProd E
  let h := e.trans ((b.prodCongr (Homeomorph.refl (Ioi (0 : ℝ)))).trans e.symm)
  have hn (x : ({0}ᶜ : Set E)) : ‖(h x : E)‖ = ‖(x : E)‖ := by
    simp [h, e, norm_smul,
      mem_sphere_zero_iff_norm.mp (b (e x).1).property]
  have hin (x : {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}) : (x : E) ∈ ({0}ᶜ : Set E) := by
    change (x : E) ≠ 0
    intro hx
    have := x.property.1
    norm_num [hx] at this
  let F : {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} ≃ₜ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} :=
    { toFun := fun x ↦ ⟨h ⟨x, hin x⟩, by change 1 ≤ ‖(h ⟨x, hin x⟩ : E)‖ ∧ _; rw [hn]; exact x.property⟩
      invFun := fun x ↦ ⟨h.symm ⟨x, hin x⟩, by
        have he := hn (h.symm ⟨x, hin x⟩)
        rw [h.apply_symm_apply] at he
        change 1 ≤ ‖(h.symm ⟨x, hin x⟩ : E)‖ ∧ _
        rw [← he]
        exact x.property⟩
      left_inv := fun x ↦ Subtype.ext (congrArg (fun y : ({0}ᶜ : Set E) ↦ (y : E)) (h.symm_apply_apply ⟨x, hin x⟩))
      right_inv := fun x ↦ Subtype.ext (congrArg (fun y : ({0}ᶜ : Set E) ↦ (y : E)) (h.apply_symm_apply ⟨x, hin x⟩))
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (h.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (h.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_val }
  refine ⟨F, fun x ↦ hn _, ?_⟩
  intro z hz
  have hz1 : ‖(z : E)‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
  have he : (e ⟨z, hin ⟨z, hz⟩⟩).1 = z := by
    apply Subtype.ext
    simp [e, hz1]
  change (h ⟨z, hin ⟨z, hz⟩⟩ : E) = _
  simp [h, he, e, hz1]

end HolomorphicAnosov
