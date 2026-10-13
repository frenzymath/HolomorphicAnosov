import HolomorphicAnosov.Topology.CircleDiskBoundaryExtension

/-!
# Prescribing boundary values on a topological disk

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
§2(A), printed p.860, and Hirsch, *Differential Topology* (1976), printed p.155.
DAG node: `topo.disk_prescribed_boundary_extension_g6`.
-/

noncomputable section
open Set

namespace HolomorphicAnosov

/-- A disk model which identifies its boundary with the unit circle can be corrected
to realize any prescribed boundary homeomorphism.

Source: Cairns (1951), §2(A), p.860; the normalized extension is Hirsch's radial
formula, *Differential Topology*, p.155. Restrict the given disk homeomorphism
to the indicated boundary. The boundary membership equivalence makes this
restriction bijective onto the circle, with continuous inverse induced by the
inverse disk map. Compose the inverse boundary restriction with the prescribed
boundary map to obtain a circle homeomorphism. Extend it radially and postcompose
the original disk model. On the boundary the two restriction maps cancel, leaving
exactly the prescribed values. All constructions retain the original subspace
topologies and permit either orientation of the boundary map.
-/
theorem disk_prescribed_boundary_extension
    {X : Type*} [TopologicalSpace X] (c D : Set X) (hcD : c ⊆ D)
    (F₀ : D ≃ₜ Metric.closedBall (0 : ℂ) 1)
    (hboundary : ∀ x : D, x.val ∈ c ↔ ‖(F₀ x : ℂ)‖ = 1)
    (b : c ≃ₜ Circle) :
    ∃ F : D ≃ₜ Metric.closedBall (0 : ℂ) 1,
      ∀ x : c, ∀ hx : x.val ∈ D, (F ⟨x.val, hx⟩ : ℂ) = b x := by
  let toCircle (x : c) : Circle :=
    ⟨F₀ ⟨x.val, hcD x.property⟩, by
      change (F₀ ⟨x.val, hcD x.property⟩ : ℂ) ∈ Metric.sphere 0 1
      rw [Metric.mem_sphere, dist_zero_right]
      exact (hboundary _).mp x.property⟩
  let fromCircle (z : Circle) : c :=
    ⟨(F₀.symm ⟨z, by simp⟩).val, by
      apply (hboundary _).mpr
      simp⟩
  let b₀ : c ≃ₜ Circle :=
    { toFun := toCircle
      invFun := fromCircle
      left_inv := by
        intro x
        apply Subtype.ext
        change (F₀.symm (F₀ ⟨x.val, hcD x.property⟩)).val = x.val
        simp
      right_inv := by
        intro z
        apply Subtype.ext
        change (F₀ (F₀.symm ⟨z, by simp⟩) : ℂ) = z
        simp
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (F₀.continuous.comp
          (continuous_subtype_val.subtype_mk (fun x ↦ hcD x.property))).subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (F₀.symm.continuous.comp
          (continuous_subtype_val.subtype_mk (fun z : Circle ↦ by simp))).subtype_val }
  obtain ⟨R, hR⟩ := circle_disk_boundary_extension (b₀.symm.trans b)
  refine ⟨F₀.trans R, ?_⟩
  intro x hx
  have h := hR (b₀ x)
  change (R ⟨(F₀ ⟨x.val, hcD x.property⟩ : ℂ), _⟩ : ℂ) = b (b₀.symm (b₀ x)) at h
  simpa using h

end HolomorphicAnosov
