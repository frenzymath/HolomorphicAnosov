import HolomorphicAnosov.Topology.GallierXuSurfacePresentation
import HolomorphicAnosov.Topology.AnnulusRadiusSwap

/-!
# Boundary transport from the finite normal form to the literal annulus

Source: Gallier--Xu, *A Guide to the Classification Theorem for Compact
Surfaces* (2025), Lemma 6.1 and Theorem 6.1, pp.88--96, and Cairns,
*An Elementary Proof of the Jordan-Schoenflies Theorem* (1951), preliminary
2(B), printed p.860.  This module isolates the final transport through the
carrier homeomorphism and the two boundary cycles.
-/

open Set

namespace HolomorphicAnosov.Topology

open GallierXu

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- Transport the genus-zero normal-word cylinder through the triangulated
carrier and its two boundary cycles to obtain the literal annulus
parameterization.  The possible permutation of the two cycles is absorbed by
the radial involution exchanging radii one and two.

The source construction is explicit: compose the carrier homeomorphism `H`,
the original-to-normal-form homeomorphism `H₀.trans sequence.homeomorph`, and
the quotient-cylinder homeomorphism.  The inner cycle equality and the outer
cycle equality then identify the two frontier images.  Restricting the
composite to `frontier D` gives `γ`; if Gallier--Xu's permutation `σ` swaps the
two cycle labels, compose with `z ↦ (3 - ‖z‖) z / ‖z‖` on the closed annulus.
The restriction and image equalities are the remaining carrier/subtype
bookkeeping, recorded as this named theorem-level proof boundary.
-/
theorem cairns_polygonal_annulus_boundary_transport
    (D R : Set Plane)
    {N : ℕ} (K : AbstractSimplicialComplex (Fin N))
    (B : Fin 2 → List (Fin N))
    (hfrontierD : frontier D ⊆ R \ interior D)
    (H : ↥(R \ interior D) ≃ₜ ↥(carrier K))
    (hinnerBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier D} =
        cycleCarrier (B 0))
    (houterBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
        cycleCarrier (B 1))
    {o : (s : Triangle K) → Fin 3 ≃ ↥s.val}
    {g : ℕ} (sequence : RealizedSequence (trianglePresentation K o) [normalWord g 2])
    (H₀ : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o))
    (σ : Fin 2 ≃ Fin 2)
    (hσ : ∀ j : Fin 2,
      (H₀.trans sequence.homeomorph) '' cycleCarrier (K := K) (B j) =
        edgeImage [normalWord g 2] (2 * g + 2 * (σ j).val + 1))
    (hg : g = 0)
    (T : Realization [normalWord g 2] ≃ₜ
      {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2})
    (hTinner : T '' edgeImage [normalWord g 2] (2 * g + 1) =
      Metric.sphere (0 : Plane) 1)
    (hTouter : T '' edgeImage [normalWord g 2] (2 * g + 3) =
      Metric.sphere (0 : Plane) 2) :
    ∃ (γ : frontier D ≃ₜ Metric.sphere (0 : Plane) 1)
      (Ψ : ↥(R \ interior D) ≃ₜ {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}),
      (∀ x : frontier D, ∃ y : ↥(R \ interior D),
        (y : Plane) = (x : Plane) ∧ (Ψ y : Plane) = (γ x : Plane)) ∧
      (fun x : ↥(R \ interior D) ↦ (Ψ x : Plane)) ''
        {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
        Metric.sphere (0 : Plane) 2 := by
  classical
  subst g
  let J := H₀.trans sequence.homeomorph
  let P := (H.trans J).trans T
  have hPimage (S : Set (↥(R \ interior D))) :
      P '' S = T '' (J '' (H '' S)) := by
    change (fun x ↦ T (J (H x))) '' S = T '' (J '' (H '' S))
    rw [Set.image_image, Set.image_image]
  have hPinner :
      P '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier D} =
        T '' edgeImage [normalWord 0 2] (2 * (σ 0).val + 1) := by
    rw [hPimage, hinnerBoundary, hσ 0]
    norm_num
  have hPouter :
      P '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
        T '' edgeImage [normalWord 0 2] (2 * (σ 1).val + 1) := by
    rw [hPimage, houterBoundary, hσ 1]
    norm_num
  obtain ⟨S, hS, hSinv⟩ := annulus_radius_swap
  have hS1 :
      (fun x ↦ (S x : Plane)) '' {x : {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} |
        (x : Plane) ∈ Metric.sphere (0 : Plane) 1} = Metric.sphere (0 : Plane) 2 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (x : Plane) ∈ Metric.sphere (0 : Plane) 1 at hx
      change (S x : Plane) ∈ Metric.sphere (0 : Plane) 2
      rw [mem_sphere_zero_iff_norm] at hx ⊢
      rw [hS]
      linarith
    · intro hz
      have hz' : 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 := by
        rw [mem_sphere_zero_iff_norm] at hz
        exact ⟨by linarith, by linarith⟩
      let w : {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := ⟨z, hz'⟩
      refine ⟨S w, ?_, ?_⟩
      · change (S w : Plane) ∈ Metric.sphere (0 : Plane) 1
        rw [mem_sphere_zero_iff_norm, hS]
        have hn := mem_sphere_zero_iff_norm.mp hz
        change 3 - ‖z‖ = 1
        linarith
      · exact congrArg Subtype.val (hSinv w)
  have hS2 :
      (fun x ↦ (S x : Plane)) '' {x : {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} |
        (x : Plane) ∈ Metric.sphere (0 : Plane) 2} = Metric.sphere (0 : Plane) 1 := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (x : Plane) ∈ Metric.sphere (0 : Plane) 2 at hx
      change (S x : Plane) ∈ Metric.sphere (0 : Plane) 1
      rw [mem_sphere_zero_iff_norm] at hx ⊢
      rw [hS]
      linarith
    · intro hz
      have hz' : 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 := by
        rw [mem_sphere_zero_iff_norm] at hz
        exact ⟨by linarith, by linarith⟩
      let w : {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := ⟨z, hz'⟩
      refine ⟨S w, ?_, ?_⟩
      · change (S w : Plane) ∈ Metric.sphere (0 : Plane) 2
        rw [mem_sphere_zero_iff_norm, hS]
        have hn := mem_sphere_zero_iff_norm.mp hz
        change 3 - ‖z‖ = 2
        linarith
      · exact congrArg Subtype.val (hSinv w)
  have hσ0 : (σ 0).val = 0 ∨ (σ 0).val = 1 := by omega
  have hσ1 : (σ 1).val = 0 ∨ (σ 1).val = 1 := by omega
  have hsub (A : Set ↥(R \ interior D)) (r : ℝ)
      (hA : (fun x ↦ (P x : Plane)) '' A = Metric.sphere (0 : Plane) r) :
      P '' A = {x : {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} |
        (x : Plane) ∈ Metric.sphere (0 : Plane) r} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hA ▸ ⟨y, hy, rfl⟩
    · intro hx
      obtain ⟨y, hy, he⟩ := hA.symm ▸ hx
      exact ⟨y, hy, Subtype.ext he⟩
  have hswap (A : Set ↥(R \ interior D)) (r t : ℝ)
      (hA : (fun x ↦ (P x : Plane)) '' A = Metric.sphere (0 : Plane) r)
      (hSt : (fun x ↦ (S x : Plane)) '' {x | (x : Plane) ∈ Metric.sphere (0 : Plane) r} =
        Metric.sphere (0 : Plane) t) :
      (fun x ↦ ((P.trans S) x : Plane)) '' A = Metric.sphere (0 : Plane) t := by
    change (fun x ↦ (S (P x) : Plane)) '' A = _
    rw [← Set.image_image (fun x ↦ (S x : Plane)) P A, hsub A r hA, hSt]
  have hne : σ 0 ≠ σ 1 := fun h ↦ (by norm_num : (0 : Fin 2) ≠ 1) (σ.injective h)
  obtain ⟨Ψ, hΨinner, hΨouter⟩ :
      ∃ Ψ : ↥(R \ interior D) ≃ₜ {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2},
      (fun x ↦ (Ψ x : Plane)) '' {x | (x : Plane) ∈ frontier D} =
        Metric.sphere (0 : Plane) 1 ∧
      (fun x ↦ (Ψ x : Plane)) '' {x | (x : Plane) ∈ frontier R} =
        Metric.sphere (0 : Plane) 2 := by
    rcases hσ0 with h0 | h0
    · have h1 : (σ 1).val = 1 := by
        rcases hσ1 with h1 | h1
        · exact False.elim (hne (Fin.ext (h0.trans h1.symm)))
        · exact h1
      refine ⟨P, ?_, ?_⟩
      · rw [← Set.image_image Subtype.val P]
        rw [hPinner, show 2 * (σ 0).val + 1 = 1 by omega]
        exact hTinner
      · rw [← Set.image_image Subtype.val P]
        rw [hPouter, show 2 * (σ 1).val + 1 = 3 by omega]
        exact hTouter
    · have h1 : (σ 1).val = 0 := by
        rcases hσ1 with h1 | h1
        · exact h1
        · exact False.elim (hne (Fin.ext (h0.trans h1.symm)))
      refine ⟨P.trans S, hswap _ 2 1 ?_ hS2, hswap _ 1 2 ?_ hS1⟩
      · rw [← Set.image_image Subtype.val P]
        rw [hPinner, show 2 * (σ 0).val + 1 = 3 by omega]
        exact hTouter
      · rw [← Set.image_image Subtype.val P]
        rw [hPouter, show 2 * (σ 1).val + 1 = 1 by omega]
        exact hTinner
  have hiff (x : ↥(R \ interior D)) :
      (x : Plane) ∈ frontier D ↔ (Ψ x : Plane) ∈ Metric.sphere (0 : Plane) 1 := by
    constructor
    · intro hx
      rw [← hΨinner]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hΨinner] at hx
      obtain ⟨y, hy, he⟩ := hx
      exact (Ψ.injective (Subtype.ext he)) ▸ hy
  let γ : frontier D ≃ₜ Metric.sphere (0 : Plane) 1 :=
    { toFun := fun x ↦ ⟨Ψ ⟨x, hfrontierD x.property⟩, (hiff _).mp x.property⟩
      invFun := fun w ↦ ⟨Ψ.symm ⟨w, by
        change 1 ≤ ‖(w : Plane)‖ ∧ ‖(w : Plane)‖ ≤ 2
        rw [mem_sphere_zero_iff_norm.mp w.property]
        norm_num⟩, (hiff _).mpr (by simp)⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact congrArg (fun y : ↥(R \ interior D) ↦ (y : Plane)) (Ψ.symm_apply_apply ⟨x, hfrontierD x.property⟩)
      right_inv := by
        intro w
        apply Subtype.ext
        exact congrArg (fun y : {x : Plane | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} ↦ (y : Plane)) (Ψ.apply_symm_apply ⟨w, by
          change 1 ≤ ‖(w : Plane)‖ ∧ ‖(w : Plane)‖ ≤ 2
          rw [mem_sphere_zero_iff_norm.mp w.property]
          norm_num⟩)
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (Ψ.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (Ψ.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_val }
  exact ⟨γ, Ψ, fun x ↦ ⟨⟨x, hfrontierD x.property⟩, rfl, rfl⟩, hΨouter⟩

end HolomorphicAnosov.Topology

