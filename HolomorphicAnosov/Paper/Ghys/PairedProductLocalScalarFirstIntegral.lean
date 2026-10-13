import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Complex.Basic

/-! Local scalar first integrals on paired products, with their fibres and holomorphic restrictions
to receiving curves. (Shub, Prop. 10.15 pp.150–151) -/

namespace HolomorphicAnosov.Ghys

open scoped Manifold ContDiff

/-- A local complex coordinate on the first factor of a paired product defines a scalar first
integral on an open subproduct, with fibres equal to opposite product slices and holomorphic
restrictions to complex receiving curves. (Shub, Prop. 10.15 pp.150–151) -/
theorem pairedProduct_local_scalar_firstIntegral
    {M U S : Type*} [TopologicalSpace M] [TopologicalSpace U]
    [TopologicalSpace S] [ChartedSpace ℂ U]
    (O : TopologicalSpace.Opens M) (Ψ : (U × S) ≃ₜ O)
    (c : OpenPartialHomeomorph U ℂ)
    (hc : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ c c.source) :
    ∃ (W : TopologicalSpace.Opens M) (q : M → ℂ),
      W ≤ O ∧
      (∀ u s, (Ψ (u, s)).val ∈ W ↔ u ∈ c.source) ∧
      ContinuousOn q W ∧
      (∀ u s, q (Ψ (u, s)).val = c u) ∧
      (∀ u ∈ c.source, ∀ y ∈ W,
        q y = c u ↔ ∃ s, (Ψ (u, s)).val = y) ∧
      (∀ {V : Type*} [TopologicalSpace V] [ChartedSpace ℂ V]
        (ι : V → M) (s : S) (b : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) U V ∞),
        (∀ u, ι (b u) = (Ψ (u, s)).val) →
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ (q ∘ ι) (b.symm ⁻¹' c.source) ∧
          Set.InjOn (q ∘ ι) (b.symm ⁻¹' c.source)) := by
  classical
  let W : TopologicalSpace.Opens M :=
    ⟨Subtype.val '' {y : O | (Ψ.symm y).1 ∈ c.source},
      O.isOpen.isOpenMap_subtype_val _
        (c.open_source.preimage (continuous_fst.comp Ψ.symm.continuous))⟩
  have hWO : W ≤ O := by
    rintro y ⟨v, hv, rfl⟩
    exact v.property
  have hmem (y : O) : y.val ∈ W ↔ (Ψ.symm y).1 ∈ c.source := by
    constructor
    · rintro ⟨v, hv, heq⟩
      have heq' : v = y := Subtype.ext heq
      rwa [heq'] at hv
    · intro hy
      exact ⟨y, hy, rfl⟩
  let q : M → ℂ := fun y ↦ if hy : y ∈ O then c (Ψ.symm ⟨y, hy⟩).1 else 0
  have hqO (y : O) : q y.val = c (Ψ.symm y).1 := by simp [q]
  have hqslice (u : U) (s : S) : q (Ψ (u, s)).val = c u := by
    rw [hqO, Ψ.symm_apply_apply]
  refine ⟨W, q, hWO, ?_, ?_, hqslice, ?_, ?_⟩
  · intro u s
    rw [hmem, Ψ.symm_apply_apply]
  · rw [continuousOn_iff_continuous_domRestrict]
    let liftW : W → O := fun y ↦ ⟨y.val, hWO y.property⟩
    have hlift : Continuous liftW := continuous_subtype_val.subtype_mk _
    have hcoord : Continuous (fun y : W ↦ (Ψ.symm (liftW y)).1) :=
      continuous_fst.comp (Ψ.symm.continuous.comp hlift)
    have hsource (y : W) : (Ψ.symm (liftW y)).1 ∈ c.source :=
      (hmem (liftW y)).mp y.property
    exact (c.continuousOn.comp_continuous hcoord hsource).congr
      (fun y ↦ (hqO (liftW y)).symm)
  · intro u hu y hy
    obtain ⟨v, hv, rfl⟩ := hy
    constructor
    · intro heq
      have hfirst : (Ψ.symm v).1 = u := c.injOn hv hu ((hqO v).symm.trans heq)
      refine ⟨(Ψ.symm v).2, ?_⟩
      rw [← hfirst]
      exact congrArg Subtype.val (Ψ.apply_symm_apply v)
    · rintro ⟨s, hs⟩
      rw [← hs, hqslice]
  · intro V _ _ ι s b hb
    have heq : q ∘ ι = c ∘ b.symm := by
      funext v
      change q (ι v) = c (b.symm v)
      rw [← b.apply_symm_apply v, hb, hqslice, b.symm_apply_apply]
    rw [heq]
    constructor
    · exact hc.comp b.symm.contMDiff.contMDiffOn (fun _ hv ↦ hv)
    · intro v hv w hw heq
      exact b.symm.injective (c.injOn hv hw heq)

end HolomorphicAnosov.Ghys

