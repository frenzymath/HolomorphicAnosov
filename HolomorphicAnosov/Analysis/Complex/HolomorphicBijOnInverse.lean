import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism

namespace HolomorphicAnosov
open Set

/-- The inverse of a holomorphic bijection between open subsets of the complex plane
is holomorphic. Source: McMullen, Advanced Complex Analysis, p.58, the univalence
paragraph, used in Conway VII Lemma 4.3. Open mapping gives a partial homeomorphism
with the original forward function. Its inverse identities hold on the two sets.
The nonzero-derivative theorem for holomorphic injections and the local inverse
rule show that this same inverse is complex differentiable throughout its domain. -/
theorem holomorphic_bijOn_inverse {U V : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U V) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g V ∧ MapsTo g V U ∧
      (∀ z ∈ U, g (f z) = z) ∧ (∀ w ∈ V, f (g w) = w) := by
  classical
  let p := hbij.toPartialEquiv f U V
  have hop : IsOpenMap (p.source.domRestrict p) := by
    intro W hW
    have hs : IsOpen ((Subtype.val : U → ℂ) '' W) :=
      hU.isOpenEmbedding_subtypeVal.isOpenMap W hW
    have heq : p.source.domRestrict p '' W = f '' ((Subtype.val : U → ℂ) '' W) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.val, ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
    rw [heq]
    exact lebl_scalar_open_image hU hf hbij.injOn hs (Subtype.coe_image_subset _ _)
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict p hf.continuousOn hop hU
  refine ⟨e.symm, ?_, (fun _ hw ↦ e.map_target hw), (fun _ hz ↦ e.left_inv hz), (fun _ hw ↦ e.right_inv hw)⟩
  intro w hw
  exact (e.hasDerivAt_symm hw
    (lebl_scalar_deriv_ne_zero hU hf hbij.injOn _ (e.map_target hw))
    (hf.differentiableAt (hU.mem_nhds (e.map_target hw))).hasDerivAt).differentiableAt.differentiableWithinAt

end HolomorphicAnosov
