import Mathlib.Topology.Algebra.Group.Quotient

noncomputable section

namespace HolomorphicAnosov
universe u w

/-- An open continuous quotient with the fibres of an additive-group quotient is homeomorphic to that quotient, compatibly with the representative maps. (Ghys, p. 600) -/
theorem open_quotient_homeomorph_of_fibres
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
    {S : Type u} [TopologicalSpace S]
    {U : Type w} [TopologicalSpace U]
    (π : U → S) (hπ : Function.Surjective π)
    (hcπ : Continuous π) (hoπ : IsOpenMap π)
    (D0 : U ≃ₜ E) (Λ : AddSubgroup E)
    (hfib : ∀ u v : U, π u = π v ↔
      (QuotientAddGroup.mk (D0 u) : E ⧸ Λ) = QuotientAddGroup.mk (D0 v)) :
    ∃ h : S ≃ₜ E ⧸ Λ,
      ∀ u, h (π u) = QuotientAddGroup.mk (D0 u) := by
  classical
  let s : S → U := hπ.hasRightInverse.choose
  have hs : Function.RightInverse s π := hπ.hasRightInverse.choose_spec
  let h : S → E ⧸ Λ := fun x ↦ QuotientAddGroup.mk (D0 (s x))
  have hrep (u : U) : h (π u) = QuotientAddGroup.mk (D0 u) :=
    (hfib (s (π u)) u).mp (hs (π u))
  have hcont : Continuous h := (hoπ.isQuotientMap hcπ hπ).continuous_iff.mpr (by
    have heq : h ∘ π = fun u ↦ (QuotientAddGroup.mk (D0 u) : E ⧸ Λ) :=
      funext hrep
    rw [heq]
    exact continuous_quotient_mk'.comp D0.continuous)
  have hinj : Function.Injective h := by
    intro x y heq
    exact (hs x).symm.trans (((hfib (s x) (s y)).mpr heq).trans (hs y))
  have hsurj : Function.Surjective h := by
    intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    refine ⟨π (D0.symm z), ?_⟩
    rw [hrep, D0.apply_symm_apply]
  have hopen : IsOpenMap h := by
    intro O hO
    have heq : h '' O =
        (QuotientAddGroup.mk : E → E ⧸ Λ) ''
          (D0 '' (π ⁻¹' O)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨D0 (s y), ⟨s y, by simpa [hs y] using hy, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨π u, hu, hrep u⟩
    rw [heq]
    exact QuotientAddGroup.isOpenMap_coe _
      (D0.isOpenMap _ (hcπ.isOpen_preimage _ hO))
  exact ⟨(Equiv.ofBijective h ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen, hrep⟩



end HolomorphicAnosov
