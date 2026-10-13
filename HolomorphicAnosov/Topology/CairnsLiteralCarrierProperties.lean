import HolomorphicAnosov.Topology.CairnsClosedCellRestriction

namespace HolomorphicAnosov
open Set

/-- A literal total map represented by a carrier homeomorphism is continuous
and bijective on the carrier; its restriction to a subset detects membership
in that subset's image by injectivity. This is the carrier plumbing needed
to transport the Cairns stage interior and frontier. -/
theorem literal_carrier_homeomorph_properties {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : X → Y) (H : A ≃ₜ B)
    (hH : ∀ x, (H x : Y) = f x) :
    ContinuousOn f A ∧ BijOn f A B ∧
      ∀ U : Set X, U ⊆ A → ∀ x : A, (x : X) ∈ U ↔ (H x : Y) ∈ f '' U := by
  have hc : ContinuousOn f A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : A.domRestrict f = fun x : A ↦ (H x : Y) := funext (fun x ↦ (hH x).symm)
    rw [he]
    exact continuous_subtype_val.comp H.continuous
  have hbij : BijOn f A B := by
    refine ⟨?_,?_,?_⟩
    · intro x hx
      rw [← hH ⟨x,hx⟩]
      exact (H ⟨x,hx⟩).property
    · intro x hx y hy hxy
      have he : H ⟨x,hx⟩ = H ⟨y,hy⟩ := by
        apply Subtype.ext
        simpa only [hH] using hxy
      exact congrArg Subtype.val (H.injective he)
    · intro y hy
      obtain ⟨x,hx⟩ := H.surjective ⟨y,hy⟩
      exact ⟨x,x.property,(hH x).symm.trans (congrArg Subtype.val hx)⟩
  refine ⟨hc,hbij,?_⟩
  intro U hUA x
  constructor
  · intro hx
    exact ⟨x,hx,(hH x).symm⟩
  · rintro ⟨y,hy,he⟩
    have hxy : (x : X) = y := hbij.injOn x.property (hUA hy) ((hH x).symm.trans he.symm)
    exact hxy.symm ▸ hy

end HolomorphicAnosov

