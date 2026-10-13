import HolomorphicAnosov.Topology.Homology.EuclideanCompactSupportProfile
import HolomorphicAnosov.Topology.Homology.IntegralSupportULiftProfile
import HolomorphicAnosov.Topology.Homology.IntegralSupportNeighborhoodTransport


noncomputable section
namespace HolomorphicAnosov
open Set HolomorphicAnosov.Topology _root_.Topology
universe u

/-- Open-neighborhood excision followed by a partial Euclidean chart transports the integral top-degree detection and above-dimension profile to an ambient compact support. -/
theorem integral_partial_chart_excision_composition
    (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    (A : Set M) (hA : IsCompact A)
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (hAe : A ⊆ e.source) :
    Nonempty ((∀ aA : supportSingularHomology (TopCat.of M) A
        (ModuleCat.of ℤ (ULift.{u} ℤ)) n,
      (∀ (x : M) (hx : x ∈ A),
        supportSingularHomologyRestrict (TopCat.of M)
          (ModuleCat.of ℤ (ULift.{u} ℤ))
          (Set.singleton_subset_iff.mpr hx) n aA = 0) → aA = 0) ∧
    (∀ q : ℕ, n < q →
      Subsingleton
        (supportSingularHomology (TopCat.of M) A
          (ModuleCat.of ℤ (ULift.{u} ℤ)) q : Type u))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let L : Set E := e '' A
  have hL : IsCompact L := hA.image_of_continuousOn (e.continuousOn.mono hAe)
  have hLe : L ⊆ e.target := by
    rintro y ⟨x,hx,rfl⟩
    exact e.map_source (hAe hx)
  let U : Set (ULift.{u} E) := ULift.down ⁻¹' e.target
  let K : Set (ULift.{u} E) := ULift.down ⁻¹' L
  have hK : IsClosed K := hL.isClosed.preimage continuous_uliftDown
  have hU : IsOpen U := e.open_target.preimage continuous_uliftDown
  have hKU : K ⊆ U := Set.preimage_mono hLe
  obtain ⟨hd,hv⟩ := euclidean_compact_support_profile n L hL
  obtain ⟨hd',hv'⟩ := IntegralSupportLift.profile.{u} E L n hd hv
  obtain ⟨hdU,hvU⟩ := integral_support_neighborhood_profile_restrict
    (ULift.{u} E) K U hK hU hKU n hd' hv'
  let f : e.source ≃ₜ U := {
    toFun := fun x ↦ ⟨ULift.up (e x), e.map_source x.property⟩
    invFun := fun y ↦ ⟨e.symm y.val.down, e.map_target y.property⟩
    left_inv := by intro x; exact Subtype.ext (e.left_inv x.property)
    right_inv := by intro y; exact Subtype.ext (ULift.ext (e.right_inv y.property))
    continuous_toFun := by
      exact (continuous_uliftUp.comp (continuousOn_iff_continuous_domRestrict.mp e.continuousOn)).subtype_mk _
    continuous_invFun := by
      exact (e.symm.continuousOn.comp_continuous
        (continuous_uliftDown.comp continuous_subtype_val) (fun y ↦ y.property)).subtype_mk _ }
  have hKL (x : e.source) : x.val ∈ A ↔ (f x).val ∈ K := by
    change x.val ∈ A ↔ e x.val ∈ e '' A
    constructor
    · intro hx; exact ⟨x.val,hx,rfl⟩
    · rintro ⟨y,hy,he⟩
      exact (e.injOn (hAe hy) x.property he) ▸ hy
  obtain ⟨hdV,hvV⟩ := integral_support_profile_homeomorph_transport f
    {x : e.source | x.val ∈ A} {y : U | y.val ∈ K} hKL n hdU hvU
  exact ⟨integral_support_neighborhood_profile_transport M A e.source
    hA.isClosed e.open_source hAe n hdV hvV⟩

end HolomorphicAnosov

