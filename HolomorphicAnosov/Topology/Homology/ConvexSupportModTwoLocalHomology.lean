import HolomorphicAnosov.Topology.Homology.ConvexSupportModTwoLocalProfile
import HolomorphicAnosov.Topology.Homology.SupportHomeomorphismCoefficients
import HolomorphicAnosov.Topology.Homology.SupportNeighborhoodExcisionCoefficients
import HolomorphicAnosov.Topology.Homology.ConvexModTwoRestrictionIso
import HolomorphicAnosov.Topology.Homology.SphereReducedHomology
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.SingularHomologyExcision
import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.Homology.ModTwoSingularChainsULiftDegree
import HolomorphicAnosov.Topology.Homology.ModTwoSingularChainsULiftBoundary
import HolomorphicAnosov.Topology.Homology.ModTwoULiftPointRelativeProfile
import HolomorphicAnosov.Topology.Homology.ModTwoULiftRadialRelativeProfile
import HolomorphicAnosov.Topology.Homology.ModTwoULiftSupportCoefficientTransport
import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedHomotopyEquivIso
import HolomorphicAnosov.Topology.Homology.ModTwoSupportPairProfileDescent
import HolomorphicAnosov.Topology.Homology.ModTwoSupportRestrictionLinearEquiv
import HolomorphicAnosov.Topology.Homology.ModTwoSupportProfileHomeomorphTransport
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic

/-!
Mod-two local homology of a convex compact chart support. (Hatcher, Lemma 3.27)
-/

universe u

set_option backward.isDefEq.respectTransparency false

namespace HolomorphicAnosov.Topology.Homology

open Set CategoryTheory

/-- Convex compact chart supports restrict isomorphically to each local group. (Hatcher) -/
theorem hatcher_convex_support_mod2_local_homology
    (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (U : Set M) (hU : IsOpen U) (e : U ≃ₜ EuclideanSpace ℝ (Fin n))
    (A : Set M) (hA : A.Nonempty) (hAcompact : IsCompact A) (hAU : A ⊆ U)
    (hconvex : Convex ℝ (e '' {z : U | z.val ∈ A})) :
    (∀ x : A, ∀ k : ℕ,
      IsIso (modTwoSupportRestriction M A {x.val}
        (Set.singleton_subset_iff.mpr x.property) k)) ∧
    (∀ x : A,
      Nonempty (modTwoSupportHomology M {x.val} n ≃ₗ[ZMod 2] ZMod 2) ∧
        (∀ k : ℕ, k ≠ n → Subsingleton (modTwoSupportHomology M {x.val} k)) ∧
          ∃! c : modTwoSupportHomology M {x.val} n, c ≠ 0) ∧
    (∃! c : modTwoSupportHomology M A n,
      c ≠ 0 ∧ ∀ x : A,
        (modTwoSupportRestriction M A {x.val}
          (Set.singleton_subset_iff.mpr x.property) n) c ≠ 0) := by
  classical
  have hgeometry :
      (∀ x : A, ∀ k : ℕ,
        IsIso (modTwoSupportRestriction M A {x.val}
          (Set.singleton_subset_iff.mpr x.property) k)) ∧
      (∀ x : A,
        Nonempty (modTwoSupportHomology M {x.val} n ≃ₗ[ZMod 2] ZMod 2) ∧
        ∀ k : ℕ, k ≠ n → Subsingleton (modTwoSupportHomology M {x.val} k)) := by
    have hc : IsCompact {z : U | z.val ∈ A} := by
      apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hAcompact
      simpa using hAU
    let e' : U ≃ₜ ULift.{u} (EuclideanSpace ℝ (Fin n)) :=
      e.trans Homeomorph.ulift.symm
    have hconvex' : Convex ℝ (e' '' {z : U | z.val ∈ A}) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
      obtain ⟨z, hz, he⟩ := hconvex (mem_image_of_mem e hx)
        (mem_image_of_mem e hy) ha hb hab
      refine ⟨z, hz, ?_⟩
      exact ULift.ext he
    have hchartIso (x : A) (k : ℕ) :
        IsIso (modTwoSupportRestriction (ULift.{u} (EuclideanSpace ℝ (Fin n)))
          (e' '' {z : U | z.val ∈ A}) {e' ⟨x.val, hAU x.property⟩}
          (Set.singleton_subset_iff.mpr ⟨⟨x.val, hAU x.property⟩, x.property, rfl⟩) k) :=
      convex_compact_modTwo_support_restriction_isIso _ hconvex'
        (hc.image e'.continuous) _ ⟨⟨x.val, hAU x.property⟩, x.property, rfl⟩ k
    have hsupportExcision (k : ℕ) :
        IsIso (SSetPair.homologyMap
          (HolomorphicAnosov.singularExcisionInclusion (TopCat.of M) Aᶜ U)
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) k) :=
      support_neighborhood_excision_isIso_coefficients (TopCat.of M) A U hU
        (by simpa only [hAcompact.isClosed.closure_eq] using hAU) _ k
    have hpointExcision (x : A) (k : ℕ) :
        IsIso (SSetPair.homologyMap
          (HolomorphicAnosov.singularExcisionInclusion (TopCat.of M) {x.val}ᶜ U)
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) k) :=
      support_neighborhood_excision_isIso_coefficients (TopCat.of M) {x.val} U hU
        (by simpa only [isClosed_singleton.closure_eq] using
          (Set.singleton_subset_iff.mpr (hAU x.property))) _ k
    have hlocalIso (x : A) (k : ℕ) :
        IsIso (modTwoSupportRestriction U {z : U | z.val ∈ A}
          {z : U | z.val = x.val} (fun z hz ↦ by change z.val ∈ A; rw [show z.val = x.val from hz]; exact x.property) k) := by
      have hchart := hchartIso x k
      apply support_restriction_isIso_of_homeomorph e' _ _
        (e' '' {z : U | z.val ∈ A}) {e' ⟨x.val, hAU x.property⟩} _ _
        (fun z hz ↦ by change z.val ∈ A; rw [show z.val = x.val from hz]; exact x.property)
        (Set.singleton_subset_iff.mpr ⟨⟨x.val, hAU x.property⟩, x.property, rfl⟩)
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) k
      · intro z
        exact (e'.injective.mem_set_image).symm
      · intro z
        change z.val = x.val ↔ e' z = e' ⟨x.val, hAU x.property⟩
        rw [e'.injective.eq_iff]
        exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
    have hglobalIso (x : A) (k : ℕ) :
        IsIso (modTwoSupportRestriction M A {x.val}
          (Set.singleton_subset_iff.mpr x.property) k) := by
      let iA := HolomorphicAnosov.singularExcisionInclusion (TopCat.of M) Aᶜ U
      let ix := HolomorphicAnosov.singularExcisionInclusion (TopCat.of M) {x.val}ᶜ U
      let rU := singularSupportRestrictionPair U {z : U | z.val ∈ A}
        {z : U | z.val = x.val} (fun z hz ↦ by change z.val ∈ A; rw [show z.val = x.val from hz]; exact x.property)
      let rM := singularSupportRestrictionPair M A {x.val}
        (Set.singleton_subset_iff.mpr x.property)
      let V := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
      have hs : iA ≫ rM = rU ≫ ix := by
        apply MorphismProperty.Arrow.Hom.ext
        · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
            TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
          rw [← Functor.map_comp, ← Functor.map_comp]
          rfl
        · simp
          rfl
      have hiA := hsupportExcision k
      have hix := hpointExcision x k
      have hrU := hlocalIso x k
      have hh := congrArg (fun f ↦ SSetPair.homologyMap f V k) hs
      simp only [SSetPair.homologyMap_comp] at hh
      have heq : SSetPair.homologyMap rM V k =
          inv (SSetPair.homologyMap iA V k) ≫
            (SSetPair.homologyMap rU V k ≫ SSetPair.homologyMap ix V k) := by
        rw [← hh]
        simp
      change IsIso (SSetPair.homologyMap rM V k)
      rw [heq]
      infer_instance
    refine ⟨hglobalIso, ?_⟩
    exact hatcher_convex_support_mod2_local_point_profile n M U hU e A hA hAcompact hAU hconvex
  obtain ⟨hiso, hprofile⟩ := hgeometry
  have huniq (x : A) : ∃! c : modTwoSupportHomology M {x.val} n, c ≠ 0 := by
    obtain ⟨eₓ⟩ := (hprofile x).1
    have hne : eₓ.symm 1 ≠ 0 := by
      intro h
      have := congrArg eₓ h
      simp at this
    refine ⟨eₓ.symm 1, hne, ?_⟩
    intro c hc
    apply eₓ.injective
    rw [eₓ.apply_symm_apply]
    have hec : eₓ c ≠ 0 := by simpa using hc
    generalize eₓ c = z at hec ⊢
    fin_cases z
    · exact (hec rfl).elim
    · rfl
  refine ⟨hiso, fun x ↦ ⟨(hprofile x).1, (hprofile x).2, huniq x⟩, ?_⟩
  obtain ⟨x₀, hx₀⟩ := hA
  let x : A := ⟨x₀, hx₀⟩
  let f := modTwoSupportRestriction M A {x.val}
    (Set.singleton_subset_iff.mpr x.property) n
  have : IsIso f := hiso x n
  have hf := ConcreteCategory.bijective_of_isIso f
  obtain ⟨cₓ, hcₓ, hunique⟩ := huniq x
  obtain ⟨c, hc⟩ := hf.surjective cₓ
  have hc0 : c ≠ 0 := by
    intro hz
    apply hcₓ
    rw [← hc, hz, map_zero]
  refine ⟨c, ⟨hc0, ?_⟩, ?_⟩
  · intro y
    have : IsIso (modTwoSupportRestriction M A {y.val}
      (Set.singleton_subset_iff.mpr y.property) n) := hiso y n
    exact fun hz ↦ hc0 ((ConcreteCategory.bijective_of_isIso
      (modTwoSupportRestriction M A {y.val}
        (Set.singleton_subset_iff.mpr y.property) n)).injective (hz.trans (map_zero _).symm))
  · intro c' hc'
    apply hf.injective
    exact (hunique (f c') (hc'.2 x)).trans hc.symm

end HolomorphicAnosov.Topology.Homology
