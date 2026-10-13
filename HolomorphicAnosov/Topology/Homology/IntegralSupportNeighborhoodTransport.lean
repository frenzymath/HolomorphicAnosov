import HolomorphicAnosov.Topology.Homology.SupportNeighborhoodExcisionCoefficients
import HolomorphicAnosov.Topology.Homology.IntegralSupportRestrictionNormalization

noncomputable section
namespace HolomorphicAnosov
open Set CategoryTheory HolomorphicAnosov.Topology _root_.Topology
universe u

/-- The literal inclusion of an open support neighborhood induces an isomorphism
on support homology. Source: Hatcher, Algebraic Topology, excision p.124 and
Lemma 3.27 p.237. This is the native support-pair form of neighborhood excision. -/
theorem integral_support_neighborhood_map_isIso
    (M : Type u) [TopologicalSpace M] (K U : Set M) (hU : IsOpen U)
    (hKU : closure K ⊆ U) (R : ModuleCat.{u} ℤ) (q : ℕ) :
    IsIso (SSetPair.homologyMap
      (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of M)
        {x : U | x.val ∈ K} K
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
        (fun _ hx hK ↦ hx hK)) R q) := by
  exact support_neighborhood_excision_isIso_coefficients (TopCat.of M) K U hU hKU R q

/-- Neighborhood inclusion commutes with restriction of supports, by the literal
pair-map square. Source: Hatcher, Algebraic Topology, maps of pairs p.118. -/
theorem integral_support_neighborhood_restriction_naturality
    (M : Type u) [TopologicalSpace M] (K L U : Set M) (hLK : L ⊆ K)
    (R : ModuleCat.{u} ℤ) (q : ℕ) :
    SSetPair.homologyMap
      (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of M)
        {x : U | x.val ∈ K} K
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
        (fun _ hx hK ↦ hx hK)) R q ≫
      SSetPair.homologyMap
        (supportSingularPairMap (X := TopCat.of M) (Y := TopCat.of M) K L
          (𝟙 _) (fun _ hx hL ↦ hx (hLK hL))) R q =
    SSetPair.homologyMap
      (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of U)
        {x : U | x.val ∈ K} {x : U | x.val ∈ L}
        (𝟙 _) (fun _ hx hL ↦ hx (hLK hL))) R q ≫
      SSetPair.homologyMap
        (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of M)
          {x : U | x.val ∈ L} L
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
          (fun _ hx hL ↦ hx hL)) R q := by
  rw [← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp]
  congr 1

end HolomorphicAnosov

namespace HolomorphicAnosov
open Set CategoryTheory HolomorphicAnosov.Topology _root_.Topology
universe u

/-- Excision transports detection and above-dimension vanishing from an open
neighborhood to its ambient space. Source: Hatcher, Algebraic Topology, Lemma
3.27 pp.237–238. Lift an ambient class uniquely by neighborhood excision.
Naturality and injectivity at singleton supports imply that the lifted class
has zero point restrictions, hence is zero by neighborhood detection.
Surjectivity transfers vanishing in higher degrees. -/
theorem integral_support_neighborhood_profile_transport
    (M : Type u) [TopologicalSpace M] [T2Space M]
    (K U : Set M) (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ)
    (hdetect : ∀ b : supportSingularHomology (TopCat.of U) {z : U | z.val ∈ K}
        (ModuleCat.of ℤ (ULift.{u} ℤ)) n,
      (∀ z : U, ∀ (hz : z.val ∈ K), supportSingularHomologyRestrict (TopCat.of U)
        (ModuleCat.of ℤ (ULift.{u} ℤ)) (Set.singleton_subset_iff.mpr hz) n b = 0) → b = 0)
    (hvanish : ∀ q, n < q → Subsingleton
      (supportSingularHomology (TopCat.of U) {z : U | z.val ∈ K}
        (ModuleCat.of ℤ (ULift.{u} ℤ)) q : Type u)) :
    (∀ a : supportSingularHomology (TopCat.of M) K
        (ModuleCat.of ℤ (ULift.{u} ℤ)) n,
      (∀ x (hx : x ∈ K), supportSingularHomologyRestrict (TopCat.of M)
        (ModuleCat.of ℤ (ULift.{u} ℤ)) (Set.singleton_subset_iff.mpr hx) n a = 0) → a = 0) ∧
    (∀ q, n < q → Subsingleton
      (supportSingularHomology (TopCat.of M) K
        (ModuleCat.of ℤ (ULift.{u} ℤ)) q : Type u)) := by
  let R := ModuleCat.of ℤ (ULift.{u} ℤ)
  let f (A : Set M) (q : ℕ) := SSetPair.homologyMap
    (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of M)
      {z : U | z.val ∈ A} A
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
      (fun _ hz hA ↦ hz hA)) R q
  have hi (A : Set M) (hA : IsClosed A) (hAU : A ⊆ U) (q : ℕ) : IsIso (f A q) := by
    apply integral_support_neighborhood_map_isIso M A U hU
    rwa [hA.closure_eq]
  have hiK (q : ℕ) : IsIso (f K q) := hi K hK hKU q
  have hbij (q : ℕ) : Function.Bijective (f K q) := by
    have : IsIso (f K q) := hiK q
    exact ConcreteCategory.bijective_of_isIso (f K q)
  constructor
  · intro a ha
    obtain ⟨b, hb⟩ := (hbij n).2 a
    have hbzero : b = 0 := by
      apply hdetect b
      intro z hz
      let g := SSetPair.homologyMap
        (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of M)
          ({z} : Set U) ({z.val} : Set M)
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
          (fun y hy hval ↦ hy (Subtype.ext hval))) R n
      have hig : IsIso g := by
        have hgen (V : Set U) (hV : ∀ y : U, y ∈ V ↔ y.val ∈ ({z.val} : Set M)) :
            IsIso (SSetPair.homologyMap
              (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of M)
                V {z.val} (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
                (fun y hy hv ↦ hy ((hV y).mpr hv))) R n) := by
          have he : V = {y : U | y.val ∈ ({z.val} : Set M)} := Set.ext hV
          subst V
          exact hi {z.val} isClosed_singleton (Set.singleton_subset_iff.mpr z.property) n
        exact hgen {z} (fun y ↦ by simp only [Set.mem_singleton_iff]; exact Subtype.ext_iff)
      have hginj := ConcreteCategory.bijective_of_isIso g |>.1
      apply hginj
      rw [map_zero, integral_support_restrict_native_apply]
      have hnat : f K n ≫ SSetPair.homologyMap
          (supportSingularPairMap (X := TopCat.of M) (Y := TopCat.of M)
            K {z.val} (𝟙 _) (fun _ hx hv ↦ hx ((Set.singleton_subset_iff.mpr hz) hv))) R n =
          SSetPair.homologyMap
            (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of U)
              {y : U | y.val ∈ K} {z} (𝟙 _)
              (fun y hx hv ↦ hx ((show y = z from hv) ▸ hz))) R n ≫ g := by
        dsimp only [f, g]
        rw [← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp]
        congr 1
      have hleft : supportSingularHomologyRestrict (TopCat.of M) R
          (Set.singleton_subset_iff.mpr hz) n (f K n b) = 0 := by
        rw [hb]
        exact ha z.val hz
      rw [integral_support_restrict_native_apply] at hleft
      exact (congrArg (fun m ↦ m b) hnat).symm.trans hleft
    rw [hbzero, map_zero] at hb
    exact hb.symm
  · intro q hq
    have := hvanish q hq
    exact Function.Surjective.subsingleton (hbij q).2
/-- Excision also transports the ambient compact-support profile to its open
neighborhood. Source: Hatcher, Algebraic Topology, maps of pairs p.118 and
excision p.124. Naturality shows that the image of a class with zero point
restrictions again has zero point restrictions. Ambient detection and
injectivity of excision then kill the original class. Higher-degree
subsingleton groups transfer by the same injective map. -/
theorem integral_support_neighborhood_profile_restrict
    (M : Type u) [TopologicalSpace M] [T2Space M]
    (K U : Set M) (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (n : ℕ)
    (hdetect : ∀ a : supportSingularHomology (TopCat.of M) K
        (ModuleCat.of ℤ (ULift.{u} ℤ)) n,
      (∀ x (hx : x ∈ K), supportSingularHomologyRestrict (TopCat.of M)
        (ModuleCat.of ℤ (ULift.{u} ℤ)) (Set.singleton_subset_iff.mpr hx) n a = 0) → a = 0)
    (hvanish : ∀ q, n < q → Subsingleton
      (supportSingularHomology (TopCat.of M) K
        (ModuleCat.of ℤ (ULift.{u} ℤ)) q : Type u)) :
    (∀ b : supportSingularHomology (TopCat.of U) {z : U | z.val ∈ K}
        (ModuleCat.of ℤ (ULift.{u} ℤ)) n,
      (∀ z : U, ∀ (hz : z.val ∈ K), supportSingularHomologyRestrict (TopCat.of U)
        (ModuleCat.of ℤ (ULift.{u} ℤ)) (Set.singleton_subset_iff.mpr hz) n b = 0) → b = 0) ∧
    (∀ q, n < q → Subsingleton
      (supportSingularHomology (TopCat.of U) {z : U | z.val ∈ K}
        (ModuleCat.of ℤ (ULift.{u} ℤ)) q : Type u)) := by
  let R := ModuleCat.of ℤ (ULift.{u} ℤ)
  let f (q : ℕ) := SSetPair.homologyMap
    (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of M)
      {z : U | z.val ∈ K} K
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
      (fun _ hz hA ↦ hz hA)) R q
  have hinj (q : ℕ) : Function.Injective (f q) := by
    have : IsIso (f q) := integral_support_neighborhood_map_isIso M K U hU
      (by rwa [hK.closure_eq]) R q
    exact (ConcreteCategory.bijective_of_isIso (f q)).1
  constructor
  · intro b hb
    apply hinj n
    rw [map_zero]
    apply hdetect
    intro x hx
    let z : U := ⟨x, hKU hx⟩
    let g := SSetPair.homologyMap
      (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of M)
        ({z} : Set U) ({x} : Set M)
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
        (fun y hy hval ↦ hy (Subtype.ext hval))) R n
    have hnat : f n ≫ SSetPair.homologyMap
        (supportSingularPairMap (X := TopCat.of M) (Y := TopCat.of M)
          K {x} (𝟙 _) (fun _ hy hv ↦ hy ((Set.singleton_subset_iff.mpr hx) hv))) R n =
        SSetPair.homologyMap
          (supportSingularPairMap (X := TopCat.of U) (Y := TopCat.of U)
            {y : U | y.val ∈ K} {z} (𝟙 _)
            (fun y hy hv ↦ hy ((show y = z from hv) ▸ hx))) R n ≫ g := by
      dsimp only [f, g]
      rw [← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp]
      congr 1
    have hz := hb z hx
    rw [integral_support_restrict_native_apply] at hz ⊢
    have ht := congrArg (fun m ↦ m b) hnat
    exact ht.trans ((congrArg (fun a ↦ g a) hz).trans (map_zero g.hom))
  · intro q hq
    have := hvanish q hq
    exact Function.Injective.subsingleton (hinj q)

end HolomorphicAnosov
