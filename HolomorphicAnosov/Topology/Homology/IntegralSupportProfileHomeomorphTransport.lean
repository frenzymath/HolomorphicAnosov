import HolomorphicAnosov.Topology.Homology.SupportHomeomorphism
import HolomorphicAnosov.Topology.Homology.IntegralSupportRestrictionNormalization
set_option maxHeartbeats 800000

noncomputable section
namespace HolomorphicAnosov
open Set CategoryTheory HolomorphicAnosov.Topology _root_.Topology
universe u

/-- Integral compact-support detection and above-dimension vanishing transport across an
ambient homeomorphism carrying one support onto another. -/
theorem integral_support_profile_homeomorph_transport
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (K : Set X) (L : Set Y)
    (hKL : ∀ x, x ∈ K ↔ e x ∈ L) (n : ℕ)
    (hdetect : ∀ b : supportSingularHomology (TopCat.of Y) L
        (ModuleCat.of ℤ (ULift.{u} ℤ)) n,
      (∀ y (hy : y ∈ L), supportSingularHomologyRestrict (TopCat.of Y)
        (ModuleCat.of ℤ (ULift.{u} ℤ)) (Set.singleton_subset_iff.mpr hy) n b = 0) → b = 0)
    (hvanish : ∀ q : ℕ, n < q →
      Subsingleton (supportSingularHomology (TopCat.of Y) L
        (ModuleCat.of ℤ (ULift.{u} ℤ)) q : Type u)) :
    (∀ a : supportSingularHomology (TopCat.of X) K
        (ModuleCat.of ℤ (ULift.{u} ℤ)) n,
      (∀ x (hx : x ∈ K), supportSingularHomologyRestrict (TopCat.of X)
        (ModuleCat.of ℤ (ULift.{u} ℤ)) (Set.singleton_subset_iff.mpr hx) n a = 0) → a = 0) ∧
    (∀ q : ℕ, n < q → Subsingleton (supportSingularHomology (TopCat.of X) K
      (ModuleCat.of ℤ (ULift.{u} ℤ)) q : Type u)) := by
  let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
  let E (A : Set X) (B : Set Y) (hAB : ∀ x, x ∈ A ↔ e x ∈ B) (q : ℕ) :
      supportSingularHomology (TopCat.of X) A R q ≃ₗ[ℤ]
        supportSingularHomology (TopCat.of Y) B R q := by
    let f := SSetPair.homologyMap
      (supportSingularPairMap (X := TopCat.of X) (Y := TopCat.of Y) A B
        (TopCat.ofHom ⟨e, e.continuous⟩)
        (fun x hx hB ↦ hx ((hAB x).mpr hB))) R q
    letI : IsIso f := support_homeomorph_homology_isIso e A B hAB R q
    exact LinearEquiv.ofBijective (ModuleCat.Hom.hom f)
      (ConcreteCategory.bijective_of_isIso f)
  have hnat (A : Set X) (B : Set Y)
      (hAB : ∀ x, x ∈ A ↔ e x ∈ B) (hAK : A ⊆ K) (hBL : B ⊆ L) (q : ℕ)
      (a : supportSingularHomology (TopCat.of X) K R q) :
      (E A B hAB q) (supportSingularHomologyRestrict (TopCat.of X) R hAK q a) =
      supportSingularHomologyRestrict (TopCat.of Y) R hBL q ((E K L hKL q) a) := by
    rw [integral_support_restrict_native_apply, integral_support_restrict_native_apply]
    exact congrArg (fun f ↦ f a)
      (support_homeomorph_restriction_naturality e K A L B hKL hAB hAK hBL R q).symm
  let hpoint (x : X) (y : Y) (hxy : y = e x) :
      ∀ z, z ∈ ({x} : Set X) ↔ e z ∈ ({y} : Set Y) := by
    intro z; simp only [mem_singleton_iff]; subst y; exact e.injective.eq_iff.symm
  constructor
  · intro a ha
    have hz : (E K L hKL n) a = 0 := by
      apply hdetect (E K L hKL n a)
      intro y hy
      let x := e.symm y
      have hx : x ∈ K := (hKL x).mpr (by simpa [x] using hy)
      have hxy : y = e x := by simp [x]
      have hz := hnat {x} {y} (hpoint x y hxy) (Set.singleton_subset_iff.mpr hx)
        (Set.singleton_subset_iff.mpr hy) n a
      rw [ha x hx, map_zero] at hz
      exact hz.symm
    apply (E K L hKL n).injective
    simpa using hz
  · intro q hq
    let : Subsingleton (supportSingularHomology (TopCat.of Y) L R q : Type u) := hvanish q hq
    exact ⟨fun a b ↦ (E K L hKL q).injective (Subsingleton.elim _ _)⟩

end HolomorphicAnosov
