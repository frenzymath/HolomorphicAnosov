import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.Homology.ModTwoSupportHomeomorphism
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Transport of a mod-two point profile across an ambient homeomorphism

Source: Hatcher, *Algebraic Topology*, functorial relative homology pp.115–118
and chart transport in Lemma 3.27, p.237.  The statement packages the literal
support-pair homeomorphism used by the local profile provider.
-/

namespace HolomorphicAnosov.Topology.Homology

open CategoryTheory

universe u
noncomputable section

/-- A point relative-homology profile is invariant under an ambient homeomorphism
that carries the singleton point to the target singleton.

Proof plan: restrict `e` to the complements of the two singleton supports and
form the induced isomorphism of the literal `SSetPair`s.  Apply the singular
homology functor with the lifted `ZMod 2` coefficient object.  The induced
linear equivalence transports the degree-n `ZMod 2` generator and carries every
off-degree `Subsingleton` instance across its inverse.

Source obligation: Hatcher pp.115–118 and p.237.  The remaining formal work is
the carrier-level extraction of linear equivalences from the pair isomorphism.
-/
theorem modTwo_support_profile_homeomorph_transport
    (n : ℕ) {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X)
    (hpoint :
      Nonempty (modTwoSupportHomology Y {e x} n ≃ₗ[ZMod 2] ZMod 2) ∧
        ∀ k : ℕ, k ≠ n → Subsingleton (modTwoSupportHomology Y {e x} k)) :
    Nonempty (modTwoSupportHomology X {x} n ≃ₗ[ZMod 2] ZMod 2) ∧
      ∀ k : ℕ, k ≠ n → Subsingleton (modTwoSupportHomology X {x} k) := by
  let hKL : ∀ z : X, z ∈ ({x} : Set X) ↔ e z ∈ ({e x} : Set Y) := by
    intro z
    simp only [Set.mem_singleton_iff]
    exact e.injective.eq_iff.symm
  have hIso (k : ℕ) : IsIso (SSetPair.homologyMap
      (supportSingularPairMap (X := TopCat.of X) (Y := TopCat.of Y)
        ({x} : Set X) ({e x} : Set Y)
        (TopCat.ofHom ⟨e, e.continuous⟩)
        (fun z hz hL ↦ hz ((hKL z).mpr hL)))
      (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) k) := by
    exact HolomorphicAnosov.HatcherCompactSupport.modTwo_support_homeomorph_homology_isIso e {x} {e x} hKL k
  let E (k : ℕ) : modTwoSupportHomology X {x} k ≃ₗ[ZMod 2]
      modTwoSupportHomology Y {e x} k :=
    LinearEquiv.ofBijective
      (ModuleCat.Hom.hom (SSetPair.homologyMap
        (supportSingularPairMap (X := TopCat.of X) (Y := TopCat.of Y)
          ({x} : Set X) ({e x} : Set Y)
          (TopCat.ofHom ⟨e, e.continuous⟩)
          (fun z hz hL ↦ hz ((hKL z).mpr hL)))
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) k))
      (ConcreteCategory.bijective_of_isIso _)
  rcases hpoint with ⟨hn, hrest⟩
  refine ⟨?_, ?_⟩
  · rcases hn with ⟨q⟩
    exact ⟨(E n).trans q⟩
  · intro k hk
    let : Subsingleton (modTwoSupportHomology Y {e x} k) := hrest k hk
    let : Nonempty (modTwoSupportHomology X {x} k ≃ₗ[ZMod 2]
        modTwoSupportHomology Y {e x} k) := ⟨E k⟩
    constructor
    intro a b
    apply (E k).injective
    exact Subsingleton.elim _ _


end
end HolomorphicAnosov.Topology.Homology
