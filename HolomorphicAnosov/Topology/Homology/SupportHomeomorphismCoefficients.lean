import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Homeomorphism comparison for support restrictions with module coefficients
Source: Hatcher, Algebraic Topology, functorial relative homology pp.115–118
and the chart comparison of Lemma 3.27, p.237. -/

open CategoryTheory Set
namespace HolomorphicAnosov.Topology.Homology
universe u v

set_option backward.isDefEq.respectTransparency false

/-- A homeomorphism transports the isomorphism property of the canonical support
restriction, over any commutative coefficient ring. Source: Hatcher pp.115–118,
Lemma 3.27 p.237. The homeomorphism restricts to homeomorphisms of complements,
so both vertical pair maps are isomorphisms. The support-restriction square
commutes on literal point maps. Applying relative homology and cancelling the
vertical isomorphisms proves the assertion in every degree. -/
theorem support_restriction_isIso_of_homeomorph
    {R : Type v} [CommRing R] {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A B : Set X) (C D : Set Y)
    (hA : ∀ x, x ∈ A ↔ e x ∈ C) (hB : ∀ x, x ∈ B ↔ e x ∈ D)
    (hBA : B ⊆ A) (hDC : D ⊆ C) (V : ModuleCat.{u} R) (k : ℕ)
    [IsIso (SSetPair.homologyMap (singularSupportRestrictionPair Y C D hDC) V k)] :
    IsIso (SSetPair.homologyMap (singularSupportRestrictionPair X A B hBA) V k) := by
  let transport (K : Set X) (L : Set Y) (h : ∀ x, x ∈ K ↔ e x ∈ L) :=
    HolomorphicAnosov.singularSubspacePairMap (TopCat.ofHom ⟨e, e.continuous⟩)
      Kᶜ Lᶜ (fun x hx hL ↦ hx ((h x).mpr hL))
  have ht (K : Set X) (L : Set Y) (h : ∀ x, x ∈ K ↔ e x ∈ L) :
      IsIso (SSetPair.homologyMap (transport K L h) V k) := by
    let ec : ↥(Kᶜ) ≃ₜ ↥(Lᶜ) := e.subtype (fun x ↦ not_congr (h x))
    have hl : IsIso (transport K L h).hom.left := by
      change IsIso (TopCat.toSSet.map
        (TopCat.isoOfHomeo (X := TopCat.of ↥(Kᶜ)) (Y := TopCat.of ↥(Lᶜ)) ec).hom)
      infer_instance
    have hr : IsIso (transport K L h).hom.right := by
      change IsIso (TopCat.toSSet.map
        (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e).hom)
      infer_instance
    have ha : IsIso (transport K L h).hom :=
      Arrow.isIso_of_isIso_left_of_isIso_right _
    have hf : IsIso (SSetPair.forget.map (transport K L h)) := ha
    have : IsIso (transport K L h) := isIso_of_reflects_iso _ SSetPair.forget
    change IsIso ((SSetPair.homologyFunctor V k).map _)
    infer_instance
  have hsq : transport A C hA ≫ singularSupportRestrictionPair Y C D hDC =
      singularSupportRestrictionPair X A B hBA ≫ transport B D hB := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    · simp
      rfl
  have htA := ht A C hA
  have htB := ht B D hB
  have hh := congrArg (fun f ↦ SSetPair.homologyMap f V k) hsq
  simp only [SSetPair.homologyMap_comp] at hh
  have hc : IsIso (SSetPair.homologyMap (singularSupportRestrictionPair X A B hBA) V k ≫
      SSetPair.homologyMap (transport B D hB) V k) := by
    rw [← hh]
    infer_instance
  have heq : SSetPair.homologyMap (singularSupportRestrictionPair X A B hBA) V k =
      (SSetPair.homologyMap (singularSupportRestrictionPair X A B hBA) V k ≫
        SSetPair.homologyMap (transport B D hB) V k) ≫
          inv (SSetPair.homologyMap (transport B D hB) V k) := by simp
  rw [heq]
  infer_instance

end HolomorphicAnosov.Topology.Homology
