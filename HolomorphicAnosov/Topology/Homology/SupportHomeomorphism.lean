import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietoris
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Homeomorphism transport of support homology

Source: Hatcher, Algebraic Topology, functorial relative homology pp.115–117
and the chart comparison in Lemma 3.27, pp.237–238.
-/

open CategoryTheory HolomorphicAnosov.Topology _root_.Topology
namespace HolomorphicAnosov
universe u
/-- A homeomorphism carrying K onto L induces an isomorphism on actual
support homology in every degree and for every integer-module coefficient
object. Source: Hatcher, pp.115–117 and Lemma 3.27, pp.237–238.

Proof: restrict the homeomorphism to the two complements. Both components of
the native singular pair map are isomorphisms. The forgetful functor to arrows
reflects isomorphisms; apply the genuine relative homology functor. -/
theorem support_homeomorph_homology_isIso {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (K : Set X) (L : Set Y) (hKL : ∀ x, x ∈ K ↔ e x ∈ L)
    (R : ModuleCat.{u} ℤ) (q : ℕ) :
    IsIso (SSetPair.homologyMap
      (supportSingularPairMap (X := TopCat.of X) (Y := TopCat.of Y) K L
        (TopCat.ofHom ⟨e, e.continuous⟩) (fun x hx hL ↦ hx ((hKL x).mpr hL))) R q) := by
  let f := supportSingularPairMap (X := TopCat.of X) (Y := TopCat.of Y) K L
    (TopCat.ofHom ⟨e, e.continuous⟩) (fun x hx hL ↦ hx ((hKL x).mpr hL))
  let ec : ↥(Kᶜ) ≃ₜ ↥(Lᶜ) := e.subtype (fun x ↦ not_congr (hKL x))
  have hleft : IsIso f.hom.left := by
    change IsIso (TopCat.toSSet.map
      (TopCat.isoOfHomeo (X := TopCat.of ↥(Kᶜ)) (Y := TopCat.of ↥(Lᶜ)) ec).hom)
    infer_instance
  have hright : IsIso f.hom.right := by
    change IsIso (TopCat.toSSet.map (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e).hom)
    infer_instance
  have harrow : IsIso f.hom := Arrow.isIso_of_isIso_left_of_isIso_right f.hom
  have hforget : IsIso (SSetPair.forget.map f) := harrow
  have hf : IsIso f := isIso_of_reflects_iso f SSetPair.forget
  change IsIso ((SSetPair.homologyFunctor R q).map f)
  infer_instance

/-- Homeomorphism transport commutes with support restriction. Source:
functoriality of relative homology, Hatcher pp.115–117. The squares already
commute on literal simplicial-pair maps, so applying relative homology gives
the required equality without an abstract identification of the groups. -/
theorem support_homeomorph_restriction_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (K A : Set X) (L B : Set Y)
    (hKL : ∀ x, x ∈ K ↔ e x ∈ L) (hAB : ∀ x, x ∈ A ↔ e x ∈ B)
    (hAK : A ⊆ K) (hBL : B ⊆ L) (R : ModuleCat.{u} ℤ) (q : ℕ) :
    SSetPair.homologyMap
      (supportSingularPairMap (X := TopCat.of X) (Y := TopCat.of Y) K L
        (TopCat.ofHom ⟨e, e.continuous⟩) (fun x hx hL ↦ hx ((hKL x).mpr hL))) R q ≫
      SSetPair.homologyMap (supportSingularPairMap (X := TopCat.of Y) (Y := TopCat.of Y) L B (𝟙 (TopCat.of Y))
        (fun _ hx hB ↦ hx (hBL hB))) R q =
    SSetPair.homologyMap (supportSingularPairMap (X := TopCat.of X) (Y := TopCat.of X) K A (𝟙 (TopCat.of X))
      (fun _ hx hA ↦ hx (hAK hA))) R q ≫
      SSetPair.homologyMap
        (supportSingularPairMap (X := TopCat.of X) (Y := TopCat.of Y) A B
          (TopCat.ofHom ⟨e, e.continuous⟩) (fun x hx hB ↦ hx ((hAB x).mpr hB))) R q := by
  rw [← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp]
  congr 1

end HolomorphicAnosov

