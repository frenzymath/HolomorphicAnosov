import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietoris
import HolomorphicAnosov.Topology.Homology.SupportHomeomorphism
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Homeomorphism transport for mod-two support homology

This is the coefficient-`ZMod 2` counterpart of the existing integer-module
`support_homeomorph_homology_isIso`.  It is the chart-transport interface
needed by Hatcher's compact-support detection argument: a homeomorphism of
ambient spaces carrying a support set onto another support set induces an
isomorphism on the literal relative singular support groups over the lifted
one-dimensional `ZMod 2` module.

Source: Hatcher, *Algebraic Topology*, pp.115--118 and Lemma 3.27, p.237,
with coefficients p.153.  The proof is the same pair-map argument as the
integer provider: restrict the homeomorphism to complements, observe that
both components of the singular-pair map are isomorphisms, and apply the
relative homology functor.  The declaration is named separately because the
existing provider is fixed to `ModuleCat ℤ`; no coefficient coercion is
silently assumed here.
-/

noncomputable section

open CategoryTheory HolomorphicAnosov.Topology _root_.Topology
namespace HolomorphicAnosov.HatcherCompactSupport

universe u

theorem modTwo_support_homeomorph_homology_isIso
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (K : Set X) (L : Set Y)
    (hKL : ∀ x, x ∈ K ↔ e x ∈ L) (q : ℕ) :
    IsIso (SSetPair.homologyMap
      (supportSingularPairMap (X := TopCat.of X) (Y := TopCat.of Y) K L
        (TopCat.ofHom ⟨e, e.continuous⟩)
        (fun x hx hL ↦ hx ((hKL x).mpr hL)))
      (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) q) := by
  let f := supportSingularPairMap (X := TopCat.of X) (Y := TopCat.of Y) K L
    (TopCat.ofHom ⟨e, e.continuous⟩)
    (fun x hx hL ↦ hx ((hKL x).mpr hL))
  let ec : ↥(Kᶜ) ≃ₜ ↥(Lᶜ) := e.subtype (fun x ↦ not_congr (hKL x))
  have hleft : IsIso f.hom.left := by
    change IsIso (TopCat.toSSet.map
      (TopCat.isoOfHomeo (X := TopCat.of ↥(Kᶜ)) (Y := TopCat.of ↥(Lᶜ)) ec).hom)
    infer_instance
  have hright : IsIso f.hom.right := by
    change IsIso (TopCat.toSSet.map
      (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e).hom)
    infer_instance
  have harrow : IsIso f.hom := Arrow.isIso_of_isIso_left_of_isIso_right f.hom
  have hforget : IsIso (SSetPair.forget.map f) := harrow
  have hf : IsIso f := isIso_of_reflects_iso f SSetPair.forget
  change IsIso ((SSetPair.homologyFunctor
    (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) q).map f)
  infer_instance

end HolomorphicAnosov.HatcherCompactSupport

