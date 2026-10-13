import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.StandardSimplexPuncturedTransport
import HolomorphicAnosov.Topology.EmbeddedSimplexLocalRelativeClass
import HolomorphicAnosov.Topology.PointNeighborhoodExcision
import HolomorphicAnosov.Topology.SingularSubspaceHomeomorphHomology

/-!
# Closed-embedding transport for the local simplex class

DAG node: `topo.embedded_simplex_interior_transport_g20`.
Source: Hatcher, *Algebraic Topology*, pp.118–125 (functoriality and excision),
and local orientation comparison pp.233–234. The closed embedding identifies
the standard simplex with its image; when the deleted point lies in the
ambient interior of that image, excision identifies the image pair with the
ambient punctured Euclidean pair.
-/

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov

/-- The closed embedding's canonical homeomorphism onto its range induces a
bijection on the relative homology pairs obtained by deleting the corresponding
point. This is the functorial half of the image-to-ambient transport. -/
theorem embeddedSimplex_range_homology_bijective (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), EuclideanSpace ℝ (Fin (n + 1))))
    (hemb : Topology.IsClosedEmbedding s)
    (t : Convexity.StdSimplex ℝ (Fin (n + 2)))
    (ht : s t = 0) :
    Function.Bijective (SSetPair.homologyMap
      (singularSubspacePairMap
        (TopCat.ofHom ⟨hemb.toIsEmbedding.toHomeomorph,
          hemb.toIsEmbedding.toHomeomorph.continuous⟩)
        ({t} : Set _)ᶜ
        {y : Set.range s | (y : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0}
        (by
          intro x hx
          change (hemb.toIsEmbedding.toHomeomorph x : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0
          intro hz
          apply hx
          apply hemb.toIsEmbedding.toHomeomorph.injective
          apply Subtype.ext
          exact hz.trans ht.symm))
      reducedSingularIntegralCoefficients (n + 1)).hom := by
  let h := hemb.toIsEmbedding.toHomeomorph
  let A : Set (Convexity.StdSimplex ℝ (Fin (n + 2))) := ({t} : Set _)ᶜ
  let B : Set (Set.range s) := {y | (y : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0}
  have hh : ∀ x, h x ∈ B ↔ x ∈ A := by
    intro x
    constructor
    · intro hx hxt
      apply hx
      change s x = 0
      rw [hxt, ht]
    · intro hx hz
      apply hx
      apply h.injective
      apply Subtype.ext
      exact hz.trans ht.symm
  exact singular_subspace_homeomorph_homology_bijective
    (X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
    (Y := TopCat.of (Set.range s)) h A B hh
    reducedSingularIntegralCoefficients (n + 1)

/-- The image-to-ambient inclusion itself is an isomorphism by excision. -/
theorem embeddedSimplex_range_to_ambient_excision_isIso (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), EuclideanSpace ℝ (Fin (n + 1))))
    (hzero : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈ interior (Set.range s)) :
    IsIso (SSetPair.homologyMap
      (singularExcisionInclusion (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
        ({0} : Set _)ᶜ (Set.range s))
      reducedSingularIntegralCoefficients (n + 1)) := by
  exact point_neighborhood_excision_isIso
    (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) 0 (Set.range s)
    hzero reducedSingularIntegralCoefficients (n + 1)


section
open Opposite
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false

/-- Chain-level coefficient-one representative comparison used by the closed
embedding transport.

Source: Hatcher, pp. 118--125 and 233--234. the relative
chain map induced by an embedded simplex sends the projected identity
singular simplex in the punctured standard simplex to the projected singular
simplex defining `simplexLocalRelativeChain`.  Expand the
relative projection as the natural quotient map, use naturality of the
relative chain projection, and apply `SSet.ι_chainComplexMap_f` to the
identity simplex.  The resulting singular simplex is definitionally the
postcomposition by `s`, so the two coefficient-one chains are equal.  This
proved helper isolates the chain-representative calculation from the separate
homology-isomorphism and radial-transport arguments above.
-/
theorem embeddedSimplex_punctured_chain_representative_provider (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)),
      EuclideanSpace ℝ (Fin (n + 1))))
    (hemb : Topology.IsClosedEmbedding s)
    (t : Convexity.StdSimplex ℝ (Fin (n + 2)))
    (ht : s t = 0) :
    let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))
    let _Y := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
    let R := reducedSingularIntegralCoefficients
    let P := singularSubspacePair X ({t} : Set _)ᶜ
    let f := singularSubspacePairMap (TopCat.ofHom s) ({t} : Set _)ᶜ ({0} : Set _)ᶜ
      (fun _x hx hz ↦ hx (hemb.injective (hz.trans ht.symm)))
    let σ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm
      (ContinuousMap.id (Convexity.StdSimplex ℝ (Fin (n + 2))))
    (SSetPair.chainComplexMap f R).f (n + 1)
      ((P.chainComplexπ R).f (n + 1)
        (((TopCat.toSSet.obj X).ιChainComplex (R := R) σ) (ULift.up 1))) =
      simplexLocalRelativeChain (n + 1) s := by
  dsimp only
  let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))
  let Y := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
  let R := reducedSingularIntegralCoefficients
  let P := singularSubspacePair X ({t} : Set _)ᶜ
  let Q := singularSubspacePair Y ({0} : Set _)ᶜ
  let f := singularSubspacePairMap (TopCat.ofHom s) ({t} : Set _)ᶜ ({0} : Set _)ᶜ
    (fun x hx hz ↦ hx (hemb.injective (hz.trans ht.symm)))
  let σ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm
    (ContinuousMap.id (Convexity.StdSimplex ℝ (Fin (n + 2))))
  have hp : (P.chainComplexπ R).f (n + 1) ≫
      (SSetPair.chainComplexMap f R).f (n + 1) =
      (SSet.chainComplexMap f.hom.right R).f (n + 1) ≫
        (Q.chainComplexπ R).f (n + 1) := by
    simpa [SSetPair.chainComplexFunctorRight, SSetPair.chainComplexπ,
      SSetPair.chainComplexMap, SSet.chainComplexMap, HomologicalComplex.comp_f] using
      (congrArg (fun g ↦ g.f (n + 1))
        ((((SSetPair.chainComplexFunctorπ (ModuleCat ℤ)).app R).naturality f))).symm
  have hσ : f.hom.right.app _ σ = (Y.toSSetObjEquiv _).symm s := by
    apply (Y.toSSetObjEquiv _).injective
    ext u
    rfl
  have hm : (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
      (P.chainComplexπ R).f (n + 1) ≫ (SSetPair.chainComplexMap f R).f (n + 1) =
      (TopCat.toSSet.obj Y).ιChainComplex (R := R) ((Y.toSSetObjEquiv _).symm s) ≫
        (Q.chainComplexπ R).f (n + 1) := by
    rw [hp, ← Category.assoc, SSet.ι_chainComplexMap_f]
    change (TopCat.toSSet.obj Y).ιChainComplex (R := R) (f.hom.right.app _ σ) ≫
      (Q.chainComplexπ R).f (n + 1) = _
    exact congrArg (fun τ ↦ (TopCat.toSSet.obj Y).ιChainComplex (R := R) τ ≫
      (Q.chainComplexπ R).f (n + 1)) hσ
  exact congrArg (fun g ↦ g.hom (ULift.up 1)) hm

end

end HolomorphicAnosov


namespace HolomorphicAnosov
set_option backward.isDefEq.respectTransparency false

/-- The canonical map induced by the simplex is bijective on point-relative
homology when zero lies in its image interior. Factor it through the range
homeomorphism and then use point-neighborhood excision. -/
theorem embeddedSimplex_homologyMap_bijective (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), EuclideanSpace ℝ (Fin (n + 1))))
    (hemb : Topology.IsClosedEmbedding s)
    (hzero : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈ interior (Set.range s))
    (t : Convexity.StdSimplex ℝ (Fin (n + 2))) (ht : s t = 0) :
    Function.Bijective (SSetPair.homologyMap
      (singularSubspacePairMap (TopCat.ofHom s) ({t} : Set _)ᶜ ({0} : Set _)ᶜ
        (fun _x hx hz ↦ hx (hemb.injective (hz.trans ht.symm))))
      reducedSingularIntegralCoefficients (n + 1)).hom := by
  let h := hemb.toIsEmbedding.toHomeomorph
  let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))
  let Y := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
  let C := Set.range s
  let A : Set X := {t}ᶜ
  let B : Set Y := {0}ᶜ
  let a := singularSubspacePairMap (TopCat.ofHom ⟨h, h.continuous⟩) A
    {y : C | (y : Y) ∈ B}
    (fun x hx hz ↦ hx (hemb.injective (hz.trans ht.symm)))
  let b := singularExcisionInclusion Y B C
  let f := singularSubspacePairMap (TopCat.ofHom s) A B
    (fun x hx hz ↦ hx (hemb.injective (hz.trans ht.symm)))
  have hab : a ≫ b = f := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
      rw [← Functor.map_comp]
      rfl
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
      rw [← Functor.map_comp]
      rfl
  have ha : Function.Bijective (SSetPair.homologyMap a
      reducedSingularIntegralCoefficients (n + 1)).hom :=
    embeddedSimplex_range_homology_bijective n s hemb t ht
  have hb : IsIso (SSetPair.homologyMap b
      reducedSingularIntegralCoefficients (n + 1)) :=
    embeddedSimplex_range_to_ambient_excision_isIso n s hzero
  have hb' : Function.Bijective (SSetPair.homologyMap b
      reducedSingularIntegralCoefficients (n + 1)).hom :=
    (asIso (SSetPair.homologyMap b reducedSingularIntegralCoefficients (n + 1))).toLinearEquiv.bijective
  change Function.Bijective (SSetPair.homologyMap f reducedSingularIntegralCoefficients (n + 1)).hom
  rw [← hab, SSetPair.homologyMap_comp]
  exact hb'.comp ha

end HolomorphicAnosov

namespace HolomorphicAnosov
set_option backward.isDefEq.respectTransparency false

/-- Naturality carries the punctured identity class to the literal local class
of the embedded simplex. Source: Hatcher pp.111,118; the chain equality proved
above descends through the native cycle and homology quotient maps. -/
theorem embeddedSimplex_punctured_class_map (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), EuclideanSpace ℝ (Fin (n + 1))))
    (hemb : Topology.IsClosedEmbedding s)
    (t : Convexity.StdSimplex ℝ (Fin (n + 2))) (ht : s t = 0)
    (hfaces : ∀ (i : Fin (n + 2)) (u : Convexity.StdSimplex ℝ (Fin (n + 1))),
      t ≠ Convexity.StdSimplex.map i.succAbove u) :
    (SSetPair.homologyMap
      (singularSubspacePairMap (TopCat.ofHom s) ({t} : Set _)ᶜ ({0} : Set _)ᶜ
        (fun x hx hz ↦ hx (hemb.injective (hz.trans ht.symm))))
      reducedSingularIntegralCoefficients (n + 1))
        (standardSimplexPuncturedClass n t hfaces) = simplexLocalRelativeClass n s (by
          intro i u hs
          exact hfaces i u (hemb.injective (ht.trans hs.symm))) := by
  let f := singularSubspacePairMap (TopCat.ofHom s) ({t} : Set _)ᶜ ({0} : Set _)ᶜ
    (fun x hx hz ↦ hx (hemb.injective (hz.trans ht.symm)))
  unfold standardSimplexPuncturedClass simplexLocalRelativeClass
  apply GoodPair.shortComplex_homologyMap_cycle
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ)
      (n + 1)).map (SSetPair.chainComplexMap f reducedSingularIntegralCoefficients))
  exact embeddedSimplex_punctured_chain_representative_provider n s hemb t ht

end HolomorphicAnosov

namespace HolomorphicAnosov
set_option backward.isDefEq.respectTransparency false

/-- With the explicit image-interior premise available in the local-generator
parent, the canonical relative homology map is an equivalence preserving the
coefficient-one class. Source: Hatcher excision pp.119--124 and induced maps
p.111. Combine the range homeomorphism with excision, then use chain naturality. -/
theorem embeddedSimplex_closedEmbedding_transport_of_interior (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), EuclideanSpace ℝ (Fin (n + 1))))
    (hemb : Topology.IsClosedEmbedding s)
    (hzero : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈ interior (Set.range s))
    (t : Convexity.StdSimplex ℝ (Fin (n + 2))) (ht : s t = 0)
    (hfaces : ∀ (i : Fin (n + 2)) (u : Convexity.StdSimplex ℝ (Fin (n + 1))),
      t ≠ Convexity.StdSimplex.map i.succAbove u) :
    ∃ e :
      (singularSubspacePair
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
        ({t} : Set _)ᶜ).homology (C := ModuleCat ℤ)
          reducedSingularIntegralCoefficients (n + 1) ≃ₗ[ℤ]
      (singularSubspacePair
        (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
        ({0} : Set _)ᶜ).homology (C := ModuleCat ℤ) reducedSingularIntegralCoefficients
          (n + 1),
      e (standardSimplexPuncturedClass n t hfaces) = simplexLocalRelativeClass n s (by
        intro i u hs
        exact hfaces i u (hemb.injective (ht.trans hs.symm))) := by
  let f := SSetPair.homologyMap
    (singularSubspacePairMap (TopCat.ofHom s) ({t} : Set _)ᶜ ({0} : Set _)ᶜ
      (fun x hx hz ↦ hx (hemb.injective (hz.trans ht.symm))))
    reducedSingularIntegralCoefficients (n + 1)
  exact ⟨LinearEquiv.ofBijective f.hom
    (embeddedSimplex_homologyMap_bijective n s hemb hzero t ht),
    embeddedSimplex_punctured_class_map n s hemb t ht hfaces⟩

end HolomorphicAnosov
