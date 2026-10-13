import HolomorphicAnosov.Topology.EuclideanSupportOrientation

/-!
# Inclusion naturality of Euclidean supported orientations

Stage 1 DAG node: `topo.euclidean_support_orientation_subset_naturality_g13`.

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), §1.1 and §1.3, printed p.1; Hatcher,
*Algebraic Topology*, pp.118–124 (excision and naturality of relative homology maps).

Proof dependencies: `topo.euclidean_support_orientation_g10` (the native support pair,
finite inclusion, its excision `IsIso` certificate, and the definition of the supported
orientation); Mathlib `SSetPair.homologyMap_comp`,
`CategoryTheory.MorphismProperty.Arrow.Hom.ext`, `CategoryTheory.Functor.map_comp`,
and `CategoryTheory.IsIso.eq_inv_comp`/`IsIso.hom_inv_id`.

Mathlib search evidence (searched 2026-10-10): Mathlib has functorial composition for
ordinary singular-pair homology maps and the categorical inverse identities, but no theorem
packaging naturality of this particular Euclidean compactification-supported orientation.
The statement below is therefore a project-level Stage 1 provider.

The map is the literal inclusion of native subspaces `V → U`, with the complement map
`V \ K → U \ K`; no abstract equivalence of open sets is introduced.

Axiom audit (2026-10-10): compiling this module and printing
`#print axioms HolomorphicAnosov.euclideanSupportOrientation_subset_naturality` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`. The new map and naturality proof
contain no `sorry`; the inherited `sorryAx` comes from upstream declarations used by the
orientation definition/certificate, in particular `euclideanPositiveCompactificationClass`
and `singular_homology_excision_barycentric_subdivision` (both currently have postponed
proof obligations in their source dependency chain). This module does not conceal or add
that axiom; after those upstream providers are completed, the same theorem should print
only the comparator-permitted axioms.
-/

noncomputable section

namespace HolomorphicAnosov

open CategoryTheory Set

/-- The pair map induced by an inclusion of native Euclidean subspaces `V ⊆ U`.

Source: Dold §1.1 p.1; Hatcher p.118. Its ambient component is the subtype inclusion
`V → U`, and its complement component sends a point outside `K` in `V` to the same
ambient point outside `K` in `U`.
-/
private def euclideanSupportPairSubsetMap
    (n : ℕ) (V U K : Set (EuclideanSpace ℝ (Fin n)))
    (hVU : V ⊆ U) :
    euclideanSupportPair n V K ⟶ euclideanSupportPair n U K :=
  singularSubspacePairMap
    (TopCat.ofHom ⟨fun x : V => (⟨x.1, hVU x.2⟩ : U),
      continuous_subtype_val.subtype_mk _⟩)
    {u : V | (u : EuclideanSpace ℝ (Fin n)) ∉ K}
    {u : U | (u : EuclideanSpace ℝ (Fin n)) ∉ K}
    (by
      intro u hu hk
      exact hu hk)

/-- The subset pair map followed by finite compactification inclusion is the smaller
finite compactification inclusion. -/
private theorem euclideanSupportPairSubsetMap_comp_finiteInclusion
    (n : ℕ) (V U K : Set (EuclideanSpace ℝ (Fin n)))
    (hVU : V ⊆ U) :
    euclideanSupportPairSubsetMap n V U K hVU ≫
        euclideanSupportPairInclusion n U K =
      euclideanSupportPairInclusion n V K := by
  apply MorphismProperty.Arrow.Hom.ext
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
    rw [← Functor.map_comp]
    rfl
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
    rw [← Functor.map_comp]
    rfl

/-- Inclusion naturality of the canonical supported orientation.

For compact `K ⊆ V ⊆ U`, the relative homology map induced by `V ↪ U` sends
`o(V,K)` to `o(U,K)`. This is Dold's restriction/naturality assertion for the
canonical excision-supported class, written on the native pairs used by the index.
-/
theorem euclideanSupportOrientation_subset_naturality
    (n : ℕ) (V U K : Set (EuclideanSpace ℝ (Fin n)))
    (hV : IsOpen V) (hU : IsOpen U) (hK : IsCompact K)
    (hKV : K ⊆ V) (hVU : V ⊆ U) :
    SSetPair.homologyMap
        (singularSubspacePairMap
          (TopCat.ofHom ⟨fun x : V => (⟨x.1, hVU x.2⟩ : U),
            continuous_subtype_val.subtype_mk _⟩)
          {u : V | (u : EuclideanSpace ℝ (Fin n)) ∉ K}
          {u : U | (u : EuclideanSpace ℝ (Fin n)) ∉ K} (by
            intro u hu hk
            exact hu hk))
      reducedSingularIntegralCoefficients n
      (euclideanSupportOrientation n V K hV hK hKV) =
      euclideanSupportOrientation n U K hU hK (hKV.trans hVU) := by
  let eV := euclideanSupportHomologyInclusion n V K
  let eU := euclideanSupportHomologyInclusion n U K
  let r := SSetPair.homologyMap
    (euclideanSupportPairSubsetMap n V U K hVU)
      reducedSingularIntegralCoefficients n
  let hViso : IsIso eV := euclideanSupportHomologyInclusion_isIso n V K hV hK hKV
  let hUiso : IsIso eU := euclideanSupportHomologyInclusion_isIso n U K hU hK
    (hKV.trans hVU)
  have her : r ≫ eU = eV := by
    change SSetPair.homologyMap (euclideanSupportPairSubsetMap n V U K hVU)
        reducedSingularIntegralCoefficients n ≫
      SSetPair.homologyMap (euclideanSupportPairInclusion n U K)
        reducedSingularIntegralCoefficients n = _
    rw [← SSetPair.homologyMap_comp]
    rw [euclideanSupportPairSubsetMap_comp_finiteInclusion]
    rfl
  have hinv : (inv eV) ≫ r = inv eU := by
    symm
    apply (IsIso.eq_inv_comp eV).2
    rw [← her]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  change (r.hom ((inv eV).hom
      ((euclideanSupportCompactificationProjection n K).hom
        (euclideanPositiveCompactificationClass n)))) =
    (inv eU).hom ((euclideanSupportCompactificationProjection n K).hom
      (euclideanPositiveCompactificationClass n))
  rw [← hinv]
  rfl

end HolomorphicAnosov
