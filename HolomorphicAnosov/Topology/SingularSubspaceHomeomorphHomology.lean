import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex

/-!
# Homeomorphisms of subspaces induce bijections on relative singular homology

Source: Hatcher, Algebraic Topology, §2.1 pp.118–119, functoriality of relative homology.
DAG node: `topo.singular_subspace_homeomorph_homology_bijective_g16`.
-/

noncomputable section
open CategoryTheory
namespace HolomorphicAnosov

/-- A homeomorphism carrying one specified subspace exactly onto another induces a
bijection on the native relative singular homology, with any integer-module coefficients.

Source: Hatcher, Algebraic Topology, pp.118–119. Restrict the homeomorphism and its inverse
to the specified subspaces. The two maps of singular pairs compose to the identity on
both components, since the singular functor preserves compositions and identities.
Applying the relative homology functor gives an isomorphism, whose underlying linear
equivalence is bijective. No nonempty, open, closed, or good-pair hypothesis is used.
-/
theorem singular_subspace_homeomorph_homology_bijective
    {X Y : TopCat.{u}} (h : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hh : ∀ x, h x ∈ B ↔ x ∈ A) (R : ModuleCat.{u} ℤ) (n : ℕ) :
    Function.Bijective (SSetPair.homologyMap
      (singularSubspacePairMap (TopCat.ofHom ⟨h, h.continuous⟩) A B
        (fun x hx ↦ (hh x).2 hx)) R n).hom := by
  let f : X ⟶ Y := TopCat.ofHom ⟨h, h.continuous⟩
  let g : Y ⟶ X := TopCat.ofHom ⟨h.symm, h.symm.continuous⟩
  have hg : Set.MapsTo g B A := by
    intro y hy
    exact (hh (h.symm y)).1 (by simpa using hy)
  let e : singularSubspacePair X A ≅ singularSubspacePair Y B :=
    { hom := singularSubspacePairMap f A B (fun x hx ↦ (hh x).2 hx)
      inv := singularSubspacePairMap g B A hg
      hom_inv_id := by
        apply MorphismProperty.Arrow.Hom.ext
        · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = 𝟙 _
          rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
          congr 1
          ext x
          exact h.symm_apply_apply x.val
        · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = 𝟙 _
          rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
          congr 1
          ext x
          exact h.symm_apply_apply x
      inv_hom_id := by
        apply MorphismProperty.Arrow.Hom.ext
        · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = 𝟙 _
          rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
          congr 1
          ext y
          exact h.apply_symm_apply y.val
        · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = 𝟙 _
          rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
          congr 1
          ext y
          exact h.apply_symm_apply y }
  exact ((SSetPair.homologyFunctor R n).mapIso e).toLinearEquiv.bijective

end HolomorphicAnosov
