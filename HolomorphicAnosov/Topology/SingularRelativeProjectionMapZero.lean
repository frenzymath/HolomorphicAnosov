import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex

/-!
# Maps supported in a subspace vanish in relative chains

Source: Hatcher, Algebraic Topology, p.118, the relative singular chain quotient;
Bredon, Topology and Geometry, IV16.3 p.222, independence under addition of
subspace chains. DAG node: `topo.singular_relative_projection_map_zero_g18`.
-/

open CategoryTheory

namespace HolomorphicAnosov.Topology

universe u

set_option backward.isDefEq.respectTransparency false in
/-- If the image of a continuous map lies in a subspace, its singular chain map
followed by projection to chains relative to that subspace is zero.

Source: Hatcher p.118 and Bredon IV16.3 p.222. Proof: factor the continuous map
through the subspace with its induced topology. Functoriality factors its chain
map through the chain map of the subspace inclusion. The canonical relative
projection is a cokernel of that inclusion map, so this composite is zero.
The statement applies in degree zero and to empty or full subspaces. -/
theorem singularRelativeProjection_map_eq_zero {X Y : TopCat.{u}}
    (f : X ⟶ Y) (B : Set Y) (hf : ∀ x, f x ∈ B) (n : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) singularIntegralCoefficients.{u}).f n ≫
      ((singularSubspacePair Y B).chainComplexπ singularIntegralCoefficients.{u}).f n = 0 := by
  let fB : X ⟶ TopCat.of B :=
    TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have hfactor : f = fB ≫ singularSubspaceInclusion Y B := rfl
  rw [hfactor, Functor.map_comp]
  change (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj singularIntegralCoefficients.{u}).map
    (TopCat.toSSet.map fB ≫ TopCat.toSSet.map (singularSubspaceInclusion Y B))).f n ≫ _ = _
  rw [Functor.map_comp, HomologicalComplex.comp_f, Category.assoc]
  have hzero := (singularSubspacePair Y B).chainComplex_condition_f
    singularIntegralCoefficients.{u} n
  change (SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion Y B))
    singularIntegralCoefficients.{u}).f n ≫ _ = 0 at hzero
  rw [hzero]
  simp

end HolomorphicAnosov.Topology

