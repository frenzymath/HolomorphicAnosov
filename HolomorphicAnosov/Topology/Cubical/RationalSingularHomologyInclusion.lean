import HolomorphicAnosov.Topology.Cubical.RationalSingularHomology

/-!
# Rational singular homology induced by subset inclusion

Source: Hatcher, *Algebraic Topology*, coefficient chains p.153 and naturality
pp.111–112. DAG node: `topo.cubical_rational_singular_homology_inclusion_g12`.
-/

noncomputable section
open CategoryTheory
namespace HolomorphicAnosov.Cubical

/-- The actual singular-homology morphism induced by continuous subtype inclusion.
Source: Hatcher, Theorem 2.35, pp. 139–140, naturality for subcomplex inclusions. -/
abbrev rationalSingularHomologyInclusion {N : ℕ} {A B : Set (Fin N → ℝ)}
    (hAB : A ⊆ B) (q : ℕ) : rationalSingularHomology A q ⟶ rationalSingularHomology B q :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
    (ModuleCat.of ℚ ℚ)).map (TopCat.ofHom (ContinuousMap.inclusion hAB))

end HolomorphicAnosov.Cubical
