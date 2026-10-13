import HolomorphicAnosov.Topology.SignedSingularCrossProductNaturality
import HolomorphicAnosov.Topology.SingularRelativeProjectionMapZero

/-!
# Relative projection of a product supported in the second subspace

Source: Bredon, Topology and Geometry, IV§16.3 p.222; Hatcher, Algebraic
Topology, §2.1 p.118. This is the symmetric support statement for X×B.
DAG node: `topo.signed_cross_product_right_subspace_vanishes_g18`.
-/

open CategoryTheory
open scoped Simplicial

namespace HolomorphicAnosov.Topology

open HolomorphicAnosov.SignedSingularCrossProduct

universe u

/-- The product of an arbitrary X-chain with a chain carried by B projects to
zero in the relative chain complex of `(X×Y, A×Y ∪ X×B)`.

Source: Bredon IV16.3 p.222 and Hatcher p.118. Use naturality for the identity
of X and the inclusion B→Y, then apply the factor-through-subspace projection
zero lemma to X×B→X×Y. -/
theorem signedCrossProduct_right_subspace_vanishes
    {X Y : TopCat.{u}} (A : Set X) (B : Set Y) (p q : ℕ)
    (a : Chain X p) (b : Chain (TopCat.of B) q) :
    ((singularSubspacePair (TopCat.of (X × Y)) (A ×ˢ Set.univ ∪ Set.univ ×ˢ B)).chainComplexπ singularIntegralCoefficients).f (p + q)
      (signedSingularCrossProduct X Y p q a
        ((SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion Y B)) singularIntegralCoefficients).f q b)) = 0 := by
  let proj : Chain (TopCat.of (X × Y)) (p + q) ⟶
      ((singularSubspacePair (TopCat.of (X × Y))
        (A ×ˢ Set.univ ∪ Set.univ ×ˢ B)).chainComplex singularIntegralCoefficients).X (p + q) :=
    ((singularSubspacePair (TopCat.of (X × Y))
      (A ×ˢ Set.univ ∪ Set.univ ×ˢ B)).chainComplexπ singularIntegralCoefficients).f (p + q)
  change proj (signedSingularCrossProduct X Y p q a
    ((SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion Y B))
      singularIntegralCoefficients).f q b)) = 0
  let iB : TopCat.of B ⟶ Y := singularSubspaceInclusion Y B
  let idX : X ⟶ X := 𝟙 X
  let j : TopCat.of (X × B) ⟶ TopCat.of (X × Y) :=
    TopCat.ofHom (idX.hom.prodMap iB.hom)
  have hj : ∀ z, j z ∈ (A ×ˢ Set.univ ∪ Set.univ ×ˢ B) := by
    rintro ⟨x, b'⟩
    exact Or.inr ⟨Set.mem_univ _, b'.property⟩
  have hz := singularRelativeProjection_map_eq_zero j
    (A ×ˢ Set.univ ∪ Set.univ ×ˢ B) hj (p + q)
  have hn := signedSingularCrossProduct_naturality
    X (TopCat.of B) X Y idX iB p q a b
  have hz' := congrArg (fun k ↦ k
    (signedSingularCrossProduct X (TopCat.of B) p q a b)) hz
  change proj ((SSet.chainComplexMap (TopCat.toSSet.map j)
      singularIntegralCoefficients).f (p + q)
      (signedSingularCrossProduct X (TopCat.of B) p q a b)) = 0 at hz'
  have hprod :
      signedSingularCrossProduct X Y p q a
          ((SSet.chainComplexMap (TopCat.toSSet.map iB)
            singularIntegralCoefficients).f q b) =
        (SSet.chainComplexMap (TopCat.toSSet.map j)
          singularIntegralCoefficients).f (p + q)
          (signedSingularCrossProduct X (TopCat.of B) p q a b) := by
    symm
    simpa [iB, idX, j] using hn
  rw [hprod]
  exact hz' 

end HolomorphicAnosov.Topology

