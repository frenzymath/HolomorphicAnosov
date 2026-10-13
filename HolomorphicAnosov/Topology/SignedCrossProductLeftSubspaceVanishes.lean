import HolomorphicAnosov.Topology.SignedSingularCrossProduct
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import HolomorphicAnosov.Topology.SignedSingularCrossProductNaturality
import HolomorphicAnosov.Topology.SingularRelativeProjectionMapZero

/-!
# The signed product of a subspace chain vanishes relatively

Node: `topo.signed_cross_product_left_subspace_vanishes_g18`.
Source: Bredon, Topology and Geometry, IV §16.3, p.222; Hatcher,
Algebraic Topology, §2.1, p.118. The statement uses the native chain maps
and relative projection explicitly, avoiding an import of the consuming
relative-product theorem merely for its reducible aliases.
-/

open CategoryTheory
open scoped Simplicial
noncomputable section
universe u
namespace HolomorphicAnosov.Topology
open HolomorphicAnosov.SignedSingularCrossProduct

/-- The product with a chain supported in the first subspace is zero in the
relative product pair.

Source: Bredon IV §16.3, p.222, independence under addition of subspace chains;
Hatcher §2.1, p.118, quotient description of relative singular chains.

Proof: let j be the product of the inclusion A → X and the identity of Y.
Its image is contained in A × Y, hence in A × Y ∪ X × B. The relative-projection
map-zero theorem says that its singular chain map followed by the projection
to this relative pair is zero. Naturality of the signed product identifies
the product of the included A-chain and b with j applied to the product of
a and b formed in A × Y; the second-factor chain map is the identity by
functoriality. Apply the zero composite to that product chain. This works in
degree zero, for an empty A, and without any open-subspace or excision premise.

The native expressions below are definitionally the aliases `chainMap`,
`relativeProjection` and `ProductSubspace` used by the consumer; only their
abbreviated presentation has been expanded, not the chain complex or product.
-/
theorem signedCrossProduct_left_subspace_vanishes {X Y : TopCat.{u}}
    (A : Set X) (B : Set Y) (p q : ℕ)
    (a : Chain (TopCat.of A) p) (b : Chain Y q) :
    (((singularSubspacePair (TopCat.of (X × Y))
        (A ×ˢ Set.univ ∪ Set.univ ×ˢ B)).chainComplexπ
          singularIntegralCoefficients).f (p + q))
      (signedSingularCrossProduct X Y p q
        ((SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion X A))
          singularIntegralCoefficients).f p a) b) = 0 := by
  let proj : Chain (TopCat.of (X × Y)) (p + q) ⟶
      ((singularSubspacePair (TopCat.of (X × Y))
        (A ×ˢ Set.univ ∪ Set.univ ×ˢ B)).chainComplex singularIntegralCoefficients).X (p + q) :=
    ((singularSubspacePair (TopCat.of (X × Y))
      (A ×ˢ Set.univ ∪ Set.univ ×ˢ B)).chainComplexπ singularIntegralCoefficients).f (p + q)
  change proj (signedSingularCrossProduct X Y p q
    ((SSet.chainComplexMap (TopCat.toSSet.map (singularSubspaceInclusion X A))
      singularIntegralCoefficients).f p a) b) = 0
  let iA : TopCat.of A ⟶ X := singularSubspaceInclusion X A
  let idY : Y ⟶ Y := 𝟙 Y
  let j : TopCat.of (A × Y) ⟶ TopCat.of (X × Y) :=
    TopCat.ofHom (iA.hom.prodMap idY.hom)
  have hj : ∀ z, j z ∈ (A ×ˢ Set.univ ∪ Set.univ ×ˢ B) := by
    rintro ⟨a', y⟩
    exact Or.inl ⟨a'.property, Set.mem_univ _⟩
  have hz := singularRelativeProjection_map_eq_zero j
    (A ×ˢ Set.univ ∪ Set.univ ×ˢ B) hj (p + q)
  have hn := signedSingularCrossProduct_naturality
    (TopCat.of A) Y X Y iA idY p q a b
  have hz' := congrArg (fun k ↦ k
    (signedSingularCrossProduct (TopCat.of A) Y p q a b)) hz
  change proj ((SSet.chainComplexMap (TopCat.toSSet.map j)
      singularIntegralCoefficients).f (p + q)
      (signedSingularCrossProduct (TopCat.of A) Y p q a b)) = 0 at hz'
  have hprod :
      signedSingularCrossProduct X Y p q
          ((SSet.chainComplexMap (TopCat.toSSet.map iA)
            singularIntegralCoefficients).f p a) b =
        (SSet.chainComplexMap (TopCat.toSSet.map j)
          singularIntegralCoefficients).f (p + q)
          (signedSingularCrossProduct (TopCat.of A) Y p q a b) := by
    symm
    simpa [iA, idY, j] using hn
  rw [hprod]
  exact hz' 

end HolomorphicAnosov.Topology
