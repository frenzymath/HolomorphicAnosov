import HolomorphicAnosov.Topology.SignedSingularCrossProduct

/-!
# Naturality of the signed staircase simplex sum

Source: Hatcher, Algebraic Topology, §3.B pp.277–278; Bredon IV§16 pp.220–222.
Postcomposition preserves each simplex of the explicit signed triangulation.
DAG node: `topo.signed_simplex_product_naturality_g18`.
The proof is extracted from the existing G1/G5 simplex-naturality calculation.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.SignedSingularCrossProduct
universe u

/-- The signed product of two simplex generators commutes with continuous maps.
Source: Hatcher pp.277–278, signed simplex-product construction.
Proof: distribute the chain map over the finite sum and its integer coefficients.
The native simplicial-chain map sends a simplex generator to its postcomposition.
Postcomposing the two coordinate functions of each staircase simplex is
exactly the staircase simplex of the postcomposed generators. -/
theorem simplexProduct_naturality {X Y X' Y' : TopCat.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q) :
    (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (f.hom.prodMap g.hom)))
      (ModuleCat.of ℤ (ULift.{u} ℤ))).f (p + q) (simplexProduct X Y σ τ) =
      simplexProduct X' Y' ((TopCat.toSSet.map f).app _ σ)
        ((TopCat.toSSet.map g).app _ τ) := by
  simp only [simplexProduct, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  change (((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex
      (productSimplex X Y w σ τ)) ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (f.hom.prodMap g.hom)))
        (ModuleCat.of ℤ (ULift.{u} ℤ))).f (p + q)).hom (ULift.up 1) = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

end HolomorphicAnosov.SignedSingularCrossProduct

