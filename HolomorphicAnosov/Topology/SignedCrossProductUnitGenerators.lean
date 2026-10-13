import HolomorphicAnosov.Topology.SignedSingularCrossProduct

/-!
# The signed chain product on unit simplex generators

Source: Hatcher, Algebraic Topology, §3.B pp.277–278, the simplex-product
formula extended bilinearly to singular chains. This extracts the compiled
G5 `probe_generators` calculation into a public module.
DAG node: `topo.signed_cross_product_unit_generators_g18`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.SignedSingularCrossProduct
universe u

/-- The bilinear signed cross product agrees with the explicit signed simplex sum
on two generators with positive unit coefficients.

Source: Hatcher, §3.B pp.277–278. Proof: apply the coproduct-descending linear
map to the first summand inclusion and then the second. The two defining
scalar-to-linear-map equivalences evaluate the unit coefficient as scalar one.
The resulting scalar action on the signed simplex sum is the identity.
This holds in every pair of natural degrees, including zero, without
nonemptiness hypotheses on the spaces. -/
theorem signedSingularCrossProduct_unit_generators (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X p) (τ : Simplex Y q) :
    signedSingularCrossProduct X Y p q
      (((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) (ULift.up 1))
      (((TopCat.toSSet.obj Y).ιChainComplex
        (R := ModuleCat.of ℤ (ULift.{u} ℤ)) τ) (ULift.up 1)) =
      simplexProduct X Y σ τ := by
  simp [signedSingularCrossProduct, rightLinear, SSet.ιChainComplex,
    LinearMap.ringLmapEquivSelf]
  exact (Chain (TopCat.of (X × Y)) (p + q)).isModule.one_smul _

end HolomorphicAnosov.SignedSingularCrossProduct

