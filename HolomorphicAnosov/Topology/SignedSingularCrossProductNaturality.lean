import HolomorphicAnosov.Topology.SignedSimplexProductNaturality
import HolomorphicAnosov.Topology.SignedCrossProductUnitGenerators
import HolomorphicAnosov.Topology.SingularChainUnitGeneratorExt

/-!
# Naturality of the integral signed chain cross product

Source: Bredon, Topology and Geometry, IV§16 Theorem16.1, pp.221–222,
postcomposition on simplex generators and extension by bilinearity; Hatcher,
Algebraic Topology, pp.277–278, for the fixed signed staircase model.
DAG node: `topo.signed_singular_cross_product_naturality_g18`.
-/

open CategoryTheory
open scoped Simplicial

namespace HolomorphicAnosov.Topology

open HolomorphicAnosov.SignedSingularCrossProduct

universe u

/-- Applying a pair of continuous maps commutes with the signed integral
singular-chain cross product in every pair of natural degrees.

Source: Bredon IV16.1 pp.221–222 and Hatcher pp.277–278. Proof: both sides
are bilinear in the two chains. Apply the unit-generator extensionality
principle in each variable. Chain maps send each generator to its
postcomposed simplex; the product on unit generators is the signed staircase
sum. Naturality of that finite simplex sum proves the resulting equality.
There are no nonempty-space or positive-degree restrictions. -/
theorem signedSingularCrossProduct_naturality
    (X Y X' Y' : TopCat.{u}) (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ)
    (a : Chain X p) (b : Chain Y q) :
    (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (f.hom.prodMap g.hom)))
      (ModuleCat.of ℤ (ULift.{u} ℤ))).f (p + q)
        (signedSingularCrossProduct X Y p q a b) =
      signedSingularCrossProduct X' Y' p q
        ((SSet.chainComplexMap (TopCat.toSSet.map f)
          (ModuleCat.of ℤ (ULift.{u} ℤ))).f p a)
        ((SSet.chainComplexMap (TopCat.toSSet.map g)
          (ModuleCat.of ℤ (ULift.{u} ℤ))).f q b) := by
  let cf := (SSet.chainComplexMap (TopCat.toSSet.map f)
    (ModuleCat.of ℤ (ULift.{u} ℤ))).f p
  let cg := (SSet.chainComplexMap (TopCat.toSSet.map g)
    (ModuleCat.of ℤ (ULift.{u} ℤ))).f q
  let cfg := (SSet.chainComplexMap
    (TopCat.toSSet.map (TopCat.ofHom (f.hom.prodMap g.hom)))
    (ModuleCat.of ℤ (ULift.{u} ℤ))).f (p + q)
  let post : (Chain Y q →ₗ[ℤ] Chain (TopCat.of (X × Y)) (p + q)) →+
      (Chain Y q →ₗ[ℤ] Chain (TopCat.of (X' × Y')) (p + q)) :=
    { toFun := fun k => cfg.hom.comp k
      map_zero' := by ext b; simp
      map_add' := by intro k₁ k₂; ext b; simp }
  let pre : (Chain Y' q →ₗ[ℤ] Chain (TopCat.of (X' × Y')) (p + q)) →+
      (Chain Y q →ₗ[ℤ] Chain (TopCat.of (X' × Y')) (p + q)) :=
    { toFun := fun k => k.comp cg.hom
      map_zero' := by ext b; simp
      map_add' := by intro k₁ k₂; ext b; simp }
  let L := post.toIntLinearMap.comp (signedSingularCrossProduct X Y p q)
  let R := pre.toIntLinearMap.comp ((signedSingularCrossProduct X' Y' p q).comp cf.hom)
  have h : ModuleCat.ofHom L = ModuleCat.ofHom R := by
    apply singularChain_unitGenerator_ext X p
    intro σ
    let sa := ((TopCat.toSSet.obj X).ιChainComplex
      (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) (ULift.up 1)
    have h₂ : ModuleCat.ofHom (L sa) = ModuleCat.ofHom (R sa) := by
      apply singularChain_unitGenerator_ext Y q
      intro τ
      have hf := congrArg (fun k : ModuleCat.of ℤ (ULift.{u} ℤ) ⟶ Chain X' p =>
        k (ULift.up 1)) (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X)
          (TopCat.toSSet.obj X') (TopCat.toSSet.map f)
          (ModuleCat.of ℤ (ULift.{u} ℤ)) σ)
      have hg := congrArg (fun k : ModuleCat.of ℤ (ULift.{u} ℤ) ⟶ Chain Y' q =>
        k (ULift.up 1)) (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj Y)
          (TopCat.toSSet.obj Y') (TopCat.toSSet.map g)
          (ModuleCat.of ℤ (ULift.{u} ℤ)) τ)
      change cfg (signedSingularCrossProduct X Y p q sa
        (((TopCat.toSSet.obj Y).ιChainComplex
          (R := ModuleCat.of ℤ (ULift.{u} ℤ)) τ) (ULift.up 1))) =
        signedSingularCrossProduct X' Y' p q (cf sa)
          (cg (((TopCat.toSSet.obj Y).ιChainComplex
            (R := ModuleCat.of ℤ (ULift.{u} ℤ)) τ) (ULift.up 1)))
      change cf sa = _ at hf
      change cg (((TopCat.toSSet.obj Y).ιChainComplex
        (R := ModuleCat.of ℤ (ULift.{u} ℤ)) τ) (ULift.up 1)) = _ at hg
      rw [hf, hg]
      dsimp only [sa]
      rw [signedSingularCrossProduct_unit_generators,
        signedSingularCrossProduct_unit_generators]
      exact simplexProduct_naturality f g σ τ
    exact congrArg ModuleCat.Hom.hom h₂
  exact congrArg (fun k => k a b) h

end HolomorphicAnosov.Topology

