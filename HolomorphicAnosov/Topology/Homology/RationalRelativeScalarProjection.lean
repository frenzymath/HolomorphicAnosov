import HolomorphicAnosov.Topology.Homology.RationalScalarTransportNaturality

/-! # Scalar transport commutes with the native relative projection

The chain-level compatibility used to transport the relative shuffle comparison
back to rational coefficients. Source: Bredon VI pp.318–320, implemented through
Mathlib's functorial cokernel and coefficient-comparison constructions.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace HolomorphicAnosov.RationalScalarTransport
set_option backward.isDefEq.respectTransparency false

/-- The native rational scalar comparison commutes with the actual projection
from absolute to relative chains. The relative comparison is defined by the
cokernel universal property, so its defining equation gives the scalar-change
square. Naturality of the coefficient projection gives the final coefficient-unit
square; composing them gives the stated equation.
DAG node: `topo.rational_relative_scalar_projection_g1`. -/
@[reassoc]
theorem nativeRelativeChainComparison_projection (P : SSetPair.{u}) :
    (scalarFunctor.mapHomologicalComplex (.down ℕ)).map
        (P.chainComplexπ qCoefficients) ≫ (nativeRelativeChainComparison P).hom =
      (nativeChainComparison P.right).hom ≫
        P.chainComplexπ (ModuleCat.of LiftQ.{u} LiftQ.{u}) := by
  have hrelative : (scalarFunctor.mapHomologicalComplex (.down ℕ)).map
        (P.chainComplexπ qCoefficients) ≫ (relativeChainComparison P).hom =
      (chainComparison P.right).hom ≫ P.chainComplexπ liftedCoefficients := by
    have h := CokernelCofork.π_mapOfIsColimit
      (isColimitCoforkMapOfIsColimit' (scalarFunctor.mapHomologicalComplex (.down ℕ))
        (P.chainComplex_condition qCoefficients)
        (P.isColimitCokernelCoforkChainComplex qCoefficients))
      (P.cokernelCoforkChainComplex liftedCoefficients)
      (Arrow.isoMk (chainComparison P.left) (chainComparison P.right)
        ((SSet.chainComplexFunctorObjCompMapIso.{u} scalarFunctor qCoefficients).hom.naturality
          P.hom).symm).hom
    exact h
  have hcoefficient := NatTrans.congr_app
    ((SSetPair.chainComplexFunctorπ (ModuleCat.{u} LiftQ.{u})).naturality
      coefficientComparison.hom) P
  change _ ≫ ((relativeChainComparison P).hom ≫ _) =
    ((chainComparison P.right).hom ≫ _) ≫ _
  rw [← Category.assoc, hrelative, Category.assoc, ← Category.assoc]
  exact congrArg (fun k ↦ (chainComparison P.right).hom ≫ k) hcoefficient.symm

end HolomorphicAnosov.RationalScalarTransport
