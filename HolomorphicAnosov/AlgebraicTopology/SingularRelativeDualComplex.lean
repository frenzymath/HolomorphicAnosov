import HolomorphicAnosov.AlgebraicTopology.CochainDualCokernel
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex

/-!
# Duality between relative singular chains and cochains

Source: Hatcher, *Algebraic Topology*, printed pp.199–200. The dual of the
relative chain cokernel is the kernel of cochain restriction; its inclusion
is the dual of the chain projection.
-/

open CategoryTheory CategoryTheory.Limits Opposite
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false

/-- Relative cochains are the dual of the relative singular chain complex, and
its inclusion in absolute cochains is dual to the relative-chain projection.
Source: Hatcher, Algebraic Topology, pp.199–200. The relative chain projection
is a cokernel. Its dual is a kernel by `cochain_dual_cokernel_iso`, giving the
isomorphism and the compatibility with inclusion from the kernel universal property. -/
theorem singular_relative_dual_complex_iso (R : Type u) [CommRing R]
    (X : TopCat.{u}) (A : Set X) :
    ∃ e : (dualFunctor R).obj
        (op ((singularSubspacePair X A).chainComplex (ModuleCat.of R R))) ≅
        relativeComplex R X A,
      e.hom ≫ kernel.ι (pullback R (subspaceInclusion X A)) =
        (dualFunctor R).map ((singularSubspacePair X A).chainComplexπ (ModuleCat.of R R)).op := by
  exact cochain_dual_cokernel_iso R _ _
    ((singularSubspacePair X A).chainComplex_condition (ModuleCat.of R R))
    ((singularSubspacePair X A).isColimitCokernelCoforkChainComplex (ModuleCat.of R R))

end HolomorphicAnosov.SingularCochain
