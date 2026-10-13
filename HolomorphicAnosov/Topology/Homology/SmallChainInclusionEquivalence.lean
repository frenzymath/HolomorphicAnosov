import HolomorphicAnosov.Topology.SingularHomologyExcision

open CategoryTheory Set

namespace HolomorphicAnosov

universe u

/-- The literal inclusion of chains small for an interior cover is a chain
homotopy equivalence with arbitrary abelian coefficients.

Source: Hatcher, Algebraic Topology, Proposition 2.21 and its proof,
pp.121–124; arbitrary coefficient groups p.153. The variable-depth subdivision
construction gives a retraction rho onto chains whose simplices lie entirely
in either cover member. On that subcomplex rho is the identity, while on all
chains its composite with inclusion is homotopic to the identity by the actual
subdivision homotopy. These two already constructed identities give the stated
chain equivalence, with forward map exactly the inclusion. This includes empty
spaces, empty cover members, and ordinary degree zero. -/
theorem small_chain_inclusion_homotopy_equivalence
    (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = univ) (R : ModuleCat.{u} ℤ) :
    ∃ e : HomotopyEquiv
      ((singularSubspace X A ⊔ singularSubspace X B).toSSet.chainComplex R)
      ((TopCat.toSSet.obj X).chainComplex R),
      e.hom = SSet.chainComplexMap (singularSubspace X A ⊔ singularSubspace X B).ι R := by
  refine ⟨{
    hom := SSet.chainComplexMap (singularSubspace X A ⊔ singularSubspace X B).ι R
    inv := NativeBarycentricOperators.smallChainRetraction X A B hcover R
    homotopyHomInvId := Homotopy.ofEq
      (NativeBarycentricOperators.inclusion_smallChainRetraction X A B hcover R)
    homotopyInvHomId := ?_ }, rfl⟩
  rw [NativeBarycentricOperators.smallChainRetraction_inclusion]
  exact (NativeBarycentricOperators.guardedSubdivisionHomotopy X A B hcover R).symm

end HolomorphicAnosov

