import HolomorphicAnosov.Targets.Theorem11Support.Surface.latticeEquiv

/-!
The restricted lattice automorphism agrees with the ambient complex-linear map.
-/

noncomputable section

namespace HolomorphicAnosov.Theorem11SupportW10

universe u

@[simp] theorem latticeEquiv_apply (L : FullComplexLattice 2)
    (B : LatticeLinearEquiv L) (v : L.lattice) :
    (latticeEquiv L B v : ComplexModel 2) = B.linear v := rfl

end HolomorphicAnosov.Theorem11SupportW10

