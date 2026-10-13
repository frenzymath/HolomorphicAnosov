import HolomorphicAnosov.Targets.Theorem11Support.Surface.integerMatrix

/-!
The entries of a lattice automorphism matrix are its basis coordinates.
-/

noncomputable section

namespace HolomorphicAnosov.Theorem11SupportW10

universe u

/-- The `j`-th column is the lattice-coordinate vector of the image of `b j`. -/
theorem integerMatrix_apply (L : FullComplexLattice 2) (B : LatticeLinearEquiv L)
    (b : Module.Basis (Fin 4) ℤ L.lattice) (i j : Fin 4) :
    integerMatrix L B b i j = b.repr (latticeEquiv L B (b j)) i :=
  LinearMap.toMatrix_apply b b _ i j

end HolomorphicAnosov.Theorem11SupportW10

