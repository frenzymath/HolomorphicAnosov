import Mathlib.Algebra.Module.ZLattice.Basic
import HolomorphicAnosov.Geometry.ComplexModel

/-!
A full complex lattice is a discrete integer submodule of the complex model with full real span.
-/

namespace HolomorphicAnosov

structure FullComplexLattice (d : ℕ) where
  lattice : Submodule ℤ (ComplexModel d)
  discrete : DiscreteTopology lattice
  full : letI := discrete; IsZLattice ℝ lattice

end HolomorphicAnosov
