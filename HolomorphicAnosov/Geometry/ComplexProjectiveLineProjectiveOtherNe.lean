import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLineBase

namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section


/-- The normalized representatives in the two charts use the other coordinate. (Demailly, §15.A) -/
theorem projective_other_ne (j : Fin 2) : j + 1 ≠ j := by
  fin_cases j <;> decide

