import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLineBase

namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section


/-- The projective quotient map is a quotient map for the native topology. (Demailly, §15.A) -/
theorem projective_quotient_map : Topology.IsQuotientMap
    (fun v : {v : ComplexModel 2 // v ≠ 0} ↦ complexProjectiveLineMk v.1 v.2) :=
  isQuotientMap_quotient_mk'

