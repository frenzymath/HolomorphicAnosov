import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLineBase
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveQuotientMap
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveSourceMk

namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section


/-- The coordinate-nonvanishing subset is open in the projective quotient topology. (Demailly, §15.A) -/
theorem projective_source_open (j : Fin 2) : IsOpen (complexProjectiveLineChartSource j) := by
  apply projective_quotient_map.isOpen_preimage.mp
  have heq : (fun v : {v : ComplexModel 2 // v ≠ 0} ↦ complexProjectiveLineMk v.1 v.2) ⁻¹'
      complexProjectiveLineChartSource j = {v | v.1 j ≠ 0} := by
    ext v
    exact projective_source_mk j v.1 v.2
  rw [heq]
  exact isOpen_ne_fun ((continuous_apply j).comp continuous_subtype_val) continuous_const

