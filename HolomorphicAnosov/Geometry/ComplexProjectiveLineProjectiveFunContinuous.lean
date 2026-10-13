import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLineBase
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveQuotientMap
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveSourceOpen
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveSourceMk
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveFunMk

namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section


/-- The quotient ratio is continuous on its nonzero-denominator domain. (Demailly, §15.A) -/
theorem projective_fun_continuous (j : Fin 2) :
    ContinuousOn (complexProjectiveLineChartFun j) (complexProjectiveLineChartSource j) := by
  apply (projective_quotient_map.continuousOn_isOpen_iff (projective_source_open j)).mpr
  have hratio : ContinuousOn (fun v : {v : ComplexModel 2 // v ≠ 0} ↦
      (fun _ : Fin 1 ↦ v.1 (j + 1) / v.1 j))
      ((fun v : {v : ComplexModel 2 // v ≠ 0} ↦ complexProjectiveLineMk v.1 v.2) ⁻¹'
        complexProjectiveLineChartSource j) := by
    apply continuousOn_pi.mpr
    intro k
    apply (((continuous_apply (j + 1)).comp continuous_subtype_val).continuousOn).div
      (((continuous_apply j).comp continuous_subtype_val).continuousOn)
    intro v hv
    exact (projective_source_mk j v.1 v.2).mp hv
  apply hratio.congr
  intro v _
  exact projective_fun_mk j v.1 v.2

