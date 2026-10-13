import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLineBase
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveQuotientMap

namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section


/-- The normalized representative depends continuously on the projective point. (Demailly, §15.A) -/
theorem projective_inv_continuous (j : Fin 2) :
    Continuous (complexProjectiveLineChartInv j) := by
  have hv : Continuous (complexProjectiveLineChartVector j) := by
    apply continuous_pi
    intro i
    by_cases hi : i = j
    · simpa only [complexProjectiveLineChartVector, hi, ite_true] using
        (continuous_const : Continuous (fun _ : ComplexModel 1 ↦ (1 : ℂ)))
    · simpa only [complexProjectiveLineChartVector, hi, ite_false] using
        (continuous_apply (0 : Fin 1))
  exact projective_quotient_map.continuous.comp (hv.subtype_mk (fun z ↦
    complexProjectiveLineChartVector_ne_zero j z))

