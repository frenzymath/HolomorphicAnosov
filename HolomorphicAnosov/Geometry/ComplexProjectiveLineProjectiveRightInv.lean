import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLineBase
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveFunMk
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveOtherNe

namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section


/-- The ratio chart recovers the corresponding coordinate of the normalized representative. (Demailly, §15.A) -/
theorem projective_right_inv (j : Fin 2) (z : ComplexModel 1) :
    complexProjectiveLineChartFun j (complexProjectiveLineChartInv j z) = z := by
  rw [complexProjectiveLineChartInv, projective_fun_mk]
  ext k
  have hk : k = 0 := Subsingleton.elim _ _
  simp [complexProjectiveLineChartVector, hk]

