import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic




/-! This file defines the quotient model of the complex projective line and its homogeneous-coordinate maps. (Demailly, V §15.A, p. 277; Ghys, p. 597).
-/
namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section

/-- The complex projective line is the quotient of nonzero complex pairs by nonzero scalar multiplication. (Demailly, V §15.A, p. 277). -/
abbrev ComplexProjectiveLine := Projectivization ℂ (ComplexModel 2)

/-- This is the native quotient topology on the nonzero-pair space. -/
instance complexProjectiveLineTopology : TopologicalSpace ComplexProjectiveLine :=
  inferInstanceAs
    (TopologicalSpace (Quotient (projectivizationSetoid ℂ (ComplexModel 2))))

/-- The homogeneous point `[x₀:x₁]` is the quotient class of a nonzero pair. (Demailly, V §15.A, p. 277). -/
def complexProjectiveLineMk (x : ComplexModel 2) (hx : x ≠ 0) : ComplexProjectiveLine :=
  Projectivization.mk ℂ x hx

/-- The `j`th homogeneous open set is `Ω_j = {[x] | x_j ≠ 0}`. (Demailly, V §15.A, p. 277). -/
def complexProjectiveLineChartSource (j : Fin 2) : Set ComplexProjectiveLine :=
  {p | p.rep j ≠ 0}

/-- The ratio chart is `τ_j([x]) = x_(j+1)/x_j` in the one-coordinate complex model. (Demailly, V §15.A, p. 277). -/
def complexProjectiveLineChartFun (j : Fin 2) (p : ComplexProjectiveLine) :
    ComplexModel 1 :=
  fun _ ↦ p.rep (j + 1) / p.rep j

/-- The normalized homogeneous vector has `j`th coordinate one and other coordinate `z`. -/
def complexProjectiveLineChartVector (j : Fin 2) (z : ComplexModel 1) : ComplexModel 2 :=
  fun i ↦ if i = j then 1 else z 0

/-- The normalized chart vector is nonzero because its `j`th coordinate is one. -/
theorem complexProjectiveLineChartVector_ne_zero (j : Fin 2) (z : ComplexModel 1) :
    complexProjectiveLineChartVector j z ≠ 0 := by
  intro h
  have h₁ := congrArg (fun v : ComplexModel 2 ↦ v j) h
  simp [complexProjectiveLineChartVector] at h₁

/-- The inverse of `τ_j` sends `z` to `[z:1]` for `j=1` and to `[1:z]` for `j=0`. (Demailly, V §15.A, p. 277). -/
def complexProjectiveLineChartInv (j : Fin 2) (z : ComplexModel 1) :
    ComplexProjectiveLine :=
  complexProjectiveLineMk (complexProjectiveLineChartVector j z)
    (complexProjectiveLineChartVector_ne_zero j z)


end

end HolomorphicAnosov
