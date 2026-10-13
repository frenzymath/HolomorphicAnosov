import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.HermitianTangentMetric

/-! This file defines complex one-forms and their holomorphicity in compatible charts. (Demailly, I §3.C.) -/



open scoped ContDiff

namespace HolomorphicAnosov

universe u

/-- A complex one-form assigns a continuous complex-linear functional on each native complex tangent fibre. In finite dimension all complex-linear functionals are continuous. (Demailly, I §3.C; Zhang, Lemmas 4.2–4.3.) -/
abbrev ComplexOneForm (d : ℕ) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] :=
  ∀ x : X, TangentSpace (complexModel d) x →L[ℂ] ℂ

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- The scalar coefficient of a complex one-form in the `i`th holomorphic coordinate. The native inverse-chart differential transports the standard coordinate vector to the tangent fibre at `e.symm z`; evaluation by the actual form gives the coefficient of `dz_i`. (Demailly, I §3.C; Zhang, Lemmas 4.2–4.3.) -/
noncomputable def complexOneFormChartCoefficient (θ : ComplexOneForm d X)
    (e : OpenPartialHomeomorph X (ComplexModel d)) (i : Fin d) (z : ComplexModel d) : ℂ :=
  θ (e.symm z) (hermitianTangentChartFrame e z i)

/-- A complex one-form is holomorphic when all its scalar cotangent coefficients are holomorphic on the actual target of every compatible complex chart. (Demailly, I §3.C; Zhang, Lemmas 4.2–4.3.) -/
def IsHolomorphicComplexOneForm [IsManifold (complexModel d) ∞ X]
    (θ : ComplexOneForm d X) : Prop :=
  ∀ e : OpenPartialHomeomorph X (ComplexModel d),
    e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
    ∀ i : Fin d, ContDiffOn ℂ ∞ (complexOneFormChartCoefficient θ e i) e.target

end HolomorphicAnosov
