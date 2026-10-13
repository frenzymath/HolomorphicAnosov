import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Real tangent top forms, their chart coefficients, and their pullbacks are defined using paired
real and imaginary coordinate directions. Smooth positive forms have smooth positive
coefficients in every compatible holomorphic chart. (Demailly, VI §4, pp. 296–297; I (1.13), p.
10) -/

open scoped ContDiff

namespace HolomorphicAnosov

universe u

/-- Paired real coordinate indices for a complex `d`-dimensional model. (Demailly, VI §4, p. 296) -/
abbrev ComplexPairedIndex (d : ℕ) := Fin d × Fin 2

/-- The continuous real-linear map giving real and imaginary coordinates in paired order. (Demailly,
VI §4, p. 296) -/
noncomputable def complexPairedCoordinates (d : ℕ) :
    ComplexModel d →L[ℝ] (ComplexPairedIndex d → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    (if i.2 = 0 then Complex.reCLM else Complex.imCLM).comp
      (ContinuousLinearMap.proj i.1)

/-- The continuous alternating determinant form on paired real coordinates. (Demailly, VI §4, p.
296) -/
noncomputable def pairedCoordinateDeterminant (d : ℕ) :
    (ComplexPairedIndex d → ℝ) [⋀^ComplexPairedIndex d]→L[ℝ] ℝ :=
  { (Matrix.detRowAlternating :
      (ComplexPairedIndex d → ℝ) [⋀^ComplexPairedIndex d]→ₗ[ℝ] ℝ) with
    cont := continuous_id.matrix_det }

/-- The canonical paired-coordinate real top form on the complex model. (Demailly, VI §4, p. 296) -/
noncomputable def complexCoordinateTopForm (d : ℕ) :
    ComplexModel d [⋀^ComplexPairedIndex d]→L[ℝ] ℝ :=
  (pairedCoordinateDeterminant d).compContinuousLinearMap (complexPairedCoordinates d)

/-- A family of continuous alternating real top forms on the real tangent fibres. (Demailly, I §1.B;
VI §4, p. 296) -/
abbrev RealTangentTopForm (d : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] :=
  ∀ x : X, TangentSpace (realModel d) x [⋀^ComplexPairedIndex d]→L[ℝ] ℝ

variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- The real inverse-chart tangent frame in paired real and imaginary order. (Demailly, VI §4, p.
296) -/
noncomputable def realTangentPairedChartFrame
    (e : OpenPartialHomeomorph X (ComplexModel d)) (z : ComplexModel d)
    (i : ComplexPairedIndex d) : TangentSpace (realModel d) (e.symm z) :=
  mfderiv (realModel d) (realModel d) e.symm z
    ((NormedSpace.fromTangentSpace z).symm
      (Pi.single i.1 (if i.2 = 0 then 1 else Complex.I)))

/-- The coefficient of a top form evaluated on the paired inverse-chart tangent frame. (Demailly, I
§1.B; VI §4, p. 296) -/
noncomputable def realTangentTopFormChartCoefficient (ν : RealTangentTopForm d X)
    (e : OpenPartialHomeomorph X (ComplexModel d)) (z : ComplexModel d) : ℝ :=
  ν (e.symm z) (realTangentPairedChartFrame e z)

/-- A real top form is smooth and positive for the complex orientation when its coefficient in every
compatible holomorphic chart is real smooth and positive. (Demailly, VI §4, (4.2), pp. 296–297) -/
def IsSmoothPositiveRealTangentTopForm [IsManifold (complexModel d) ∞ X]
    (ν : RealTangentTopForm d X) : Prop :=
  ∀ e : OpenPartialHomeomorph X (ComplexModel d),
    e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
    ContDiffOn ℝ ∞ (realTangentTopFormChartCoefficient ν e) e.target ∧
      ∀ z ∈ e.target, 0 < realTangentTopFormChartCoefficient ν e z

/-- The type of real tangent top forms with smooth positive coefficients in every compatible
holomorphic chart. (Demailly, VI §4, pp. 296–297) -/
abbrev SmoothPositiveRealTangentTopForm [IsManifold (complexModel d) ∞ X] :=
  {ν : RealTangentTopForm d X // IsSmoothPositiveRealTangentTopForm ν}

/-- The pullback of a real tangent top form by composition with the real manifold differential.
(Demailly, I (1.13), p. 10) -/
noncomputable def realTangentTopFormPullback (F : X → X) (ν : RealTangentTopForm d X) :
    RealTangentTopForm d X :=
  fun x => (ν (F x)).compContinuousLinearMap (mfderiv (realModel d) (realModel d) F x)

/-- Pointwise multiplication of a real tangent top form by a real function. (Demailly, I §1.B; VI
§4) -/
noncomputable def realTangentTopFormScale (J : X → ℝ) (ν : RealTangentTopForm d X) :
    RealTangentTopForm d X :=
  fun x => J x • ν x

/-- The coordinate top form transported to a real tangent fibre by the chart differential.
(Demailly, I (1.13), p. 10) -/
noncomputable def realTangentCoordinateTopFormAt
    (e : OpenPartialHomeomorph X (ComplexModel d)) (x : X) :
    TangentSpace (realModel d) x [⋀^ComplexPairedIndex d]→L[ℝ] ℝ :=
  (complexCoordinateTopForm d).compContinuousLinearMap
    ((NormedSpace.fromTangentSpace (e x)).toContinuousLinearMap.comp
      (mfderiv (realModel d) (realModel d) e x))

end HolomorphicAnosov
