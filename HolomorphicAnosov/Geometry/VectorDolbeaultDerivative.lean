import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.Star

/-!
This file defines the tangent-valued antiholomorphic derivative in preferred holomorphic
coordinates and local representatives of conjugate-linear tensor fields. (Zhang, Lemma 4.3;
Demailly, Ch. I §3.C and Ch. V §11) -/

namespace HolomorphicAnosov

open scoped Manifold ContDiff

noncomputable section

variable {d : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [IsManifold (complexModel d) 1 X]

/-- The coordinate coefficients of `V` in the preferred tangent trivialization anchored at `x`,
pulled back along the inverse base chart. (Demailly, Ch. II §3.1, pp. 85–86) -/
def preferredVectorCoefficients
    (V : (y : X) → TangentSpace (complexModel d) y) (x : X) :
    ComplexModel d → ComplexModel d :=
  fun z ↦ (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
    ⟨(chartAt (ComplexModel d) x).symm z, V ((chartAt (ComplexModel d) x).symm z)⟩).2

/-- The `(j,k)` Wirtinger derivative of the tangent coefficients of `V` at `x`, given by half the
real-coordinate derivative plus `I` times the imaginary-coordinate derivative. (Demailly, Ch. I
§3.C, pp. 22–24) -/
def vectorDolbeaultCoefficient
    (V : (y : X) → TangentSpace (complexModel d) y) (x : X) (j k : Fin d) : ℂ :=
  (fderiv ℝ (fun z ↦ preferredVectorCoefficients V x z j) (chartAt (ComplexModel d) x x)
      (Pi.single k 1) +
    Complex.I * fderiv ℝ (fun z ↦ preferredVectorCoefficients V x z j)
      (chartAt (ComplexModel d) x x) (Pi.single k Complex.I)) / 2

/-- The complex-linear map whose matrix entries are `vectorDolbeaultCoefficient V x j k`. (Zhang,
Lemma 4.3, p. 15; Demailly, Ch. V §11, pp. 267–268) -/
def vectorDolbeaultMatrix
    (V : (y : X) → TangentSpace (complexModel d) y) (x : X) :
    ComplexModel d →L[ℂ] ComplexModel d :=
  ContinuousLinearMap.pi fun j ↦
    ∑ k : Fin d, vectorDolbeaultCoefficient V x j k • ContinuousLinearMap.proj k

/-- The tangent-valued Dolbeault derivative of `V` at `x`, represented by a continuous conjugate-
linear map on the tangent fiber using the preferred trivialization. (Zhang, Lemma 4.3, p. 15;
Demailly, Ch. V §11, pp. 267–268) -/
def vectorDolbeault
    (V : (y : X) → TangentSpace (complexModel d) y) (x : X) :
    TangentSpace (complexModel d) x →L⋆[ℂ] TangentSpace (complexModel d) x :=
  let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
  (t.symmL ℂ x).comp ((vectorDolbeaultMatrix V x).comp
    (((starL ℂ : ComplexModel d ≃L⋆[ℂ] ComplexModel d).toContinuousLinearMap).comp
      (t.continuousLinearMapAt ℂ x)))

/-- The local representative of a tangent-valued `(0,1)`-tensor field in the preferred chart
anchored at `a`, with both input and output expressed in its tangent trivialization. (Demailly,
Ch. II §3.1, pp. 85–86 and Ch. V §11, p. 267) -/
def preferredAntilinearTensorCoefficients
    (B : (x : X) → TangentSpace (complexModel d) x →L⋆[ℂ]
      TangentSpace (complexModel d) x) (a : X) :
    ComplexModel d → (ComplexModel d →L⋆[ℂ] ComplexModel d) :=
  fun z ↦
    let x := (chartAt (ComplexModel d) a).symm z
    let t := trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) a
    (t.continuousLinearMapAt ℂ x).comp ((B x).comp (t.symmL ℂ x))

end

end HolomorphicAnosov
