import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.PullbackCoordinateFormPointwise

open Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff Classical
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- Under the chart transport identity, the coordinate form of a quotient-line pullback connection
is the sum of a logarithmic gauge differential and the target coordinate form pulled back by the
coordinate map. -/
theorem pullback_coordinate_form_chart_transport
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (Dp D : QuotientLineConnection.Connection P)
    (f : Biholomorph d d X X)
    (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x))
    {V W : Opens X} (e : QuotientLineConnection.HolomorphicFrame P V)
    (e' : QuotientLineConnection.HolomorphicFrame P W)
    (c c' : OpenPartialHomeomorph X (ComplexModel d))
    (F : ComplexModel d → ComplexModel d)
    (z : ComplexModel d)
    (_hz : z ∈ c.target ∩ c.symm ⁻¹' (V : Set X))
    (_hfz : f (c.symm z) ∈ W)
    (hpull : Dp.form V e (c.symm z) =
      (QuotientLineConnection.imageFrameCoefficient f hf e e' (c.symm z))⁻¹ •
        QuotientLineConnection.realDifferential
          (QuotientLineConnection.imageFrameCoefficient f hf e e') (c.symm z) +
      (D.form W e' (f (c.symm z))).comp
        (mfderiv (realModel d) (realModel d) f (c.symm z)))
    (htransport :
      ((D.form W e' (f (c.symm z))).comp
          (mfderiv (realModel d) (realModel d) f (c.symm z))).comp
        ((mfderiv (realModel d) (realModel d) c.symm z).comp
          (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap) =
      (QuotientLineConnection.coordinateForm D e' c'
          (F z)).comp (fderiv ℝ F z)) :
    QuotientLineConnection.coordinateForm Dp e c z =
      ((QuotientLineConnection.imageFrameCoefficient f hf e e' (c.symm z))⁻¹ •
        QuotientLineConnection.realDifferential
          (QuotientLineConnection.imageFrameCoefficient f hf e e') (c.symm z)).comp
        ((mfderiv (realModel d) (realModel d) c.symm z).comp
          (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap) +
      (QuotientLineConnection.coordinateForm D e' c' (F z)).comp (fderiv ℝ F z) := by
  have hpoint := pullback_coordinate_form_pointwise P Dp D f hf e e' c z hpull
  simpa only [ContinuousLinearMap.add_comp, htransport] using hpoint


end HolomorphicAnosov.ConnectionCalculus

