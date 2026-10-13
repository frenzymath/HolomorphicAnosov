import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.BiholomorphToReal

open Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff Classical
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- On a source and target frame overlap, the coordinate form of a pullback connection is obtained
from the frame pullback law by composition with the inverse-chart differential. -/
theorem pullback_coordinate_form_pointwise
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (Dp D : QuotientLineConnection.Connection P)
    (f : Biholomorph d d X X)
    (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x))
    {V W : Opens X} (e : QuotientLineConnection.HolomorphicFrame P V)
    (e' : QuotientLineConnection.HolomorphicFrame P W)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (z : ComplexModel d)
    (hpull : Dp.form V e (c.symm z) =
      (QuotientLineConnection.imageFrameCoefficient f hf e e' (c.symm z))⁻¹ •
        QuotientLineConnection.realDifferential
          (QuotientLineConnection.imageFrameCoefficient f hf e e') (c.symm z) +
      (D.form W e' (f (c.symm z))).comp
        (mfderiv (realModel d) (realModel d) f (c.symm z))) :
    QuotientLineConnection.coordinateForm Dp e c z =
      ((QuotientLineConnection.imageFrameCoefficient f hf e e' (c.symm z))⁻¹ •
        QuotientLineConnection.realDifferential
          (QuotientLineConnection.imageFrameCoefficient f hf e e') (c.symm z) +
        (D.form W e' (f (c.symm z))).comp
          (mfderiv (realModel d) (realModel d) f (c.symm z))).comp
        ((mfderiv (realModel d) (realModel d) c.symm z).comp
          (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap) := by
  rw [QuotientLineConnection.coordinateForm, hpull]

end HolomorphicAnosov.ConnectionCalculus

