import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_transverse_differential_transport
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (U : (x : M) → Submodule ℂ (TangentSpace (complexModel d) x))
    (f : Biholomorph d d M M) (hU : ∀ x (v : TangentSpace (complexModel d) x),
      v ∈ U x → mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    {V W : TopologicalSpace.Opens M} (e : QuotientLineConnection.HolomorphicFrame U V)
    (e' : QuotientLineConnection.HolomorphicFrame U W) (t t' : M → ℂ)
    (hformula : ∀ y ∈ V, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v =
        transverseScalarDifferential t y v • e.sectionValue y)
    (hformula' : ∀ y ∈ W, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v =
        transverseScalarDifferential t' y v • e'.sectionValue y)
    (x : M) (hx : x ∈ V) (hfx : f x ∈ W)
    (v : TangentSpace (complexModel d) x) :
    transverseScalarDifferential t' (f x)
      (mfderiv (complexModel d) (complexModel d) f x v) =
      QuotientLineConnection.imageFrameCoefficient f hU e e' x *
        transverseScalarDifferential t x v := by
  have hproj : QuotientLineConnection.projection U (f x)
      (mfderiv (complexModel d) (complexModel d) f x v) =
      QuotientLineConnection.quotientDerivative f hU x
        (QuotientLineConnection.projection U x v) := rfl
  have hh := hformula' (f x) hfx (mfderiv (complexModel d) (complexModel d) f x v)
  rw [hproj, hformula x hx v, map_smul] at hh
  have hcoeff := congrArg (e'.coordinate (f x) hfx) hh
  simp only [map_smul, e'.normalized (f x) hfx, smul_eq_mul, mul_one] at hcoeff
  simpa [QuotientLineConnection.imageFrameCoefficient, hfx, mul_comm] using hcoeff.symm


end
end HolomorphicAnosov.Paper.Zhang
