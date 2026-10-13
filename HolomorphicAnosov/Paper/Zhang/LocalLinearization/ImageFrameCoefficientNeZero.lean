import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.QuotientDerivativeSurjective

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_imageFrameCoefficient_ne_zero
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (U : (x : M) → Submodule ℂ (TangentSpace (complexModel d) x))
    (f : Biholomorph d d M M) (hU : ∀ x (v : TangentSpace (complexModel d) x),
      v ∈ U x → mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    {V W : TopologicalSpace.Opens M} (e : QuotientLineConnection.HolomorphicFrame U V)
    (e' : QuotientLineConnection.HolomorphicFrame U W) (x : M)
    (hx : x ∈ V) (hfx : f x ∈ W) :
    QuotientLineConnection.imageFrameCoefficient (d := d) f hU e e' x ≠ 0 := by
  intro hc
  have hz : QuotientLineConnection.quotientDerivative f hU x (e.sectionValue x) = 0 := by
    apply (e'.coordinate (f x) hfx).injective
    simpa [QuotientLineConnection.imageFrameCoefficient, hfx] using hc
  obtain ⟨q, hq⟩ := localLinearization_quotientDerivative_surjective U f hU x
    ((e'.coordinate (f x) hfx).symm 1)
  have hspan : q = (e.coordinate x hx q) • e.sectionValue x := by
    apply (e.coordinate x hx).injective
    simp [e.normalized x hx]
  have hone : (e'.coordinate (f x) hfx).symm 1 = 0 := by
    rw [← hq, hspan, map_smul, hz, smul_zero]
  exact (one_ne_zero : (1 : ℂ) ≠ 0)
    (by simpa using congrArg (e'.coordinate (f x) hfx) hone)


end
end HolomorphicAnosov.Paper.Zhang
