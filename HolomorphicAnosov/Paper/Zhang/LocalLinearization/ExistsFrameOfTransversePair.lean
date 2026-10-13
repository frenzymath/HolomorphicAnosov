import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_exists_frame_of_transverse_pair
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (V : TopologicalSpace.Opens M)
    (σ : ∀ x : M, QuotientLineConnection.Fibre U x) (t : M → ℂ)
    (hσ : QuotientLineConnection.IsHolomorphicSection U V σ)
    (hnσ : ∀ x ∈ V, σ x ≠ 0)
    (hformula : ∀ x ∈ V, ∀ v : TangentSpace (complexModel d) x,
      QuotientLineConnection.projection U x v = transverseScalarDifferential t x v • σ x) :
    ∃ e : QuotientLineConnection.HolomorphicFrame U V, e.sectionValue = σ := by
  classical
  have hbij : ∀ x, x ∈ V → Function.Bijective
      (LinearMap.toSpanSingleton ℂ (QuotientLineConnection.Fibre U x) (σ x)) := by
    intro x hx
    refine ⟨smul_left_injective ℂ (hnσ x hx), ?_⟩
    intro w
    obtain ⟨v, hv⟩ := (U x).mkQ_surjective w
    exact ⟨transverseScalarDifferential t x v, (hformula x hx v).symm.trans hv⟩
  let e : ∀ x, x ∈ V → QuotientLineConnection.Fibre U x ≃ₗ[ℂ] ℂ :=
    fun x hx ↦ (LinearEquiv.ofBijective
      (LinearMap.toSpanSingleton ℂ (QuotientLineConnection.Fibre U x) (σ x))
      (hbij x hx)).symm
  refine ⟨⟨σ, hσ, e, ?_⟩, rfl⟩
  intro x hx
  have hnormal := (LinearEquiv.ofBijective
      (LinearMap.toSpanSingleton ℂ (QuotientLineConnection.Fibre U x) (σ x))
      (hbij x hx)).symm_apply_apply (1 : ℂ)
  simpa only [LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply,
    one_smul] using hnormal


end
end HolomorphicAnosov.Paper.Zhang
