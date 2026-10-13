import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_image_coefficient_locally_holomorphic
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (U : (x : M) → Submodule ℂ (TangentSpace (complexModel d) x))
    (f : Biholomorph d d M M) (hU : ∀ x (v : TangentSpace (complexModel d) x),
      v ∈ U x → mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    {V W : TopologicalSpace.Opens M} (e : QuotientLineConnection.HolomorphicFrame U V)
    (e' : QuotientLineConnection.HolomorphicFrame U W) (t' : M → ℂ)
    (ht' : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t' W)
    (hformula : ∀ y ∈ W, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v =
        transverseScalarDifferential t' y v • e'.sectionValue y)
    (x : M) (hx : x ∈ V) (hfx : f x ∈ W) :
    ∃ N : Set M, IsOpen N ∧ x ∈ N ∧ N ⊆ (V : Set M) ∩ f ⁻¹' (W : Set M) ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞
        (QuotientLineConnection.imageFrameCoefficient f hU e e') N := by
  obtain ⟨A, v, hA, hxA, hAV, hv, hvs⟩ := e.holomorphic x hx
  let N : TopologicalSpace.Opens M := ⟨A ∩ f ⁻¹' (W : Set M),
    hA.inter (W.isOpen.preimage f.continuous)⟩
  have hNV : (N : Set M) ⊆ V := fun y hy ↦ hAV hy.1
  have hNW : MapsTo f N W := fun y hy ↦ hy.2
  have htf : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ (t' ∘ f) N :=
    ht'.comp f.contMDiff.contMDiffOn hNW
  have htm := htf.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    N.isOpen.uniqueMDiffOn
  have hcomp := htm.comp (hv.mono inter_subset_left) (fun y hy ↦ hy)
  have hscalar := (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℂ, ℂ)
    (n := ∞)).comp_contMDiffOn hcomp
  refine ⟨N, N.isOpen, ⟨hxA, hfx⟩, (fun y hy ↦ ⟨hNV hy, hy.2⟩), ?_⟩
  apply hscalar.congr
  intro y hy
  have hyW : f y ∈ W := hy.2
  have hcoef := congrArg (e'.coordinate (f y) hyW)
    (hformula (f y) hyW (mfderiv (complexModel d) (complexModel d) f y (v y)))
  have hproj : QuotientLineConnection.projection U (f y)
      (mfderiv (complexModel d) (complexModel d) f y (v y)) =
      QuotientLineConnection.quotientDerivative f hU y (e.sectionValue y) := by
    rw [← hvs y hy.1]
    rfl
  rw [hproj] at hcoef
  simp only [map_smul, e'.normalized (f y) hyW, smul_eq_mul, mul_one] at hcoef
  change QuotientLineConnection.imageFrameCoefficient f hU e e' y =
    mfderivWithin (complexModel d) 𝓘(ℂ, ℂ) (t' ∘ f) (N : Set M) y (v y)
  rw [mfderivWithin_of_isOpen N.isOpen hy,
    mfderiv_comp y (((ht' (f y) hyW).contMDiffAt
      (W.isOpen.mem_nhds hyW)).mdifferentiableAt (by simp))
      (f.contMDiff.mdifferentiable (by simp) y)]
  change (e'.coordinate (f y) hyW)
      (QuotientLineConnection.quotientDerivative f hU y (e.sectionValue y)) =
    mfderiv (complexModel d) 𝓘(ℂ, ℂ) t' (f y)
      (mfderiv (complexModel d) (complexModel d) f y (v y)) at hcoef
  simpa [QuotientLineConnection.imageFrameCoefficient, hyW] using hcoef


end
end HolomorphicAnosov.Paper.Zhang
