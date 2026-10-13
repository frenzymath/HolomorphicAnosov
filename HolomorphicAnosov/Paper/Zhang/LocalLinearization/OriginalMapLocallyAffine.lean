import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.InvariantParallelScaleDerivativeZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.QuotientDerivativeSurjective
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ImageFrameCoefficientNeZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ParallelImageCoefficientDerivativeZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ImageCoefficientLocallyHolomorphic
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.TransverseDifferentialTransport
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ExistsFrameOfTransversePair
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ComplexScalarRealSmooth
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.FrameSelfCoefficientDerivativeZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ScalarLocallyConstantOfRealDifferentialZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ScalarLocallyConstantOfComplexDifferentialZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ParallelFrameFormZero

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_original_map_locally_affine
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (f : Biholomorph d d M M)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (nabla : QuotientLineConnection.Connection U)
    (hinvariant : QuotientLineConnection.IsInvariant nabla f hU)
    (V W : TopologicalSpace.Opens M)
    (σ σ' : ∀ x : M, QuotientLineConnection.Fibre U x) (t t' : M → ℂ)
    (hσ : QuotientLineConnection.IsHolomorphicSection U V σ)
    (hσ' : QuotientLineConnection.IsHolomorphicSection U W σ')
    (hnσ : ∀ x ∈ V, σ x ≠ 0) (hnσ' : ∀ x ∈ W, σ' x ≠ 0)
    (hpσ : QuotientLineConnection.IsParallelOn nabla V σ)
    (hpσ' : QuotientLineConnection.IsParallelOn nabla W σ')
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (ht' : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t' W)
    (hformula : ∀ y ∈ V, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v = transverseScalarDifferential t y v • σ y)
    (hformula' : ∀ y ∈ W, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v = transverseScalarDifferential t' y v • σ' y)
    (x : M) (hx : x ∈ V) (hfx : f x ∈ W) :
    ∃ (c : ℂˣ) (b : ℂ) (N : Set M), IsOpen N ∧ x ∈ N ∧
      N ⊆ (V : Set M) ∩ f ⁻¹' (W : Set M) ∧
      (∀ y ∈ N, t' (f y) = (c : ℂ) * t y + b) ∧
      ∀ v : TangentSpace (complexModel d) x,
        transverseScalarDifferential t' (f x)
          (mfderiv (complexModel d) (complexModel d) f x v) =
            (c : ℂ) * transverseScalarDifferential t x v := by
  obtain ⟨e, he⟩ := localLinearization_exists_frame_of_transverse_pair U V σ t
    hσ hnσ hformula
  obtain ⟨e', he'⟩ := localLinearization_exists_frame_of_transverse_pair U W σ' t'
    hσ' hnσ' hformula'
  have hf1 : ∀ y ∈ V, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v =
        transverseScalarDifferential t y v • e.sectionValue y := by simpa [he] using hformula
  have hf2 : ∀ y ∈ W, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v =
        transverseScalarDifferential t' y v • e'.sectionValue y := by simpa [he'] using hformula'
  have hep : QuotientLineConnection.IsParallelOn nabla V e.sectionValue := by
    simpa [he] using hpσ
  have he'p : QuotientLineConnection.IsParallelOn nabla W e'.sectionValue := by
    simpa [he'] using hpσ'
  let g := QuotientLineConnection.imageFrameCoefficient f hU e e'
  obtain ⟨A, hA, hxA, hAVW, hg⟩ :=
    localLinearization_image_coefficient_locally_holomorphic U f hU e e' t' ht' hf2 x hx hfx
  let A' : TopologicalSpace.Opens M := ⟨A, hA⟩
  have hzero : ∀ y ∈ A', QuotientLineConnection.realDifferential (d := d) g y = 0 := by
    intro y hy
    exact localLinearization_parallel_image_coefficient_derivative_zero U f hU nabla
      hinvariant e e' y (hAVW hy).1 (hAVW hy).2
      (localLinearization_parallel_frame_form_zero U nabla V e hep y (hAVW hy).1)
      (localLinearization_parallel_frame_form_zero U nabla W e' he'p (f y) (hAVW hy).2)
  obtain ⟨B, hB, hxB, hBA, hconst⟩ :=
    localLinearization_scalar_locally_constant_of_real_differential_zero A' g
      (localLinearization_complex_scalar_real_smooth hg) hzero x hxA
  let c : ℂ := g x
  have hc : c ≠ 0 := localLinearization_imageFrameCoefficient_ne_zero U f hU e e' x hx hfx
  let B' : TopologicalSpace.Opens M := ⟨B, hB⟩
  have hBV : (B' : Set M) ⊆ V := fun y hy ↦ (hAVW (hBA hy)).1
  have hBW : MapsTo f B' W := fun y hy ↦ (hAVW (hBA hy)).2
  have htf : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ (t' ∘ f) B' :=
    ht'.comp f.contMDiff.contMDiffOn hBW
  have hder : ∀ y ∈ B', transverseScalarDifferential (d := d)
      (fun y ↦ t' (f y) - c * t y) y = 0 := by
    intro y hy
    have hyd := localLinearization_transverse_differential_transport U f hU e e' t t'
      hf1 hf2 y (hBV hy) (hBW hy)
    have hcY : g y = c := hconst y hy
    have hdy := ((ht y (hBV hy)).contMDiffAt
      (V.isOpen.mem_nhds (hBV hy))).mdifferentiableAt (by simp)
    have hdf := (htf y hy).contMDiffAt (B'.isOpen.mem_nhds hy)
    change mvfderiv (complexModel d) (fun y ↦ t' (f y) - c * t y) y = 0
    rw [mvfderiv_fun_sub (g := fun y ↦ t' (f y)) (g' := fun y ↦ c * t y)
      (hdf.mdifferentiableAt (by simp)) (mdifferentiableAt_const.mul hdy),
      mvfderiv_fun_mul (f := fun _ : M ↦ c) (g := t) mdifferentiableAt_const hdy]
    ext v
    have hchain := mfderiv_comp y
      (((ht' (f y) (hBW hy)).contMDiffAt
        (W.isOpen.mem_nhds (hBW hy))).mdifferentiableAt (by simp))
      (f.contMDiff.mdifferentiable (by simp) y)
    have hv := hyd v
    change mvfderiv (complexModel d) t' (f y)
      (mfderiv (complexModel d) (complexModel d) f y v) =
        g y * mvfderiv (complexModel d) t y v at hv
    rw [hcY] at hv
    simp only [sub_apply, smul_apply, mvfderiv_const, zero_apply,
      smul_zero, add_zero, smul_eq_mul, sub_eq_zero]
    have hchain' : mfderiv (complexModel d) 𝓘(ℂ, ℂ) (fun y ↦ t' (f y)) y =
        (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t' (f y)).comp
          (mfderiv (complexModel d) (complexModel d) f y) := hchain
    simpa only [mvfderiv, hchain', ContinuousLinearMap.comp_apply] using hv
  have hh : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞
      (fun y ↦ t' (f y) - c * t y) B' :=
    htf.sub (contMDiffOn_const.mul (ht.mono hBV))
  obtain ⟨N, hN, hxN, hNB, hNconst⟩ :=
    localLinearization_scalar_locally_constant_of_complex_differential_zero B'
      (fun y ↦ t' (f y) - c * t y) hh hder x hxB
  refine ⟨Units.mk0 c hc, t' (f x) - c * t x, N, hN, hxN,
    (fun y hy ↦ hAVW (hBA (hNB hy))), ?_, ?_⟩
  · intro y hy
    have hz := hNconst y hy
    change t' (f y) = c * t y + (t' (f x) - c * t x)
    linear_combination hz
  · exact localLinearization_transverse_differential_transport U f hU e e' t t'
      hf1 hf2 x hx hfx


end
end HolomorphicAnosov.Paper.Zhang
