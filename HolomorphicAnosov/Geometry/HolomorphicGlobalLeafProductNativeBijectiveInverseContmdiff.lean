import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- Coordinate inverse-function branches of an actual bijective complex smooth map identify with its original set-theoretic inverse.    Both original chart source conditions are retained before using the chart's injectivity. -/
theorem native_bijective_inverse_contMDiff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
    (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K)
    [I.Boundaryless] [J.Boundaryless]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
    (e : M ≃ N) (he : ContMDiff I J ∞ e)
    (hder : ∀ x : M, Function.Bijective (mfderiv I J e x)) :
    ContMDiff J I ∞ e.symm := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  intro y
  let x := e.symm y
  let χ := extChartAt I x
  let η := extChartAt J y
  let a := χ x
  let f : E → F := η ∘ e ∘ χ.symm
  have hχx : χ.symm a = x := (extChartAt I x).left_inv (mem_extChartAt_source x)
  have hex : e x = y := e.apply_symm_apply y
  have hχ : ContMDiffAt 𝓘(ℂ, E) I ∞ χ.symm a := by
    simpa only [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x)
  have hη : ContMDiffAt J 𝓘(ℂ, F) ∞ η (e (χ.symm a)) := by
    rw [hχx, hex]
    exact contMDiffAt_extChartAt
  have hf : ContDiffAt ℂ ∞ f a :=
    (hη.comp a ((he (χ.symm a)).comp a hχ)).contDiffAt
  have hχder : mfderiv 𝓘(ℂ, E) I χ.symm a = ContinuousLinearMap.id ℂ E := by
    have hh := mfderivWithin_range_extChartAt_symm (I := I) (x := x)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hh
    change mfderiv 𝓘(ℂ, E) I χ.symm a = ContinuousLinearMap.id ℂ E at hh
    exact hh
  have hηder : mfderiv J 𝓘(ℂ, F) η (e (χ.symm a)) =
      ContinuousLinearMap.id ℂ F := by
    rw [hχx, hex]
    exact mfderiv_extChartAt_self
  have hfder : fderiv ℂ f a = mfderiv I J e x := by
    rw [← mfderiv_eq_fderiv]
    change mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) (η ∘ (e ∘ χ.symm)) a = _
    rw [mfderiv_comp a (hη.mdifferentiableAt (by simp))
      (((he (χ.symm a)).comp a hχ).mdifferentiableAt (by simp)),
      mfderiv_comp a ((he (χ.symm a)).mdifferentiableAt (by simp))
        (hχ.mdifferentiableAt (by simp))]
    simp only [Function.comp_apply] at hηder ⊢
    rw [hχder, hηder]
    ext v
    change (mfderiv I J e (χ.symm a)) v =
      (mfderiv I J e x) v
    rw [hχx]
  have hbij : Function.Bijective (fderiv ℂ f a) := hfder ▸ hder x
  let L : E ≃L[ℂ] F :=
    (LinearEquiv.ofBijective (fderiv ℂ f a).toLinearMap hbij).toContinuousLinearEquiv
  have hL : (L : E →L[ℂ] F) = fderiv ℂ f a := by ext v; rfl
  have hf' : HasFDerivAt f (L : E →L[ℂ] F) a := by
    rw [hL]
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  let g := hf.localInverse hf' (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hfa : f a = η y := by simp only [f, Function.comp_apply, hχx, hex]
  have hg : ContDiffAt ℂ ∞ g (η y) := hfa ▸ hf.to_localInverse hf' (by simp)
  have hga : g (η y) = a := hfa ▸ hf.localInverse_apply_image hf' (by simp)
  let Φ : N → M := χ.symm ∘ g ∘ η
  have hΦy : Φ y = x := by
    change χ.symm (g (η y)) = x
    rw [hga, hχx]
  have hΦ : ContMDiffAt J I ∞ Φ y :=
    ((hga ▸ hχ).comp (η y) hg.contMDiffAt).comp y contMDiffAt_extChartAt
  have hηcont : ContinuousAt η y :=
    (contMDiffAt_extChartAt (I := J) (n := ∞)).continuousAt
  have hright : ∀ᶠ b in 𝓝 (η y), f (g b) = b := by
    have hh := (hf.hasStrictFDerivAt' hf' (by simp)).eventually_right_inverse
    change ∀ᶠ b in 𝓝 (f a), f (g b) = b at hh
    rwa [hfa] at hh
  have hpre : ∀ᶠ z in 𝓝 y, f (g (η z)) = η z := hηcont.eventually hright
  have heΦ : ContinuousAt (e ∘ Φ) y :=
    ((hΦy ▸ he x).comp y hΦ).continuousAt
  have hmem : ∀ᶠ z in 𝓝 y, e (Φ z) ∈ η.source := by
    apply heΦ.preimage_mem_nhds
    exact (isOpen_extChartAt_source y).mem_nhds
      (by simpa only [Function.comp_apply, hΦy, hex] using mem_extChartAt_source y)
  have heq : e.symm =ᶠ[𝓝 y] Φ := by
    filter_upwards [hpre, hmem, extChartAt_source_mem_nhds (I := J) y] with z hz hmemz hzs
    have hz' : η (e (Φ z)) = η z := hz
    have hh : e (Φ z) = z := η.injOn hmemz hzs hz'
    exact ((e.symm_apply_apply (Φ z)).symm.trans (congrArg e.symm hh)).symm
  exact hΦ.congr_of_eventuallyEq heq

