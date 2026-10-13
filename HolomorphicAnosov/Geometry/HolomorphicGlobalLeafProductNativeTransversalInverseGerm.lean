import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransversalDerivativeBijective

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- The inverse-function theorem supplies an actual intrinsic stable transversal germ, with its inverse identity on a neighborhood in the original transverse coordinate space.    The domain membership is retained, not inferred from H. -/
theorem native_transversal_inverse_germ {d p q : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (Fs : RegularHolomorphicFoliation.{u, v} d p q M)
    (Fu : RegularHolomorphicFoliation.{u, w} d q p M)
    (htransverse : ∀ y : M, IsCompl (Fs.tangent y) (Fu.tangent y))
    (x : M) (i : Fu.boxIndex) (z : Fs.Leaf x)
    (hz : z.val ∈ (Fu.box i).source) :
    ∃ ψ : ComplexModel p → Fs.Leaf x,
      ContMDiffAt (complexModel p) (complexModel p) ∞ ψ ((Fu.box i) z.val).2 ∧
      ψ ((Fu.box i) z.val).2 = z ∧
      ∀ᶠ b in 𝓝 (((Fu.box i) z.val).2),
        (ψ b).val ∈ (Fu.box i).source ∧ ((Fu.box i) (ψ b).val).2 = b := by
  let Q : Fs.Leaf x → ComplexModel p := fun y ↦ ((Fu.box i) y.val).2
  let χ := extChartAt (complexModel p) z
  let a := χ z
  let f : ComplexModel p → ComplexModel p := Q ∘ χ.symm
  have hχ : ContMDiffAt (complexModel p) (complexModel p) ∞ χ.symm a := by
    have hh := contMDiffWithinAt_extChartAt_symm_range_self (I := complexModel p)
      (n := ∞) z
    simpa only [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] using hh
  have hχz : χ.symm a = z := (extChartAt (complexModel p) z).left_inv
    (mem_extChartAt_source z)
  have hQa : ContMDiffAt (complexModel p) (complexModel p) ∞ Q (χ.symm a) := by
    rw [hχz]
    have hbox := (Fu.box_holomorphic i).contMDiffAt
      ((Fu.box i).open_source.mem_nhds hz)
    exact contMDiffAt_snd.comp z
      (hbox.comp z (Fs.inclusion_holomorphic (Quotient.mk Fs.partition x) z))
  have hf : ContDiffAt ℂ ∞ f a := (hQa.comp a hχ).contDiffAt
  have hχder : mfderiv (complexModel p) (complexModel p) χ.symm a =
      ContinuousLinearMap.id ℂ (ComplexModel p) := by
    have hh := mfderivWithin_range_extChartAt_symm (I := complexModel p) (x := z)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hh
    change mfderiv (complexModel p) (complexModel p) χ.symm a =
      ContinuousLinearMap.id ℂ (ComplexModel p) at hh
    exact hh
  have hfder : fderiv ℂ f a = mfderiv (complexModel p) (complexModel p) Q z := by
    rw [← mfderiv_eq_fderiv]
    change mfderiv (complexModel p) (complexModel p) (Q ∘ χ.symm) a = _
    rw [mfderiv_comp a (hQa.mdifferentiableAt (by simp))
      (hχ.mdifferentiableAt (by simp)), hχder]
    ext v
    change (mfderiv (complexModel p) (complexModel p) Q (χ.symm a)) v =
      (mfderiv (complexModel p) (complexModel p) Q z) v
    rw [hχz]
  have hbij : Function.Bijective (fderiv ℂ f a) := by
    rw [hfder]
    exact native_transversal_derivative_bijective Fs Fu htransverse x i z hz
  let e : ComplexModel p ≃L[ℂ] ComplexModel p :=
    (LinearEquiv.ofBijective (fderiv ℂ f a).toLinearMap hbij).toContinuousLinearEquiv
  have he : (e : ComplexModel p →L[ℂ] ComplexModel p) = fderiv ℂ f a := by
    ext y
    rfl
  have hf' : HasFDerivAt f (e : ComplexModel p →L[ℂ] ComplexModel p) a := by
    rw [he]
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  let g := hf.localInverse hf' (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hfa : f a = Q z := by simp only [f, Function.comp_apply, hχz]
  have hg : ContDiffAt ℂ ∞ g (Q z) := hfa ▸ hf.to_localInverse hf' (by simp)
  have hga : g (Q z) = a := hfa ▸ hf.localInverse_apply_image hf' (by simp)
  refine ⟨χ.symm ∘ g, ?_, ?_, ?_⟩
  · exact (hga ▸ hχ).comp (Q z) hg.contMDiffAt
  · change χ.symm (g (Q z)) = z
    rw [hga, hχz]
  · have hmem : ∀ᶠ b in 𝓝 (Q z), (χ.symm (g b)).val ∈ (Fu.box i).source := by
      have hcont := (Fs.inclusion_holomorphic (Quotient.mk Fs.partition x)).continuous
        |>.continuousAt (x := z)
      have hbase : (χ.symm ∘ g) (Q z) = z := by
        change χ.symm (g (Q z)) = z
        rw [hga, hχz]
      have h := (hbase ▸ hcont).comp
        ((hga ▸ hχ).comp (Q z) hg.contMDiffAt).continuousAt
      have hz' : ((fun y : Fs.Leaf x ↦ y.val) ∘ χ.symm ∘ g) (Q z) ∈
          (Fu.box i).source := by
        simpa only [Function.comp_apply, hga, hχz] using hz
      exact h.preimage_mem_nhds ((Fu.box i).open_source.mem_nhds hz')
    have hinv : ∀ᶠ b in 𝓝 (Q z), f (g b) = b := by
      have hh := (hf.hasStrictFDerivAt' hf' (by simp)).eventually_right_inverse
      change ∀ᶠ b in 𝓝 (f a), f (g b) = b at hh
      rwa [hfa] at hh
    filter_upwards [hmem, hinv] with b hb hbi
    exact ⟨hb, hbi⟩

