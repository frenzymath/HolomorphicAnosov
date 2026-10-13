import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeSameBoxPartition
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

namespace HolomorphicAnosov

/-- A leaf-constant projection restricting to the identity on a section is holomorphic at a section
point where the section is holomorphic and its transverse coordinate derivative is bijective. (Zhang,
Lemma 4.2, p.14; Nisoli, §1.3, Eqs. (1.9)–(1.11), pp.21–23) -/
theorem foliation_transversal_projection_contMDiffAt
    {d r c : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (F : RegularHolomorphicFoliation d r c M)
    (q : M → ComplexModel c) (τ : ComplexModel c → M)
    (hq : ∀ a b, F.partition a b → q a = q b)
    (hsection : ∀ z, q (τ z) = z)
    (z : ComplexModel c) (i : F.boxIndex) (hz : τ z ∈ (F.box i).source)
    (hτ : ContMDiffAt (complexModel c) (complexModel d) ∞ τ z)
    (hbij : Function.Bijective
      (fderiv ℂ (fun w ↦ ((F.box i) (τ w)).2) z)) :
    ContMDiffAt (complexModel d) (complexModel c) ∞ q (τ z) := by
  classical
  let Q : M → ComplexModel c := fun y ↦ ((F.box i) y).2
  let T : ComplexModel c → ComplexModel c := Q ∘ τ
  have hQ : ContMDiffAt (complexModel d) (complexModel c) ∞ Q (τ z) :=
    contMDiffAt_snd.comp (τ z) ((F.box_holomorphic i).contMDiffAt
      ((F.box i).open_source.mem_nhds hz))
  have hT : ContDiffAt ℂ ∞ T z := (hQ.comp z hτ).contDiffAt
  let e : ComplexModel c ≃L[ℂ] ComplexModel c :=
    (LinearEquiv.ofBijective (fderiv ℂ T z).toLinearMap hbij).toContinuousLinearEquiv
  have he : (e : ComplexModel c →L[ℂ] ComplexModel c) = fderiv ℂ T z := rfl
  have hT' : HasFDerivAt T (e : ComplexModel c →L[ℂ] ComplexModel c) z := by
    rw [he]
    exact (hT.differentiableAt (by simp)).hasFDerivAt
  let g := hT.localInverse hT' (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hg : ContDiffAt ℂ ∞ g (T z) := hT.to_localInverse hT' (by simp)
  have hgz : g (T z) = z := hT.localInverse_apply_image hT' (by simp)
  have hinv : ∀ᶠ b in 𝓝 (T z), T (g b) = b :=
    (hT.hasStrictFDerivAt' hT' (by simp)).eventually_right_inverse
  have hτg : ContMDiffAt (complexModel c) (complexModel d) ∞ (τ ∘ g) (T z) :=
    (hgz ▸ hτ).comp (T z) hg.contMDiffAt
  have hmem : ∀ᶠ b in 𝓝 (T z), τ (g b) ∈ (F.box i).source := by
    apply hτg.continuousAt.preimage_mem_nhds
    simpa only [Function.comp_apply, hgz] using (F.box i).open_source.mem_nhds hz
  have hformula : ∀ᶠ y in 𝓝 (τ z), q y = g (Q y) := by
    have hpre := hQ.continuousAt.eventually (hinv.and hmem)
    filter_upwards [(F.box i).open_source.mem_nhds hz, hpre] with y hy hp
    have hrel : F.partition y (τ (g (Q y))) :=
      native_same_box_partition F i y (τ (g (Q y))) hy hp.2 hp.1.symm
    exact (hq _ _ hrel).trans (hsection _)
  exact (hg.contMDiffAt.comp (τ z) hQ).congr_of_eventuallyEq hformula


end HolomorphicAnosov
