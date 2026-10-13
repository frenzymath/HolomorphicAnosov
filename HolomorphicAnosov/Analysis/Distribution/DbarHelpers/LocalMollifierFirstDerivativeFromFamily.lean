import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.FixedSupportFirstDerivativeSections
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ScaledKernelDerivativeSectionPairing
import Mathlib.Analysis.Distribution.TestFunction

/-!
# local_mollifier_first_derivative_from_family

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, Theorem6.4, p.69,
derivative sign for a translated convolution kernel; Proposition6.3, pp.68–69, differentiation of
a fixed-support family.
DAG node: `analysis.dbar_helper_local_mollifier_first_derivative_from_family_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
For a local fixed-compact-support family of scaled mollifier tests, the derivative of the paired
scalar function in a coordinate direction is the negative pairing with the corresponding spatial
test derivative.

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, Theorem6.4, p.69,
derivative sign for a translated convolution kernel; Proposition6.3, pp.68–69, differentiation of
a fixed-support family.

Proof/construction: The explicit two-variable scaled kernel is jointly smooth. Apply the
fixed-support first-derivative family provider. The given paired function agrees locally with the
provider function, since their test sections agree pointwise on the open parameter domain.
Derivatives of locally equal functions agree. Identify the derivative section pairing by the
translated-kernel sign theorem.
-/
theorem local_mollifier_first_derivative_from_family {m : ℕ} (hm : 0 < m)
    (U P : Opens (EuclideanSpace ℝ (Fin m)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (ε : ℝ) (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U)
    (hSupport : ∀ p ∈ P, tsupport (fun y ↦ (((ε⁻¹)^m : ℝ) : ℂ) *
      ((ρ (ε⁻¹ • (p-y)) : ℝ) : ℂ)) ⊆ K)
    (κ : ∀ p, p ∈ P → TestFunction U ℂ ⊤)
    (hκ : ∀ p hp y, κ p hp y = (((ε⁻¹)^m : ℝ) : ℂ) *
      ((ρ (ε⁻¹ • (p-y)) : ℝ) : ℂ))
    (F : EuclideanSpace ℝ (Fin m) → ℂ) (hF : ∀ p hp, F p = T (κ p hp))
    (j : Fin m) (x : EuclideanSpace ℝ (Fin m)) (hx : x ∈ P) :
    (fderiv ℝ F x) (EuclideanSpace.single j 1) =
      -T (TestFunction.lineDerivCLM ℂ (EuclideanSpace.single j 1) (κ x hx)) := by
  let H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℂ :=
    fun p y ↦ (((ε⁻¹)^m : ℝ) : ℂ) * ((ρ (ε⁻¹ • (p-y)) : ℝ) : ℂ)
  have hH : ContDiff ℝ ∞ (Function.uncurry H) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (ρ.contDiff.comp ((contDiff_fst.sub contDiff_snd).const_smul ε⁻¹)))
  obtain ⟨s, hs, _, hd⟩ := fixed_support_first_derivative_sections
    hm hm U P T K hK hKU H hH.contDiffOn hSupport
  obtain ⟨θ, hθ, hpair⟩ := hd j x hx
  have heq : F =ᶠ[nhds x] (fun p ↦ T (s p)) := by
    filter_upwards [P.isOpen.mem_nhds hx] with p hp
    rw [hF p hp]
    congr 1
    ext y
    exact (hκ p hp y).trans (hs p hp y).symm
  rw [heq.fderiv_eq, hpair]
  exact (scaled_kernel_derivative_section_pairing U T ρ ε x
    (EuclideanSpace.single j 1) (κ x hx) θ (hκ x hx) hθ).2


end HolomorphicAnosov.Analysis.Distribution
