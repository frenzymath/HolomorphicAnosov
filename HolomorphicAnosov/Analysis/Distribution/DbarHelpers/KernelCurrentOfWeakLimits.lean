import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.Kernel_regularized_pairing

/-!
# KernelCurrentOfWeakLimits

Source: Demailly, Complex Analytic and Differential Geometry (2012), I §3.E (3.29), p.28,
regularize the current and take the weak limit; weak convergence on fixed tests in I §2.D.3
(2.23), p.19.
DAG node: `analysis.dbar_helper_kernel_current_of_weak_limits_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Suppose regularized scalar functions eventually obey an integrable kernel representation and their
pairings against two fixed tests converge to the corresponding current pairings. If one of these
tests is the kernel integral of the other and its current pairing is the integral of that test
against g, then g represents the current on the original test.

Source: Demailly (2012), I §3.E (3.29), p.28, regularize the current and take the weak limit; weak
convergence on fixed tests in I §2.D.3 (2.23), p.19.

Proof: For every sufficiently small regularization parameter, the kernel-pairing identity
identifies the integrals against the two fixed tests. The two scalar functions of the parameter
are therefore eventually equal. Their assumed limits must agree by uniqueness of limits in the
complex plane. Substitute the assumed current pairing of the integrated test and commute the two
scalar factors to obtain the asserted representation.
-/
theorem kernel_current_of_weak_limits {n : ℕ}
    (U P : Opens (Fin n → ℂ)) (_hPU : P ≤ U)
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (H : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (g : (Fin n → ℂ) → ℂ) (φ : TestFunction P ℂ ⊤)
    (η : TestFunction U ℂ ⊤)
    (hη : ∀ y, η y = ∫ p in (P : Set _), φ p * H p y)
    (hpair : T η = ∫ p in (P : Set _), φ p * g p)
    (Q : ℝ → Opens (Fin n → ℂ)) (f : ℝ → (Fin n → ℂ) → ℂ)
    (hweakφ : Tendsto (fun ε ↦ ∫ p in (P : Set _), f ε p * φ p)
      (𝓝[>] (0 : ℝ)) (𝓝 (T (TestFunction.monoCLM ℂ φ))))
    (hweakη : Tendsto (fun ε ↦ ∫ y in (Q ε : Set _), f ε y * η y)
      (𝓝[>] (0 : ℝ)) (𝓝 (T η)))
    (hregular : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ p ∈ P, f ε p = ∫ y in (Q ε : Set _), H p y * f ε y) ∧
      Integrable (fun q : (Fin n → ℂ) × (Fin n → ℂ) ↦
        φ q.1 * H q.1 q.2 * f ε q.2)
        ((volume.restrict (P : Set _)).prod (volume.restrict (Q ε : Set _)))) :
    T (TestFunction.monoCLM ℂ φ) = ∫ p in (P : Set _), g p * φ p := by
  have heq : T (TestFunction.monoCLM ℂ φ) = T η :=
    tendsto_nhds_unique (hweakφ.congr' (by
      filter_upwards [hregular] with ε hε
      exact kernel_regularized_pairing P (Q ε) H φ η (f ε) hη hε.1 hε.2)) hweakη
  rw [heq, hpair]
  congr 1
  funext p
  exact mul_comm _ _


end HolomorphicAnosov.Analysis.Distribution
