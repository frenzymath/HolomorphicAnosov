import HolomorphicAnosov.Analysis.SchwarzRealBoundaryExtension
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Metric Complex
open scoped Topology _root_.Topology ComplexConjugate

namespace HolomorphicAnosov

/-- A holomorphic function on an upper half-disk, continuous on its real diameter
and zero there, vanishes on the entire closed upper half-disk.

Source: Tao, 246C Notes 2, Theorem 20, final injectivity paragraph,
`literature/Tao-246C-Notes2-2018.txt:269`: Schwarz reflection across a flattened
constant boundary arc followed by analytic continuation. Reflection itself is
Bullett, MTH6111 Section V, Proposition 23.1, implemented in the imported public
provider. This theorem supplies only the flat-boundary analytic part; it does not
assume or prove the circle-flattening construction.

Proof: Reflect the function across its real diameter by the public Schwarz
reflection theorem. Its ambient extension is analytic throughout the open disk.
The distinct real points a+1/(n+1) eventually lie in that disk, converge to its
center, and are zeros. The analytic identity theorem on the connected disk
therefore makes the reflected function zero everywhere. Its literal agreement
with the original function gives the conclusion, including diameter points. -/
theorem eq_zero_of_schwarz_real_zero_boundary
    (a r : ℝ) (hr : 0 < r)
    (f : {z : ℂ // z ∈ ball (a : ℂ) r ∧ 0 ≤ z.im} → ℂ)
    (hf_cont : Continuous f)
    (hf_holo : DifferentiableOn ℂ (Function.extend Subtype.val f (fun _ ↦ 0))
      {z : ℂ | z ∈ ball (a : ℂ) r ∧ 0 < z.im})
    (hf_zero : ∀ z : {z : ℂ // z ∈ ball (a : ℂ) r ∧ 0 ≤ z.im},
      (z : ℂ).im = 0 → f z = 0) :
    ∀ z, f z = 0 := by
  have hconj : ∀ z ∈ ball (a : ℂ) r, conj z ∈ ball (a : ℂ) r := by
    intro z hz
    simpa only [mem_ball, dist_conj_comm, conj_ofReal] using hz
  obtain ⟨hGhol, hGcont, hGagree, hGconj⟩ :=
    schwarz_real_boundary_extension isOpen_ball hconj f hf_cont hf_holo
      (fun z hz ↦ by rw [hf_zero z hz]; rfl)
  let G := schwarzRealBoundaryExtension hconj f
  let g : ℂ → ℂ := Function.extend Subtype.val G (fun _ ↦ 0)
  have hgval (z : ball (a : ℂ) r) : g z = G z :=
    Subtype.val_injective.extend_apply _ _ z
  have hghol : AnalyticOnNhd ℂ g (ball (a : ℂ) r) :=
    hGhol.analyticOnNhd isOpen_ball
  let s : ℕ → ℂ := fun n ↦ ((a + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  have hlim : Tendsto s atTop (𝓝 (a : ℂ)) := by
    have hreal : Tendsto (fun n : ℕ ↦ a + 1 / ((n : ℝ) + 1)) atTop (𝓝 a) := by
      simpa using (tendsto_const_nhds (x := a)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact (Complex.continuous_ofReal.tendsto a).comp hreal
  have hcl : (a : ℂ) ∈ closure ({z | g z = 0} \ {(a : ℂ)}) := by
    apply mem_closure_of_tendsto hlim
    filter_upwards [hlim.eventually (ball_mem_nhds (a : ℂ) hr)] with n hn
    refine ⟨?_, ?_⟩
    · change g (s n) = 0
      rw [hgval ⟨s n, hn⟩]
      exact (hGagree ⟨s n, hn, by simp [s]⟩).trans (hf_zero _ (by simp [s]))
    · simp only [mem_singleton_iff]
      intro he
      have hre := congrArg Complex.re he
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      simp only [s, ofReal_re] at hre
      linarith
  have hzero : EqOn g 0 (ball (a : ℂ) r) :=
    hghol.eqOn_zero_of_preconnected_of_mem_closure (convex_ball _ _).isPreconnected
      (mem_ball_self hr) hcl
  intro z
  calc
    f z = G ⟨z, z.property.1⟩ := (hGagree z).symm
    _ = g z := (hgval ⟨z, z.property.1⟩).symm
    _ = 0 := hzero z.property.1

end HolomorphicAnosov
