import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Uniform smallness near a compact zero section

Source: Lee, *Introduction to Smooth Manifolds* (2003), proof of Theorem 17.19,
pp. 457–458, equations (17.23)–(17.24). This isolates the compact uniformity
step for a continuous matrix field vanishing on a compact zero section.
The value space can be any seminormed additive group.
-/

namespace HolomorphicAnosov.ExponentialCutoff

open Set Filter Metric
open scoped Topology _root_.Topology

/-- A continuous field vanishing along a compact zero section is uniformly small
on a single closed ball in the vector variable, inside its original open domain.

Source: Lee (2003), pp. 457–458, equations (17.23)–(17.24).
Proof: continuity at each `(p,0)` gives an open neighborhood where the norm is
less than `ε` and the point remains in `U`. Compactness makes this neighborhood
uniform in `p ∈ K`. Choose a positive closed-ball radius inside that neighborhood
and smaller than the prescribed `R`. Empty `K` and zero-dimensional fibres are
covered by the same neighborhood-filter argument. -/
theorem compact_zero_section_smallness
    {P V W : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [SeminormedAddCommGroup W]
    (K : Set P) (hK : IsCompact K) (U : Set (P × V)) (hU : IsOpen U)
    (F : P × V → W) (hF : ContinuousOn F U)
    (hzeroU : ∀ p ∈ K, (p, (0 : V)) ∈ U)
    (hzero : ∀ p ∈ K, F (p, 0) = 0)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
      ∀ p ∈ K, ∀ v : V, ‖v‖ ≤ δ → (p, v) ∈ U ∧ ‖F (p, v)‖ < ε := by
  have hlocal (p : P) (hp : p ∈ K) :
      ∀ᶠ z : V × P in 𝓝 (0, p), (z.2, z.1) ∈ U ∧ ‖F (z.2, z.1)‖ < ε := by
    have hswap : ContinuousAt (Prod.swap : V × P → P × V) (0, p) :=
      continuous_swap.continuousAt
    have hcont : ContinuousAt (fun z : V × P ↦ F (z.2, z.1)) (0, p) :=
      (hF.continuousAt (hU.mem_nhds (hzeroU p hp))).comp (f := Prod.swap) hswap
    have hn : ‖F (p, 0)‖ < ε := by simpa [hzero p hp] using hε
    exact (hswap.eventually (hU.mem_nhds (hzeroU p hp))).and
      (hcont.norm.eventually (gt_mem_nhds hn))
  have huniform : ∀ᶠ v : V in 𝓝 0, ∀ p ∈ K, (p, v) ∈ U ∧ ‖F (p, v)‖ < ε :=
    hK.eventually_forall_of_forall_eventually hlocal
  obtain ⟨d, hd, hdball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp huniform
  refine ⟨min d (R / 2), lt_min hd (by positivity),
    lt_of_le_of_lt (min_le_right _ _) (by linarith), ?_⟩
  intro p hp v hv
  exact hdball (by simpa using hv.trans (min_le_left d (R / 2))) p hp


end HolomorphicAnosov.ExponentialCutoff
