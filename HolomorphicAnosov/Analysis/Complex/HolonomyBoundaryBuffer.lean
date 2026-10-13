import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Compact boundary separation for Ghys Proposition 2.2

This is the explicit compact boundary-buffer argument used in the omitted
orientation step of Ghys, *Holomorphic Anosov systems* (1995), Proposition 2.2,
pp. 589–590. The source uses compact holonomy neighborhoods and uniform
approximation; this auxiliary statement spells out the separation estimate.
DAG node: `analysis.holonomy_boundary_buffer_g3`.
-/

namespace HolomorphicAnosov.Ghys

open Set Filter

/-- On a compact boundary disjoint from a marked point, injectivity and continuity
provide a positive image-distance buffer. Local uniform convergence on the ambient
open set is uniform on the compact set, so sufficiently late approximants preserve
more than half this buffer uniformly on the boundary.

Source: Ghys, *Holomorphic Anosov systems* (1995), Proposition 2.2,
pp. 589–590. The explicit compact-minimum and triangle-inequality argument is
agent-written to expand the omitted orientation step.
-/
theorem holonomy_boundary_buffer
    {U C B : Set ℂ} {g : ℂ → ℂ} {F : ℕ → ℂ → ℂ} {a : ℂ}
    (hC : IsCompact C) (hCU : C ⊆ U) (ha : a ∈ C)
    (hB : IsCompact B) (hBC : B ⊆ C) (haB : a ∉ B)
    (hg : ContinuousOn g C) (hi : InjOn g C)
    (hF : TendstoLocallyUniformlyOn F g Filter.atTop U) :
    ∃ m > 0, (∀ z ∈ B, m ≤ ‖g z - g a‖) ∧
      ∀ᶠ n in Filter.atTop, ∀ z ∈ B,
        ‖F n z - g z‖ < m / 4 ∧ ‖F n a - g a‖ < m / 4 ∧
        m / 2 < ‖F n z - F n a‖ := by
  have hm : ∃ m > 0, ∀ z ∈ B, m ≤ ‖g z - g a‖ := by
    by_cases hne : B.Nonempty
    · obtain ⟨z, hz, hmin⟩ := hB.exists_isMinOn hne
        (((hg.mono hBC).sub continuousOn_const).norm)
      refine ⟨‖g z - g a‖, norm_pos_iff.mpr (sub_ne_zero.mpr ?_), hmin⟩
      intro he
      exact haB ((hi (hBC hz) ha he) ▸ hz)
    · exact ⟨1, zero_lt_one, fun z hz ↦ False.elim (hne ⟨z, hz⟩)⟩
  obtain ⟨m, hm, hmin⟩ := hm
  refine ⟨m, hm, hmin, ?_⟩
  have hu : TendstoUniformlyOn F g Filter.atTop C :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hC).mp (hF.mono hCU)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) (m / 4) (by positivity)] with n hn
  intro z hz
  have hzerr : ‖F n z - g z‖ < m / 4 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hn z (hBC hz)
  have haerr : ‖F n a - g a‖ < m / 4 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hn a ha
  refine ⟨hzerr, haerr, ?_⟩
  have htri : ‖g z - g a‖ ≤ ‖F n z - g z‖ + ‖F n z - F n a‖ + ‖F n a - g a‖ := by
    calc
      ‖g z - g a‖ = ‖(g z - F n z) + (F n z - F n a) + (F n a - g a)‖ := by
        congr 1
        abel
      _ ≤ ‖g z - F n z‖ + ‖F n z - F n a‖ + ‖F n a - g a‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by rw [norm_sub_rev (g z) (F n z)]
  have := hmin z hz
  linarith

end HolomorphicAnosov.Ghys
