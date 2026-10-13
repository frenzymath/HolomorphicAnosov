import HolomorphicAnosov.Analysis.Complex.ConwayFiniteCenterBoundG7
import HolomorphicAnosov.Analysis.Complex.HolomorphicSquareRootG7

open Set Filter
open scoped Topology
namespace HolomorphicAnosov

/-- Bounded values at one point of a simply connected domain imply uniform
bounds on each compact subset for a sequence omitting zero and one.
Agent-written expansion of Conway II XVI Theorem 4.2 pp.124–125.
We expand its square-root
reduction uniformly: choose g²=f with Re g(a)≤0 and h²=1-g with Re h(a)≤0.
The center values of h stay in a compact set separated from zero and one.
A convergent center subsequence therefore falls under the covering-lift claim.
Since f=(1-h²)², a compact bound for h bounds f. If a compact bound for the
original sequence failed, a sequence exceeding n at points of that compact
set would contradict this extracted bound. -/
theorem conway_center_bound_compact_bound_g7
    {G : Set ℂ} (hG : IsOpen G) (hc : IsSimplyConnected G)
    {lam : ℂ → ℂ} (hlam : DifferentiableOn ℂ lam {z : ℂ | ‖z‖ < 1})
    (hcover : IsCoveringMapOn (fun z : {z : ℂ // ‖z‖ < 1} ↦ lam z.val)
      {w : ℂ | w ≠ 0 ∧ w ≠ 1})
    (hrange : Set.range (fun z : {z : ℂ // ‖z‖ < 1} ↦ lam z.val) =
      {w : ℂ | w ≠ 0 ∧ w ≠ 1})
    (hlocal : ∀ z : ℂ, ‖z‖ < 1 → ∃ e : OpenPartialHomeomorph ℂ ℂ,
      z ∈ e.source ∧ e.source ⊆ {w : ℂ | ‖w‖ < 1} ∧
      EqOn e lam e.source ∧ DifferentiableOn ℂ e e.source ∧
        DifferentiableOn ℂ e.symm e.target)
    (f : ℕ → ℂ → ℂ) (hf : ∀ n, DifferentiableOn ℂ (f n) G)
    (ho : ∀ n z, z ∈ G → f n z ≠ 0 ∧ f n z ≠ 1)
    {a : ℂ} (ha : a ∈ G) {M : ℝ} (hM : 0 ≤ M)
    (hcenter : ∀ n, ‖f n a‖ ≤ M) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ G →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n z, z ∈ K → ‖f n z‖ ≤ C := by
  classical
  intro K hK hKG
  by_contra hn
  push Not at hn
  have hbad : ∀ k : ℕ, ∃ n : ℕ, ∃ z ∈ K, (k : ℝ) < ‖f n z‖ := by
    intro k
    exact hn k (by positivity)
  choose idx q hq hbad using hbad
  have hgex : ∀ k : ℕ, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g G ∧
      (∀ z ∈ G, g z ^ 2 = f (idx k) z) ∧ (g a).re ≤ 0 := by
    intro k
    exact holomorphic_square_root_nonpos_re_g7 hG hc (hf _) (fun z hz ↦ (ho _ z hz).1) a
  choose g hg hgsq hgre using hgex
  have hgnz (k : ℕ) (z : ℂ) (hz : z ∈ G) : g k z ≠ 0 := by
    intro he
    have h := hgsq k z hz
    simp only [he, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    exact (ho _ z hz).1 h.symm
  have hgne (k : ℕ) (z : ℂ) (hz : z ∈ G) : g k z ≠ 1 := by
    intro he
    have h := hgsq k z hz
    simp only [he, one_pow] at h
    exact (ho _ z hz).2 h.symm
  have hhex : ∀ k : ℕ, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h G ∧
      (∀ z ∈ G, h z ^ 2 = 1 - g k z) ∧ (h a).re ≤ 0 := by
    intro k
    exact holomorphic_square_root_nonpos_re_g7 hG hc
      ((differentiableOn_const (c := (1 : ℂ))).sub (hg k)) (fun z hz ↦ sub_ne_zero.mpr (hgne k z hz).symm) a
  choose h hh hhsq hhre using hhex
  have hho (k : ℕ) (z : ℂ) (hz : z ∈ G) : h k z ≠ 0 ∧ h k z ≠ 1 := by
    constructor
    · intro he
      have heq := hhsq k z hz
      simp only [he, zero_pow (by decide : (2 : ℕ) ≠ 0)] at heq
      exact hgne k z hz (by linear_combination heq)
    · intro he
      have heq := hhsq k z hz
      simp only [he, one_pow] at heq
      exact hgnz k z hz (by linear_combination heq)
  have hnorm (k : ℕ) : ‖h k a‖ ≤ M + 2 := by
    have hg2 : ‖g k a‖ ^ 2 = ‖f (idx k) a‖ := by
      rw [← norm_pow, hgsq k a ha]
    have hh2 : ‖h k a‖ ^ 2 = ‖1 - g k a‖ := by
      rw [← norm_pow, hhsq k a ha]
    have htri : ‖1 - g k a‖ ≤ 1 + ‖g k a‖ := by
      simpa only [norm_one] using norm_sub_le (1 : ℂ) (g k a)
    have hgM : ‖g k a‖ ≤ M + 1 := by nlinarith [hcenter (idx k), norm_nonneg (g k a)]
    nlinarith [norm_nonneg (h k a)]
  have hnormlow (k : ℕ) : 1 ≤ ‖h k a‖ := by
    have hh2 : ‖h k a‖ ^ 2 = ‖1 - g k a‖ := by
      rw [← norm_pow, hhsq k a ha]
    have hr := Complex.re_le_norm (1 - g k a)
    simp only [Complex.sub_re, Complex.one_re] at hr
    nlinarith [hgre k, norm_nonneg (h k a)]
  obtain ⟨b, hbK, ψ, hψ, hb⟩ := (isCompact_closedBall (0 : ℂ) (M + 2)).isSeqCompact
    (fun k ↦ show h k a ∈ Metric.closedBall (0 : ℂ) (M + 2) by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm k)
  have hb0 : b ≠ 0 := by
    have hlow : 1 ≤ ‖b‖ := ge_of_tendsto hb.norm (.of_forall fun k ↦ hnormlow (ψ k))
    intro he
    norm_num [he] at hlow
  have hb1 : b ≠ 1 := by
    have hre : b.re ≤ 0 := le_of_tendsto (Complex.continuous_re.tendsto b |>.comp hb)
      (.of_forall fun k ↦ hhre (ψ k))
    intro he
    norm_num [he] at hre
  obtain ⟨φ, hφ, hbound⟩ := conway_finite_center_compact_bound_g7 hG hc hlam hcover
    hrange hlocal (fun k ↦ h (ψ k)) (fun k ↦ hh (ψ k)) (fun k ↦ hho (ψ k))
    ha ⟨hb0, hb1⟩ hb
  obtain ⟨B, hB⟩ := hbound K hK hKG
  let C : ℝ := (1 + (max B 0) ^ 2) ^ 2
  obtain ⟨N, hN⟩ := eventually_atTop.mp hB
  obtain ⟨j, hj⟩ := exists_nat_gt C
  let k := max N j
  let m := ψ (φ k)
  have hmk : k ≤ m := (hφ.id_le k).trans (hψ.id_le (φ k))
  have hsmall := hN k (le_max_left _ _) (q m) (hq m)
  have hfpoly : f (idx m) (q m) = (1 - h m (q m) ^ 2) ^ 2 := by
    rw [hhsq m (q m) (hKG (hq m))]
    simpa using (hgsq m (q m) (hKG (hq m))).symm
  have hfnorm : ‖f (idx m) (q m)‖ ≤ C := by
    rw [hfpoly, norm_pow]
    have htri : ‖1 - h m (q m) ^ 2‖ ≤ 1 + ‖h m (q m)‖ ^ 2 := by
      rw [← norm_pow]
      simpa only [norm_one] using norm_sub_le (1 : ℂ) (h m (q m) ^ 2)
    have hhB : ‖h m (q m)‖ ≤ max B 0 := hsmall.trans (le_max_left _ _)
    have hhB2 := pow_le_pow_left₀ (norm_nonneg (h m (q m))) hhB 2
    exact pow_le_pow_left₀ (norm_nonneg _) (htri.trans (by linarith)) 2
  have hjm : (j : ℝ) ≤ m := by exact_mod_cast (le_max_right N j).trans hmk
  have hbadm := hbad m
  linarith

end HolomorphicAnosov
