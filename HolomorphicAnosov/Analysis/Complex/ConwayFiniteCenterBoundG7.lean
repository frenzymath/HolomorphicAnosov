import HolomorphicAnosov.Analysis.Complex.ConwayCoverLiftG7
import HolomorphicAnosov.Analysis.Complex.ConwayBoundedHolomorphicSequenceNormality
import Mathlib.Analysis.Complex.AbsMax

open Set Filter
open scoped Topology
namespace HolomorphicAnosov

/-- Conway II XVI Theorem 4.2, the claim on p.124: center values converging to
an unomitted value yield a subsequence eventually bounded on each compact set.
Choose an inverse covering sheet at the limiting center value and lift each
map with initial value in this sheet. Bounded holomorphic normality extracts a
limit of the disk-valued lifts. Its center remains in the open disk, so the
maximum modulus principle keeps its whole image there. On each compact set,
the lifts eventually lie in a fixed smaller closed disk. The covering map is
bounded on that closed disk, hence so are the projected functions. -/
theorem conway_finite_center_compact_bound_g7
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
    {a b : ℂ} (ha : a ∈ G) (hb : b ≠ 0 ∧ b ≠ 1)
    (hcenter : Tendsto (fun n ↦ f n a) atTop (𝓝 b)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ K : Set ℂ, IsCompact K → K ⊆ G →
      ∃ M : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K, ‖f (φ n) z‖ ≤ M := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : {z : ℂ // ‖z‖ < 1}, lam w = b := by
    change b ∈ {w : ℂ | w ≠ 0 ∧ w ≠ 1} at hb
    rw [← hrange] at hb
    exact hb
  obtain ⟨e, hwe, hesub, heq, _, heinv⟩ := hlocal w w.property
  have hbt : b ∈ e.target := by rw [← hw, ← heq hwe]; exact e.map_source hwe
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcenter (e.open_target.mem_nhds hbt))
  have hlifts : ∀ n : ℕ, ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g G ∧ (∀ z ∈ G, ‖g z‖ < 1) ∧
      (∀ z ∈ G, lam (g z) = f (n + N) z) ∧ g a = e.symm (f (n + N) a) := by
    intro n
    have hnt := hN (n + N) (by omega)
    apply conway_holomorphic_disk_cover_lift_g7 hG hc hcover hlocal (hf _) (ho _)
      ha (hesub (e.map_target hnt))
    rw [← heq (e.map_target hnt), e.right_inv hnt]
  choose g hg hgb hgproj hga using hlifts
  obtain ⟨ψ, hψ, v, hv, hconv⟩ := conway_bounded_holomorphic_sequence_normality_g2
    hG g hg (fun K hK hKG ↦ ⟨1, by norm_num, fun n z hz ↦ (hgb n z (hKG hz)).le⟩)
  have hloc := (tendstoLocallyUniformlyOn_iff_forall_isCompact hG).mpr
    (fun K hKG hK ↦ hconv K hK hKG)
  have hlimcenter : v a = e.symm b := by
    apply tendsto_nhds_unique (hloc.tendsto_at ha)
    have hindices : Tendsto (fun n ↦ ψ n + N) atTop atTop :=
      tendsto_atTop_mono (fun n ↦ Nat.le_add_right (ψ n) N) hψ.tendsto_atTop
    simpa only [hga, Function.comp_apply] using! (e.continuousAt_symm hbt).tendsto.comp (hcenter.comp hindices)
  have hvle : ∀ z ∈ G, ‖v z‖ ≤ 1 := by
    intro z hz
    exact le_of_tendsto (hloc.tendsto_at hz).norm (.of_forall fun n ↦ (hgb _ z hz).le)
  have hvlt : ∀ z ∈ G, ‖v z‖ < 1 := by
    intro z hz
    by_contra h
    have he : ‖v z‖ = 1 := le_antisymm (hvle z hz) (le_of_not_gt h)
    have hm : IsMaxOn (norm ∘ v) G z := by
      intro t ht
      change ‖v t‖ ≤ ‖v z‖
      rw [he]
      exact hvle t ht
    have heqnorm := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
      hc.isPathConnected.isConnected.isPreconnected hG hv hz hm ha
    have hva : ‖v a‖ < 1 := by rw [hlimcenter]; exact hesub (e.map_target hbt)
    dsimp only [Function.comp_apply, Function.const_apply] at heqnorm
    rw [he] at heqnorm
    linarith
  refine ⟨fun n ↦ ψ n + N, fun m n hmn ↦ Nat.add_lt_add_right (hψ hmn) N, ?_⟩
  intro K hK hKG
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne (hv.continuousOn.mono hKG).norm
    let r : ℝ := (‖v z‖ + 1) / 2
    have hvr : ‖v z‖ < r := by dsimp [r]; linarith [hvlt z (hKG hz)]
    have hr : r < 1 := by dsimp [r]; linarith [hvlt z (hKG hz)]
    have hsub : Metric.closedBall (0 : ℂ) r ⊆ {w : ℂ | ‖w‖ < 1} := by
      intro w hw
      exact lt_of_le_of_lt (by simpa using hw) hr
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
      (hlam.continuousOn.mono hsub)
    refine ⟨M, ?_⟩
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv K hK hKG)
      (r - ‖v z‖) (sub_pos.mpr hvr)] with n hn
    intro t ht
    rw [← hgproj (ψ n) t (hKG ht)]
    apply hM
    rw [Metric.mem_closedBall, dist_zero_right]
    have hd := hn t ht
    have hm := hmax ht
    change ‖v t‖ ≤ ‖v z‖ at hm
    have htri : ‖g (ψ n) t‖ ≤ dist (v t) (g (ψ n) t) + ‖v t‖ := by
      simpa [dist_comm, dist_zero_right] using dist_triangle (g (ψ n) t) (v t) 0
    linarith
  · exact ⟨0, .of_forall fun _ z hz ↦ (hne ⟨z, hz⟩).elim⟩

end HolomorphicAnosov
