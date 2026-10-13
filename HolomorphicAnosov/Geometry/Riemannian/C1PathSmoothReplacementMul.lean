import HolomorphicAnosov.Geometry.Riemannian.LocalC1PathSmoothReplacement
import HolomorphicAnosov.Geometry.Riemannian.SmoothPathConcatenation

/-! C¹ paths on the unit interval admit smooth replacements with the same endpoints and length at
most `r²` times their length for every `r > 1`. -/

open Set MeasureTheory Bundle Filter Manifold
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology _root_.Topology

namespace HolomorphicAnosov
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- For every `r > 1`, a C¹ path on the unit interval admits a smooth path with the same endpoints
and extended Riemannian length at most `r²` times its length. (Petersen, Cor. 5.3.10, p.150) -/
theorem c1_path_smooth_replacement_mul
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {c : ℝ → M} (hc : ContMDiffOn 𝓘(ℝ) I 1 c (Icc 0 1))
    (r : ℝ≥0) (hr : 1 < r) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∃ σ : ℝ → M, ContMDiffOn 𝓘(ℝ) I ∞ σ (Icc 0 1) ∧
      σ 0 = c 0 ∧ σ 1 = c 1 ∧
      pathELength I σ 0 1 ≤ (r : ℝ≥0∞) * r * pathELength I c 0 1 := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  have hlocal (x : M) := locally_c1_path_smooth_replacement (I := I) x r hr
  choose U hU hreplace using hlocal
  choose V hVU hVo hxV using fun x ↦ mem_nhds_iff.mp (hU x)
  let cover : M → Set unitInterval := fun x ↦ (fun t ↦ c t) ⁻¹' V x
  have hcc : Continuous (fun t : unitInterval ↦ c t) := hc.continuousOn.domRestrict
  have hopen (x : M) : IsOpen (cover x) := (hVo x).preimage hcc
  have hcover : univ ⊆ ⋃ x, cover x := by
    intro t _
    exact mem_iUnion.mpr ⟨c t, hxV (c t)⟩
  obtain ⟨t, ht0, htm, ⟨N, hN⟩, htcover⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hopen hcover
  have hpart (n : ℕ) : ∃ σ : ℝ → M, ContMDiffOn 𝓘(ℝ) I ∞ σ (Icc 0 1) ∧
      σ 0 = c 0 ∧ σ 1 = c (t n) ∧
      pathELength I σ 0 1 ≤ (r : ℝ≥0∞) * r * pathELength I c 0 (t n) := by
    induction n with
    | zero =>
      refine ⟨fun _ ↦ c 0, contMDiffOn_const, rfl, ?_, ?_⟩
      · simp [ht0]
      · simp [ht0, pathELength]
    | succ n ih =>
      obtain ⟨α, hα, hα0, hα1, hαlen⟩ := ih
      have hab : (t n : ℝ) ≤ t (n + 1) := htm (Nat.le_succ n)
      rcases hab.eq_or_lt with heq | hlt
      · exact ⟨α, hα, hα0, hα1.trans (congrArg c heq), by simpa [heq] using hαlen⟩
      obtain ⟨x, hx⟩ := htcover n
      have hsub : Icc (t n : ℝ) (t (n + 1)) ⊆ Icc 0 1 :=
        Icc_subset_Icc (t n).property.1 (t (n + 1)).property.2
      have hmap : MapsTo c (Icc (t n : ℝ) (t (n + 1))) (U x) := by
        intro u hu
        exact hVU x (hx (show (⟨u, hsub hu⟩ : unitInterval) ∈ Icc (t n) (t (n+1)) from hu))
      obtain ⟨β, hβ, hβ0, hβ1, hβlen⟩ := hreplace x hlt (hc.mono hsub) hmap
      obtain ⟨σ, hσ, hσ0, hσ1, hσlen⟩ :=
        exists_smooth_path_length_eq_add g hα hβ (hα1.trans hβ0.symm)
      refine ⟨σ, hσ.contMDiffOn, hσ0.trans hα0, hσ1.trans hβ1, ?_⟩
      rw [hσlen]
      calc
        _ ≤ (r : ℝ≥0∞) * r * pathELength I c 0 (t n) +
            (r : ℝ≥0∞) * r * pathELength I c (t n) (t (n+1)) := add_le_add hαlen hβlen
        _ = (r : ℝ≥0∞) * r * pathELength I c 0 (t (n+1)) := by
          rw [← mul_add, pathELength_add (t n).property.1 hab]
  simpa [hN N le_rfl] using hpart N

end HolomorphicAnosov

