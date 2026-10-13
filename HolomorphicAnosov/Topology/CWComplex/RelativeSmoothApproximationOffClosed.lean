import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Homotopy.Affine

namespace HolomorphicAnosov

open Set Metric
open scoped Topology _root_.Topology ContDiff Manifold

/-- Bredon, Topology and Geometry, II.11.7, pp.96–97, specialized to A empty.
A continuous vector-valued map can be smoothed off an arbitrary closed set,
fixed on that set, through an arbitrarily small relative homotopy.

On the complement of B choose the pointwise approximation error less than
both epsilon/2 and the distance to B (use a constant positive bound if B is
empty). The smooth partition-of-unity approximation theorem supplies a
smooth map on that open manifold. Extend it by f on B. The distance-to-B
bound proves continuity at B. The straight-line homotopy is fixed on B and
stays within epsilon of f, as in Bredon's proof. -/
theorem relative_smooth_approximation_off_closed
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MetricSpace M] [SecondCountableTopology M]
    [LocallyCompactSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (B : Set M) (hB : IsClosed B) (f : C(M, F)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : C(M, F), ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g Bᶜ ∧
      ∃ H : ContinuousMap.HomotopyRel f g B,
        ∀ t x, dist (H (t, x)) (f x) < ε := by
  classical
  let U : TopologicalSpace.Opens M := ⟨Bᶜ, hB.isOpen_compl⟩
  have : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let δ : M → ℝ := fun x ↦ min (ε / 2) (if B.Nonempty then infDist x B else 1)
  have hδcont : Continuous δ := by
    dsimp [δ]
    split_ifs <;> fun_prop
  have hδpos : ∀ x : U, 0 < δ x := by
    intro x
    dsimp [δ]
    apply lt_min (by linarith)
    split_ifs with hb
    · exact (hB.notMem_iff_infDist_pos hb).mp x.property
    · norm_num
  obtain ⟨g₀, hg₀, _⟩ := (f.continuous.comp continuous_subtype_val).exists_contMDiff_approx
    𝓘(ℝ, E) (⊤ : ℕ∞) (hδcont.comp continuous_subtype_val) hδpos
  let q : M → F := fun x ↦ if hx : x ∈ B then f x else g₀ ⟨x, hx⟩
  have hqB : ∀ x ∈ B, q x = f x := by intro x hx; simp [q, hx]
  have hqU : ∀ x : U, q x = g₀ x := by
    intro x
    have hx : (x : M) ∉ B := x.property
    simp [q, hx]
  have hqclose : ∀ x, dist (q x) (f x) < ε := by
    intro x
    by_cases hx : x ∈ B
    · simp [hqB x hx, hε]
    · have h := hg₀ ⟨x, hx⟩
      have hδ : δ x ≤ ε / 2 := min_le_left _ _
      have hq : q x = g₀ ⟨x, hx⟩ := hqU ⟨x, hx⟩
      rw [hq]
      exact h.trans_le hδ |>.trans (by linarith)
  have hqcontU : ContinuousOn q Bᶜ := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (fun x : U ↦ q x) = g₀ := funext hqU
    change Continuous (fun x : U ↦ q x)
    rw [heq]
    exact g₀.contMDiff.continuous
  have hqcont : Continuous q := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ B
    · rw [Metric.continuousAt_iff]
      intro η hη
      obtain ⟨r, hr, hfr⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt
        (η / 2) (by linarith)
      refine ⟨min r (η / 2), lt_min hr (by linarith), ?_⟩
      intro y hy
      rw [hqB x hx]
      have hyf : dist (f y) (f x) < η / 2 := hfr (lt_of_lt_of_le hy (min_le_left _ _))
      by_cases hyB : y ∈ B
      · rw [hqB y hyB]
        linarith
      · have hδ : δ y ≤ infDist y B := by
          dsimp [δ]
          rw [ite_eq_left ⟨x, hx⟩]
          exact min_le_right _ _
        have hnear := (hg₀ ⟨y, hyB⟩).trans_le (hδ.trans (infDist_le_dist_of_mem hx))
        rw [← hqU ⟨y, hyB⟩] at hnear
        change dist (q y) (f y) < dist y x at hnear
        have hyd : dist y x < η / 2 := lt_of_lt_of_le hy (min_le_right _ _)
        exact (dist_triangle (q y) (f y) (f x)).trans_lt (by linarith)
    · exact hqcontU.continuousAt (hB.isOpen_compl.mem_nhds hx)
  let g : C(M, F) := ⟨q, hqcont⟩
  have hqsmooth : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ q Bᶜ := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    rw [← contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))]
    have heq : (fun x : U ↦ q x) = g₀ := funext hqU
    rw [heq]
    exact g₀.contMDiff.contMDiffAt
  let H : ContinuousMap.HomotopyRel f g B := {
    ContinuousMap.Homotopy.affine f g with
    prop' := fun t x hx ↦ by simp [ContinuousMap.Homotopy.affine, g, hqB x hx,
      Path.segment, AffineMap.lineMap_apply] }
  refine ⟨g, hqsmooth, H, ?_⟩
  intro t x
  have heq : H (t, x) - f x = (t : ℝ) • (g x - f x) := by
    change AffineMap.lineMap (f x) (g x) (t : ℝ) - f x = _
    rw [AffineMap.lineMap_apply]
    change ((t : ℝ) • (g x - f x) + f x) - f x = _
    exact add_sub_cancel_right _ _
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  apply lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) t.property.2)
  exact (dist_eq_norm (g x) (f x)) ▸ hqclose x

end HolomorphicAnosov
