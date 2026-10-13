import HolomorphicAnosov.Topology.ControlledExtensionDiameter

namespace HolomorphicAnosov

open Set

/-- A single diameter-controlled extension obeys every centered-ball estimate
provided by a comparison extension, simultaneously.

Source: Hatcher, Algebraic Topology, Theorem A.7, printed p.526. Choose the
extension once, before choosing a carrier point or its neighborhood, using the
factor-two diameter theorem. For any comparison extension in the radius-R ball,
the triangle inequality bounds its image diameter by 2R, hence the chosen image
diameter by 4R. A prescribed boundary value within radius r of the center is
also a value of the chosen extension. Comparing any chosen image point with
this anchor gives distance strictly less than r+4R. Compactness bounds the
chosen image and makes its real-valued diameter bound valid. Only one boundary
anchor needs to be close to the center. A zero radius for the comparison ball
makes its range condition impossible because the boundary is nonempty. -/
theorem hatcher_controlled_extension_uniform_ball
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]
    (A : Set X) (hA : A.Nonempty) (f : C(A, Y))
    (hex : ∃ g : C(X, Y), ∀ a : A, g a = f a) :
    ∃ g : C(X, Y), (∀ a : A, g a = f a) ∧
      (∀ h : C(X, Y), (∀ a : A, h a = f a) →
        Metric.diam (range g) ≤ 2 * Metric.diam (range h)) ∧
      ∀ (c : Y) (r R : ℝ), 0 ≤ R →
        (∃ a : A, dist (f a) c < r) →
        (∃ h : C(X, Y), (∀ a : A, h a = f a) ∧
          ∀ x, dist (h x) c < R) →
        ∀ x, dist (g x) c < r + 4 * R := by
  obtain ⟨g, hg, hdiam⟩ := exists_continuous_extension_diam_le_two_mul A hA f hex
  refine ⟨g, hg, hdiam, ?_⟩
  intro c r R hR hanchor hcomp x
  obtain ⟨a, ha⟩ := hanchor
  obtain ⟨h, hh, hball⟩ := hcomp
  have hd : Metric.diam (range h) ≤ 2 * R := by
    apply Metric.diam_le_of_forall_dist_le (by positivity)
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    have ht := dist_triangle_right (h u) (h v) c
    linarith [hball u, hball v]
  have hp := Metric.dist_le_diam_of_mem (isCompact_range g.continuous).isBounded
    (mem_range_self x) (mem_range_self a.val)
  have hga : dist (g a.val) c < r := by rw [hg a]; exact ha
  have ht := dist_triangle (g x) (g a.val) c
  have hgdiam := hdiam h hh
  linarith


end HolomorphicAnosov
