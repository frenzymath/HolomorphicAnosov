import HolomorphicAnosov.Geometry.HPSNativePlaqueFamilyData
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

open Set
open scoped Manifold ContDiff _root_.Topology
namespace HolomorphicAnosov
universe u

/-- A connected set meeting the interior image of a compact parameter disk and avoiding its boundary
image lies entirely in the interior image. (Lee, Prop. 11.20, pp.278–279) -/
theorem connected_subset_plaque_ball_of_avoids_sphere
    {V Y : Type*} [NormedAddCommGroup V] [ProperSpace V]
    [TopologicalSpace Y] [T2Space Y]
    (q : V → Y) {r : ℝ} (hq : ContinuousOn q (Metric.closedBall (0 : V) r))
    (hopen : IsOpen (q '' Metric.ball (0 : V) r))
    {K : Set Y} (hK : IsPreconnected K)
    (hstart : (K ∩ q '' Metric.ball (0 : V) r).Nonempty)
    (havoid : Disjoint K (q '' Metric.sphere (0 : V) r)) :
    K ⊆ q '' Metric.ball (0 : V) r := by
  apply hK.subset_of_closure_inter_subset hopen hstart
  have hc := (isCompact_closedBall (0 : V) r).image_of_continuousOn hq
  have hcl : closure (q '' Metric.ball (0 : V) r) ⊆ q '' Metric.closedBall (0 : V) r :=
    closure_minimal (image_mono Metric.ball_subset_closedBall) hc.isClosed
  rintro y ⟨hy, hyK⟩
  obtain ⟨v, hv, rfl⟩ := hcl hy
  refine ⟨v, ?_, rfl⟩
  have hne : dist v 0 ≠ r := by
    intro heq
    exact Set.disjoint_left.mp havoid hyK ⟨v, heq, rfl⟩
  exact lt_of_le_of_ne hv hne

/-- The image of a compact inner parameter sphere stays a uniform positive distance from the centers
of nearby native plaques. (HPS, pp.61–63) -/
theorem NativePlaqueFamily.uniform_inner_sphere_separation
    {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)} {x : M}
    (Φ : NativePlaqueFamily 𝓘(ℝ, E) (V := V) D x)
    {r : ℝ} (hr : 0 < r) (hrR : r < Φ.radius) :
    ∃ N : Set Φ.centerDomain, IsOpen N ∧ ⟨x, Φ.center_mem⟩ ∈ N ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ N, ∀ v ∈ Metric.sphere (0 : V) r,
        δ ≤ dist ((Φ.plaque p).param v) p.val := by
  let p₀ : Φ.centerDomain := ⟨x, Φ.center_mem⟩
  let B := Metric.ball (0 : V) Φ.radius
  let F : Φ.centerDomain × V → ℝ := fun z ↦ dist ((Φ.plaque z.1).param z.2) z.1.val
  have hF : ContinuousOn F (univ ×ˢ B) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (Φ.jointly_continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z ↦ z.property.2)))).dist
      (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
  have hball (v : V) (hv : v ∈ Metric.sphere (0 : V) r) : v ∈ B :=
    (Metric.sphere_subset_ball hrR) hv
  have hpositive (v : V) (hv : v ∈ Metric.sphere (0 : V) r) : 0 < F (p₀, v) := by
    apply dist_pos.mpr
    intro heq
    have hvdom : v ∈ (Φ.plaque p₀).domain := by rw [Φ.domain_eq]; exact hball v hv
    have hinj := (Φ.plaque p₀).embedded.injective
    have hv0 : (⟨v, hvdom⟩ : (Φ.plaque p₀).domain) = ⟨0, (Φ.plaque p₀).zero_mem⟩ := by
      apply hinj
      exact heq.trans (Φ.plaque p₀).centered.symm
    have hzero := congrArg Subtype.val hv0
    change v = 0 at hzero
    subst v
    have : r = 0 := by simpa using hv.symm
    linarith
  have hFp : ContinuousOn (fun v ↦ F (p₀, v)) (Metric.sphere (0 : V) r) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv ↦ ⟨mem_univ _, hball v hv⟩)
  obtain ⟨c, hc, hclower⟩ := (isCompact_sphere (0 : V) r).exists_forall_le' hFp hpositive
  have hevent : ∀ᶠ p in 𝓝 p₀, ∀ v ∈ Metric.sphere (0 : V) r, c / 2 < F (p, v) := by
    apply (isCompact_sphere (0 : V) r).eventually_forall_of_forall_eventually
    intro v hv
    apply (hF.continuousAt ((isOpen_univ.prod Metric.isOpen_ball).mem_nhds
      ⟨mem_univ _, hball v hv⟩)).eventually
    exact lt_mem_nhds ((half_lt_self hc).trans_le (hclower v hv))
  obtain ⟨N, hNsub, hN, hpN⟩ := mem_nhds_iff.mp hevent
  exact ⟨N, hN, hpN, c / 2, half_pos hc, fun p hp v hv ↦ (hNsub hp v hv).le⟩

/-- A connected intrinsic leaf map starting at the chart center and staying closer to it than the
inner parameter sphere image lies in the inner plaque. -/
theorem NativePlaqueIntrinsicChart.connected_map_captured
    {V W : Type u} {E L M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace L] [ChartedSpace W L] [IsManifold 𝓘(ℝ, W) ∞ L] [T2Space L]
    [TopologicalSpace X] [PreconnectedSpace X]
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)} {x : M}
    {P : NativeEmbeddedPlaque 𝓘(ℝ, E) (V := V) D x}
    (T : NativePlaqueIntrinsicChart 𝓘(ℝ, E) (W := W) (L := L) D x P)
    {r δ : ℝ} (hr : 0 < r) (hdom : Metric.closedBall (0 : V) r ⊆ P.domain)
    (hboundary : ∀ v ∈ Metric.sphere (0 : V) r, δ ≤ dist (P.param v) x)
    (q : X → L) (hq : Continuous q) (z₀ : X) (hstart : T.inclusion (q z₀) = x)
    (hclose : ∀ z, dist (T.inclusion (q z)) x < δ) :
    ∀ z, T.inclusion (q z) ∈ P.param '' Metric.ball (0 : V) r := by
  have hball : Metric.ball (0 : V) r ⊆ P.domain := Metric.ball_subset_closedBall.trans hdom
  have himage : T.toLeaf '' Metric.ball (0 : V) r =
      (T.toLeaf '' P.domain) ∩ T.inverse ⁻¹' Metric.ball (0 : V) r := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hball hv, rfl⟩, by change T.inverse (T.toLeaf v) ∈ Metric.ball (0 : V) r; rwa [T.inverse_toLeaf v (hball hv)]⟩
    · rintro ⟨hy, hinv⟩
      exact ⟨T.inverse y, hinv, T.toLeaf_inverse y hy⟩
  have hopen : IsOpen (T.toLeaf '' Metric.ball (0 : V) r) := by
    rw [himage]
    exact T.inverse_smooth.continuousOn.isOpen_inter_preimage T.leafImage_open Metric.isOpen_ball
  have hsub : range q ⊆ T.toLeaf '' Metric.ball (0 : V) r := by
    apply connected_subset_plaque_ball_of_avoids_sphere T.toLeaf
      (T.toLeaf_smooth.continuousOn.mono hdom) hopen (isPreconnected_range hq)
    · refine ⟨q z₀, mem_range_self z₀, 0, Metric.mem_ball_self hr, ?_⟩
      apply T.inclusion_injective
      rw [T.inclusion_toLeaf 0 P.zero_mem, P.centered, hstart]
    · rw [Set.disjoint_left]
      rintro _ ⟨z, rfl⟩ ⟨v, hv, heq⟩
      have hveq : P.param v = T.inclusion (q z) := by
        rw [← T.inclusion_toLeaf v (hdom (Metric.sphere_subset_closedBall hv)), heq]
      exact (not_lt_of_ge (hboundary v hv)) (hveq.symm ▸ hclose z)
  intro z
  obtain ⟨v, hv, heq⟩ := hsub (mem_range_self z)
  refine ⟨v, hv, ?_⟩
  rw [← T.inclusion_toLeaf v (hball hv), heq]

end HolomorphicAnosov

