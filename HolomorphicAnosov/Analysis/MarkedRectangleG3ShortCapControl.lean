import HolomorphicAnosov.Topology.CompactSmallConnectedSets
import HolomorphicAnosov.Analysis.CircularCapArcImage
import HolomorphicAnosov.Analysis.MarkedRectangleG3ShortCapGeometry
import HolomorphicAnosov.Analysis.MarkedRectangleG3ComponentTransport
import HolomorphicAnosov.Topology.FrontierConnectedComponentIn
import HolomorphicAnosov.Topology.OnePointBoundedDomainComplementConnected
import HolomorphicAnosov.Topology.OnePointTranslatedClosedBallComplementConnectedG12
import HolomorphicAnosov.Topology.ConnectedComplementComponent
import Mathlib.Geometry.Manifold.Instances.Sphere
import HolomorphicAnosov.Topology.JaniszewskiNonseparation
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Linarith

/-!
# Short circular caps in a Jordan domain

Source: Conway, *Functions of One Complex Variable II* (Springer, 1995), Chapter 14,
Definition 2.1 and Lemma 2.2, p.33; Definition 2.3, p.34; Theorem 5.5, proof (d) → (a),
p.50. Only the topological small-crosscut argument is used, not conformality, boundary
extension of the disk homeomorphism, or nested prime-end chains.

This formalizes `analysis.marked_rectangle_g3_short_cap_control`. The image cap is selected
by transporting the component containing the fixed interior basepoint; Janiszewski places every
point outside the small enclosing ball in that component. The proof uses the named separation
dependencies and does not assert that their transitive foundations have been discharged.
-/

open Set Filter Metric
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

noncomputable section

/-- Images of shrinking circular caps have diameter tending to zero when the corresponding
image arcs have closed rectifiable extensions of length tending to zero. The two image
endpoints are allowed to coincide.

Source: Conway, *Functions of One Complex Variable II*, Chapter 14, Theorem 5.5, p.50,
small-crosscut paragraph, with Definitions 2.1–2.3, pp.33–34. `γ` is the topologically
embedded circle; `Q` is its bounded complementary connected component. `h` is the given
homeomorphism from the open unit disk to that component. `β n` agrees with the image of
our explicit source arc on `(0,1)`, as expressed by applying `h.symm` to its interior values.
No injectivity of the closed extension or distinctness of its endpoints is assumed.
Its length is Mathlib's polygonal total variation on `[0,1]`, finite by rectifiability.

Natural-language proof:
1. Rotate the disk by `ζ⁻¹`. The source circular arc has equation
   `1 + r exp(iθ)` and lies in the disk exactly for `cos θ < -r/2`.
   It separates the disk into the cap and the connected complementary region containing 0.
   The cap is convex. The other region is connected by first moving left horizontally
   to the imaginary axis, then to 0, or directly to 0 when the real part is nonpositive.
2. Polygonal total variation bounds every chord of the closed image curve by its length.
   Thus its image lies within that length of its first boundary endpoint.
3. The compact Jordan boundary is homeomorphic to the unit circle. Uniform continuity of
   this parametrization and its inverse shows that the two boundary endpoints can be joined
   along the boundary by connected compact arcs of diameter tending to zero. When they
   coincide, use the singleton endpoint. A shorter angular arc has diameter bounded by
   twice the distance between its endpoints on the unit circle.
4. Fix `h(0)` and a positive ball about it contained in `Q`. In the Riemann sphere let
   `X` be the complement of `Q` including infinity, and let `Y n` be the closed image curve
   together with the small boundary arc. Jordan separation gives compact connected `X`;
   `Y n` is compact connected and `X ∩ Y n` is precisely the small boundary arc, connected
   also in the coincident-endpoint case. `Y n` lies in a boundary-centered ball whose radius
   is the curve length plus that boundary-arc diameter.
5. For any fixed sufficiently small positive `t`, eventually that radius is below `t`.
   Every point of `Q` outside the closed radius-`t` ball and `h(0)` are not separated by
   either `X` or `Y n`: the exterior of the ball is path connected, and `Q` is connected.
   The named Janiszewski separation result puts them in the same component of
   `Q` minus the image arc.
6. Homeomorphic transport of the source components identifies this component with the
   region containing `h(0)`. Consequently the entire image cap lies in the closed
   radius-`t` ball, and all its pairwise distances are at most `2t`.
7. Letting `t` be smaller than half any requested error gives diameter tending to zero.
   No nesting, boundary regularity, boundary extension of `h`, or conformality is used.
   The argument is relative to the node's named Jordan and Janiszewski proof dependencies;
   it does not certify their transitive foundations.
-/
theorem markedRectangleG3ShortCapControl
    (γ : sphere (0 : ℂ) 1 → ℂ) (hγ : Topology.IsEmbedding γ)
    (Q : Set ℂ) (q : ℂ)
    (hQ : Q = connectedComponentIn (range γ)ᶜ q)
    (hQ_bounded : Bornology.IsBounded Q)
    (h : (ball (0 : ℂ) 1) ≃ₜ Q)
    (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n ∧ r n < 1)
    (_hr_zero : Tendsto r atTop (𝓝 0))
    (β : ℕ → ℝ → ℂ)
    (hβ_cont : ∀ n, ContinuousOn (β n) (Icc 0 1))
    (hβ_arc : ∀ n t, t ∈ Ioo (0 : ℝ) 1 →
      ∃ hb : β n t ∈ Q,
        (h.symm ⟨β n t, hb⟩ : ℂ) = markedRectangleG3CircularArc ζ (r n) t)
    (hβ_frontier : ∀ n, β n 0 ∈ frontier Q ∧ β n 1 ∈ frontier Q)
    (_hβ_rectifiable : ∀ n, BoundedVariationOn (β n) (Icc 0 1))
    (hβ_length_zero : Tendsto (fun n ↦ eVariationOn (β n) (Icc 0 1)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ Metric.ediam
      ((fun z : ball (0 : ℂ) 1 ↦ (h z : ℂ)) ''
        {z : ball (0 : ℂ) 1 | dist (z : ℂ) ζ < r n})) atTop (𝓝 0) := by
  -- Every image chord is bounded by the original polygonal length.
  have hchord (n : ℕ) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
      (ht : t ∈ Icc (0 : ℝ) 1) :
      edist (β n s) (β n t) ≤ eVariationOn (β n) (Icc 0 1) :=
    eVariationOn.edist_le (β n) hs ht
  have hendpoint_zero : Tendsto (fun n ↦ edist (β n 0) (β n 1)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hβ_length_zero
      (fun _ ↦ bot_le) (fun n ↦ hchord n (by simp) (by simp))
  have hQopen : IsOpen Q := by
    rw [hQ]
    exact (isCompact_range hγ.continuous).isClosed.isOpen_compl.connectedComponentIn
  let q₀ : ℂ := h ⟨0, by simp⟩
  have hq₀ : q₀ ∈ Q := (h ⟨0, by simp⟩).property
  have hbase_distance : ∃ d > 0, ∀ a ∈ range γ, d ≤ dist q₀ a := by
    obtain ⟨d, hd, hdQ⟩ := Metric.isOpen_iff.mp hQopen q₀ hq₀
    refine ⟨d, hd, fun a ha ↦ ?_⟩
    by_contra hdist
    have haQ := hdQ (show a ∈ ball q₀ d by simpa [dist_comm] using lt_of_not_ge hdist)
    rw [hQ] at haQ
    exact connectedComponentIn_subset (range γ)ᶜ q haQ ha
  have hQ_complement_connected : IsConnected Qᶜ := by
    have hdim : 1 < Module.rank ℝ ℂ := by
      rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
      norm_num
    let : ConnectedSpace (sphere (0 : ℂ) 1) :=
      Subtype.connectedSpace
        (isConnected_sphere hdim (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1))
    rw [hQ]
    exact HolomorphicAnosov.Topology.connected_complement_component
      (isCompact_range hγ.continuous).isClosed (isConnected_range hγ.continuous) q
  have hXcompact : IsCompact ((OnePoint.some '' Q)ᶜ) :=
    (OnePoint.isOpenEmbedding_coe.isOpenMap _ hQopen).isClosed_compl.isCompact
  have hXconnected : IsConnected ((OnePoint.some '' Q)ᶜ) :=
    HolomorphicAnosov.onePoint_bounded_complement_connected hQ_bounded hQ_complement_connected
  have hβ_compact (n : ℕ) : IsCompact (β n '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn (hβ_cont n)
  have hβ_connected (n : ℕ) : IsConnected (β n '' Icc (0 : ℝ) 1) :=
    (isConnected_Icc (by norm_num : (0 : ℝ) ≤ 1)).image (β n) (hβ_cont n)
  have hβ_contact (n : ℕ) : (β n '' Icc (0 : ℝ) 1) ∩ Q =
      β n '' Ioo (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, htQ⟩
      have ht0 : t ≠ 0 := by
        intro heq
        exact (disjoint_frontier_iff_isOpen.mpr hQopen).le_bot
          ⟨heq ▸ (hβ_frontier n).1, htQ⟩
      have ht1 : t ≠ 1 := by
        intro heq
        exact (disjoint_frontier_iff_isOpen.mpr hQopen).le_bot
          ⟨heq ▸ (hβ_frontier n).2, htQ⟩
      exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, (hβ_arc n t ht).choose⟩
  have hzero_away (n : ℕ) : r n < dist (0 : ℂ) ζ := by
    have hh : dist (0 : ℂ) ζ = 1 := by simpa [dist_comm] using hζ
    rw [hh]
    exact (hr n).2
  -- Compact local connectedness supplies small boundary continua, including equal endpoints.
  have hsmall_boundary (ε : ℝ) (hε : 0 < ε) :
      ∃ δ > 0, ∀ a ∈ range γ, ∀ b ∈ range γ, dist a b < δ →
        ∃ K : Set ℂ, K ⊆ range γ ∧ IsCompact K ∧ IsConnected K ∧
          a ∈ K ∧ b ∈ K ∧ Metric.diam K ≤ ε := by
    let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨Complex.finrank_real_complex⟩
    let : LocallyConnectedSpace (sphere (0 : ℂ) 1) :=
      ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 1)) _
    let : CompactSpace (range γ) := isCompact_iff_compactSpace.mp (isCompact_range hγ.continuous)
    let : LocallyConnectedSpace (range γ) :=
      hγ.toHomeomorph.isQuotientMap.isCoinducing.locallyConnectedSpace
    obtain ⟨δ, hδ, hsmall⟩ :=
      HolomorphicAnosov.Topology.compact_small_connected_sets (X := range γ) hε
    refine ⟨δ, hδ, fun a ha b hb hab ↦ ?_⟩
    obtain ⟨K, hKcomp, hKconn, haK, hbK, hKdiam⟩ := hsmall ⟨a, ha⟩ ⟨b, hb⟩ hab
    refine ⟨Subtype.val '' K, ?_, hKcomp.image continuous_subtype_val,
      hKconn.image _ continuous_subtype_val.continuousOn, ⟨⟨a, ha⟩, haK, rfl⟩,
      ⟨⟨b, hb⟩, hbK, rfl⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact x.property
    · have hcoe : Isometry (Subtype.val : range γ → ℂ) := isometry_subtype_coe
      rw [hcoe.diam_image]
      exact hKdiam
  have hfrontier_curve : frontier Q ⊆ range γ := by
    rw [hQ]
    simpa only [compl_compl] using
      HolomorphicAnosov.frontier_connectedComponentIn_subset_compl
        (isCompact_range hγ.continuous).isClosed.isOpen_compl q
  have hcurve_outside : range γ ⊆ Qᶜ := by
    intro z hz hzQ
    rw [hQ] at hzQ
    exact connectedComponentIn_subset (range γ)ᶜ q hzQ hz
  -- Conway's small continuum Y consists of the closed crosscut plus a boundary connector.
  -- These are applications to the particular curves above, with no endpoint-distinctness case.
  have hsmall_enclosure (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, ∃ K Y : Set ℂ,
        K ⊆ range γ ∧ IsCompact K ∧ IsConnected K ∧
        β n 0 ∈ K ∧ β n 1 ∈ K ∧
        Y = (β n '' Icc (0 : ℝ) 1) ∪ K ∧
        IsCompact Y ∧ IsConnected Y ∧ Y ∩ Qᶜ = K ∧
        Y ∩ Q = β n '' Ioo (0 : ℝ) 1 ∧
        Y ⊆ closedBall (β n 0) ε := by
    obtain ⟨δ, hδ, hsmall⟩ := hsmall_boundary ε hε
    have hend : ∀ᶠ n in atTop, edist (β n 0) (β n 1) < ENNReal.ofReal δ :=
      (tendsto_order.1 hendpoint_zero).2 _ (ENNReal.ofReal_pos.mpr hδ)
    have hlen : ∀ᶠ n in atTop,
        eVariationOn (β n) (Icc 0 1) < ENNReal.ofReal ε :=
      (tendsto_order.1 hβ_length_zero).2 _ (ENNReal.ofReal_pos.mpr hε)
    filter_upwards [hend, hlen] with n hn hnlen
    obtain ⟨K, hKsub, hKcomp, hKconn, hK0, hK1, hKdiam⟩ :=
      hsmall (β n 0) (hfrontier_curve (hβ_frontier n).1)
        (β n 1) (hfrontier_curve (hβ_frontier n).2) (edist_lt_ofReal.mp hn)
    have hKout : K ⊆ Qᶜ := hKsub.trans hcurve_outside
    have hβ0 : β n 0 ∈ β n '' Icc (0 : ℝ) 1 := ⟨0, by simp, rfl⟩
    refine ⟨K, (β n '' Icc (0 : ℝ) 1) ∪ K, hKsub, hKcomp, hKconn,
      hK0, hK1, rfl, (hβ_compact n).union hKcomp,
      (hβ_connected n).union ⟨β n 0, hβ0, hK0⟩ hKconn, ?_, ?_, ?_⟩
    · ext z
      constructor
      · rintro ⟨hz | hz, hzQ⟩
        · obtain ⟨t, ht, rfl⟩ := hz
          by_cases ht0 : t = 0
          · simpa [ht0] using hK0
          by_cases ht1 : t = 1
          · simpa [ht1] using hK1
          exact False.elim (hzQ (hβ_arc n t
            ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
              lt_of_le_of_ne ht.2 ht1⟩).choose)
        · exact hz
      · intro hz
        exact ⟨Or.inr hz, hKout hz⟩
    · ext z
      constructor
      · rintro ⟨hz | hz, hzQ⟩
        · exact Set.ext_iff.mp (hβ_contact n) z |>.mp ⟨hz, hzQ⟩
        · exact False.elim (hKout hz hzQ)
      · intro hz
        obtain ⟨hz, hzQ⟩ := Set.ext_iff.mp (hβ_contact n) z |>.mpr hz
        exact ⟨Or.inl hz, hzQ⟩
    · intro z hz
      rcases hz with ⟨t, ht, rfl⟩ | hz
      · exact (edist_lt_ofReal.mp ((hchord n ht (by simp)).trans_lt hnlen)).le
      · exact (Metric.dist_le_diam_of_mem hKcomp.isBounded hz hK0).trans hKdiam
  have hball_exterior (a : ℂ) (R : ℝ) (hR : 0 ≤ R) :
      IsConnected ((OnePoint.some '' closedBall a R)ᶜ) :=
    HolomorphicAnosov.onePoint_translated_closedBall_complement_connected a R hR
  have hfinite_component {S : Set ℂ} {x z : ℂ} (hx : x ∈ S)
      (hz : OnePoint.some z ∈ connectedComponentIn (OnePoint.some '' S) (OnePoint.some x)) :
      z ∈ connectedComponentIn S x := by
    let C := connectedComponentIn (OnePoint.some '' S) (OnePoint.some x)
    let T := OnePoint.some ⁻¹' C
    have hTC : OnePoint.some '' T = C := by
      apply image_preimage_eq_of_subset
      exact (connectedComponentIn_subset _ _).trans (image_subset_range _ _)
    have hTpre : IsPreconnected T := by
      apply OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.mp
      rw [hTC]
      exact isPreconnected_connectedComponentIn
    have hTsub : T ⊆ S := by
      intro w hw
      have hw' := connectedComponentIn_subset (OnePoint.some '' S) (OnePoint.some x) hw
      simpa using hw'
    exact hTpre.subset_connectedComponentIn
      (mem_connectedComponentIn (mem_image_of_mem _ hx)) hTsub hz
  -- Janiszewski puts every domain point outside the enclosing disk with the basepoint.
  have hJaniszewski (K Y : Set ℂ) (a : ℂ) (R : ℝ) (hR : 0 ≤ R)
      (hKconn : IsConnected K) (hYcomp : IsCompact Y) (hYconn : IsConnected Y)
      (hinter : Y ∩ Qᶜ = K) (hYball : Y ⊆ closedBall a R)
      (hqout : q₀ ∉ closedBall a R) {z : ℂ} (hzQ : z ∈ Q)
      (hzout : z ∉ closedBall a R) :
      OnePoint.some z ∈ connectedComponentIn
        (((OnePoint.some '' Q)ᶜ) ∪ (OnePoint.some '' Y))ᶜ (OnePoint.some q₀) := by
    have hQpre : IsPreconnected Q := by
      rw [hQ]
      exact isPreconnected_connectedComponentIn
    have hqY : q₀ ∉ Y := fun hy ↦ hqout (hYball hy)
    have hzY : z ∉ Y := fun hy ↦ hzout (hYball hy)
    have hinter' : (OnePoint.some '' Q)ᶜ ∩ (OnePoint.some '' Y) =
        OnePoint.some '' K := by
      ext w
      cases w using OnePoint.rec with
      | infty => simp
      | coe w =>
        have hw : w ∈ Y ∧ w ∉ Q ↔ w ∈ K := Set.ext_iff.mp hinter w
        simpa [and_comm] using hw
    apply HolomorphicAnosov.Topology.janiszewski_nonseparation_sphere
      ((OnePoint.some '' Q)ᶜ) (OnePoint.some '' Y)
      hXcompact (hYcomp.image OnePoint.continuous_coe)
      hXconnected (hYconn.image _ OnePoint.continuous_coe.continuousOn)
    · rw [hinter']
      exact hKconn.image _ OnePoint.continuous_coe.continuousOn
    · simpa using And.intro hq₀ hqY
    · simpa using And.intro hzQ hzY
    · rw [compl_compl]
      exact (hQpre.image _ OnePoint.continuous_coe.continuousOn).subset_connectedComponentIn
        (mem_image_of_mem _ hq₀) (Subset.refl _) (mem_image_of_mem _ hzQ)
    · apply (hball_exterior a R hR).isPreconnected.subset_connectedComponentIn
        (show OnePoint.some q₀ ∈ (OnePoint.some '' closedBall a R)ᶜ by simpa using hqout)
        (compl_subset_compl.mpr (image_mono hYball))
      simpa using hzout
  have hJaniszewski_plane (K Y : Set ℂ) (a : ℂ) (R : ℝ) (hR : 0 ≤ R)
      (hKconn : IsConnected K) (hYcomp : IsCompact Y) (hYconn : IsConnected Y)
      (hinter : Y ∩ Qᶜ = K) (hYball : Y ⊆ closedBall a R)
      (hqout : q₀ ∉ closedBall a R) {z : ℂ} (hzQ : z ∈ Q)
      (hzout : z ∉ closedBall a R) : z ∈ connectedComponentIn (Q \ Y) q₀ := by
    apply hfinite_component (S := Q \ Y) (x := q₀) ⟨hq₀, fun hy ↦ hqout (hYball hy)⟩
    have heq : (((OnePoint.some '' Q)ᶜ) ∪ (OnePoint.some '' Y))ᶜ =
        OnePoint.some '' (Q \ Y) := by
      ext w
      cases w using OnePoint.rec with
      | infty => simp
      | coe w => simp
    rw [← heq]
    exact hJaniszewski K Y a R hR hKconn hYcomp hYconn hinter hYball hqout hzQ hzout
  have himage_arc (n : ℕ) (x : ball (0 : ℂ) 1) :
      (h x : ℂ) ∈ β n '' Ioo (0 : ℝ) 1 ↔ (x : ℂ) ∈ sphere ζ (r n) := by
    have harc := circular_cap_arc_image ζ (by simpa using hζ) (r n) (hr n).1 (hr n).2
    change markedRectangleG3CircularArc ζ (r n) '' Ioo 0 1 = _ at harc
    constructor
    · rintro ⟨t, ht, heq⟩
      obtain ⟨hb, hbeq⟩ := hβ_arc n t ht
      have hex : (x : ℂ) = markedRectangleG3CircularArc ζ (r n) t := by
        have hh : (⟨β n t, hb⟩ : Q) = h x := Subtype.ext heq
        simpa [hh] using hbeq
      rw [hex]
      exact (harc ▸ mem_image_of_mem (markedRectangleG3CircularArc ζ (r n)) ht).2
    · intro hx
      obtain ⟨t, ht, heq⟩ := harc.symm ▸ (show (x : ℂ) ∈ ball (0 : ℂ) 1 ∩ sphere ζ (r n)
        from ⟨x.property, hx⟩)
      obtain ⟨hb, hbeq⟩ := hβ_arc n t ht
      refine ⟨t, ht, ?_⟩
      have hh : h.symm ⟨β n t, hb⟩ = x := Subtype.ext (hbeq.trans heq)
      exact congrArg Subtype.val ((h.symm_apply_eq).mp hh)
  have hcap_bound (n : ℕ) (K Y : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
      (hKconn : IsConnected K) (hYcomp : IsCompact Y) (hYconn : IsConnected Y)
      (hinter : Y ∩ Qᶜ = K) (hYball : Y ⊆ closedBall (β n 0) R)
      (hYQ : Y ∩ Q = β n '' Ioo (0 : ℝ) 1)
      (hqout : q₀ ∉ closedBall (β n 0) R) :
      (fun z : ball (0 : ℂ) 1 ↦ (h z : ℂ)) ''
        {z : ball (0 : ℂ) 1 | dist (z : ℂ) ζ < r n} ⊆ closedBall (β n 0) R := by
    rintro z ⟨x, hx, rfl⟩
    by_contra hzout
    have hzc := hJaniszewski_plane K Y (β n 0) R hR hKconn hYcomp hYconn
      hinter hYball hqout (h x).property hzout
    let F := ball (0 : ℂ) 1 \ sphere ζ (r n)
    have hFG : h '' {x : ball (0 : ℂ) 1 | (x : ℂ) ∈ F} =
        {y : Q | (y : ℂ) ∈ Q \ Y} := by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨(h w).property, ?_⟩
        intro hy
        exact hw.2 ((himage_arc n w).mp (hYQ ▸ ⟨hy, (h w).property⟩))
      · intro hy
        refine ⟨h.symm y, ⟨(h.symm y).property, ?_⟩, h.apply_symm_apply y⟩
        intro hs
        have ha := (himage_arc n (h.symm y)).mpr hs
        rw [h.apply_symm_apply] at ha
        exact hy.2 ((show (y : ℂ) ∈ Y ∩ Q from hYQ.symm ▸ ha).1)
    have h0F : (0 : ℂ) ∈ F := by
      refine ⟨by simp, ?_⟩
      exact fun hs ↦ (ne_of_gt (hzero_away n)) (mem_sphere.mp hs)
    rw [homeomorph_component_image_ambient h F (Q \ Y) sdiff_subset hFG h0F] at hzc
    obtain ⟨w, hw, hweq⟩ := hzc
    have hwx : w = x := h.injective (Subtype.ext hweq)
    subst w
    have hxcomp : (x : ℂ) ∈ connectedComponentIn F (0 : ℂ) := by
      have hh := continuous_subtype_val.continuousOn.mapsTo_connectedComponentIn
        (show (⟨0, by simp⟩ : ball (0 : ℂ) 1) ∈ {x : ball (0 : ℂ) 1 | (x : ℂ) ∈ F}
          from h0F) hw
      exact connectedComponentIn_mono (0 : ℂ) (by
        rintro z ⟨v, hv, rfl⟩
        exact hv) hh
    have h0comp : (0 : ℂ) ∈ connectedComponentIn F (x : ℂ) := by
      rw [← connectedComponentIn_eq hxcomp]
      exact mem_connectedComponentIn h0F
    have hcap := HolomorphicAnosov.Topology.convex_cap_component
      (ball (0 : ℂ) 1) (convex_ball (0 : ℂ) 1) ζ (r n) (x : ℂ) ⟨x.property, hx⟩
    rw [hcap] at h0comp
    exact (not_lt_of_ge (hzero_away n).le) h0comp.2
  obtain ⟨d, hd, hdsep⟩ := hbase_distance
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδpos, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hδpos' : 0 < (δ : ℝ) := by exact_mod_cast hδpos
  let R := min (d / 2) ((δ : ℝ) / 2)
  have hR : 0 < R := lt_min (half_pos hd) (half_pos hδpos')
  filter_upwards [hsmall_enclosure R hR] with n hn
  obtain ⟨K, Y, hKsub, hKcomp, hKconn, hK0, hK1, hYdef, hYcomp, hYconn,
    hinter, hYQ, hYball⟩ := hn
  have hqout : q₀ ∉ closedBall (β n 0) R := by
    intro hq
    have hsep := hdsep _ (hfrontier_curve (hβ_frontier n).1)
    have hRd : R ≤ d / 2 := min_le_left _ _
    have hqd := mem_closedBall.mp hq
    linarith
  have hsub := hcap_bound n K Y R hR.le hKconn hYcomp hYconn hinter hYball hYQ hqout
  apply le_trans (Metric.ediam_le_of_forall_dist_le (C := (δ : ℝ)) (fun x hx y hy ↦ ?_))
    (by simpa using hδε.le)
  exact (dist_triangle x (β n 0) y).trans (by
    have hxR := mem_closedBall.mp (hsub hx)
    have hyR := mem_closedBall.mp (hsub hy)
    rw [dist_comm (β n 0) y]
    have hRδ : R ≤ (δ : ℝ) / 2 := min_le_right _ _
    linarith)

end

end HolomorphicAnosov.Analysis

