import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices.plaqueBoundary
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Tactic

/-!
# Directional boundaries in strict stable germs

Bowen, *Markov Partitions and Minimal Sets for Axiom A Diffeomorphisms*
(1970), Lemma 2, pp. 908–909. Pair contraction identifies the germ of the
closed stable plaque based at a point with the fixed-base plaque germ.
DAG node: `dynamics.bowen_stable_directional_boundary_trace_g10`.
The carrier-topology comparison is an agent-written expansion of the cited source.
Consequently the self-centered directional boundary of a closed set, inside
a strict stable germ, is exactly the fixed-base slice frontier there.
-/

namespace HolomorphicAnosov.Dynamics.Bowen

open Set
open HolomorphicAnosov.Bowen.RectangleSlicesPreparation

/-- The directional boundary defined in the plaque centered at each point
has nowhere-dense trace on every strict fixed-base stable germ. The displayed
equality gives the actual boundary containment, rather than assuming an open
rebase map. Only pair contraction, a positive radius and closedness are used;
neither regular closure nor a connected plaque or rectangle is assumed.

Proof: at z in the fixed plaque with dist(z,x) < γ, set
η = (γ - dist(z,x))/2 > 0. Pair contraction in the fixed plaque shows that
its points within η of z lie in the plaque centered at z. Conversely pair
contraction in each of the two plaques and the triangle inequality give
membership in the fixed plaque; the estimate uses lam^n ≤ 1. Thus the two
carriers agree in this ambient ball. Intersecting each relative-interior
witnessing ball with the η-ball gives equivalent interior tests. Closedness
of R makes both slice frontiers equal slice minus interior, so their included
frontiers agree at z. The fixed-plaque slice is closed, and its frontier is
nowhere dense. The strict-germ trace is a subset of that frontier, hence is
nowhere dense too. This expands the carrier comparison suppressed by the source. -/
theorem stableDirectionalBoundaryTrace
    {X : Type*} [MetricSpace X] (F : X ≃ₜ X) (γ lam : ℝ)
    (hγ : 0 < γ) (hlam : 0 ≤ lam ∧ lam ≤ 1)
    (hcontract : ∀ a y z : X,
      y ∈ relativeClosedStablePlaque F γ a →
      z ∈ relativeClosedStablePlaque F γ a → ∀ n : ℕ,
      dist ((F : X → X)^[n] y) ((F : X → X)^[n] z) ≤ lam ^ n * dist y z)
    (R : Set X) (hR : IsClosed R) (x : X) :
    let S := relativeClosedStablePlaque F γ x
    let B : Set S := {z | dist (z : X) x < γ ∧
      (z : X) ∈ plaqueBoundary (relativeClosedStablePlaque F γ z.val) R}
    B = {z : S | dist (z : X) x < γ} ∩ frontier (plaqueSlice S R) ∧
      IsNowhereDense B := by
  dsimp only
  let S := relativeClosedStablePlaque F γ x
  have hself (z : X) : z ∈ relativeClosedStablePlaque F γ z :=
    fun _ ↦ by simpa using hγ.le
  have hagree (z : S) (hz : dist (z : X) x < γ) :
      ∃ η > 0, ∀ t : X, dist t z.val < η →
        (t ∈ S ↔ t ∈ relativeClosedStablePlaque F γ z.val) := by
    refine ⟨(γ - dist z.val x) / 2, by linarith, ?_⟩
    intro t ht
    have hp (n : ℕ) : lam ^ n ≤ 1 := pow_le_one₀ hlam.1 hlam.2
    constructor
    · intro htx n
      have hc := hcontract x t z.val htx z.property n
      have hb := mul_le_mul_of_nonneg_right (hp n) (dist_nonneg : 0 ≤ dist t z.val)
      calc
        dist ((F : X → X)^[n] t) ((F : X → X)^[n] z.val)
            ≤ dist t z.val := hc.trans (by simpa using hb)
        _ ≤ γ := by linarith [dist_nonneg (x := z.val) (y := x)]
    · intro htz n
      have hc := hcontract z.val t z.val htz (hself z.val) n
      have hb := mul_le_mul_of_nonneg_right (hp n) (dist_nonneg : 0 ≤ dist t z.val)
      have hc' := hcontract x z.val x z.property (hself x) n
      have hb' := mul_le_mul_of_nonneg_right (hp n) (dist_nonneg : 0 ≤ dist z.val x)
      have htbound := hc.trans (by simpa using hb)
      have hzbound := hc'.trans (by simpa using hb')
      have htri := dist_triangle ((F : X → X)^[n] t)
        ((F : X → X)^[n] z.val) ((F : X → X)^[n] x)
      change dist ((F : X → X)^[n] t) ((F : X → X)^[n] x) ≤ γ
      linarith
  have hinterior (z : S) (hz : dist (z : X) x < γ) :
      (⟨z.val, hself z.val⟩ : relativeClosedStablePlaque F γ z.val) ∈
        interior (plaqueSlice (relativeClosedStablePlaque F γ z.val) R) ↔
      z ∈ interior (plaqueSlice S R) := by
    obtain ⟨η, hη, ha⟩ := hagree z hz
    simp only [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    constructor
    · rintro ⟨r, hr, hb⟩
      refine ⟨min r η, lt_min hr hη, ?_⟩
      intro t ht
      have hd : dist t.val z.val < min r η := Metric.mem_ball.mp ht
      have ht' := (ha t.val (hd.trans_le (min_le_right _ _))).mp t.property
      exact hb (show (⟨t.val, ht'⟩ : relativeClosedStablePlaque F γ z.val) ∈
        Metric.ball ⟨z.val, hself z.val⟩ r from hd.trans_le (min_le_left _ _))
    · rintro ⟨r, hr, hb⟩
      refine ⟨min r η, lt_min hr hη, ?_⟩
      intro t ht
      have hd : dist t.val z.val < min r η := Metric.mem_ball.mp ht
      have ht' := (ha t.val (hd.trans_le (min_le_right _ _))).mpr t.property
      exact hb (show (⟨t.val, ht'⟩ : S) ∈ Metric.ball z r from
        hd.trans_le (min_le_left _ _))
  have hboundary (z : S) (hz : dist (z : X) x < γ) :
      z.val ∈ plaqueBoundary (relativeClosedStablePlaque F γ z.val) R ↔
        z ∈ frontier (plaqueSlice S R) := by
    have hsclosed : IsClosed (plaqueSlice S R) := hR.preimage continuous_subtype_val
    have htclosed : IsClosed (plaqueSlice (relativeClosedStablePlaque F γ z.val) R) :=
      hR.preimage continuous_subtype_val
    have himage : z.val ∈ plaqueBoundary (relativeClosedStablePlaque F γ z.val) R ↔
        (⟨z.val, hself z.val⟩ : relativeClosedStablePlaque F γ z.val) ∈
          frontier (plaqueSlice (relativeClosedStablePlaque F γ z.val) R) := by
      change z.val ∈ Subtype.val '' _ ↔ _
      constructor
      · rintro ⟨w, hw, he⟩
        have he' : w = ⟨z.val, hself z.val⟩ := Subtype.ext he
        simpa only [he'] using hw
      · intro hh
        exact ⟨⟨z.val, hself z.val⟩, hh, rfl⟩
    rw [himage, frontier, frontier, htclosed.closure_eq, hsclosed.closure_eq]
    exact and_congr Iff.rfl (not_congr (hinterior z hz))
  have heq : {z : S | dist (z : X) x < γ ∧
      (z : X) ∈ plaqueBoundary (relativeClosedStablePlaque F γ z.val) R} =
      {z : S | dist (z : X) x < γ} ∩ frontier (plaqueSlice S R) := by
    ext z
    exact and_congr_right fun hz ↦ hboundary z hz
  refine ⟨heq, ?_⟩
  have hND : IsNowhereDense (frontier (plaqueSlice S R)) := by
    apply isClosed_frontier.isNowhereDense_iff.mpr
    exact interior_frontier (hR.preimage continuous_subtype_val)
  rw [heq]
  exact hND.mono inter_subset_right

end HolomorphicAnosov.Dynamics.Bowen

