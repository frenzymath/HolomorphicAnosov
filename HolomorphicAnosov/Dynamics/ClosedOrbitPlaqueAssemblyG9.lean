import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Final assembly of closed orbit plaques

Source: Shub, Global Stability of Dynamical Systems (1987), Theorem 6.2,
pp.71–72, and Bowen, Markov Partitions for Axiom A Diffeomorphisms (1970),
Fact 1, pp.726–727. These are the elementary final steps after constructing
native center contraction and unique local stable/unstable intersections.
-/

namespace HolomorphicAnosov

open Set

/-- Center contraction at twice the plaque radius gives contraction between
any two points in a plaque at every natural time. Indeed the triangle inequality
puts the two orbits within twice the radius. Apply center contraction with
one of the two points as center, at each iterate, and induct. Forward invariance
keeps every rebased center in the original invariant set. No local manifold or
regularity of the invariant set is needed in this final step. -/
theorem closed_orbit_plaque_pair_contraction
    {X : Type*} [PseudoMetricSpace X] (F : X → X) (K : Set X)
    (hinv : MapsTo F K K) (κ γ : ℝ) (hκ : 0 ≤ κ)
    (hcenter : ∀ x ∈ K, ∀ y ∈ K,
      (∀ n : ℕ, dist (F^[n] y) (F^[n] x) ≤ 2 * γ) →
      dist (F y) (F x) ≤ κ * dist y x)
    {x y z : X} (hy : y ∈ K) (hz : z ∈ K)
    (hyx : ∀ n : ℕ, dist (F^[n] y) (F^[n] x) ≤ γ)
    (hzx : ∀ n : ℕ, dist (F^[n] z) (F^[n] x) ≤ γ) :
    ∀ n : ℕ, dist (F^[n] y) (F^[n] z) ≤ κ ^ n * dist y z := by
  have hpair (n : ℕ) : dist (F^[n] y) (F^[n] z) ≤ 2 * γ := by
    calc
      _ ≤ dist (F^[n] y) (F^[n] x) + dist (F^[n] x) (F^[n] z) := dist_triangle _ _ _
      _ ≤ γ + γ := add_le_add (hyx n) (by simpa only [dist_comm] using hzx n)
      _ = 2 * γ := by ring
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := hcenter (F^[n] z) (hinv.iterate n hz) (F^[n] y) (hinv.iterate n hy)
      (fun m ↦ by simpa only [← Function.iterate_add_apply] using hpair (m + n))
    calc
      dist (F^[n + 1] y) (F^[n + 1] z) ≤ κ * dist (F^[n] y) (F^[n] z) := by
        simpa only [Function.iterate_succ_apply'] using hstep
      _ ≤ κ * (κ ^ n * dist y z) := mul_le_mul_of_nonneg_left ih hκ
      _ = κ ^ (n + 1) * dist y z := by rw [pow_succ]; ring

/-- A uniform center contraction separates any two complete orbits that stay
within its capture radius. Rebase the forward contraction at time -n, bound
that initial distance by δ, and let κ^n tend to zero. Source: Bowen Fact 1,
pp.726–727, expansivity from local stable contraction. -/
theorem complete_orbits_eq_of_center_contraction
    {X : Type*} [MetricSpace X] (F : X → X) (K : Set X)
    (κ δ : ℝ) (hκ : 0 ≤ κ) (hκ1 : κ < 1)
    (hcenter : ∀ x ∈ K, ∀ y ∈ K,
      (∀ n : ℕ, dist (F^[n] y) (F^[n] x) ≤ δ) →
      dist (F y) (F x) ≤ κ * dist y x)
    (a b : ℤ → X) (ha : ∀ k, a k ∈ K) (hb : ∀ k, b k ∈ K)
    (haF : ∀ k, F (a k) = a (k + 1)) (hbF : ∀ k, F (b k) = b (k + 1))
    (hclose : ∀ k, dist (a k) (b k) ≤ δ) : a 0 = b 0 := by
  have hiter (c : ℤ → X) (hc : ∀ k, F (c k) = c (k + 1)) (k : ℤ) (n : ℕ) :
      F^[n] (c k) = c (k + n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hc]
      congr 1
      simp only [Nat.cast_add, Nat.cast_one]
      ring
  have hstep (k : ℤ) : dist (a (k + 1)) (b (k + 1)) ≤ κ * dist (a k) (b k) := by
    have hh := hcenter (b k) (hb k) (a k) (ha k) (fun n ↦ by
      simpa only [hiter a haF, hiter b hbF] using hclose (k + n))
    simpa only [haF, hbF] using hh
  have hbound (n : ℕ) (k : ℤ) :
      dist (a (k + n)) (b (k + n)) ≤ κ ^ n * dist (a k) (b k) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have he : k + (↑(n + 1) : ℤ) = (k + n) + 1 := by push_cast; ring
      rw [he, pow_succ']
      exact (hstep (k + n)).trans
        ((mul_le_mul_of_nonneg_left ih hκ).trans_eq (mul_assoc _ _ _).symm)
  have hzero (n : ℕ) : dist (a 0) (b 0) ≤ κ ^ n * δ := by
    have hh := (hbound n (-(n : ℤ))).trans
      (mul_le_mul_of_nonneg_left (hclose (-(n : ℤ))) (pow_nonneg hκ n))
    simpa using hh
  have hlim : Filter.Tendsto (fun n : ℕ ↦ κ ^ n * δ) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hκ hκ1).mul_const δ
  exact dist_eq_zero.mp (le_antisymm (ge_of_tendsto hlim (Filter.Eventually.of_forall hzero)) dist_nonneg)

/-- Two points in the same closed stable plaque and the same closed unstable
plaque coincide once the double-radius center contraction holds. The triangle
inequality bounds their complete orbits by twice the plaque radius, then the
preceding rebasing argument applies. -/
theorem closed_orbit_intersection_subsingleton
    {X : Type*} [MetricSpace X] (F : X ≃ₜ X) (K : Set X)
    (hf : MapsTo F K K) (hb : MapsTo F.symm K K)
    (κ γ : ℝ) (hκ : 0 ≤ κ) (hκ1 : κ < 1)
    (hcenter : ∀ x ∈ K, ∀ y ∈ K,
      (∀ n : ℕ, dist ((F : X → X)^[n] y) ((F : X → X)^[n] x) ≤ 2 * γ) →
      dist (F y) (F x) ≤ κ * dist y x)
    {x y z w : X} (hz : z ∈ K) (hw : w ∈ K)
    (hzs : ∀ n : ℕ, dist ((F : X → X)^[n] z) ((F : X → X)^[n] x) ≤ γ)
    (hws : ∀ n : ℕ, dist ((F : X → X)^[n] w) ((F : X → X)^[n] x) ≤ γ)
    (hzu : ∀ n : ℕ, dist ((F.symm : X → X)^[n] z) ((F.symm : X → X)^[n] y) ≤ γ)
    (hwu : ∀ n : ℕ, dist ((F.symm : X → X)^[n] w) ((F.symm : X → X)^[n] y) ≤ γ) : z = w := by
  have hpow (G : X ≃ₜ X) (n : ℕ) (v : X) : (G ^ n) v = (G : X → X)^[n] v := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Homeomorph.mul_apply, Function.iterate_succ_apply', ih]
  have hpos (n : ℕ) (v : X) : (F ^ (n : ℤ)) v = (F : X → X)^[n] v := by
    rw [zpow_natCast, hpow]
  have hneg (n : ℕ) (v : X) : (F ^ (-(n : ℤ))) v = (F.symm : X → X)^[n] v := by
    rw [zpow_neg, ← inv_zpow, zpow_natCast]
    exact hpow F.symm n v
  have hmem (v : X) (hv : v ∈ K) (k : ℤ) : (F ^ k) v ∈ K := by
    obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
    · rw [hpos]; exact hf.iterate n hv
    · rw [hneg]; exact hb.iterate n hv
  have horbit (v : X) (k : ℤ) : F ((F ^ k) v) = (F ^ (k + 1)) v := by
    rw [show k + 1 = 1 + k by omega, zpow_add, zpow_one]
    rfl
  have hclose (k : ℤ) : dist ((F ^ k) z) ((F ^ k) w) ≤ 2 * γ := by
    obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
    · rw [hpos, hpos]
      exact (dist_triangle_right _ _ ((F : X → X)^[n] x)).trans
        ((add_le_add (hzs n) (hws n)).trans_eq (by ring))
    · rw [hneg, hneg]
      exact (dist_triangle_right _ _ ((F.symm : X → X)^[n] y)).trans
        ((add_le_add (hzu n) (hwu n)).trans_eq (by ring))
  have hh := complete_orbits_eq_of_center_contraction (F : X → X) K κ (2 * γ) hκ hκ1
    hcenter (fun k ↦ (F ^ k) z) (fun k ↦ (F ^ k) w)
    (hmem z hz) (hmem w hw) (horbit z) (horbit w) hclose
  simpa only [zpow_zero, Homeomorph.one_apply] using hh

/-- A unique intersection of closed forward/backward orbit plaques varies
continuously on any prescribed domain of center pairs. Each finite-time distance
inequality is closed by continuity of the iterates. Their intersection is the
graph of the unique selected point. Since the range is compact, the closed-graph
theorem gives continuity; no separate quantitative parameter estimate is needed.
This includes arbitrary domains with their original subtype topology. -/
theorem continuous_unique_closed_orbit_intersection
    {X : Type*} [MetricSpace X] [CompactSpace X]
    {T : Type*} [TopologicalSpace T]
    (F : X ≃ₜ X) (a c : T → X) (ha : Continuous a) (hc : Continuous c) (γ : ℝ)
    (hunique : ∀ p : T, ∃! z : X,
      (∀ n : ℕ, dist ((F : X → X)^[n] z) ((F : X → X)^[n] (a p)) ≤ γ) ∧
      (∀ n : ℕ, dist ((F.symm : X → X)^[n] z) ((F.symm : X → X)^[n] (c p)) ≤ γ)) :
    ∃ b : T → X, Continuous b ∧ ∀ p : T, ∀ z : X,
      ((∀ n : ℕ, dist ((F : X → X)^[n] z) ((F : X → X)^[n] (a p)) ≤ γ) ∧
       (∀ n : ℕ, dist ((F.symm : X → X)^[n] z) ((F.symm : X → X)^[n] (c p)) ≤ γ)) ↔
        z = b p := by
  classical
  choose b hb using fun p ↦ (hunique p).exists
  have hiff (p : T) (z : X) :
      ((∀ n : ℕ, dist ((F : X → X)^[n] z) ((F : X → X)^[n] (a p)) ≤ γ) ∧
       (∀ n : ℕ, dist ((F.symm : X → X)^[n] z) ((F.symm : X → X)^[n] (c p)) ≤ γ)) ↔
        z = b p := by
    constructor
    · exact fun hz ↦ (hunique p).unique hz (hb p)
    · rintro rfl
      exact hb p
  refine ⟨b, continuous_of_isClosed_graph ?_, hiff⟩
  have hgraph : b.graph =
      {q : T × X | ∀ n : ℕ,
        dist ((F : X → X)^[n] q.2) ((F : X → X)^[n] (a q.1)) ≤ γ} ∩
      {q : T × X | ∀ n : ℕ,
        dist ((F.symm : X → X)^[n] q.2) ((F.symm : X → X)^[n] (c q.1)) ≤ γ} := by
    ext q
    exact (eq_comm.trans (hiff q.1 q.2).symm)
  rw [hgraph]
  simp only [Set.ofPred_forall]
  apply IsClosed.inter <;> apply isClosed_iInter <;> intro n
  · exact isClosed_le (((F.continuous.iterate n).comp continuous_snd).dist
      ((F.continuous.iterate n).comp
        (ha.comp continuous_fst))) continuous_const
  · exact isClosed_le (((F.symm.continuous.iterate n).comp continuous_snd).dist
      ((F.symm.continuous.iterate n).comp
        (hc.comp continuous_fst))) continuous_const

end HolomorphicAnosov



