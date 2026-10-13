import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Nearest-point control for compact carriers

This is the metric part of Hatcher's controlled partial-retraction
construction.  It is independent of the subsequent CW cell selection: a
compact nonempty carrier admits a chosen nearest point at every ambient point,
and the chosen values are within twice the distance to any prescribed carrier
point.
-/

namespace HolomorphicAnosov

/-- A compact nonempty carrier has a nearest-point choice with a factor-two bound.

Source: Hatcher, *Algebraic Topology*, Theorem A.7, printed p.526, nearest-point vertex values.
The distance from any fixed ambient point is continuous on the nonempty compact carrier, so
it attains a minimum. Choose one minimizer for each ambient point. At a carrier point the
minimum is zero, forcing the chosen point to be that point. For any carrier point c,
minimality gives dist(z,p(z)) ≤ dist(z,c); the triangle inequality then gives
 dist(p(z),c) ≤ dist(p(z),z) + dist(z,c) ≤ 2 dist(z,c).
-/
theorem nearest_point_factor_two
    (N : ℕ) (C : Set (EuclideanSpace ℝ (Fin N)))
    (hC : IsCompact C) (hne : C.Nonempty) :
    ∃ nearest : EuclideanSpace ℝ (Fin N) → C,
      (∀ c : C, nearest c.val = c) ∧
      ∀ z : EuclideanSpace ℝ (Fin N), ∀ c : C,
        dist (nearest z).val c.val ≤ 2 * dist z c.val := by
  classical
  obtain ⟨c₀, hc₀⟩ := hne
  have hnearest (z : EuclideanSpace ℝ (Fin N)) :
      ∃ c : C, ∀ c' : C, dist z c.val ≤ dist z c'.val := by
    obtain ⟨c, hc, hmin⟩ := hC.exists_isMinOn ⟨c₀, hc₀⟩
      (continuous_const.dist continuous_id).continuousOn
    exact ⟨⟨c, hc⟩, fun c' ↦ hmin c'.property⟩
  choose nearest hnearest using hnearest
  have hfix (c : C) : nearest c.val = c := by
    apply Subtype.ext
    apply dist_eq_zero.mp
    have h := hnearest c.val c
    rw [dist_self] at h
    exact (dist_comm _ _).trans (le_antisymm h dist_nonneg)
  refine ⟨nearest, hfix, ?_⟩
  intro z c
  calc
    dist (nearest z).val c.val ≤ dist (nearest z).val z + dist z c.val :=
      dist_triangle _ _ _
    _ = dist z (nearest z).val + dist z c.val := by
      rw [dist_comm (nearest z).val z]
    _ ≤ dist z c.val + dist z c.val := add_le_add (hnearest z c) le_rfl
    _ = 2 * dist z c.val := (two_mul _).symm

/-- The factor-two estimate gives the strict image-distance control used near a carrier point.

Source: Hatcher, *Algebraic Topology*, Theorem A.7, printed p.526; elementary metric
and set-theoretic details for the vertex assignment.
Take the nearest-point choice p furnished by the compact minimum construction. It fixes C and
satisfies dist(p(z),c) ≤ 2 dist(z,c) for every c in C. Given ε and dist(z,c)<ε/2, multiplication
by the strictly positive number 2 preserves strict inequality, giving 2 dist(z,c)<2(ε/2)=ε.
Transitivity with the factor-two bound proves the required strict conclusion, using exactly the
same function p and the same fixing equation.
-/
theorem nearest_point_factor_two_lt
    (N : ℕ) (C : Set (EuclideanSpace ℝ (Fin N)))
    (hC : IsCompact C) (hne : C.Nonempty) :
    ∃ nearest : EuclideanSpace ℝ (Fin N) → C,
      (∀ c : C, nearest c.val = c) ∧
      ∀ z : EuclideanSpace ℝ (Fin N), ∀ c : C, ∀ ε : ℝ, 0 < ε →
        dist z c.val < ε / 2 → dist (nearest z).val c.val < ε := by
  obtain ⟨nearest, hfix, hcontrol⟩ := nearest_point_factor_two N C hC hne
  refine ⟨nearest, hfix, ?_⟩
  intro z c ε hε hz
  calc
    dist (nearest z).val c.val ≤ 2 * dist z c.val := hcontrol z c
    _ < 2 * (ε / 2) := mul_lt_mul_of_pos_left hz (by norm_num)
    _ = ε := by ring

/-- A nonsingleton carrier supplies two distinct points for an attaching anchor.

Source: Hatcher, *Algebraic Topology*, Theorem A.7, printed p.526; elementary metric
and set-theoretic details for the vertex assignment.
By definition, a set is subsingleton if every pair of its elements are equal. Suppose that there
were no two distinct elements of the given set. Then for any a and b in the set, their inequality
would produce just such a pair, so a=b by classical logic. This would prove that the set is
subsingleton, contradicting the hypothesis. Hence there are a and b in the set with a≠b, and
unpacking their subtype membership gives the two required ambient membership witnesses.
-/
theorem exists_pair_ne_of_not_subsingleton
    {α : Type*} {C : Set α} (hC : ¬ C.Subsingleton) :
    ∃ x ∈ C, ∃ y ∈ C, x ≠ y :=
  Set.not_subsingleton_iff.mp hC

end HolomorphicAnosov
