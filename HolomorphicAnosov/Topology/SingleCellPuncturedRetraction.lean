import HolomorphicAnosov.Topology.PushoutSumQuotient
import HolomorphicAnosov.Topology.CWComplex.PuncturedDiskRadialDeformation
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.CompactOpen

open CategoryTheory CategoryTheory.Limits
open Topology _root_.Topology

namespace HolomorphicAnosov
universe u

set_option backward.isDefEq.respectTransparency false in
/-- The radial retraction of a punctured cell attachment is joined to the
inclusion by a continuous homotopy fixing the old space. Source: Hatcher,
Algebraic Topology, Proposition 1.26 pp.50–51 and Theorem 4.8 p.349.
Descend the boundary-fixed radial deformation as a map into the space of
interval paths, using the compact-open topology, then uncurry. Endpoint
identities and old-space fixedness follow on quotient representatives. -/
theorem single_cell_punctured_deformation
    {X Y : TopCat.{u}} [Nonempty X] (n : ℕ)
    (φ : TopCat.diskBoundary.{u} n ⟶ X)
    (f : X ⟶ Y) (χ : TopCat.disk.{u} n ⟶ Y)
    (hpush : IsPushout φ (TopCat.diskBoundaryInclusion.{u} n) f χ)
    (p : TopCat.disk.{u} n) (hp : ‖p.down.val‖ < 1) :
    ∃ R : C({y : Y // y ≠ χ.hom p}, X),
      ∃ K : C(unitInterval × {y : Y // y ≠ χ.hom p}, Y),
        (∀ (x : X) (hx : f.hom x ≠ χ.hom p), R ⟨f.hom x, hx⟩ = x) ∧
        (∀ y, K (0, y) = y.val) ∧
        (∀ y, K (1, y) = f.hom (R y)) ∧
        (∀ t (x : X) (hx : f.hom x ≠ χ.hom p), K (t, ⟨f.hom x, hx⟩) = f.hom x) := by
  have hpboundary : p ∉ Set.range (TopCat.diskBoundaryInclusion n).hom := by
    rintro ⟨a, ha⟩
    have hnorm : ‖(TopCat.diskBoundaryInclusion n a).down.val‖ = 1 := by
      change ‖a.down.val‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using a.down.property
    rw [ha] at hnorm
    exact (ne_of_lt hp) hnorm
  let D := {b : TopCat.disk n // χ.hom b ≠ χ.hom p}
  let E := EuclideanSpace ℝ (Fin n)
  let liftD : D → {z : E // ‖z‖ ≤ 1 ∧ z ≠ p.down.val} := fun b ↦
    ⟨b.val.down.val, by
      constructor
      · simpa only [Metric.mem_closedBall, dist_zero_right] using b.val.down.property
      · intro heq
        have hb : b.val = p := ULift.ext (Subtype.ext heq)
        exact b.property (congrArg χ.hom hb)⟩
  have hlift : Continuous liftD :=
    (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_subtype_val)).subtype_mk _
  obtain ⟨H, hzero, hone, hrange, hfixed⟩ := punctured_disk_radial_deformation p.down.val hp
  let r : C(D, TopCat.diskBoundary n) :=
    ⟨fun b ↦ ULift.up ⟨H (1, liftD b), by
      simpa only [Metric.mem_sphere, dist_zero_right] using hone (liftD b)⟩,
      continuous_uliftUp.comp ((H.continuous.comp
        (continuous_const.prodMk hlift)).subtype_mk (fun b ↦ by
          simpa only [Function.comp_apply, Metric.mem_sphere, dist_zero_right] using hone (liftD b)))⟩
  let G : C(D, X) := φ.hom.comp r
  let : T1Space (TopCat.disk n) := by
    change T1Space (ULift (Metric.closedBall (0 : E) 1))
    infer_instance
  obtain ⟨R, hRX, hRB⟩ := pushout_punctured_continuous_desc hpush hpboundary
    (ContinuousMap.id X) G (by
      intro a ha
      change φ.hom a = φ.hom (r ⟨TopCat.diskBoundaryInclusion n a, ha⟩)
      apply congrArg φ.hom
      symm
      apply ULift.ext
      apply Subtype.ext
      exact hfixed 1 (liftD ⟨TopCat.diskBoundaryInclusion n a, ha⟩) (by
        change ‖a.down.val‖ = 1
        simpa only [Metric.mem_sphere, dist_zero_right] using a.down.property))
  let Q : C(D × unitInterval, TopCat.disk n) :=
    ⟨fun s ↦ ULift.up ⟨H (s.2, liftD s.1), by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          (hrange s.2 (liftD s.1)).1⟩,
      continuous_uliftUp.comp ((H.continuous.comp
        (continuous_snd.prodMk (hlift.comp continuous_fst))).subtype_mk (fun s ↦ by
          simpa only [Function.comp_apply, Metric.mem_closedBall, dist_zero_right] using
            (hrange s.2 (liftD s.1)).1))⟩
  let Fpath : C(X, C(unitInterval, Y)) :=
    (⟨fun s : X × unitInterval ↦ f.hom s.1,
      f.hom.continuous.comp continuous_fst⟩ : C(X × unitInterval, Y)).curry
  let Gpath : C(D, C(unitInterval, Y)) := (χ.hom.comp Q).curry
  have : Nonempty Y := ⟨f.hom (Classical.choice ‹Nonempty X›)⟩
  have : Nonempty C(unitInterval, Y) := ⟨ContinuousMap.const _ (Classical.choice ‹Nonempty Y›)⟩
  obtain ⟨Kpath, hKX, hKB⟩ := pushout_punctured_continuous_desc hpush hpboundary
    Fpath Gpath (by
      intro a ha
      ext t
      change f.hom (φ.hom a) = χ.hom (Q (⟨TopCat.diskBoundaryInclusion n a, ha⟩, t))
      have hQ : Q (⟨TopCat.diskBoundaryInclusion n a, ha⟩, t) =
          TopCat.diskBoundaryInclusion n a := by
        apply ULift.ext
        apply Subtype.ext
        exact hfixed t (liftD ⟨TopCat.diskBoundaryInclusion n a, ha⟩) (by
          change ‖a.down.val‖ = 1
          simpa only [Metric.mem_sphere, dist_zero_right] using a.down.property)
      rw [hQ]
      exact congrArg (fun m : TopCat.diskBoundary n ⟶ Y ↦ m a) hpush.w)
  let K : C(unitInterval × {y : Y // y ≠ χ.hom p}, Y) :=
    Kpath.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  have hKX' (t : unitInterval) (x : X) (hx : f.hom x ≠ χ.hom p) :
      K (t, ⟨f.hom x, hx⟩) = f.hom x := by
    exact congrArg (fun c : C(unitInterval, Y) ↦ c t) (hKX x)
  have hKB' (t : unitInterval) (b : D) :
      K (t, ⟨χ.hom b.val, b.property⟩) = χ.hom (Q (b, t)) := by
    exact congrArg (fun c : C(unitInterval, Y) ↦ c t) (hKB b)
  refine ⟨R, K, fun x hx ↦ hRX x, ?_, ?_, hKX'⟩
  · intro y
    obtain ⟨s, hs⟩ := (pushout_punctured_sum_isQuotient hpush hpboundary).surjective y
    cases s with
    | inl x =>
      subst y
      exact hKX' 0 x _
    | inr b =>
      subst y
      simp only [Sum.elim_inr]
      rw [hKB']
      apply congrArg χ.hom
      apply ULift.ext
      apply Subtype.ext
      exact hzero (liftD b)
  · intro y
    obtain ⟨s, hs⟩ := (pushout_punctured_sum_isQuotient hpush hpboundary).surjective y
    cases s with
    | inl x =>
      subst y
      simp only [Sum.elim_inl]
      rw [hRX]
      exact hKX' 1 x _
    | inr b =>
      subst y
      simp only [Sum.elim_inr]
      rw [hKB', hRB]
      change χ.hom (Q (b, 1)) = f.hom (φ.hom (r b))
      have hQ : Q (b, 1) = TopCat.diskBoundaryInclusion n (r b) := rfl
      rw [hQ]
      exact (congrArg (fun m : TopCat.diskBoundary n ⟶ Y ↦ m (r b)) hpush.w).symm

/-- Deleting an interior point from an attached cell admits a continuous
retraction to the original space. This is the radial-retraction step of
Hatcher, Algebraic Topology, Proposition 1.26, pp.50–51 (the arbitrary-pole
version is also used in Theorem 4.8, p.349). Radially project the punctured
closed disk onto its sphere, follow the attaching map, and use the identity
on the old space. The radial formula fixes the sphere, so these formulas
agree on the attaching locus and descend through the punctured quotient.
No separation hypothesis on either X or Y is needed. -/
theorem single_cell_punctured_retraction
    {X Y : TopCat.{u}} [Nonempty X] (n : ℕ)
    (φ : TopCat.diskBoundary.{u} n ⟶ X)
    (f : X ⟶ Y) (χ : TopCat.disk.{u} n ⟶ Y)
    (hpush : IsPushout φ (TopCat.diskBoundaryInclusion.{u} n) f χ)
    (p : TopCat.disk.{u} n) (hp : ‖p.down.val‖ < 1) :
    ∃ R : C({y : Y // y ≠ χ.hom p}, X),
      ∀ (x : X) (hx : f.hom x ≠ χ.hom p), R ⟨f.hom x, hx⟩ = x := by
  obtain ⟨R, K, hR, _⟩ := single_cell_punctured_deformation n φ f χ hpush p hp
  exact ⟨R, hR⟩

end HolomorphicAnosov

