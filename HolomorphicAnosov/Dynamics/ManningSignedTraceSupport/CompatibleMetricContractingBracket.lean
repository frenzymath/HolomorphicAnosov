import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.FactBracketOriginalMetricMembership
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.OriginalPlaqueIntersectionUnique

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped Classical
noncomputable section

/-- Restrict a continuous contracting bracket to a closed close-pair domain in a
compatible original metric. Compactness supplies a uniform comparison radius.
The existing contraction transfer puts the same bracket in the desired original
closed plaques; original expansivity gives uniqueness. No new bracket values are
chosen on the close-pair domain, and neither dynamics nor topology is changed. -/
theorem compatible_metric_contracting_bracket {X : Type*}
    [new : MetricSpace X] [CompactSpace X]
    (F : @Homeomorph X X new.toUniformSpace.toTopologicalSpace
      new.toUniformSpace.toTopologicalSpace)
    {ε₀ κ : ℝ} (hε₀ : 0 < ε₀) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (B : {p : X × X // new.dist p.1 p.2 ≤ ε₀} → X) (hB : Continuous B)
    (hdiag : ∀ x : X, B ⟨(x, x), by simpa using hε₀.le⟩ = x)
    (hs : ∀ p, ∀ n : ℕ,
      new.dist ((F ^ (n : ℤ)) (B p)) ((F ^ (n : ℤ)) p.val.1) ≤
        κ ^ n * new.dist (B p) p.val.1)
    (hu : ∀ p, ∀ n : ℕ,
      new.dist ((F ^ (-(n : ℤ))) (B p)) ((F ^ (-(n : ℤ))) p.val.2) ≤
        κ ^ n * new.dist (B p) p.val.2)
    (old : MetricSpace X)
    (ht : old.toUniformSpace.toTopologicalSpace = new.toUniformSpace.toTopologicalSpace)
    {e b : ℝ} (hb : 0 < b) (hbe : 2 * b ≤ e)
    (hexp : ∀ x y : X,
      (∀ j : ℤ, old.dist ((F ^ j) x) ((F ^ j) y) ≤ e) → x = y) :
    letI : MetricSpace X := new
    ∃ ε > 0, ∃ C : {p : X × X // old.dist p.1 p.2 ≤ ε} → X,
      Continuous C ∧
      (∀ p, (∀ n : ℕ, old.dist ((F ^ (n : ℤ)) (C p)) ((F ^ (n : ℤ)) p.val.1) ≤ b) ∧
        (∀ n : ℕ, old.dist ((F ^ (-(n : ℤ))) (C p)) ((F ^ (-(n : ℤ))) p.val.2) ≤ b)) ∧
      (∀ p z, (∀ n : ℕ, old.dist ((F ^ (n : ℤ)) z) ((F ^ (n : ℤ)) p.val.1) ≤ b) →
        (∀ n : ℕ, old.dist ((F ^ (-(n : ℤ))) z) ((F ^ (-(n : ℤ))) p.val.2) ≤ b) →
        z = C p) := by
  let : MetricSpace X := new
  obtain ⟨t, htpos, hmem⟩ := fact_bracket_original_metric_membership
    F hε₀.le hκ0 hκ1 B hB hdiag hs hu old ht hb
  obtain ⟨r, hr, hmod⟩ := compatible_metric_modulus old ht
    (min ε₀ t) (lt_min hε₀ htpos)
  let ε := r / 2
  have hε : 0 < ε := half_pos hr
  have hsmall : ∀ p : {p : X × X // old.dist p.1 p.2 ≤ ε},
      new.dist p.val.1 p.val.2 < min ε₀ t := by
    intro p
    exact hmod _ _ (p.property.trans_lt (half_lt_self hr))
  let embed : {p : X × X // old.dist p.1 p.2 ≤ ε} →
      {p : X × X // new.dist p.1 p.2 ≤ ε₀} :=
    fun p ↦ ⟨p.val, ((hsmall p).trans_le (min_le_left _ _)).le⟩
  let C := B ∘ embed
  have hc : Continuous C := hB.comp (continuous_subtype_val.subtype_mk _)
  have hCmem : ∀ p, (∀ n : ℕ,
      old.dist ((F ^ (n : ℤ)) (C p)) ((F ^ (n : ℤ)) p.val.1) ≤ b) ∧
      (∀ n : ℕ, old.dist ((F ^ (-(n : ℤ))) (C p)) ((F ^ (-(n : ℤ))) p.val.2) ≤ b) := by
    intro p
    exact hmem (embed p) ((hsmall p).trans_le (min_le_right _ _))
  refine ⟨ε, hε, C, hc, hCmem, ?_⟩
  intro p z hzS hzU
  have hcS := (hCmem p).1
  have hcU := (hCmem p).2
  apply @original_plaque_intersection_unique X (old.replaceTopology ht.symm) F e b hbe hexp
    p.val.1 p.val.2 (C p) z
  · constructor
    · intro n
      simpa only [← zpow_natCast] using hcS n
    · intro n
      exact hcU n
  · constructor
    · intro n
      simpa only [← zpow_natCast] using hzS n
    · intro n
      exact hzU n


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
