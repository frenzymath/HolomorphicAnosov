import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData
import HolomorphicAnosov.Dynamics.Bowen.BracketCovarianceOfGuards

/-!
# Closed-overlap ingredients for Bowen Markov rectangles

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970),
Fact 1 pp.726–727, Lemma 11(a) pp.730–731 and Lemma 25 pp.739–740.
All distances, orbit plaques, bracket guards and compact cells are unchanged.
-/

namespace HolomorphicAnosov.BowenBasicSetCoding
open Set
variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Bowen Lemma25 stable inclusion at a closed overlap. The transported witness
r=[w,z] is in the source witness's stable slice. Its known image lies in T; covariance
on the guarded pair (x,r) then places Fz in T without presuming Fz was already there. -/
theorem stable_inclusion_at_closed_overlap (F : X ≃ₜ X) (γ lam : ℝ)
    (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (E T : Set X) (hEc : IsCompact E) (hTc : IsCompact T)
    (hEd : Metric.diam E ≤ H.closeRadius) (hTd : Metric.diam T ≤ H.closeRadius)
    (hEb : ∀ p ∈ E, ∀ q ∈ E, H.bracket p q ∈ E)
    (hTb : ∀ p ∈ T, ∀ q ∈ T, H.bracket p q ∈ T)
    (hzero : ∀ p ∈ E, ∀ q ∈ E, F p ∈ T → F q ∈ T →
      dist (F (H.bracket p q)) (F q) ≤ γ)
    (w : X) (hw : w ∈ E) (_hfw : F w ∈ T)
    (hincl : F '' (E ∩ Dynamics.relativeClosedStablePlaque F γ w) ⊆
      T ∩ Dynamics.relativeClosedStablePlaque F γ (F w))
    (x : X) (hx : x ∈ E) (hfx : F x ∈ T) :
    F '' (E ∩ Dynamics.relativeClosedStablePlaque F γ x) ⊆
      T ∩ Dynamics.relativeClosedStablePlaque F γ (F x) := by
  rintro t ⟨z, hz, rfl⟩
  let r := H.bracket w z
  have hwz : dist w z ≤ H.closeRadius :=
    (Metric.dist_le_diam_of_mem hEc.isBounded hw hz.1).trans hEd
  have hrE : r ∈ E := hEb w hw z hz.1
  have hrplaques := H.bracket_mem w z hwz
  have hfrT : F r ∈ T := (hincl ⟨r, ⟨hrE, hrplaques.1⟩, rfl⟩).1
  have hxr : dist x r ≤ H.closeRadius :=
    (Metric.dist_le_diam_of_mem hEc.isBounded hx hrE).trans hEd
  have hzr : z = H.bracket x r := by
    apply H.bracket_unique x r z hxr
    exact ⟨hz.2, fun n ↦ by simpa only [dist_comm] using hrplaques.2 n⟩
  have hcov := Dynamics.Bowen.bracket_covariance_of_guards F γ lam H hxr
    ((Metric.dist_le_diam_of_mem hTc.isBounded hfx hfrT).trans hTd)
    (hzero x hx r hrE hfx hfrT)
  constructor
  · rw [hzr, hcov]
    exact hTb (F x) hfx (F r) hfrT
  · intro n
    simpa only [Function.iterate_succ_apply] using hz.2 (n + 1)



end HolomorphicAnosov.BowenBasicSetCoding
