import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricModulus
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.StablePlaqueSmallStartAllSmall

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Agent-expanded comparison of the SAME compact dynamical plaques in two compatible metrics. Choose a forward identity modulus into the new radius c/2 and use half its input radius as b. Choose the reverse identity modulus into b, then apply the strict-buffer lemma to F and F inverse; the minimum initial radius works for both. Old closed b-orbit bounds imply new closed c-orbit bounds without an initial-closeness assumption. The reverse implication uses the small-pair guard and all-time strict buffer. This is not equality of arbitrary same-radius plaques, nor a choice of different partition rectangles. The producer must still return its retained rectangles small enough for the resulting initial radius. -/
theorem compatible_both_plaques_on_small_pairs {X : Type*}
    [new : MetricSpace X] [CompactSpace X] (old : MetricSpace X)
    (ht : old.toUniformSpace.toTopologicalSpace = new.toUniformSpace.toTopologicalSpace)
    (F : @Homeomorph X X new.toUniformSpace.toTopologicalSpace new.toUniformSpace.toTopologicalSpace)
    {c : ℝ} (hpos : 0 < c)
    (hexp : ∀ x y : X, (∀ j : ℤ, new.dist ((F ^ j) x) ((F ^ j) y) ≤ c) → x = y) :
    ∃ b > 0, ∃ a > 0, ∀ x y : X, new.dist x y < a →
      (∀ G ∈ ({F, F⁻¹} : Set (@Homeomorph X X new.toUniformSpace.toTopologicalSpace
        new.toUniformSpace.toTopologicalSpace)),
        (∀ k : ℕ, old.dist ((G ^ (k : ℤ)) x) ((G ^ (k : ℤ)) y) ≤ b) ↔
        ∀ k : ℕ, new.dist ((G ^ (k : ℤ)) x) ((G ^ (k : ℤ)) y) ≤ c) := by
  let : MetricSpace X := new
  have holdcomp : @CompactSpace X old.toUniformSpace.toTopologicalSpace := ht.symm ▸
    (inferInstance : @CompactSpace X new.toUniformSpace.toTopologicalSpace)
  obtain ⟨d, hd, hforward⟩ := @compatible_metric_modulus X new inferInstance old ht
    (c / 2) (half_pos hpos)
  let b := d / 2
  have hb : 0 < b := half_pos hd
  obtain ⟨r, hr, hreverse⟩ := @compatible_metric_modulus X old holdcomp new ht.symm b hb
  obtain ⟨as_, has, hs⟩ := @stable_plaque_small_start_all_small X new inferInstance
    F c hexp r hr
  have hexpi : ∀ x y : X,
      (∀ j : ℤ, new.dist ((F⁻¹ ^ j) x) ((F⁻¹ ^ j) y) ≤ c) → x = y := by
    intro x y h
    apply hexp x y
    intro j
    have hpow : F⁻¹ ^ (-j) = F ^ j := by
      simp
    simpa only [hpow] using h (-j)
  obtain ⟨au, hau, hu⟩ := @stable_plaque_small_start_all_small X new inferInstance
    F⁻¹ c hexpi r hr
  refine ⟨b, hb, min as_ au, lt_min has hau, ?_⟩
  intro x y hxy G hG
  constructor
  · intro h k
    exact ((hforward _ _ ((h k).trans_lt (half_lt_self hd))).le).trans
      (half_le_self hpos.le)
  · intro h k
    have hsmall : new.dist ((G ^ (k : ℤ)) x) ((G ^ (k : ℤ)) y) < r := by
      rcases Set.mem_insert_iff.mp hG with hG | hG
      · subst G; exact hs x y (hxy.trans_le (min_le_left _ _)) h k
      · have hG' : G = F⁻¹ := Set.mem_singleton_iff.mp hG
        subst G; exact hu x y (hxy.trans_le (min_le_right _ _)) h k
    exact (hreverse _ _ hsmall).le


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
