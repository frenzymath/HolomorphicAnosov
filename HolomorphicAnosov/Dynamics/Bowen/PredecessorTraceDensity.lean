import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Density of unique legal predecessors in a regular-closed slice

Bowen, Markov Partitions and Minimal Sets for Axiom A Diffeomorphisms (1970),
Lemma 2 pp.908–909 and Lemma 6(b) p.911. This agent-written finite-label
interface combines closedness of the actual collision trace, local transport
into closed frontiers, and the countable Baire argument on a regular-closed
slice. It does not assert the geometric local frontier transport premise.
-/

namespace HolomorphicAnosov.Dynamics.Bowen
open Set

/-- All-time uniqueness of legal predecessor labels is dense in a
regular-closed slice, provided each collision trace is locally transported
by a continuous open map into a closed frontier. The chart and target may
depend on the time and point; no global chart or uniform collar is assumed.
The slice and label family may be empty. -/
theorem predecessorTraceDensity
    {P X : Type*} [TopologicalSpace P] [BaireSpace P] [TopologicalSpace X]
    {N : ℕ} (F : X ≃ₜ X) (a : P → X) (ha : Continuous a)
    (R : Fin N → Set X) (hR : ∀ i, IsClosed (R i))
    (E : Fin N → Fin N → Prop)
    (K : Set P) (hK : K = closure (interior K))
    (hloc : ∀ (n : ℤ) (z : P),
      (∃ i k j : Fin N, i ≠ k ∧ E i j ∧ E k j ∧
        (F ^ n) (a z) ∈ R i ∧ (F ^ n) (a z) ∈ R k ∧
        F ((F ^ n) (a z)) ∈ R j) →
      ∃ (O : Set P), IsOpen O ∧ z ∈ O ∧
        ∃ (Y : Type*) (_ : TopologicalSpace Y) (f : O → Y),
          Continuous f ∧ IsOpenMap f ∧ ∃ C : Set Y, IsClosed C ∧
          ∀ w : O,
            (∃ i k j : Fin N, i ≠ k ∧ E i j ∧ E k j ∧
              (F ^ n) (a w.val) ∈ R i ∧ (F ^ n) (a w.val) ∈ R k ∧
              F ((F ^ n) (a w.val)) ∈ R j) → f w ∈ frontier C) :
    closure {z : P | z ∈ interior K ∧ ∀ n : ℤ, ∀ j : Fin N,
      F ((F ^ n) (a z)) ∈ R j →
        {i : Fin N | (F ^ n) (a z) ∈ R i ∧ E i j}.Subsingleton} = K := by
  classical
  let B : ℤ → Set P := fun n ↦ {z | ∃ i k j : Fin N,
    i ≠ k ∧ E i j ∧ E k j ∧ (F ^ n) (a z) ∈ R i ∧
      (F ^ n) (a z) ∈ R k ∧ F ((F ^ n) (a z)) ∈ R j}
  have hB : ∀ n, IsClosed (B n) := by
    intro n
    dsimp only [B]
    simp only [ofPred_exists]
    apply isClosed_iUnion_of_finite
    intro i
    apply isClosed_iUnion_of_finite
    intro k
    apply isClosed_iUnion_of_finite
    intro j
    have hn : Continuous (fun z ↦ (F ^ n) (a z)) := (F ^ n).continuous.comp ha
    exact isClosed_const.inter (isClosed_const.inter (isClosed_const.inter
      ((hR i).preimage hn |>.inter ((hR k).preimage hn |>.inter
        ((hR j).preimage (F.continuous.comp hn))))))
  have hND : ∀ n, IsNowhereDense (B n) := by
    intro n
    apply (hB n).isNowhereDense_iff.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨O, hO, hzO, Y, tY, f, hf, hopen, C, hC, hbad⟩ :=
      hloc n z (show z ∈ B n from interior_subset hz)
    let : TopologicalSpace Y := tY
    let V : Set O := Subtype.val ⁻¹' interior (B n)
    have hV : IsOpen V := isOpen_interior.preimage continuous_subtype_val
    have hVne : V.Nonempty := ⟨⟨z, hzO⟩, hz⟩
    have hsub : f '' V ⊆ frontier C := by
      rintro _ ⟨w, hw, rfl⟩
      exact hbad w (show w.val ∈ B n from interior_subset hw)
    have hempty := (hopen V hV).subset_interior_iff.mpr hsub
    rw [interior_frontier hC] at hempty
    exact (hVne.image f).ne_empty (subset_empty_iff.mp hempty)
  have hdense : Dense (⋂ n : ℤ, (B n)ᶜ) := dense_iInter_of_isOpen
    (fun n ↦ (hB n).isOpen_compl)
    (fun n ↦ (isClosed_isNowhereDense_iff_compl.mp ⟨hB n, hND n⟩).2)
  apply Subset.antisymm
  · apply closure_minimal (fun z hz ↦ interior_subset hz.1)
    rw [hK]
    exact isClosed_closure
  · intro z hz
    apply mem_closure_iff.mpr
    intro V hV hzV
    have hn : (V ∩ interior K).Nonempty := mem_closure_iff.mp (hK ▸ hz) V hV hzV
    obtain ⟨w, hw, hgood⟩ := hdense.inter_open_nonempty (V ∩ interior K)
      (hV.inter isOpen_interior) hn
    refine ⟨w, hw.1, hw.2, ?_⟩
    intro n j hj i hi k hk
    by_contra hne
    exact mem_iInter.mp hgood n ⟨i, k, j, hne, hi.2, hk.2, hi.1, hk.1, hj⟩

end HolomorphicAnosov.Dynamics.Bowen

