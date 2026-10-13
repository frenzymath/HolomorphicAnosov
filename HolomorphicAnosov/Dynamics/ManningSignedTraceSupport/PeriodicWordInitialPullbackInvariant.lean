import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.MatchedBlocksInvariantPullback
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimeNatCast
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimeSucc
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimePeriod
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWord

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set CodingAdapter
open scoped Classical
noncomputable section

/-- For a supported periodic tuple word, each time-zero block pulls back to a set invariant under the fibre return permutation. (Manning, pp. 218–219) -/
theorem periodicWord_initial_pullback_invariant {A X : Type*} [Fintype A]
    {N r m : ℕ} (R : Fin N → Set X) (T : Matrix (Fin N) (Fin N) ℤ)
    (c : Composition r) (hm : 0 < m) (l : ℤ → A → Fin N)
    (hforced : ∀ j a b, T (l j a) (l (j + 1) b) = 1 → a = b)
    (x : Fin m → X)
    (hlabel : ∀ j i, x (integerPeriodicTime hm j) ∈ R i → ∃ a, l j a = i)
    (g : A ≃ A) (hreturn : ∀ a, l (m : ℤ) a = l 0 (g a))
    (w : PeriodicWord R T c hm)
    (hw : ∀ t k i, i ∈ (w.val t).val k → x t ∈ R i) (k : Fin c.length) :
    (Finset.univ.filter (fun a ↦ l 0 a ∈ (w.val ⟨0, hm⟩).val k)).image g =
      Finset.univ.filter (fun a ↦ l 0 a ∈ (w.val ⟨0, hm⟩).val k) := by
  classical
  let S : ℤ → Finset (Fin N) := fun j ↦ (w.val (integerPeriodicTime hm j)).val k
  have hzero : integerPeriodicTime hm 0 = ⟨0, hm⟩ := by
    simpa using integerPeriodicTime_natCast hm ⟨0, hm⟩
  have hperiod : S (m : ℤ) = S 0 := by
    dsimp [S]
    rw [show (m : ℤ) = 0 + m by omega, integerPeriodicTime_period]
  have h := matched_blocks_invariant_pullback T l hforced S
    (fun j i hi ↦ hlabel j i (hw _ k i hi))
    (fun j ↦ by
      simpa only [S, integerPeriodicTime_succ] using
        w.property (integerPeriodicTime hm j) k)
    g (m : ℤ) hperiod hreturn
  simpa only [S, hzero] using h

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
