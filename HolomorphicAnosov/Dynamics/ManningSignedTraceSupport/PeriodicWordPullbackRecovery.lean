import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.MatchedBlocksPullbackConstant
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SupportedAlphabetPullback
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimeNatCast
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimeSucc
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWord

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set CodingAdapter
open scoped Classical
noncomputable section

/-- Each symbol of a supported periodic tuple word is recovered from its time-zero fibre blocks. (Manning, pp. 218–219) -/
theorem periodicWord_pullback_recovery {A X : Type*} [Fintype A]
    {N r m : ℕ} (R : Fin N → Set X) (T : Matrix (Fin N) (Fin N) ℤ)
    (c : Composition r) (hm : 0 < m) (l : ℤ → A → Fin N)
    (hl : ∀ j, Function.Injective (l j))
    (hforced : ∀ j a b, T (l j a) (l (j + 1) b) = 1 → a = b)
    (x : Fin m → X)
    (hlabel : ∀ j i, x (integerPeriodicTime hm j) ∈ R i → ∃ a, l j a = i)
    (w : PeriodicWord R T c hm)
    (hw : ∀ t k i, i ∈ (w.val t).val k → x t ∈ R i)
    (t : Fin m) (k : Fin c.length) :
    (Finset.univ.filter (fun a ↦ l 0 a ∈ (w.val ⟨0, hm⟩).val k)).image (l t.val) =
      (w.val t).val k := by
  classical
  let S : ℤ → Finset (Fin N) := fun j ↦ (w.val (integerPeriodicTime hm j)).val k
  have hconst := matched_blocks_pullback_constant T l hforced S
    (fun j i hi ↦ hlabel j i (hw _ k i hi))
    (fun j ↦ by simpa only [S, integerPeriodicTime_succ] using
      w.property (integerPeriodicTime hm j) k) (t.val : ℤ)
  have hzero : integerPeriodicTime hm 0 = ⟨0, hm⟩ := by
    simpa using integerPeriodicTime_natCast hm ⟨0, hm⟩
  simp only [S, integerPeriodicTime_natCast, hzero] at hconst
  rw [← hconst]
  have hpull := supported_alphabet_pullback R c (l t.val) (hl _) (x t)
    (fun i hi ↦ hlabel t.val i (by simpa only [integerPeriodicTime_natCast] using hi))
    (w.val t) (hw t)
  exact hpull.2.2.2 k

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
