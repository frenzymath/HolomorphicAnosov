import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.BlockMatchingTargetsEq
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicPhysicalPoints

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set
open scoped Classical
noncomputable section

/-- A periodic tuple word supported on one physical orbit is determined by its initial blocks when each orbit label has a unique legal successor. (Manning, pp. 217–219) -/
theorem periodicWord_eq_of_zero {X : Type*} (F : X → X) {N r m : ℕ}
    (R : Fin N → Set X) (T : Matrix (Fin N) (Fin N) ℤ) (c : Composition r)
    (hm : 0 < m) {x : X}
    (hunique : ∀ n : ℕ, ∀ i j k : Fin N,
      (F^[n]) x ∈ R i → (F^[n + 1]) x ∈ R j → (F^[n + 1]) x ∈ R k →
      T i j = 1 → T i k = 1 → j = k)
    {w v : PeriodicWord R T c hm}
    (hw : x ∈ periodicPhysicalPoints R T c F hm w)
    (hv : x ∈ periodicPhysicalPoints R T c F hm v)
    (hzero : w.val ⟨0, hm⟩ = v.val ⟨0, hm⟩) : w = v := by
  have hall : ∀ n (hn : n < m), w.val ⟨n, hn⟩ = v.val ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero => intro hn; exact hzero
    | succ n ih =>
      intro hn
      have hn' : n < m := by omega
      have heq := ih hn'
      have hnext : nextTime hm ⟨n, hn'⟩ = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hn
      apply Subtype.ext
      funext k
      apply blockMatching_targets_eq T
        (by simpa only [hnext] using w.property ⟨n, hn'⟩ k)
        (by simpa only [hnext, heq] using v.property ⟨n, hn'⟩ k)
      intro i hi j hj l hl hij hil
      exact hunique n i j l (hw.2 ⟨n, hn'⟩ k i hi)
        (hw.2 ⟨n + 1, hn⟩ k j hj) (hv.2 ⟨n + 1, hn⟩ k l hl) hij hil
  apply Subtype.ext
  funext t
  exact hall t.val t.isLt

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
