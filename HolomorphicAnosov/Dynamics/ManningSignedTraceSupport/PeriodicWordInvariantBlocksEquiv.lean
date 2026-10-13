import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWord
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.SupportedAlphabetPullback
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimeNatCast
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWordPullbackRecovery
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicWordInitialPullbackInvariant
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.InvariantBlocksPeriodicWord

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
open Set CodingAdapter
open scoped Classical
noncomputable section

/-- Supported periodic tuple words of a fixed composition are equivalent to ordered invariant families of fibre blocks of that composition. (Manning, pp. 218–219) -/
def periodicWordInvariantBlocksEquiv {A X : Type*} [Fintype A]
    {N r m : ℕ} (R : Fin N → Set X) (T : Matrix (Fin N) (Fin N) ℤ)
    (c : Composition r) (hm : 0 < m) (l : ℤ → A → Fin N)
    (hl : ∀ j, Function.Injective (l j))
    (hforced : ∀ j a b, T (l j a) (l (j + 1) b) = 1 → a = b)
    (hedge : ∀ j a, T (l j a) (l (j + 1) a) = 1)
    (x : Fin m → X) (hx : ∀ j a, x (integerPeriodicTime hm j) ∈ R (l j a))
    (hlabel : ∀ j i, x (integerPeriodicTime hm j) ∈ R i → ∃ a, l j a = i)
    (g : A ≃ A) (hreturn : ∀ a, l (m : ℤ) a = l 0 (g a)) :
    {w : PeriodicWord R T c hm // ∀ t k i, i ∈ (w.val t).val k → x t ∈ R i} ≃
    {S : Fin c.length → Finset A // (∀ k, (S k).Nonempty) ∧
      (∀ k, (S k).card = c.blocksFun k) ∧
      (Pairwise fun k j ↦ Disjoint (S k) (S j)) ∧ ∀ k, (S k).image g = S k} := by
  classical
  have hz : integerPeriodicTime hm 0 = ⟨0, hm⟩ := by
    simpa using integerPeriodicTime_natCast hm ⟨0, hm⟩
  let f := fun (w : {w : PeriodicWord R T c hm //
      ∀ t k i, i ∈ (w.val t).val k → x t ∈ R i}) ↦
    (⟨fun k ↦ Finset.univ.filter (fun a ↦ l 0 a ∈ (w.val.val ⟨0, hm⟩).val k), by
      have hp := supported_alphabet_pullback R c (l 0) (hl 0) (x ⟨0, hm⟩)
        (fun i hi ↦ hlabel 0 i (by simpa only [hz] using hi))
        (w.val.val ⟨0, hm⟩) (w.property ⟨0, hm⟩)
      exact ⟨hp.1, hp.2.1, hp.2.2.1,
        fun k ↦ by
          simpa using periodicWord_initial_pullback_invariant R T c hm l hforced x hlabel
            g hreturn w.val w.property k⟩⟩ :
      {S : Fin c.length → Finset A // (∀ k, (S k).Nonempty) ∧
        (∀ k, (S k).card = c.blocksFun k) ∧
        (Pairwise fun k j ↦ Disjoint (S k) (S j)) ∧ ∀ k, (S k).image g = S k})
  let G : Fin m → A ≃ A := fun t ↦ if t.val + 1 < m then Equiv.refl A else g
  have he (t : Fin m) (a : A) :
      T (l t.val a) (l (nextTime hm t).val (G t a)) = 1 := by
    by_cases ht : t.val + 1 < m
    · have hn : (nextTime hm t).val = t.val + 1 := Nat.mod_eq_of_lt ht
      simpa only [G, ite_eq_left ht, Equiv.refl_apply, hn, Nat.cast_add, Nat.cast_one]
        using hedge (t.val : ℤ) a
    · have ht' : t.val + 1 = m := by omega
      have hn : (nextTime hm t).val = 0 := by change (t.val + 1) % m = 0; simp [ht']
      have h := hedge (t.val : ℤ) a
      rw [show (t.val : ℤ) + 1 = (m : ℤ) by exact_mod_cast ht', hreturn] at h
      simpa only [G, ite_eq_right ht, hn, Nat.cast_zero] using h
  let v := fun S : {S : Fin c.length → Finset A // (∀ k, (S k).Nonempty) ∧
      (∀ k, (S k).card = c.blocksFun k) ∧
      (Pairwise fun k j ↦ Disjoint (S k) (S j)) ∧ ∀ k, (S k).image g = S k} ↦
    invariantBlocksPeriodicWord R T c hm (fun t ↦ l t.val) (fun t ↦ hl t.val) x
      (fun t a ↦ by simpa only [integerPeriodicTime_natCast] using hx t.val a) G he
      S.val S.property.1 S.property.2.1 S.property.2.2.1 (by
        intro t k
        dsimp only [G]
        split_ifs
        · simp
        · exact S.property.2.2.2 k)
  refine ⟨f, fun S ↦ ⟨v S, ?_⟩, ?_, ?_⟩
  · intro t k i hi
    change i ∈ (S.val k).image (l t.val) at hi
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    simpa only [integerPeriodicTime_natCast] using hx t.val a
  · intro w
    apply Subtype.ext
    apply Subtype.ext
    funext t
    apply Subtype.ext
    funext k
    exact periodicWord_pullback_recovery R T c hm l hl hforced x hlabel w.val w.property t k
  · intro S
    apply Subtype.ext
    funext k
    change Finset.univ.filter (fun a ↦ l 0 a ∈ (S.val k).image (l 0)) = S.val k
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, (hl 0).eq_iff, exists_eq_right]

end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
