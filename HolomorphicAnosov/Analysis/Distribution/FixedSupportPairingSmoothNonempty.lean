import HolomorphicAnosov.Analysis.Distribution.FixedSupportPairingContDiff
import HolomorphicAnosov.Analysis.Distribution.FixedSupportPairingFirstDerivative
import HolomorphicAnosov.Analysis.Distribution.FixedSupportParameterDerivativeLinear

/-!
# Nonempty-domain smooth fixed-support pairing provider

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026), Proposition 6.3,
pp. 68–69.  This provider isolates the nonempty-parameter-domain part of the
fixed-support parameter pairing theorem.  It has the exact conclusion consumed
by the parent theorem. The higher-order induction is proved here from the
separate, proved first-derivative provider.

Proof route from the source: on a compact parameter ball in `P`, all spatial
and parameter jets of `H` have support in `K`; the finite-order estimate for a
continuous distribution bounds the pairing by finitely many fixed-support
seminorms.  Compact uniform continuity of those jets gives continuity of every
paired jet.  The segment fundamental theorem of calculus gives the Fréchet
derivative of the pairing as the pairing of the corresponding parameter jet.
Induction on the order, followed by the coordinate expansion of iterated
Fréchet derivatives, yields the displayed smoothness and multi-index formula.
The proof below formalizes the smoothness induction and the iterated derivative
formula without an admission. The first-derivative provider and the higher
induction now use only the standard Lean axioms.
-/

noncomputable section
open Set
open scoped ContDiff
namespace HolomorphicAnosov.Analysis

/-- Dyatlov's fixed-support smooth-pairing argument on a nonempty open parameter domain. -/
theorem distribution_pairing_smooth_on_fixed_support_nonempty
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (P : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)))
    (hP : (P : Set (EuclideanSpace ℝ (Fin k))).Nonempty)
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U)
    (H : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) → ℂ)
    (hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)))
    (hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K)
    (sections : EuclideanSpace ℝ (Fin k) → TestFunction U ℂ ⊤)
    (hSections : ∀ p ∈ P, ∀ y, sections p y = H p y) :
    ContDiffOn ℝ ∞ (fun p ↦ T (sections p)) (P : Set _) ∧
    (∀ (α : Fin k → ℕ) (p : EuclideanSpace ℝ (Fin k)), p ∈ P →
      let directions := (List.finRange k).flatMap
        (fun i ↦ List.replicate (α i) (EuclideanSpace.single i (1 : ℝ)))
      ∃ differentiatedSection : TestFunction U ℂ ⊤,
        (∀ y, differentiatedSection y =
          iteratedFDerivWithin ℝ directions.length (fun q ↦ H q y) (P : Set _) p
            directions.get) ∧
        iteratedFDerivWithin ℝ directions.length (fun q ↦ T (sections q))
          (P : Set _) p directions.get = T differentiatedSection) := by
  classical
  refine ⟨distribution_pairing_contDiff_on_fixed_support hm hk U P hP T K hK hKU
    H hH hSupport sections hSections, ?_⟩
  have hformula (n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin k)) :
      ∀ p ∈ P, ∃ f : TestFunction U ℂ ⊤,
        (∀ y, f y = iteratedFDerivWithin ℝ n (fun q ↦ H q y) (P : Set _) p v) ∧
        iteratedFDerivWithin ℝ n (fun q ↦ T (sections q)) (P : Set _) p v = T f := by
    induction n generalizing H sections with
    | zero =>
      intro p hp
      exact ⟨sections p, fun y ↦ by simpa using hSections p hp y, by simp⟩
    | succ n ih =>
      let w := v
      let v := w (Fin.last n)
      let G := fun p y ↦ (fderivWithin ℝ (fun q ↦ H q y) (P : Set _) p) v
      have hA : ContDiffOn ℝ ∞
          (fun z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) ↦
            fderivWithin ℝ (fun q ↦ H q z.2) (P : Set _) z.1)
          ((P : Set _) ×ˢ (U : Set _)) := by
        intro z hz
        have hf : ContDiffWithinAt ℝ ∞
            (Function.uncurry (fun z : EuclideanSpace ℝ (Fin k) ×
              EuclideanSpace ℝ (Fin m) ↦ fun q ↦ H q z.2))
            (((P : Set _) ×ˢ (U : Set _)) ×ˢ (P : Set _)) (z, z.1) := by
          have hg : ContDiff ℝ ∞ (fun w :
              (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) ×
                EuclideanSpace ℝ (Fin k) ↦ (w.2, w.1.2)) :=
            contDiff_snd.prodMk contDiff_fst.snd
          exact (hH.comp hg.contDiffOn (fun w hw ↦ ⟨hw.2, hw.1.2⟩))
            (z, z.1) ⟨hz, hz.1⟩
        exact hf.fderivWithin (m := ∞) contDiffWithinAt_fst P.isOpen.uniqueDiffOn
          (by simp) hz (fun w hw ↦ hw.1)
      have hG : ContDiffOn ℝ ∞ (Function.uncurry G) ((P : Set _) ×ˢ (U : Set _)) :=
        hA.clm_apply contDiffOn_const
      have hex (p) (hp : p ∈ P) : ∃ f : TestFunction U ℂ ⊤,
          (∀ y, f y = G p y) ∧ tsupport (f : EuclideanSpace ℝ (Fin m) → ℂ) ⊆ K := by
        obtain ⟨J, hJ, hJs⟩ := fixed_support_parameter_derivative_linear U P K hK hKU
          H hH hSupport p hp
        exact ⟨J v, hJ v, hJs v⟩
      let S : EuclideanSpace ℝ (Fin k) → TestFunction U ℂ ⊤ :=
        fun p ↦ if hp : p ∈ P then (hex p hp).choose else 0
      have hS (p) (hp : p ∈ P) : ∀ y, S p y = G p y := by
        simpa only [S, dite_eq_left hp] using (hex p hp).choose_spec.1
      have hGs : ∀ p ∈ P, tsupport (G p) ⊆ K := by
        intro p hp
        have heq : (S p : EuclideanSpace ℝ (Fin m) → ℂ) = G p := funext (hS p hp)
        rw [← heq]
        simpa only [S, dite_eq_left hp] using (hex p hp).choose_spec.2
      intro p hp
      obtain ⟨f, hf, heq⟩ := ih G hG hGs S hS (Fin.init w) p hp
      have hscalar := distribution_pairing_contDiff_on_fixed_support
        hm hk U P hP T K hK hKU H hH hSupport sections hSections
      have hpair : EqOn (fun q ↦ T (S q))
          (fun q ↦ (fderivWithin ℝ (fun r ↦ T (sections r)) (P : Set _) q) v)
          (P : Set _) := by
        intro q hq
        obtain ⟨L, hd, hLv⟩ := distribution_pairing_fixed_support_first_derivative
          hm hk U P hP T K hK hKU H hH hSupport sections hSections q hq
        obtain ⟨g, hg, hLg⟩ := hLv v
        have hgS : g = S q := by
          ext y
          exact (hg y).trans (hS q hq y).symm
        change T (S q) = (fderivWithin ℝ (fun r ↦ T (sections r)) (P : Set _) q) v
        rw [hd.fderivWithin (P.isOpen.uniqueDiffWithinAt (𝕜 := ℝ) hq), hLg, hgS]
      refine ⟨f, ?_, ?_⟩
      · intro y
        rw [hf y]
        have hHy : ContDiffOn ℝ ∞ (fun q ↦ H q y) (P : Set _) := by
          by_cases hy : y ∈ U
          · exact hH.comp (contDiff_id.prodMk contDiff_const).contDiffOn
              (fun q hq ↦ ⟨hq, hy⟩)
          · apply contDiffOn_const.congr
            intro q hq
            exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hKU (hSupport q hq h)))
        change iteratedFDerivWithin ℝ n
          (fun q ↦ (fderivWithin ℝ (fun r ↦ H r y) (P : Set _) q) v)
          (P : Set _) p (Fin.init w) = _
        rw [iteratedFDerivWithin_clm_apply_const_apply P.isOpen.uniqueDiffOn
          (hHy.fderivWithin P.isOpen.uniqueDiffOn (m := ∞) (by simp)) (by simp) hp]
        exact (iteratedFDerivWithin_succ_apply_right P.isOpen.uniqueDiffOn hp w).symm
      · rw [← heq, iteratedFDerivWithin_congr hpair hp n]
        rw [iteratedFDerivWithin_clm_apply_const_apply P.isOpen.uniqueDiffOn
          (hscalar.fderivWithin P.isOpen.uniqueDiffOn (m := ∞) (by simp)) (by simp) hp]
        exact iteratedFDerivWithin_succ_apply_right P.isOpen.uniqueDiffOn hp w
  intro α p hp
  exact hformula _ _ p hp

end HolomorphicAnosov.Analysis
