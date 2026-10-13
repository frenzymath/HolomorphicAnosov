import HolomorphicAnosov.Analysis.DistributionSmoothFixedSupportFamily
import Mathlib.Data.List.Nodup

/-!
# First coordinate derivatives of fixed-support distribution pairings

Source: Semyon Dyatlov, 18.155 distributions notes (2026), Proposition 6.3, pp.68–69, first
derivative formula (6.9) and its Taylor-remainder proof, with proper-support alternative
specialized to one fixed compact support.
DAG node: `analysis.dbar_helper_fixed_support_first_derivative_sections_g6`.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
A jointly smooth family of complex tests supported in one fixed compact subset of an open
Euclidean spatial domain has smooth distributional pairing, with each ordinary coordinate
derivative represented by a test section whose pairing equals the corresponding derivative of the
pairing.

Source: Dyatlov, 18.155 notes, Proposition 6.3, pp.68–69, first derivative formula (6.9) and its
Taylor-remainder proof, with proper-support alternative specialized to one fixed compact support.

Proof: Apply the fixed-support smooth-family theorem to obtain the smooth sections and its
multi-index derivative identity. For coordinate j specialize the multi-index to one at j and zero
elsewhere. The native filter and count identities for the repetition-free coordinate list show
that its direction list contains exactly the single jth unit vector: filter at j, count its unique
occurrence, and map to the unit vector. Thus the order is one. The first iterated Frechet
derivative is the ordinary derivative on the open parameter domain. Use this identity for the
section and its pairing, obtaining exactly Dyatlov formula (6.9).
-/
theorem fixed_support_first_derivative_sections {m k : ℕ}
    (hm : 0 < m) (hk : 0 < k)
    (U : Opens (EuclideanSpace ℝ (Fin m)))
    (P : Opens (EuclideanSpace ℝ (Fin k)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U)
    (H : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) → ℂ)
    (hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)))
    (hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K) :
    ∃ s : EuclideanSpace ℝ (Fin k) → TestFunction U ℂ ⊤,
      (∀ p ∈ P, ∀ y, s p y = H p y) ∧
      ContDiffOn ℝ ∞ (fun p ↦ T (s p)) (P : Set _) ∧
      ∀ (j : Fin k) p, p ∈ P → ∃ θ : TestFunction U ℂ ⊤,
        (∀ y, θ y = (fderiv ℝ (fun q ↦ H q y) p) (EuclideanSpace.single j 1)) ∧
        (fderiv ℝ (fun q ↦ T (s q)) p) (EuclideanSpace.single j 1) = T θ := by
  classical
  obtain ⟨s, hs, hsm, hd, _⟩ := distribution_smooth_fixed_support_family
    hm hk U P T K hK hKU H hH hSupport
  refine ⟨s, hs, hsm, ?_⟩
  intro j p hp
  have h := hd (Pi.single j 1) p hp
  dsimp only at h
  have hdirections : (List.finRange k).flatMap (fun i ↦ List.replicate
      ((Pi.single j (1 : ℕ) : Fin k → ℕ) i) (EuclideanSpace.single i (1 : ℝ))) =
      [EuclideanSpace.single j (1 : ℝ)] := by
    have hfilter : (List.finRange k).filter (· = j) = [j] := by
      rw [List.filter_eq, List.count_eq_one_of_mem (List.nodup_finRange k) (List.mem_finRange j)]
      rfl
    have heq : (List.finRange k).flatMap (fun i ↦ List.replicate
        ((Pi.single j (1 : ℕ) : Fin k → ℕ) i) (EuclideanSpace.single i (1 : ℝ))) =
        ((List.finRange k).filter (· = j)).map (fun i ↦ EuclideanSpace.single i (1 : ℝ)) := by
      rw [← List.filterMap_eq_filter, List.map_filterMap, List.filterMap_eq_flatMap_toList]
      apply List.flatMap_congr
      intro i hi
      by_cases h : i = j <;> simp [Option.guard, h]
    rw [heq, hfilter]
    rfl
  rw [hdirections] at h
  obtain ⟨θ, hθ, hpair⟩ := h
  refine ⟨θ, ?_, ?_⟩
  · intro y
    simpa only [List.length_singleton, iteratedFDerivWithin_one_apply (P.isOpen.uniqueDiffWithinAt (𝕜 := ℝ) hp),
      fderivWithin_of_isOpen P.isOpen hp, List.get_eq_getElem,
      Fin.val_zero, List.getElem_cons_zero] using hθ y
  · simpa only [List.length_singleton, iteratedFDerivWithin_one_apply (P.isOpen.uniqueDiffWithinAt (𝕜 := ℝ) hp),
      fderivWithin_of_isOpen P.isOpen hp, List.get_eq_getElem,
      Fin.val_zero, List.getElem_cons_zero] using hpair


end HolomorphicAnosov.Analysis.Distribution
