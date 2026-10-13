import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Parameter derivatives of fixed-support test families

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026),
Proposition 6.3, pp. 68–69, the differentiated tests in formula (6.9).
-/

noncomputable section
open Set
open scoped ContDiff
namespace HolomorphicAnosov.Analysis

/-- Every iterated parameter derivative of a jointly smooth fixed-support family is a test
function supported in the original compact set.

Source: Dyatlov Proposition 6.3, pp. 68–69. The parameter derivative fields are jointly
smooth, by induction using the derivative of a smooth function with parameters and the
continuous linear currying map. Evaluation on the prescribed tuple of directions is a
continuous linear map. Outside the fixed compact support, the entire parameter function
vanishes on the parameter domain, so all its within derivatives vanish there. The open
cover by the spatial domain and the complement of the compact support gives the smooth
zero extension. Compactness then packages it as a test. Order zero and empty supports
are included; the parameter point is required to lie in the open parameter domain. -/
theorem fixed_support_parameter_derivative_test
    {m k : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (P : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)))
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U)
    (H : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) → ℂ)
    (hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)))
    (hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K)
    (n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin k))
    (p : EuclideanSpace ℝ (Fin k)) (hp : p ∈ P) :
    ∃ f : TestFunction U ℂ ⊤,
      (∀ y, f y = iteratedFDerivWithin ℝ n (fun q ↦ H q y) (P : Set _) p v) ∧
      tsupport (f : EuclideanSpace ℝ (Fin m) → ℂ) ⊆ K := by
  let D (i : ℕ) (z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) :=
    iteratedFDerivWithin ℝ i (fun q ↦ H q z.2) (P : Set _) z.1
  have hD (i : ℕ) : ContDiffOn ℝ ∞ (D i) ((P : Set _) ×ˢ (U : Set _)) := by
    induction i with
    | zero =>
      exact ContDiffOn.continuousLinearMap_comp
        (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin k)) ℂ).symm.toContinuousLinearMap
        hH
    | succ i ih =>
      intro z hz
      have hf : ContDiffWithinAt ℝ ∞
          (Function.uncurry (fun z : EuclideanSpace ℝ (Fin k) ×
            EuclideanSpace ℝ (Fin m) ↦ fun q ↦ D i (q, z.2)))
          (((P : Set _) ×ˢ (U : Set _)) ×ˢ (P : Set _)) (z, z.1) := by
        have hg : ContDiff ℝ ∞ (fun w :
            (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) ×
              EuclideanSpace ℝ (Fin k) ↦ (w.2, w.1.2)) :=
          contDiff_snd.prodMk contDiff_fst.snd
        exact (ih.comp hg.contDiffOn (fun w hw ↦ ⟨hw.2, hw.1.2⟩))
          (z, z.1) ⟨hz, hz.1⟩
      have hd := hf.fderivWithin (m := ∞) contDiffWithinAt_fst P.isOpen.uniqueDiffOn
        (by simp) hz (fun w hw ↦ hw.1)
      exact hd.continuousLinearMap_comp
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (i + 1) ↦ EuclideanSpace ℝ (Fin k)) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let F : EuclideanSpace ℝ (Fin m) → ℂ := fun y ↦ D n (p, y) v
  have hFU : ContDiffOn ℝ ∞ F (U : Set _) := by
    apply ContDiffOn.continuousLinearMap_comp (ContinuousMultilinearMap.apply ℝ _ ℂ v)
    exact (hD n).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun y hy ↦ ⟨hp, hy⟩)
  have hFzero : EqOn F 0 Kᶜ := by
    intro y hy
    have heq : EqOn (fun q ↦ H q y) (fun _ ↦ (0 : ℂ)) (P : Set _) := by
      intro q hq
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hSupport q hq h))
    change iteratedFDerivWithin ℝ n (fun q ↦ H q y) (P : Set _) p v = 0
    rw [iteratedFDerivWithin_congr heq hp n]
    simp
  have hFsupp : tsupport F ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (hFzero hyK)
  have hF : ContDiff ℝ ∞ F := by
    apply contDiff_of_contDiffOn_union_of_isOpen hFU
      (contDiffOn_const.congr hFzero) _ U.isOpen hK.isClosed.isOpen_compl
    exact Set.eq_univ_of_forall (fun y ↦ by
      by_cases hy : y ∈ K
      · exact Or.inl (hKU hy)
      · exact Or.inr hy)
  exact ⟨TestFunction.mk F hF (HasCompactSupport.intro hK hFzero)
    (hFsupp.trans hKU), fun _ ↦ rfl, hFsupp⟩

end HolomorphicAnosov.Analysis

