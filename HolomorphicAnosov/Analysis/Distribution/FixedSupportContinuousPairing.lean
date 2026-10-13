import HolomorphicAnosov.Analysis.Distribution.FixedSupportJetContinuity
import HolomorphicAnosov.Analysis.TestFunctionFixedSupport

open Set
open scoped ContDiff

namespace HolomorphicAnosov.Analysis

/-- The continuity assertion in Dyatlov, Proposition 6.3, pp.68–69, equations
(6.7)–(6.8). Joint smoothness makes every spatial jet jointly continuous on the
parameter domain times the compact support. The compact-open exponential law
then gives continuity in each fixed-support seminorm, hence in the fixed-support
test topology. Composing its canonical inclusion with the continuous distribution
gives continuity of the pairing. Representatives outside the parameter domain
do not enter this argument. -/
theorem distribution_pairing_continuous_on_fixed_support
    {m k : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (P : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U)
    (H : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) → ℂ)
    (hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)))
    (hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K)
    (sections : EuclideanSpace ℝ (Fin k) → TestFunction U ℂ ⊤)
    (hSections : ∀ p ∈ P, ∀ y, sections p y = H p y) :
    ContinuousOn (fun p ↦ T (sections p)) (P : Set _) := by
  let D (i : ℕ) (z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) :=
    iteratedFDerivWithin ℝ i (H z.1) (U : Set _) z.2
  have hD (i : ℕ) : ContDiffOn ℝ ∞ (D i) ((P : Set _) ×ˢ (U : Set _)) := by
    induction i with
    | zero =>
      exact ContDiffOn.continuousLinearMap_comp
        (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin m)) ℂ).symm.toContinuousLinearMap hH
    | succ i ih =>
      intro z hz
      have hf : ContDiffWithinAt ℝ ∞
          (Function.uncurry (fun z : EuclideanSpace ℝ (Fin k) ×
            EuclideanSpace ℝ (Fin m) ↦ fun y ↦ D i (z.1, y)))
          (((P : Set _) ×ˢ (U : Set _)) ×ˢ (U : Set _)) (z, z.2) := by
        have hg : ContDiff ℝ ∞ (fun w :
            (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) ×
              EuclideanSpace ℝ (Fin m) ↦ (w.1.1, w.2)) :=
          contDiff_fst.fst.prodMk contDiff_snd
        exact (ih.comp hg.contDiffOn (fun w hw ↦ ⟨hw.1.1, hw.2⟩))
          (z, z.2) ⟨hz, hz.2⟩
      have hd := hf.fderivWithin (m := ∞) contDiffWithinAt_snd U.isOpen.uniqueDiffOn
        (by simp) hz (fun w hw ↦ hw.2)
      exact hd.continuousLinearMap_comp
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (i + 1) ↦ EuclideanSpace ℝ (Fin m)) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let Φ : P → ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ ⟨K, hK⟩ :=
    fun p ↦ ⟨sections p, (sections p).contDiff, by
      intro y hy
      have heq : sections p y = H p y := hSections p p.property y
      exact heq.trans (image_eq_zero_of_notMem_tsupport
        (fun h ↦ hy (hSupport p p.property h)))⟩
  have hΦ : Continuous Φ := by
    apply fixed_support_family_continuous_of_jets
    intro n
    have hc : Continuous (fun z : P × (⟨K, hK⟩ : TopologicalSpace.Compacts _) ↦
        D n (z.1.val, z.2.val)) :=
      (hD n).continuousOn.comp_continuous
        (continuous_subtype_val.prodMap continuous_subtype_val)
        (fun z ↦ ⟨z.1.property, hKU z.2.property⟩)
    convert hc using 1
    funext z
    change iteratedFDeriv ℝ n (sections z.1.val) z.2.val = _
    have heq : (sections z.1.val : EuclideanSpace ℝ (Fin m) → ℂ) = H z.1.val :=
      funext (hSections z.1.val z.1.property)
    rw [heq]
    change iteratedFDeriv ℝ n (H z.1.val) z.2.val =
      iteratedFDerivWithin ℝ n (H z.1.val) (U : Set _) z.2.val
    exact (iteratedFDerivWithin_of_isOpen n U.isOpen (hKU z.2.property)).symm
  have hc := T.continuous.comp ((TestFunction.ofSupportedInCLM ℂ hKU).continuous.comp hΦ)
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hc using 1
  funext p
  congr 1

end HolomorphicAnosov.Analysis

