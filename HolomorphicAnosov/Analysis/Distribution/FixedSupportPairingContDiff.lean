import HolomorphicAnosov.Analysis.Distribution.FixedSupportPairingFirstDerivative
import HolomorphicAnosov.Analysis.Distribution.FixedSupportParameterDerivativeLinear
import HolomorphicAnosov.Analysis.Distribution.FixedSupportSeminormUniformModulus
import HolomorphicAnosov.Analysis.Distribution.FixedSupportLocalParameterTaylorRemainder
import HolomorphicAnosov.Analysis.Distribution.FixedSupportFiniteOrderBound
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smoothness of fixed-support distribution pairings

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026), Proposition 6.3,
pp. 68–69, equations (6.7)–(6.9). The finite-order distribution bound and a
common modulus for spatial jets give continuity on a compact parameter core.
The proved first-derivative formula then gives smoothness by induction.
DAG node: `analysis.distribution_fixed_support_pairing_contDiff_g10`.
-/

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology _root_.Topology
namespace HolomorphicAnosov.Analysis

/-- Smoothness of a distribution pairing with a jointly smooth family supported in one
compact set. Compact uniform continuity controls the finitely many spatial seminorms
needed by the distribution. Then induction applies the first-derivative representation
to the smooth supported family obtained by differentiation in each fixed direction. -/
theorem distribution_pairing_contDiff_on_fixed_support
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
    ContDiffOn ℝ ∞ (fun p ↦ T (sections p)) (P : Set _) := by
  classical
  apply contDiffOn_infty.mpr
  intro n
  induction n generalizing H sections with
  | zero =>
    apply contDiffOn_zero.mpr
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
    intro p hp
    obtain ⟨ρ,hρ,hρP,_⟩ := local_parameter_taylor_remainder (P : Set _) (U : Set _)
      P.isOpen H hH K hK hKU p hp
    let Q : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin k)) :=
      ⟨Metric.closedBall p ρ, isCompact_closedBall p ρ⟩
    let Φ : Q → ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ ⟨K,hK⟩ :=
      fun q ↦ ⟨sections q, (sections q).contDiff, by
        intro y hy
        exact (hSections q (hρP q.property) y).trans
          (image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hSupport q (hρP q.property) h)))⟩
    have hjet (i : ℕ) : UniformContinuous
        (fun z : Q × (⟨K,hK⟩ : TopologicalSpace.Compacts _) ↦
          iteratedFDeriv ℝ i (Φ z.1) z.2.val) := by
      have hc : Continuous (fun z : Q × (⟨K,hK⟩ : TopologicalSpace.Compacts _) ↦
          D i (z.1.val,z.2.val)) :=
        (hD i).continuousOn.comp_continuous
          (continuous_subtype_val.prodMap continuous_subtype_val)
          (fun z ↦ ⟨hρP z.1.property,hKU z.2.property⟩)
      have heq : (fun z : Q × (⟨K,hK⟩ : TopologicalSpace.Compacts _) ↦
          iteratedFDeriv ℝ i (Φ z.1) z.2.val) =
          (fun z : Q × (⟨K,hK⟩ : TopologicalSpace.Compacts _) ↦ D i (z.1.val,z.2.val)) := by
        funext z
        change iteratedFDeriv ℝ i (sections z.1.val) z.2.val = _
        have hs : (sections z.1.val : EuclideanSpace ℝ (Fin m) → ℂ) = H z.1.val :=
          funext (hSections z.1.val (hρP z.1.property))
        rw [hs]
        exact (iteratedFDerivWithin_of_isOpen i U.isOpen (hKU z.2.property)).symm
      rw [heq]
      exact CompactSpace.uniformContinuous_of_continuous hc
    obtain ⟨s,C,hC,hbound⟩ := distribution_fixed_support_finite_order_bound U T K hK hKU
    have huc : UniformContinuous (fun q : Q ↦ T (sections q)) := by
      apply Metric.uniformContinuous_iff.mpr
      intro ε hε
      have hCp : (0 : ℝ) < C := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC)
      obtain ⟨δ,hδ,hδb⟩ := fixed_support_seminorm_uniform_modulus Φ s
        (fun i _ ↦ hjet i) (ε / (2*C)) (div_pos hε (mul_pos (by norm_num) hCp))
      refine ⟨δ,hδ,?_⟩
      intro q r hqr
      have hv : T (TestFunction.ofSupportedIn hKU (Φ q - Φ r)) =
          T (sections q) - T (sections r) := by
        change T ((TestFunction.ofSupportedInCLM ℂ hKU) (Φ q - Φ r)) = _
        rw [map_sub,map_sub]
        rfl
      rw [dist_eq_norm,← hv]
      have hb := hbound (Φ q - Φ r)
      have hm := hδb q r hqr
      change ‖T (TestFunction.ofSupportedIn hKU (Φ q - Φ r))‖ ≤
        (C : ℝ) * s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ ⟨K,hK⟩) (Φ q - Φ r) at hb
      have hc : (C : ℝ) * (ε/(2*C)) = ε/2 := by field_simp
      calc
        _ ≤ (C : ℝ) * s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ ⟨K,hK⟩)
            (Φ q - Φ r) := hb
        _ ≤ (C : ℝ) * (ε/(2*C)) := mul_le_mul_of_nonneg_left hm hCp.le
        _ = ε/2 := hc
        _ < ε := half_lt_self hε
    have hq : ContinuousOn (fun q ↦ T (sections q)) (Q : Set _) :=
      continuousOn_iff_continuous_domRestrict.mpr huc.continuous
    exact (hq.continuousAt (Metric.closedBall_mem_nhds p hρ)).continuousWithinAt
  | succ n ih =>
    have hfirst := distribution_pairing_fixed_support_first_derivative
      hm hk U P hP T K hK hKU H hH hSupport sections hSections
    have hdiff : DifferentiableOn ℝ (fun q ↦ T (sections q)) (P : Set _) := by
      intro p hp
      obtain ⟨L, hd, _⟩ := hfirst p hp
      exact hd.differentiableWithinAt
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiffOn_succ_of_fderiv_apply hdiff (by simp)
    intro v
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
    have hSn := ih G hG hGs S hS
    apply hSn.congr
    intro p hp
    obtain ⟨L, hd, hLv⟩ := hfirst p hp
    obtain ⟨f, hf, hLf⟩ := hLv v
    have hfS : f = S p := by
      ext y
      exact (hf y).trans (hS p hp y).symm
    rw [hd.fderivWithin (P.isOpen.uniqueDiffWithinAt (𝕜 := ℝ) hp), hLf, hfS]

end HolomorphicAnosov.Analysis

