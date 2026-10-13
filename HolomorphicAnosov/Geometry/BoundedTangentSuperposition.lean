import HolomorphicAnosov.Analysis.BoundedDependentSuperposition
import HolomorphicAnosov.Geometry.UniformExponentialLift.base
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.FiniteCompactPairedTangentCores
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.FrameCoordinateMetricBound
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.CompactZeroSectionSmallness
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.CommonRadius

noncomputable section
namespace HolomorphicAnosov.ExponentialLift
open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- Compact continuously varying vertical jets give uniform first-derivative bounds and a common derivative modulus on every bounded metric disc (HPS, Theorem 5.5; Lee, Lemma 11.19 and Theorem 17.19; Walter, Corollary 4.3.6). -/
theorem exists_uniform_native_vertical_derivative
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) (f : M → M) (hf : Continuous f)
    (hfA : MapsTo f A A)
    (G : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    (r : ℕ∞) (hr : 1 ≤ r) (hjets : HasContinuousVerticalJets A f r G)
    (s : ℝ) (_hs : 0 < s) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (∀ p y, HasFDerivAt (G p) (fderiv ℝ (G p) y) y) ∧
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ p y, ‖y‖ < s → ‖fderiv ℝ (G p) y‖ ≤ K) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ p x y,
        ‖x‖ < s → ‖y‖ < s → ‖y - x‖ < δ →
        ‖fderiv ℝ (G p) y - fderiv ℝ (G p) x‖ < ε := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hd (p : A) : ContDiff ℝ r (G p) := by
    have hc := hjets.1 p
    simp only [Set.preimage_univ, contDiffOn_univ] at hc
    have hc' : ContDiff ℝ r ((tangentSpaceCastModel 𝓘(ℝ, E) (f p)) ∘
        G p ∘ (tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm) := hc
    rw [(tangentSpaceCastModel 𝓘(ℝ, E) (f p)).comp_contDiff_iff,
      (tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm.contDiff_comp_iff] at hc'
    exact hc'
  have hr0 : (r : ℕ∞ω) ≠ 0 := by
    exact_mod_cast ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ∞) < 1) hr)
  refine ⟨fun p y ↦ ((hd p).contDiffAt.differentiableAt hr0).hasFDerivAt, ?_⟩
  have hfirst (a b : M) : ContinuousOn
      (fun z : A × E ↦ fderiv ℝ (fibreExpression A f G a b z.1) z.2)
      {z | (z.1 : M) ∈ (chartAt E a).source ∧ f z.1 ∈ (chartAt E b).source} := by
    have hc := (continuousMultilinearCurryFin1 ℝ E E).continuous.comp_continuousOn
      (hjets.2 a b 1 hr)
    simp only [Set.mem_univ, and_true] at hc
    convert hc using 1
    funext z
    ext u
    simp only [Function.comp_apply, continuousMultilinearCurryFin1_apply,
      iteratedFDeriv_one_apply]
    rfl
  have hcompactFrame (a b : M) (Q : Set A) (hQ : IsCompact Q)
      (hQa : ∀ p ∈ Q, (p : M) ∈ (chartAt E a).source)
      (hQb : ∀ p ∈ Q, f p ∈ (chartAt E b).source) (B : ℝ) :
      (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Q, ∀ u : E, ‖u‖ ≤ B →
        ‖fderiv ℝ (fibreExpression A f G a b p) u‖ ≤ C) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ p ∈ Q, ∀ x y : E,
        ‖x‖ ≤ B → ‖y - x‖ < δ →
        ‖fderiv ℝ (fibreExpression A f G a b p) y -
          fderiv ℝ (fibreExpression A f G a b p) x‖ < ε := by
    let P := {p : A // p ∈ Q}
    have : CompactSpace P := isCompact_iff_compactSpace.mp hQ
    let D : P × E → E →L[ℝ] E := fun z ↦
      fderiv ℝ (fibreExpression A f G a b z.1.val) z.2
    have hD : Continuous D := by
      apply (hfirst a b).comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      intro z
      exact ⟨hQa z.1.val z.1.property, hQb z.1.val z.1.property⟩
    have hK : IsCompact ((Set.univ : Set P) ×ˢ Metric.closedBall (0 : E) B) :=
      isCompact_univ.prod (isCompact_closedBall 0 B)
    constructor
    · obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hD.continuousOn
      refine ⟨max C 0, le_max_right _ _, ?_⟩
      intro p hp u hu
      exact (hC (⟨p, hp⟩, u) ⟨Set.mem_univ _, by simpa using hu⟩).trans (le_max_left _ _)
    · intro ε hε
      have hF : Continuous (fun z : (P × E) × E ↦
          D (z.1.1, z.1.2 + z.2) - D z.1) :=
        (hD.comp ((continuous_fst.comp continuous_fst).prodMk
          ((continuous_snd.comp continuous_fst).add continuous_snd))).sub
          (hD.comp continuous_fst)
      obtain ⟨δ, hδ, _, hsmall⟩ := ExponentialCutoff.compact_zero_section_smallness
        _ hK Set.univ isOpen_univ _ hF.continuousOn
        (fun _ _ ↦ Set.mem_univ _) (by intro p hp; simp)
        (R := 1) zero_lt_one hε
      refine ⟨δ, hδ, ?_⟩
      intro p hp x y hx hy
      have h := (hsmall (⟨p, hp⟩, x) ⟨Set.mem_univ _, by simpa using hx⟩ (y - x) hy.le).2
      simpa only [D, add_sub_cancel] using h
  obtain ⟨cores, frames, hcores, hcompact, hcover⟩ :=
    ExponentialCutoff.exists_finite_compact_paired_cores (E := E) A hA f hf hfA
  have hpair (a b : A) :
      (∃ K : ℝ, 0 ≤ K ∧ ∀ p : A, (p : M) ∈ cores a → f p ∈ cores b →
        ∀ y, ‖y‖ < s → ‖fderiv ℝ (G p) y‖ ≤ K) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ p : A, (p : M) ∈ cores a → f p ∈ cores b →
        ∀ x y, ‖x‖ < s → ‖y‖ < s → ‖y - x‖ < δ →
          ‖fderiv ℝ (G p) y - fderiv ℝ (G p) x‖ < ε := by
    let ea := trivializationAt E (TangentSpace 𝓘(ℝ, E)) (a : M)
    let eb := trivializationAt E (TangentSpace 𝓘(ℝ, E)) (b : M)
    obtain ⟨Ca, hCa, hCaB⟩ := ExponentialCutoff.coordinate_metric_upper_bound
      g A hA (cores a) (hcores a).1 ea inferInstance (hcores a).2.2
    obtain ⟨Cb, hCb, hCbB⟩ := ExponentialCutoff.coordinate_metric_lower_bound
      g A hA (cores b) (hcores b).1 eb inferInstance (hcores b).2.2
    have hCa0 : 0 < Ca := lt_of_lt_of_le zero_lt_one hCa
    have hCb0 : 0 < Cb := lt_of_lt_of_le zero_lt_one hCb
    obtain ⟨⟨K, hK, hKB⟩, hmod⟩ := hcompactFrame a b _ (hcompact a b)
      (fun p hp ↦ (hcores a).2.2 hp.1)
      (fun p hp ↦ (hcores b).2.2 hp.2) (Ca * s)
    have htransfer (p : A) (hp : (p : M) ∈ cores a) (hfp : f p ∈ cores b) :
        let J := ea.continuousLinearEquivAt ℝ (p : M) ((hcores a).2.2 hp)
        let L := eb.continuousLinearEquivAt ℝ (f p) ((hcores b).2.2 hfp)
        (∀ v, ‖J v‖ ≤ Ca * ‖v‖) ∧ (∀ v, ‖L.symm v‖ ≤ Cb * ‖v‖) ∧
        ∀ y v, L.symm (fderiv ℝ (fibreExpression A f G a b p) (J y) (J v)) =
          fderiv ℝ (G p) y v := by
      dsimp only
      let J := ea.continuousLinearEquivAt ℝ (p : M) ((hcores a).2.2 hp)
      let L := eb.continuousLinearEquivAt ℝ (f p) ((hcores b).2.2 hfp)
      refine ⟨?_, ?_, ?_⟩
      · intro v
        have h := hCaB p hp (J v)
        change ‖J v‖ ≤ Ca * ‖ea.symmL ℝ (p : M) (J v)‖ at h
        simpa only [← ea.symm_continuousLinearEquivAt_eq (R := ℝ) ((hcores a).2.2 hp),
          J, ContinuousLinearEquiv.symm_apply_apply] using h
      · intro v
        have h := hCbB ⟨f p, hfA p.property⟩ hfp v
        change ‖eb.symmL ℝ (f p) v‖ ≤ Cb * ‖v‖ at h
        simpa only [← eb.symm_continuousLinearEquivAt_eq (R := ℝ) ((hcores b).2.2 hfp),
          L] using h
      · intro y v
        change L.symm (fderiv ℝ (fibreExpression A f G a b p) (J y) (J v)) = _
        have hexpr : fibreExpression A f G a b p = L ∘ G p ∘ J.symm := by
          ext u
          change eb.continuousLinearMapAt ℝ (f p) (G p (ea.symmL ℝ (p : M) u)) =
            L (G p (J.symm u))
          rw [← eb.coe_continuousLinearEquivAt_eq (R := ℝ) ((hcores b).2.2 hfp),
            ← ea.symm_continuousLinearEquivAt_eq (R := ℝ) ((hcores a).2.2 hp)]
        simp only [hexpr, ← Function.comp_assoc, L.comp_fderiv, J.symm.comp_right_fderiv,
          ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          J.symm_apply_apply, L.symm_apply_apply]
    constructor
    · refine ⟨Cb * K * Ca, by positivity, ?_⟩
      intro p hp hfp y hy
      obtain ⟨hJ, hL, heq⟩ := htransfer p hp hfp
      let J := ea.continuousLinearEquivAt ℝ (p : M) ((hcores a).2.2 hp)
      let L := eb.continuousLinearEquivAt ℝ (f p) ((hcores b).2.2 hfp)
      have hJy : ‖J y‖ ≤ Ca * s := (hJ y).trans
        (mul_le_mul_of_nonneg_left hy.le hCa0.le)
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro v
      rw [← heq y v]
      calc
        ‖L.symm (fderiv ℝ (fibreExpression A f G a b p) (J y) (J v))‖
            ≤ Cb * ‖fderiv ℝ (fibreExpression A f G a b p) (J y) (J v)‖ := hL _
        _ ≤ Cb * (K * ‖J v‖) := mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
            (hKB p ⟨hp, hfp⟩ _ hJy) (norm_nonneg _))) hCb0.le
        _ ≤ Cb * (K * (Ca * ‖v‖)) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hJ v) hK) hCb0.le
        _ = (Cb * K * Ca) * ‖v‖ := by ring
    · intro ε hε
      let η := ε / (2 * Cb * Ca)
      have hη : 0 < η := div_pos hε (by positivity)
      obtain ⟨δ, hδ, hδB⟩ := hmod η hη
      refine ⟨δ / Ca, div_pos hδ hCa0, ?_⟩
      intro p hp hfp x y hx hy hxy
      obtain ⟨hJ, hL, heq⟩ := htransfer p hp hfp
      let J := ea.continuousLinearEquivAt ℝ (p : M) ((hcores a).2.2 hp)
      let L := eb.continuousLinearEquivAt ℝ (f p) ((hcores b).2.2 hfp)
      have hJx : ‖J x‖ ≤ Ca * s := (hJ x).trans
        (mul_le_mul_of_nonneg_left hx.le hCa0.le)
      have hJxy : ‖J y - J x‖ < δ := by
        rw [← J.map_sub]
        exact (hJ (y - x)).trans_lt (by simpa only [mul_comm] using (lt_div_iff₀ hCa0).mp hxy)
      have hb := (hδB p ⟨hp, hfp⟩ (J x) (J y) hJx hJxy).le
      have hnorm : ‖fderiv ℝ (G p) y - fderiv ℝ (G p) x‖ ≤ Cb * η * Ca := by
        apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
        intro v
        change ‖fderiv ℝ (G p) y v - fderiv ℝ (G p) x v‖ ≤ _
        rw [← heq y v, ← heq x v, ← L.symm.map_sub]
        calc
          ‖L.symm ((fderiv ℝ (fibreExpression A f G a b p) (J y) -
              fderiv ℝ (fibreExpression A f G a b p) (J x)) (J v))‖
              ≤ Cb * ‖(fderiv ℝ (fibreExpression A f G a b p) (J y) -
                fderiv ℝ (fibreExpression A f G a b p) (J x)) (J v)‖ := hL _
          _ ≤ Cb * (η * ‖J v‖) := mul_le_mul_of_nonneg_left
            ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right hb (norm_nonneg _))) hCb0.le
          _ ≤ Cb * (η * (Ca * ‖v‖)) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hJ v) hη.le) hCb0.le
          _ = (Cb * η * Ca) * ‖v‖ := by ring
      apply hnorm.trans_lt
      have he : Cb * η * Ca = ε / 2 := by dsimp [η]; field_simp
      rw [he]
      exact half_lt_self hε
  choose K hK hKB using fun a b ↦ (hpair a b).1
  let pairs := frames ×ˢ frames
  refine ⟨∑ i ∈ pairs, K i.1 i.2, Finset.sum_nonneg (fun i _ ↦ hK i.1 i.2), ?_, ?_⟩
  · intro p y hy
    obtain ⟨a, ha, hpc⟩ := mem_iUnion₂.mp (hcover (mem_univ p))
    obtain ⟨b, hb, hp, hfp⟩ := mem_iUnion₂.mp hpc
    exact (hKB a b p hp hfp y hy).trans
      (Finset.single_le_sum (s := pairs) (a := (a, b)) (fun i _ ↦ hK i.1 i.2)
        (Finset.mem_product.mpr ⟨ha, hb⟩))
  · intro ε hε
    by_cases hempty : pairs = ∅
    · refine ⟨1, zero_lt_one, ?_⟩
      intro p x y hx hy hxy
      obtain ⟨a, ha, hpc⟩ := mem_iUnion₂.mp (hcover (mem_univ p))
      obtain ⟨b, hb, _, _⟩ := mem_iUnion₂.mp hpc
      have hi : (a, b) ∈ pairs := Finset.mem_product.mpr ⟨ha, hb⟩
      simp only [hempty, Finset.notMem_empty] at hi
    · choose δ hδ hδB using fun i : A × A ↦ (hpair i.1 i.2).2 ε hε
      obtain ⟨d, hd, _, hdb⟩ := ExponentialCutoff.finite_common_radius
        pairs (Finset.nonempty_iff_ne_empty.mpr hempty) δ (fun _ ↦ 1)
        (fun i _ ↦ hδ i) (fun _ _ ↦ zero_lt_one) (R := 1) zero_lt_one
      refine ⟨d, hd, ?_⟩
      intro p x y hx hy hxy
      obtain ⟨a, ha, hpc⟩ := mem_iUnion₂.mp (hcover (mem_univ p))
      obtain ⟨b, hb, hp, hfp⟩ := mem_iUnion₂.mp hpc
      apply hδB (a, b) p hp hfp x y hx hy
      exact hxy.trans_le (by simpa only [one_mul] using hdb (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩))

/-- Native C¹ superposition is defined on all bounded tangent sections over a compact set (Walter, Corollary 4.3.6). -/
theorem exists_bounded_tangent_superposition
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) (f : M → M) (hf : Continuous f)
    (hfA : MapsTo f A A)
    (G : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    (r : ℕ∞) (hr : 1 ≤ r) (hjets : HasContinuousVerticalJets A f r G)
    (hzero : ∀ p, G p 0 = 0) (s : ℝ) (hs : 0 < s) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ C : lp (fun p : A ↦ TangentSpace 𝓘(ℝ, E) (p : M)) ⊤ →
        lp (fun p : A ↦ TangentSpace 𝓘(ℝ, E) (f p)) ⊤,
      C 0 = 0 ∧ ContDiffOn ℝ 1 C (Metric.ball 0 s) ∧
      ∀ w ∈ Metric.ball 0 s, ∀ p, C w p = G p (w p) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨hd, K, hK, hb, hu⟩ :=
    exists_uniform_native_vertical_derivative g A hA f hf hfA G r hr hjets s hs
  exact Analysis.exists_bounded_dependent_superposition s hs G
    (fun p ↦ fderiv ℝ (G p)) (fun p y _ ↦ hd p y) hzero K hK hb hu


end HolomorphicAnosov.ExponentialLift
