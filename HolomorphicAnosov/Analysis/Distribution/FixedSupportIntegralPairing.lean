import HolomorphicAnosov.Analysis.Distribution.FixedSupportFiniteOrderBound
import HolomorphicAnosov.Analysis.Distribution.FixedSupportRiemannApproximation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Integration and distribution pairing on a fixed support

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026), Lemma 6.8 and Remark 6.9,
pp. 71–73. All test pairings are complex linear, without conjugation.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology _root_.Topology
namespace HolomorphicAnosov.Analysis

set_option maxHeartbeats 400000 in
/-- A continuous distribution commutes with integration of a jointly smooth test
family after multiplication by a compactly supported parameter test.

Source: Dyatlov, *Lecture notes for 18.155: distributions, elliptic regularity, and
applications to PDEs* (2 October 2026), Lemma 6.8, pp. 71–73, and Remark 6.9, p. 72,
which expressly permits a generic integrand. The scalar integration smoothness argument
is the order-zero case of Proposition 6.3, pp. 68–69, with the variables reversed.

Proof: let `J = tsupport φ` and put `β(p,y) = φ(p) * H(p,y)`. For `p` outside `P`,
`φ(p) = 0`, so the product itself is its zero extension in the parameter variable,
regardless of the values assigned to `H` there. Its support lies in `J × K`.
On `P × U` it is jointly smooth. Near a point with parameter outside `P`, the compact
set `J ⊆ P` is absent and the product is locally zero. These open neighborhoods give a
smooth zero extension on the parameter space times `U`.

For each `y`, the parameter function is continuous with compact support in `J`, hence
Lebesgue integrable. Define `η(y)` to be its integral. On each compact spatial ball in
`U`, all mixed derivatives of `β` are bounded and uniformly continuous on the product
with a compact parameter box enclosing `J`. Differentiation under the scalar integral
follows from the parameter-segment fundamental theorem of calculus and domination by
the finite box volume times a uniform derivative bound. Repeating this argument for
every spatial derivative proves that `η` is smooth on `U`. Outside `K` the integrand
vanishes on a spatial neighborhood, so `η` vanishes there as well and its topological
support lies in `K`. The open cover `U ∪ Kᶜ` makes it globally smooth. Compactness of
`K` now packages `η` as a test function on `U`.

For mesh size `δ > 0`, form the finite grid sum
`Rδ(y) = δ^k * Σ_{a ∈ δℤ^k} β(a,y)`; only grid points in `J` contribute. Its spatial
derivatives are the corresponding finite sums. Rewrite each as the integral of the
step function constant on half-open mesh cubes. Fix a compact parameter box with a
positive margin around `J`; for all small meshes it contains every contributing cube.
On that box times `K`, uniform continuity of every fixed spatial derivative bounds the
error between its sampled value and its value in the cube by its modulus of continuity
at `sqrt k * δ`. Integrating bounds the corresponding derivative error uniformly in
`y` by the box volume times that modulus, which tends to zero. Outside `K` all errors
are zero. Thus `Rδ` converges to `η` in every fixed-support derivative seminorm, and the
canonical fixed-support inclusion transfers this convergence to the LF test space.
Continuity of `T`, equivalently its finite-order bound on `K`, gives `T(Rδ) → T(η)`.

Complex linearity identifies `T(Rδ)` with the grid sum for `φ(p) * T(sections p)`:
inside `P` this is the section identity, while outside `P` the factor `φ` is zero.
The assumed continuity on `P` and the compact support of `φ` give a continuous compactly
supported zero extension of this scalar product. It is Lebesgue integrable, and its
step-function sums converge to its integral by the same compact uniform-continuity
estimate. Uniqueness of limits proves the stated equality. The restricted and ambient
integrals coincide because both products vanish outside `P`. Empty domains or supports,
and zero tests, yield zero integrals. No Banach structure on the entire test space or
Bochner integral with values in that space is assumed. -/
theorem distribution_pairing_integral_on_fixed_support
    {m k : ℕ} (_hm : 0 < m) (_hk : 0 < k)
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (P : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U)
    (H : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) → ℂ)
    (hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)))
    (hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K)
    (sections : EuclideanSpace ℝ (Fin k) → TestFunction U ℂ ⊤)
    (hSections : ∀ p ∈ P, ∀ y, sections p y = H p y)
    (hPairing : ContinuousOn (fun p ↦ T (sections p)) (P : Set _))
    (φ : TestFunction P ℂ ⊤) :
    ∃ η : TestFunction U ℂ ⊤,
      (∀ y, IntegrableOn (fun p ↦ φ p * H p y) (P : Set _) volume) ∧
      (∀ y, η y = ∫ p in (P : Set _), φ p * H p y ∂volume) ∧
      tsupport (η : EuclideanSpace ℝ (Fin m) → ℂ) ⊆ K ∧
      IntegrableOn (fun p ↦ φ p * T (sections p)) (P : Set _) volume ∧
      T η = ∫ p in (P : Set _), φ p * T (sections p) ∂volume := by
  let J := tsupport (φ : EuclideanSpace ℝ (Fin k) → ℂ)
  let β : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) → ℂ :=
    fun q ↦ φ q.1 * H q.1 q.2
  have hJK : IsCompact (J ×ˢ K) := φ.hasCompactSupport.prod hK
  have hβzero : EqOn β 0 (J ×ˢ K)ᶜ := by
    intro q hq
    change φ q.1 * H q.1 q.2 = 0
    by_cases hp : q.1 ∈ J
    · have hy : q.2 ∉ K := fun hy ↦ hq ⟨hp, hy⟩
      rw [image_eq_zero_of_notMem_tsupport
        (fun h ↦ hy (hSupport q.1 (φ.tsupport_subset hp) h)), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hp, zero_mul]
  have hβsupport : tsupport β ⊆ J ×ˢ K := by
    apply closure_minimal _ hJK.isClosed
    intro q hq
    by_contra hn
    exact hq (hβzero hn)
  have hβsmooth : ContDiff ℝ ∞ β := by
    have hi : ContDiffOn ℝ ∞ β ((P : Set _) ×ˢ (U : Set _)) :=
      ((φ.contDiff.comp contDiff_fst).contDiffOn.mul hH)
    have he : ContDiffOn ℝ ∞ β (J ×ˢ K)ᶜ := contDiffOn_const.congr hβzero
    have hu : ((P : Set _) ×ˢ (U : Set _)) ∪ (J ×ˢ K)ᶜ = univ := by
      apply eq_univ_of_forall
      intro q
      by_cases hq : q ∈ J ×ˢ K
      · exact Or.inl ⟨φ.tsupport_subset hq.1, hKU hq.2⟩
      · exact Or.inr hq
    exact contDiff_of_contDiffOn_union_of_isOpen hi he hu
      (P.isOpen.prod U.isOpen) hJK.isClosed.isOpen_compl
  have hcont : ∀ y, ContinuousOn (fun p ↦ H p y) (P : Set _) := by
    intro y
    by_cases hy : y ∈ U
    · exact hH.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn (fun p hp ↦ ⟨hp, hy⟩)
    · apply continuousOn_const.congr
      intro p hp
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hKU (hSupport p hp h)))
  have hInt : ∀ y, IntegrableOn (fun p ↦ φ p * H p y) (P : Set _) volume := by
    intro y
    have hc := (φ.continuous.continuousOn.mul (hcont y)).mono φ.tsupport_subset
    have hi := hc.integrableOn_compact φ.hasCompactSupport (μ := volume)
    have hs : Function.support (fun p ↦ φ p * H p y) ⊆ tsupport φ :=
      (Function.support_mul_subset_left _ _).trans (subset_tsupport _)
    exact ((integrableOn_iff_integrable_of_support_subset hs).mp hi).integrableOn
  have hIntPair : IntegrableOn (fun p ↦ φ p * T (sections p)) (P : Set _) volume := by
    have hc := (φ.continuous.continuousOn.mul hPairing).mono φ.tsupport_subset
    have hi := hc.integrableOn_compact φ.hasCompactSupport (μ := volume)
    have hs : Function.support (fun p ↦ φ p * T (sections p)) ⊆ tsupport φ :=
      (Function.support_mul_subset_left _ _).trans (subset_tsupport _)
    exact ((integrableOn_iff_integrable_of_support_subset hs).mp hi).integrableOn
  let η₀ := fun y ↦ ∫ p in (P : Set _), φ p * H p y ∂volume
  have hηeq : ∀ y, η₀ y = ∫ p in J, β (p, y) ∂volume := by
    intro y
    change (∫ p in (P : Set _), β (p, y) ∂volume) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp ↦ ?_)]
    · symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      change φ p * H p y = 0
      rw [image_eq_zero_of_notMem_tsupport hp, zero_mul]
    · change φ p * H p y = 0
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hp (φ.tsupport_subset h)), zero_mul]
  let D (i : ℕ) := iteratedFDeriv ℝ i β
  let I (i : ℕ) (y : (EuclideanSpace ℝ (Fin m))) := ∫ p in J, D i (p, y) ∂volume
  let L : (EuclideanSpace ℝ (Fin m)) →L[ℝ] (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) := ContinuousLinearMap.inr ℝ _ _
  let A (i : ℕ) :=
    ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m))
      (ContinuousMultilinearMap ℝ (fun _ : Fin i ↦ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m))) ℂ)).flip L).comp
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m))) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  have hDsmooth (i : ℕ) : ContDiff ℝ ∞ (D i) :=
    hβsmooth.iteratedFDeriv_right (by simp)
  have hDcompact (i : ℕ) : HasCompactSupport (D i) :=
    (HasCompactSupport.intro hJK hβzero).iteratedFDeriv i
  have hDI (i : ℕ) (y : (EuclideanSpace ℝ (Fin m))) : IntegrableOn (fun p ↦ D i (p, y)) J volume :=
    ((hDsmooth i).continuous.comp
      (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact
        φ.hasCompactSupport
  have hIcontinuous (i : ℕ) : Continuous (I i) := by
    obtain ⟨C, hC⟩ := (hDsmooth i).continuous.bounded_above_of_compact_support (hDcompact i)
    apply continuous_of_dominated (bound := fun _ ↦ C)
    · intro y
      exact (hDI i y).aestronglyMeasurable
    · intro y
      exact Filter.Eventually.of_forall (fun p ↦ hC (p, y))
    · exact integrableOn_const φ.hasCompactSupport.measure_lt_top.ne
    · exact Filter.Eventually.of_forall (fun p ↦ (hDsmooth i).continuous.comp
        (continuous_const.prodMk continuous_id))
  have hIderiv (i : ℕ) (y : (EuclideanSpace ℝ (Fin m))) : HasFDerivAt (I i) (A i (I (i + 1) y)) y := by
    have : SecondCountableTopologyEither (EuclideanSpace ℝ (Fin k))
        (EuclideanSpace ℝ (Fin m) →L[ℝ]
          ContinuousMultilinearMap ℝ
            (fun _ : Fin i ↦ EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) ℂ) :=
      ⟨Or.inl inferInstance⟩
    have hdf := (hDsmooth i).continuous_fderiv (by simp)
    obtain ⟨C, hC⟩ := hdf.bounded_above_of_compact_support
      ((hDcompact i).fderiv (𝕜 := ℝ))
    have hraw : HasFDerivAt (I i)
        (∫ p in J, (fderiv ℝ (D i) (p, y)).comp L ∂volume) y := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun y p ↦ D i (p, y))
        (F' := fun y p ↦ (fderiv ℝ (D i) (p, y)).comp L)
        (μ := volume.restrict J) (s := univ) (bound := fun _ ↦ C) Filter.univ_mem
      · exact Filter.Eventually.of_forall (fun y ↦ (hDI i y).aestronglyMeasurable)
      · exact hDI i y
      · exact ((hdf.comp (continuous_id.prodMk continuous_const)).clm_comp
          continuous_const).aestronglyMeasurable
      · apply Filter.Eventually.of_forall
        intro p y hy
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          ((mul_le_of_le_one_right (norm_nonneg _)
            (ContinuousLinearMap.norm_inr_le_one ℝ _ _)).trans (hC (p, y)))
      · exact integrableOn_const φ.hasCompactSupport.measure_lt_top.ne
      · apply Filter.Eventually.of_forall
        intro p y hy
        exact (((hDsmooth i).differentiable (by simp) (p, y)).hasFDerivAt).comp y
          ((hasFDerivAt_const p y).prodMk (hasFDerivAt_id y))
    have heq : A i (I (i + 1) y) =
        ∫ p in J, (fderiv ℝ (D i) (p, y)).comp L ∂volume := by
      exact (ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ)
        (Fₗ := EuclideanSpace ℝ (Fin m) →L[ℝ]
          ContinuousMultilinearMap ℝ
            (fun _ : Fin i ↦ EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) ℂ)
        (A i) (hDI (i + 1) y)).symm
    exact heq.symm ▸ hraw
  have hIfinite (r : ℕ) : ∀ i, ContDiff ℝ r (I i) := by
    induction r with
    | zero => intro i; exact contDiff_zero.mpr (hIcontinuous i)
    | succ r ih =>
      intro i
      have hA : ContDiff ℝ r (A i) := ContinuousLinearMap.contDiff
        (F := EuclideanSpace ℝ (Fin m) →L[ℝ]
          ContinuousMultilinearMap ℝ
            (fun _ : Fin i ↦ EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) ℂ) (A i)
      exact contDiff_succ_iff_hasFDerivAt.mpr
        ⟨fun y ↦ A i (I (i + 1) y), hA.comp (ih (i + 1)), hIderiv i⟩
  have hIsmooth : ContDiff ℝ ∞ (I 0) := contDiff_infty.mpr (fun r ↦ hIfinite r 0)
  have hηsmooth : ContDiff ℝ ∞ η₀ := by
    let ev : ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m))) ℂ →L[ℝ] ℂ :=
      ContinuousMultilinearMap.apply ℝ _ ℂ (fun i ↦ Fin.elim0 i)
    have heq : (fun y ↦ ev (I 0 y)) = η₀ := by
      funext y
      rw [show ev (I 0 y) = ∫ p in J, ev (D 0 (p, y)) ∂volume from
        (ev.integral_comp_comm (hDI 0 y)).symm]
      simpa only [ev, D, ContinuousMultilinearMap.apply_apply,
        iteratedFDeriv_zero_apply] using (hηeq y).symm
    rw [← heq]
    exact ev.contDiff.comp hIsmooth
  have hηsupport : tsupport η₀ ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hyK
    apply hy
    change (∫ p in (P : Set _), φ p * H p y ∂volume) = 0
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro p hp
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hyK (hSupport p hp h)), mul_zero]
  let η : TestFunction U ℂ ⊤ := TestFunction.mk η₀ hηsmooth
    (hK.of_isClosed_subset (isClosed_tsupport _) hηsupport) (hηsupport.trans hKU)
  refine ⟨η, hInt, fun _ ↦ rfl, hηsupport, hIntPair, ?_⟩
  let Kc : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin m)) := ⟨K, hK⟩
  let Ψ : EuclideanSpace ℝ (Fin k) →
      ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ Kc := fun p ↦
    ⟨fun y ↦ β (p, y), hβsmooth.comp (contDiff_const.prodMk contDiff_id), by
      intro y hy
      exact hβzero (fun h ↦ hy h.2)⟩
  let ηK : ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ Kc :=
    ⟨η₀, hηsmooth, fun y hy ↦ image_eq_zero_of_notMem_tsupport
      (fun h ↦ hy (hηsupport h))⟩
  let inc := TestFunction.ofSupportedInCLM ℂ (K := Kc) (Ω := U) hKU (n := ⊤) (F := ℂ)
  have hincη : inc ηK = η := by rfl
  have hincΨ (p : EuclideanSpace ℝ (Fin k)) : inc (Ψ p) = φ p • sections p := by
    ext y
    change φ p * H p y = φ p • sections p y
    by_cases hp : p ∈ P
    · rw [hSections p hp y, smul_eq_mul]
    · simp only [φ.zero_on_compl hp, Pi.zero_apply, zero_mul, zero_smul]
  have hsum (S : Finset (EuclideanSpace ℝ (Fin k)))
      (c : EuclideanSpace ℝ (Fin k) → ℂ) :
      T (inc (∑ p ∈ S, c p • Ψ p)) = ∑ p ∈ S, c p * (φ p * T (sections p)) := by
    simp only [map_sum, map_smul, hincΨ, smul_eq_mul]
  have hbound := distribution_fixed_support_finite_order_bound U T K hK hKU
  obtain ⟨s, C, hC, hbound⟩ := hbound
  have hJetFormula (i : ℕ) (p : EuclideanSpace ℝ (Fin k))
      (y : EuclideanSpace ℝ (Fin m)) :
      iteratedFDeriv ℝ i (Ψ p) y =
        (D i (p, y)).compContinuousLinearMap (fun _ ↦ L) := by
    change iteratedFDeriv ℝ i (fun y ↦ β (p, y)) y = _
    have ht : ContDiff ℝ ∞ (fun z ↦ β ((p, 0) + z)) :=
      hβsmooth.comp (contDiff_const.add contDiff_id)
    have he := L.iteratedFDeriv_comp_right ht y (i := i) (by simp)
    simpa only [Function.comp_def, iteratedFDeriv_comp_add_left, L,
      ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add, D, Ψ] using he
  have hJetUniform (i : ℕ) : UniformContinuous
      (fun q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) ↦
        iteratedFDeriv ℝ i (Ψ q.1) q.2) := by
    simp_rw [hJetFormula]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (F := ℂ) (fun _ : Fin i ↦ L)).uniformContinuous.comp
        ((hDsmooth i).continuous.uniformContinuous_of_tendsto_cocompact
          (hDcompact i).is_zero_at_infty)
  have hScalarSupport : tsupport (fun p ↦ φ p * T (sections p)) ⊆ J := by
    apply closure_minimal _ (isClosed_tsupport _)
    exact (Function.support_mul_subset_left _ _).trans (subset_tsupport _)
  have hScalarContinuous : Continuous (fun p ↦ φ p * T (sections p)) :=
    (φ.continuous.continuousOn.mul hPairing).continuous_of_tsupport_subset P.isOpen
      (hScalarSupport.trans φ.tsupport_subset)
  have hScalarUniform : UniformContinuous (fun p ↦ φ p * T (sections p)) :=
    hScalarContinuous.uniformContinuous_of_tendsto_cocompact
      (show HasCompactSupport (fun p ↦ φ p * T (sections p)) from
        φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hScalarSupport).is_zero_at_infty
  have hSampling (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0,
      ∀ p q : EuclideanSpace ℝ (Fin k), dist p q < δ →
        s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc) (Ψ p - Ψ q) ≤ ε ∧
        ‖φ p * T (sections p) - φ q * T (sections q)‖ ≤ ε := by
    have hfinite (t : Finset ℕ) : ∃ δ > 0,
        ∀ p q : EuclideanSpace ℝ (Fin k), dist p q < δ →
          (∀ i ∈ t, ∀ y : EuclideanSpace ℝ (Fin m),
            ‖iteratedFDeriv ℝ i (Ψ p) y - iteratedFDeriv ℝ i (Ψ q) y‖ ≤ ε) ∧
          ‖φ p * T (sections p) - φ q * T (sections q)‖ ≤ ε := by
      induction t using Finset.induction_on with
      | empty =>
        obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hScalarUniform ε hε
        exact ⟨δ, hδ, fun p q hpq ↦ ⟨by simp, by simpa [dist_eq_norm] using (hd hpq).le⟩⟩
      | @insert i t hi ih =>
        obtain ⟨δ, hδ, hd⟩ := ih
        obtain ⟨δi, hδi, hdi⟩ := Metric.uniformContinuous_iff.mp (hJetUniform i) ε hε
        refine ⟨min δ δi, lt_min hδ hδi, fun p q hpq ↦ ?_⟩
        obtain ⟨ht, hs⟩ := hd p q (lt_of_lt_of_le hpq (min_le_left _ _))
        refine ⟨?_, hs⟩
        intro j hj y
        rcases Finset.mem_insert.mp hj with rfl | hj
        · have hpqy : dist (p, y) (q, y) < δi := by
            simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using
              (lt_of_lt_of_le hpq (min_le_right _ _))
          simpa only [dist_eq_norm] using (hdi hpqy).le
        · exact ht j hj y
    obtain ⟨δ, hδ, hd⟩ := hfinite s
    refine ⟨δ, hδ, fun p q hpq ↦ ?_⟩
    obtain ⟨hj, hs⟩ := hd p q hpq
    refine ⟨Seminorm.finset_sup_apply_le hε.le (fun i hi ↦ ?_), hs⟩
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ hε.le i (Ψ p - Ψ q)).mpr
    intro y hy
    change ‖iteratedFDeriv ℝ i ((Ψ p : _ → ℂ) - (Ψ q : _ → ℂ)) y‖ ≤ ε
    rw [iteratedFDeriv_sub_apply ((Ψ p).contDiff.of_le (by simp)).contDiffAt
      ((Ψ q).contDiff.of_le (by simp)).contDiffAt]
    exact hj i hi y
  have hsumBound (S : Finset (EuclideanSpace ℝ (Fin k)))
      (c : EuclideanSpace ℝ (Fin k) → ℂ) :
      ‖(∑ p ∈ S, c p * (φ p * T (sections p))) - T η‖ ≤
        C • s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc)
          ((∑ p ∈ S, c p • Ψ p) - ηK) := by
    have hb := hbound ((∑ p ∈ S, c p • Ψ p) - ηK)
    change ‖T (inc ((∑ p ∈ S, c p • Ψ p) - ηK))‖ ≤ _ at hb
    simpa only [map_sub, hincη, hsum] using hb
  let q : ℕ → SimpleFunc (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)) :=
    fun r ↦ SimpleFunc.approxOn id measurable_id Set.univ 0 (Set.mem_univ _) r
  have hqpoint (p : EuclideanSpace ℝ (Fin k)) :
      Filter.Tendsto (fun r ↦ q r p) Filter.atTop (𝓝 p) := by
    exact SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ _) (by simp)
  let g : EuclideanSpace ℝ (Fin k) → ℂ := fun p ↦ φ p * T (sections p)
  have hgcompact : HasCompactSupport g :=
    φ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport _) hScalarSupport
  have hgJ : (∫ p in J, g p ∂volume) = ∫ p in (P : Set _), g p ∂volume := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp ↦ ?_),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp ↦ ?_)]
    · exact image_eq_zero_of_notMem_tsupport
        (fun h ↦ hp (φ.tsupport_subset (hScalarSupport h)))
    · exact image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hScalarSupport h))
  have hScalarSampleLimit : Filter.Tendsto (fun r ↦ ∫ p in J, g (q r p) ∂volume)
      Filter.atTop (𝓝 (∫ p in (P : Set _), g p ∂volume)) := by
    rw [← hgJ]
    obtain ⟨B, hB⟩ := hScalarContinuous.bounded_above_of_compact_support hgcompact
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ B)
    · intro r
      exact (hScalarContinuous.measurable.comp (q r).measurable).aestronglyMeasurable
    · exact integrableOn_const φ.hasCompactSupport.measure_lt_top.ne
    · intro r
      exact Filter.Eventually.of_forall (fun p ↦ hB (q r p))
    · exact Filter.Eventually.of_forall (fun p ↦
        hScalarContinuous.continuousAt.tendsto.comp (hqpoint p))
  let μ := volume.restrict J
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    φ.hasCompactSupport.measure_lt_top.ne
  let Ssample : ℕ → Finset (EuclideanSpace ℝ (Fin k)) := fun r ↦ (q r).range
  let csample : ℕ → EuclideanSpace ℝ (Fin k) → ℂ := fun r a ↦
    (μ.real ((q r) ⁻¹' {a}) : ℂ)
  have hSampleSum (r : ℕ) :
      (∫ p in J, g (q r p) ∂volume) = ∑ a ∈ Ssample r, csample r a * g a := by
    classical
    have heq : (fun p ↦ g (q r p)) = fun p ↦ ∑ a ∈ (q r).range,
        ((q r) ⁻¹' {a}).indicator (fun _ ↦ g a) p := by
      funext p
      simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
      rw [Finset.sum_eq_single (q r p)]
      · simp
      · intro b hb hne
        exact ite_eq_right (Ne.symm hne)
      · intro hn
        exact (hn (SimpleFunc.mem_range.mpr ⟨p, rfl⟩)).elim
    change (∫ p, g (q r p) ∂μ) = _
    rw [heq, integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [integral_indicator_const _ ((q r).measurableSet_preimage {a})]
      simp only [csample, Complex.real_smul]
    · intro a ha
      exact (integrable_const (g a)).indicator ((q r).measurableSet_preimage {a})
  have hScalarWeights : Filter.Tendsto
      (fun r ↦ ∑ p ∈ Ssample r, csample r p * (φ p * T (sections p)))
      Filter.atTop (𝓝 (∫ p in (P : Set _), φ p * T (sections p) ∂volume)) := by
    simpa only [hSampleSum, g] using hScalarSampleLimit
  suffices hRiemann : ∃ (S : ℕ → Finset (EuclideanSpace ℝ (Fin k)))
      (c : ℕ → EuclideanSpace ℝ (Fin k) → ℂ),
      Filter.Tendsto (fun r ↦
        s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc)
          ((∑ p ∈ S r, c r p • Ψ p) - ηK)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun r ↦ ∑ p ∈ S r, c r p * (φ p * T (sections p)))
        Filter.atTop (𝓝 (∫ p in (P : Set _), φ p * T (sections p) ∂volume)) by
    obtain ⟨S, c, hfixed, hscalar⟩ := hRiemann
    have hTlimit' : Filter.Tendsto
        (fun r ↦ ∑ p ∈ S r, c r p * (φ p * T (sections p)))
        Filter.atTop (𝓝 (T η)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      have hscaled : Filter.Tendsto (fun r ↦
          C • s.sup (ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ Kc)
            ((∑ p ∈ S r, c r p • Ψ p) - ηK)) Filter.atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := C)).smul hfixed
      exact squeeze_zero (fun r ↦ norm_nonneg _) (fun r ↦ hsumBound (S r) (c r)) hscaled
    exact tendsto_nhds_unique hTlimit' hscalar
  have hβcompact : HasCompactSupport β := HasCompactSupport.intro hJK hβzero
  have hDerivativeIntegral₀ := fixed_support_integrated_derivative_identity
    J volume Kc β η₀ Ψ L hβsmooth hβcompact hηeq hJetFormula
  have hDerivativeIntegral : ∀ i y,
      iteratedFDeriv ℝ i (ηK : EuclideanSpace ℝ (Fin m) → ℂ) y =
        ∫ p in J, iteratedFDeriv ℝ i (Ψ p) y ∂volume := by
    change ∀ i y, iteratedFDeriv ℝ i η₀ y =
      ∫ p in J, iteratedFDeriv ℝ i (Ψ p) y ∂volume
    exact hDerivativeIntegral₀
  have hJetBound : ∀ i ∈ s, ∃ B : ℝ, ∀ p y,
      ‖iteratedFDeriv ℝ i (Ψ p) y‖ ≤ B := by
    intro i _
    obtain ⟨B, hB⟩ := (hDsmooth i).continuous.bounded_above_of_compact_support (hDcompact i)
    let R := ContinuousMultilinearMap.compContinuousLinearMapL
      (F := ℂ) (fun _ : Fin i ↦ L)
    refine ⟨‖R‖ * B, fun p y ↦ ?_⟩
    rw [hJetFormula]
    exact (R.le_opNorm (D i (p, y))).trans
      (mul_le_mul_of_nonneg_left (hB (p, y)) (norm_nonneg _))
  have hfixed := fixed_support_simple_function_riemann J volume Kc s Ψ ηK q
      hqpoint (fun ε hε ↦ by
        obtain ⟨δ, hδ, h⟩ := hSampling ε hε
        exact ⟨δ, hδ, fun p q hpq ↦ (h p q hpq).1⟩) hJetBound hDerivativeIntegral
  refine ⟨Ssample, csample, ?_, hScalarWeights⟩
  simpa only [Ssample, csample, μ] using hfixed

end HolomorphicAnosov.Analysis

