import HolomorphicAnosov.Geometry.HermitianMetricVolumeJacobian
import HolomorphicAnosov.Geometry.ComplexPairedTopFormDeterminant
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

open Bundle Set Filter MeasureTheory
open scoped ContDiff Manifold Topology
namespace HolomorphicAnosov
noncomputable section
universe u
attribute [local instance] complex_isManifold_real

/-- The real basis of the complex coordinate model consisting of paired real and imaginary
coordinate directions. -/
private def pairedModelBasis (d : ℕ) : Module.Basis (ComplexPairedIndex d) ℝ (ComplexModel d) :=
  (Pi.basis (fun _ : Fin d ↦ Complex.basisOneI)).reindex
    (Equiv.sigmaEquivProd (Fin d) (Fin 2))

private theorem pairedModelBasis_apply {d : ℕ} (i : ComplexPairedIndex d) :
    pairedModelBasis d i = Pi.single i.1 (if i.2 = 0 then 1 else Complex.I) := by
  rcases i with ⟨i, j⟩
  rw [pairedModelBasis, Module.Basis.reindex_apply]
  change (Pi.basis (fun _ : Fin d ↦ Complex.basisOneI)) ⟨i, j⟩ = _
  rw [Pi.basis_apply]
  congr 1
  fin_cases j <;> simp [Complex.coe_basisOneI]

/-- Composition of a real top form with a linear map multiplies its evaluation on the paired
coordinate basis by the real determinant. -/
private theorem paired_top_form_comp_det {d : ℕ}
    (β : ContinuousAlternatingMap ℝ (ComplexModel d) ℝ (ComplexPairedIndex d))
    (A : ComplexModel d →L[ℝ] ComplexModel d) :
    β (fun i ↦ A (Pi.single i.1 (if i.2 = 0 then 1 else Complex.I))) =
      β (fun i ↦ Pi.single i.1 (if i.2 = 0 then 1 else Complex.I)) * A.toLinearMap.det := by
  have h := congrArg (fun f : AlternatingMap ℝ (ComplexModel d) ℝ (ComplexPairedIndex d) ↦
      f (A.toLinearMap ∘ pairedModelBasis d))
    (β.toAlternatingMap.eq_smul_basis_det (pairedModelBasis d))
  simp only [AlternatingMap.smul_apply, smul_eq_mul, Module.Basis.det_comp,
    Module.Basis.det_self, mul_one] at h
  change β (fun i ↦ A (pairedModelBasis d i)) =
    β (pairedModelBasis d) * A.toLinearMap.det at h
  simpa only [show (pairedModelBasis d : ComplexPairedIndex d → ComplexModel d) =
    (fun i ↦ Pi.single i.1 (if i.2 = 0 then 1 else Complex.I)) from
      funext pairedModelBasis_apply] using h

/-- Evaluation of a native real top form along a coordinate map gives the real Jacobian factor.
(Demailly, I §1.B.5, p.10, (1.13)) -/
theorem native_topForm_coordinate_map
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (η : RealTangentTopForm d X) (H : ComplexModel d → X)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (z : ComplexModel d)
    (hH : ContMDiffAt (realModel d) (realModel d) ∞ H z)
    (hz : H z ∈ c.source) :
    η (H z) (fun i ↦ mfderiv (realModel d) (realModel d) H z
      ((NormedSpace.fromTangentSpace z).symm
        (Pi.single i.1 (if i.2 = 0 then 1 else Complex.I)))) =
      realTangentTopFormChartCoefficient η c (c (H z)) *
        (fderiv ℝ (fun w ↦ c (H w)) z).toLinearMap.det := by
  have hcat : ContMDiffAt (realModel d) (realModel d) ∞ c (H z) := by
    obtain ⟨hcont, hd⟩ := contMDiffAt_iff.mp (contMDiffAt_of_mem_maximalAtlas hc hz)
    exact contMDiffAt_iff.mpr ⟨hcont, hd.restrict_scalars ℝ⟩
  have hcinv : ContMDiffAt (realModel d) (realModel d) ∞ c.symm (c (H z)) := by
    obtain ⟨hcont, hd⟩ := contMDiffAt_iff.mp
      (contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hz))
    exact contMDiffAt_iff.mpr ⟨hcont, hd.restrict_scalars ℝ⟩
  have hcoord := hcat.comp z hH
  have hevent : (c.symm ∘ (c ∘ H)) =ᶠ[𝓝 z] H := by
    filter_upwards [hH.continuousAt.eventually (c.open_source.mem_nhds hz)] with w hw
    exact c.left_inv hw
  have hderiv := hevent.mfderiv_eq (I := realModel d) (I' := realModel d)
  rw [mfderiv_comp z (hcinv.mdifferentiableAt (by simp))
    (hcoord.mdifferentiableAt (by simp)), mfderiv_eq_fderiv] at hderiv
  let β : ContinuousAlternatingMap ℝ (ComplexModel d) ℝ (ComplexPairedIndex d) :=
    (η (c.symm (c (H z)))).compContinuousLinearMap
      ((mfderiv (realModel d) (realModel d) c.symm (c (H z))).comp
        (NormedSpace.fromTangentSpace (c (H z))).symm.toContinuousLinearMap)
  have h := paired_top_form_comp_det β (fderiv ℝ (fun w ↦ c (H w)) z)
  change η (c.symm (c (H z)))
      (fun i ↦ mfderiv (realModel d) (realModel d) c.symm (c (H z))
        ((fderiv ℝ (fun w ↦ c (H w)) z)
          (Pi.single i.1 (if i.2 = 0 then 1 else Complex.I)))) =
      realTangentTopFormChartCoefficient η c (c (H z)) *
        (fderiv ℝ (fun w ↦ c (H w)) z).toLinearMap.det at h
  rw [c.left_inv hz] at h
  convert h using 1
  apply congrArg (η (H z))
  funext i
  exact (congrArg (fun L ↦ L (Pi.single i.1 (if i.2 = 0 then 1 else Complex.I))) hderiv).symm

/-- A positive native pullback scalar equals the density-weighted absolute coordinate Jacobian.
(Demailly, I §1.C, p.11; Zhang, (31), p.16) -/
theorem native_positive_jacobian_coordinate
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (η : RealTangentTopForm d X) (hη : IsSmoothPositiveRealTangentTopForm η)
    (F : Biholomorph d d X X) (J : X → ℝ) (hJpos : ∀ x, 0 < J x)
    (hJ : realTangentTopFormPullback F η = realTangentTopFormScale J η)
    (c q : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (hq : q ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (z : ComplexModel d) (hz : z ∈ c.target) (hqz : F (c.symm z) ∈ q.source) :
    J (c.symm z) * realTangentTopFormChartCoefficient η c z =
      realTangentTopFormChartCoefficient η q (q (F (c.symm z))) *
        |(fderiv ℝ (fun w ↦ q (F (c.symm w))) z).toLinearMap.det| := by
  have hcinv : ContMDiffAt (realModel d) (realModel d) ∞ c.symm z := by
    obtain ⟨hcont, hd⟩ := contMDiffAt_iff.mp (contMDiffAt_symm_of_mem_maximalAtlas hc hz)
    exact contMDiffAt_iff.mpr ⟨hcont, hd.restrict_scalars ℝ⟩
  have hF : ContMDiff (realModel d) (realModel d) ∞ F := F.toReal.contMDiff
  have heq := native_topForm_coordinate_map η (F ∘ c.symm) q hq z
    ((hF (c.symm z)).comp z hcinv) hqz
  rw [mfderiv_comp z ((hF _).mdifferentiableAt (by simp))
    (hcinv.mdifferentiableAt (by simp))] at heq
  have hscale := congrArg (fun ν : RealTangentTopForm d X ↦
    realTangentTopFormChartCoefficient ν c z) hJ
  have heq' : J (c.symm z) * realTangentTopFormChartCoefficient η c z =
      realTangentTopFormChartCoefficient η q (q (F (c.symm z))) *
        (fderiv ℝ (fun w ↦ q (F (c.symm w))) z).toLinearMap.det :=
    hscale.symm.trans heq
  have hsource := (hη c hc).2 z hz
  have htarget := (hη q hq).2 (q (F (c.symm z))) (q.map_source hqz)
  have hdet : 0 ≤ (fderiv ℝ (fun w ↦ q (F (c.symm w))) z).toLinearMap.det := by
    nlinarith [hJpos (c.symm z)]
  rwa [abs_of_nonneg hdet]

/-- The Jacobian mass of a chart piece is bounded by the mass of its containing target-chart piece.
(Zhang, (31), p.16; Demailly, I §1.C, p.11) -/
theorem native_positive_jacobian_piece_integral_le
    {d : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (η : RealTangentTopForm d X) (hη : IsSmoothPositiveRealTangentTopForm η)
    (F : Biholomorph d d X X) (J : X → ℝ) (hJpos : ∀ x, 0 < J x)
    (hJ : realTangentTopFormPullback F η = realTangentTopFormScale J η)
    (c q : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (hq : q ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (S : Set (ComplexModel d)) (hS : MeasurableSet S) (hSc : S ⊆ c.target)
    (L : Set X) (hL : IsCompact L) (hLq : L ⊆ q.source)
    (himage : ∀ z ∈ S, F (c.symm z) ∈ L) :
    (∫ z in S, J (c.symm z) * realTangentTopFormChartCoefficient η c z) ≤
      ∫ w in q '' L, realTangentTopFormChartCoefficient η q w := by
  let G : ComplexModel d → ComplexModel d := fun z ↦ q (F (c.symm z))
  have hderiv : ∀ z ∈ S, HasFDerivWithinAt G (fderiv ℝ G z) S z := by
    intro z hz
    have hqin := hLq (himage z hz)
    have hdiff := (contMDiffAt_of_mem_maximalAtlas hq hqin).comp z
      ((F.contMDiff (c.symm z)).comp z
        (contMDiffAt_symm_of_mem_maximalAtlas hc (hSc hz)))
    exact (hdiff.contDiffAt.restrict_scalars ℝ).differentiableAt (by simp)
      |>.hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn G S := by
    intro z hz w hw heq
    exact c.symm.injOn (hSc hz) (hSc hw)
      (F.injective (q.injOn (hLq (himage z hz)) (hLq (himage w hw)) heq))
  have hsub : G '' S ⊆ q '' L := by
    rintro _ ⟨z, hz, rfl⟩
    exact Set.mem_image_of_mem q (himage z hz)
  have hqL : IsCompact (q '' L) := hL.image_of_continuousOn (q.continuousOn.mono hLq)
  have hqLt : q '' L ⊆ q.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact q.map_source (hLq hx)
  have hint : IntegrableOn (realTangentTopFormChartCoefficient η q) (q '' L) volume :=
    ((hη q hq).1.continuousOn.mono hqLt).integrableOn_compact hqL
  calc
    _ = ∫ z in S, |(fderiv ℝ G z).toLinearMap.det| •
        realTangentTopFormChartCoefficient η q (G z) := by
      apply setIntegral_congr_fun hS
      intro z hz
      simpa only [G, smul_eq_mul, mul_comm] using
        native_positive_jacobian_coordinate η hη F J hJpos hJ c q hc hq z
          (hSc hz) (hLq (himage z hz))
    _ = ∫ w in G '' S, realTangentTopFormChartCoefficient η q w :=
      (integral_image_eq_integral_abs_det_fderiv_smul volume hS hderiv hinj _).symm
    _ ≤ _ := setIntegral_mono_set hint
      (ae_restrict_of_forall_mem hqL.measurableSet fun w hw ↦ (hη q hq).2 w (hqLt hw) |>.le)
      (Filter.Eventually.of_forall fun _ hx ↦ hsub hx)

/-- The integral of a nonnegative integrable function over a set is at most the sum of its integrals
over a finite cover of that set. -/
private theorem integral_le_sum_finite_cover
    {E ι : Type*} [MeasurableSpace E] (μ : Measure E) (K : Set E) (hK : MeasurableSet K)
    (w : E → ℝ) (hw : IntegrableOn w K μ) (hwpos : ∀ z ∈ K, 0 ≤ w z)
    (t : Finset ι) (S : ι → Set E) (hS : ∀ i ∈ t, MeasurableSet (S i))
    (hsub : ∀ i ∈ t, S i ⊆ K) (hcover : ∀ z ∈ K, ∃ i ∈ t, z ∈ S i) :
    (∫ z in K, w z ∂μ) ≤ ∑ i ∈ t, ∫ z in S i, w z ∂μ := by
  classical
  have hi : ∀ i ∈ t, Integrable (Set.indicator (S i) w) (μ.restrict K) :=
    fun i hi ↦ hw.indicator (hS i hi)
  calc
    _ ≤ ∫ z in K, ∑ i ∈ t, Set.indicator (S i) w z ∂μ := by
      apply integral_mono_ae hw (integrable_finsetSum t hi)
      filter_upwards [ae_restrict_mem hK] with z hz
      obtain ⟨i, hi, hzi⟩ := hcover z hz
      have hsum := Finset.single_le_sum (s := t)
        (fun j _ ↦ show 0 ≤ Set.indicator (S j) w z from by
          by_cases hj : z ∈ S j
          · simpa only [Set.indicator_of_mem hj] using hwpos z hz
          · simp only [Set.indicator_of_notMem hj, le_refl]) hi
      simpa only [Set.indicator_of_mem hzi] using hsum
    _ = ∑ i ∈ t, ∫ z in S i, w z ∂μ := by
      rw [integral_finsetSum _ hi]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_indicator (hS i hi), Measure.restrict_restrict (hS i hi),
        Set.inter_eq_left.mpr (hsub i hi)]

/-- On a compact manifold, positive native Jacobians have a uniform integral bound on each compact
chart support, independent of the biholomorphism. (Zhang, Lemma 4.3, (31), p.16; Demailly, I
§1.C, p.11) -/
theorem native_positive_jacobian_compact_chart_bound
    {d : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (η : RealTangentTopForm d X) (hη : IsSmoothPositiveRealTangentTopForm η)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (K : Set (ComplexModel d)) (hK : IsCompact K) (hKc : K ⊆ c.target) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (F : Biholomorph d d X X) (J : X → ℝ),
      Continuous J → (∀ x, 0 < J x) →
      realTangentTopFormPullback F η = realTangentTopFormScale J η →
      (∫ z in K, J (c.symm z)) ≤ M := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, le_rfl, ?_⟩
    intro F J _ _ _
    simp [hKe]
  have hlocal (x : X) : ∃ L : Set X, L ∈ 𝓝 x ∧
      L ⊆ (chartAt (ComplexModel d) x).source ∧ IsCompact L :=
    local_compact_nhds ((chartAt (ComplexModel d) x).open_source.mem_nhds (mem_chart_source _ x))
  choose L hLnhds hLsource hLcompact using hlocal
  obtain ⟨t, htcover⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ interior (L x))
    (fun _ ↦ isOpen_interior)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (hLnhds x)⟩)
  let mass := fun x : X ↦ ∫ w in (chartAt (ComplexModel d) x) '' L x,
    realTangentTopFormChartCoefficient η (chartAt (ComplexModel d) x) w
  let ρ := realTangentTopFormChartCoefficient η c
  have hρ : ContinuousOn ρ K := (hη c hc).1.continuousOn.mono hKc
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne hρ
  have hm : 0 < ρ z₀ := (hη c hc).2 z₀ (hKc hz₀)
  refine ⟨max 0 ((ρ z₀)⁻¹ * ∑ x ∈ t, mass x), le_max_left _ _, ?_⟩
  intro F J hJcont hJpos hJ
  let H : ComplexModel d → X := fun z ↦ F (c.symm z)
  let S : X → Set (ComplexModel d) := fun x ↦ K ∩ H ⁻¹' L x
  let w : ComplexModel d → ℝ := fun z ↦ J (c.symm z) * ρ z
  have hH : ContinuousOn H K := F.continuous.comp_continuousOn (c.symm.continuousOn.mono hKc)
  have hSclosed (x : X) : IsClosed (S x) :=
    hH.preimage_isClosed_of_isClosed hK.isClosed (hLcompact x).isClosed
  have hwcont : ContinuousOn w K :=
    (hJcont.comp_continuousOn (c.symm.continuousOn.mono hKc)).mul hρ
  have hwint : IntegrableOn w K volume := hwcont.integrableOn_compact hK
  have hwpos : ∀ z ∈ K, 0 ≤ w z :=
    fun z hz ↦ (mul_pos (hJpos _) ((hη c hc).2 z (hKc hz))).le
  have hcover : ∀ z ∈ K, ∃ x ∈ t, z ∈ S x := by
    intro z hz
    obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp (htcover (Set.mem_univ (H z)))
    exact ⟨x, hxt, hz, show H z ∈ L x from interior_subset hx⟩
  have hsum : (∫ z in K, w z) ≤ ∑ x ∈ t, mass x := by
    apply (integral_le_sum_finite_cover volume K hK.measurableSet w hwint hwpos t S
      (fun x _ ↦ (hSclosed x).measurableSet) (fun _ _ ↦ Set.inter_subset_left) hcover).trans
    apply Finset.sum_le_sum
    intro x hx
    exact native_positive_jacobian_piece_integral_le η hη F J hJpos hJ c
      (chartAt (ComplexModel d) x) hc (IsManifold.chart_mem_maximalAtlas x)
      (S x) (hSclosed x).measurableSet (fun _ hz ↦ hKc hz.1)
      (L x) (hLcompact x) (hLsource x) (fun _ hz ↦ hz.2)
  have hJint : IntegrableOn (fun z ↦ J (c.symm z)) K volume :=
    (hJcont.comp_continuousOn (c.symm.continuousOn.mono hKc)).integrableOn_compact hK
  calc
    _ ≤ ∫ z in K, (ρ z₀)⁻¹ * w z := by
      apply setIntegral_mono_on hJint (hwint.const_mul _) hK.measurableSet
      intro z hz
      have hmz : ρ z₀ ≤ ρ z := hmin hz
      have hb := mul_le_mul_of_nonneg_left hmz (hJpos (c.symm z)).le
      change J (c.symm z) ≤ (ρ z₀)⁻¹ * (J (c.symm z) * ρ z)
      apply (le_inv_mul_iff₀ hm).mpr
      simpa only [mul_comm] using hb
    _ = (ρ z₀)⁻¹ * ∫ z in K, w z := integral_const_mul _ _
    _ ≤ (ρ z₀)⁻¹ * ∑ x ∈ t, mass x := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hm.le)
    _ ≤ _ := le_max_right _ _

end
end HolomorphicAnosov
