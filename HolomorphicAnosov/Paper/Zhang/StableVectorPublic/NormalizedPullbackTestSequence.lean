import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.NormalizedPullbackPreparation
import HolomorphicAnosov.Geometry.ContinuousOriginalNorm
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealTangentSmooth
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.SmoothNormalizedSection
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.EventualConormBound
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.NormalizedPullbackConvergence
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.FrameDolbeaultCoordinates
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.HermitianDolbeaultSquareBound
import HolomorphicAnosov.Paper.Zhang.StableVectorPublic.NativeTopFormChartIntegral

open scoped ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov
noncomputable section
universe u
open Bundle Filter MeasureTheory DistributionalSection
open scoped Topology Manifold

open Bundle Filter MeasureTheory DistributionalSection in
open scoped Topology in
/-- The normalized stable section admits smooth approximating sections whose coefficients converge
uniformly on compact test supports and whose Wirtinger derivatives tend to zero in L² there.
(Zhang, Lemma 4.3, eqs. (24)–(31)) -/
theorem normalized_pullback_test_sequence
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    (hd : 3 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hS_real : ∀ x, ((S x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.stable.toDistribution x)
    (hU_real : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hcompl : ∀ x, IsCompl (S x) (U x))
    (hrank : ∀ x, Module.finrank ℂ (S x) = 1)
    (hS_invariant : ∀ x, (S x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = S (f x))
    (hU_invariant : ∀ x, (U x).map
      (mfderiv (complexModel d) (complexModel d) f x).toLinearMap = U (f x))
    (θ : (x : X) → TangentSpace (complexModel d) x →L[ℂ] ℂ)
    (hθ_holomorphic : ∀ c : OpenPartialHomeomorph X (ComplexModel d),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ∀ j : Fin d, DifferentiableOn ℂ
        (fun z ↦ θ (c.symm z) (hermitianTangentChartFrame c z j)) c.target)
    (hθ_nonzero : ∀ x, θ x ≠ 0)
    (hθ_kernel : ∀ x, LinearMap.ker (θ x).toLinearMap = U x)
    (μ : ℂ) (hμ_pos : 0 < ‖μ‖) (hμ_lt : ‖μ‖ < 1)
    (hθ_pullback : ∀ x (v : TangentSpace (complexModel d) x),
      θ (f x) (mfderiv (complexModel d) (complexModel d) f x v) = μ * θ x v)
    (e : (x : X) → TangentSpace (complexModel d) x)
    (he_continuous : Continuous
      (fun x ↦ (⟨x, e x⟩ : TangentBundle (complexModel d) X)))
    (he_stable : ∀ x, e x ∈ S x)
    (he_normalized : ∀ x, θ x (e x) = 1) :
    ∃ sn : ℕ → (x : X) → TangentSpace (complexModel d) x,
      ∀ (c : OpenPartialHomeomorph X (ComplexModel d)),
        c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
        ∀ (fr : Trivialization (ComplexModel d)
          (TotalSpace.proj : TangentBundle (complexModel d) X → X)),
          IsHolomorphicFrame (d := d) fr → ∀ k : Fin d,
          (∀ n, ContDiffOn ℝ ∞ (coefficient (sn n) c fr k) (frameDomain c fr)) ∧
          (∀ φ : TestFunction (frameDomain c fr) ℂ ⊤,
            ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
              ∀ᶠ n in atTop, ∀ z ∈ tsupport φ,
                ‖coefficient (sn n) c fr k z - coefficient e c fr k z‖ ≤ ε n) ∧
          (∀ (j : Fin d) (φ : TestFunction (frameDomain c fr) ℂ ⊤),
            Tendsto (fun n ↦ ∫ z in tsupport φ,
              ‖(2 : ℂ)⁻¹ * (fderiv ℝ (coefficient (sn n) c fr k) z (Pi.single j 1) +
                Complex.I * fderiv ℝ (coefficient (sn n) c fr k) z
                  (Pi.single j Complex.I))‖ ^ 2 ∂volume) atTop (𝓝 0)) := by
  classical
  let : VectorBundle ℝ (ComplexModel d) (TangentSpace (complexModel d) : X → Type _) :=
    OneFormBundle.real_vector_bundle
  let : ContMDiffVectorBundle ∞ (ComplexModel d) (TangentSpace (complexModel d) : X → Type _)
      (realModel d) := OneFormBundle.real_tangent_smooth
  have hθ : IsHolomorphicComplexOneForm θ := by
    intro c hc j
    have hscalar : ContDiffOn ℂ ∞
        (fun z (_ : Fin 1) ↦ θ (c.symm z) (hermitianTangentChartFrame c z j)) c.target :=
      (complex_contDiffOn_iff_differentiableOn c.open_target).mpr
        (differentiableOn_pi.mpr (fun _ ↦ hθ_holomorphic c hc j))
    exact (contDiffOn_pi.mp hscalar) 0
  have hμ : μ ≠ 0 := norm_pos_iff.mp hμ_pos
  obtain ⟨e₀, he₀smooth, he₀normalized⟩ :=
    exists_smooth_normalized_tangent_section θ hθ hθ_nonzero
  have he₀coeff := (smooth_section_iff_preferred_coefficients e₀).mp he₀smooth
  have he₀chart := smooth_section_tangent_chart_coefficient e₀ he₀smooth
  obtain ⟨⟨h, hh, hunit, horth⟩, hjacobian⟩ := normalized_hermitian_jacobian
    θ hθ hθ_nonzero e₀ he₀chart he₀normalized f μ hμ hθ_pullback
  obtain ⟨g, hgpos, hgcont, hgcontract⟩ :=
    anosov_original_complex_block_bounds f a S U hS_real hU_real
  have hUrank : ∀ x, 0 < Module.finrank ℂ (U x) := by
    intro x
    have hdim := Submodule.finrank_add_eq_of_isCompl (hcompl x)
    rw [hrank x] at hdim
    have htdim : Module.finrank ℂ (TangentSpace (complexModel d) x) = d := by
      change Module.finrank ℂ (ComplexModel d) = d
      simp [ComplexModel]
    rw [htdim] at hdim
    omega
  obtain ⟨A, B, lam, hA, hB, hlam, hoperators⟩ :=
    compact_anosov_hermitian_operator_bounds f S U a.splitting.stable a.splitting.unstable
      hS_real hU_real hcompl hS_invariant hU_invariant hUrank g hgpos hgcont
      a.k a.one_le_k hgcontract h hh

  let sn : ℕ → (x : X) → TangentSpace (complexModel d) x := fun n x ↦
    μ ^ n • (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x).inverse
      (e₀ ((f : X → X)^[n] x))
  obtain ⟨hF, B₀, hB₀, hB₀smooth, hpull⟩ :=
    normalized_vector_dolbeault_pullback f θ hθ hθ_nonzero μ hμ hθ_pullback
      e₀ he₀coeff he₀normalized
  have hsmooth (n : ℕ) : ContMDiff (realModel d)
      ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
      (fun x ↦ TotalSpace.mk' (ComplexModel d) x (sn n x)) :=
    (smooth_section_iff_preferred_coefficients (sn n)).mpr (hpull n).1
  let p := HermitianFibreAlgebra.hermitianBoundsRealSeminorm h
  have hp : Continuous (fun z : TangentBundle (complexModel d) X ↦ p z.proj z.snd) :=
    Preparation.continuous_hermitian_tangent_norm h hh
  have hppos : ∀ x v, v ≠ 0 → 0 < p x v :=
    fun x _ hv ↦ HermitianFibreAlgebra.coreLength_pos (h x) hv
  have hdiffcont : Continuous (fun x ↦
      TotalSpace.mk' (ComplexModel d) x (e₀ x - e x)) := by
    have hezero : ContMDiff (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) 0
        (fun x ↦ TotalSpace.mk' (ComplexModel d) x (e x)) :=
      contMDiff_zero_iff.mpr he_continuous
    exact ((he₀smooth.of_le (show (0 : ℕ∞ω) ≤ ∞ from bot_le)).sub_section hezero).continuous
  obtain ⟨L, hL⟩ := isCompact_univ.bddAbove_image (hp.comp hdiffcont).continuousOn
  have herror : ∀ x, hermitianBoundsNorm h x (e₀ x - e x) ≤ L := by
    intro x
    exact hL (Set.mem_image_of_mem _ (Set.mem_univ x))
  have hconvergence := (normalized_stable_pullback_convergence f S U hcompl hS_invariant
    θ hθ_kernel μ hμ_lt hθ_pullback e e₀ he_stable he_normalized he₀normalized
    h hh A L lam (zero_le_one.trans hA) hlam herror
    (fun n x ↦ (hoperators n x).2.1)).1
  let ε := fun n : ℕ ↦ A * L * (‖μ‖ / lam) ^ n
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (div_nonneg (norm_nonneg μ) (by linarith : 0 ≤ lam))
        ((div_lt_one (by linarith : 0 < lam)).mpr (hμ_lt.trans hlam))).const_mul (A * L)
  have hsnerror : ∀ n x, p x (sn n x - e x) ≤ ε n := by
    intro n x
    have hinv : (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x).inverse =
        (hermitianBoundsDerivative f n x).symm.toContinuousLinearMap :=
      ContinuousLinearMap.inverse_equiv (hermitianBoundsDerivative f n x)
    change hermitianBoundsNorm h x (sn n x - e x) ≤ A * L * (‖μ‖ / lam) ^ n
    dsimp only [sn]
    rw [hinv]
    exact hconvergence n x
  obtain ⟨_, η, ⟨hη, hηcoeff, hηJ⟩, _⟩ := hjacobian h hh hunit horth
  choose J hJ hJunique using hηJ
  obtain ⟨K₀, hK₀, hBbound⟩ := uniform_hermitian_antilinear_tensor_bound
    (vectorDolbeault e₀) (fun a ↦ (hB₀smooth a).continuousOn) h hh
  have hconorm := eventually_conorm_ge_one
    (fun n x ↦ fibreNormConorm (hermitianBoundsNorm h x)
      (hermitianBoundsNorm h (hermitianBoundsIterate f n x)) (U x)
      (hermitianBoundsDerivative f n x)) A lam (zero_lt_one.trans_le hA) hlam
      (fun n x ↦ (hoperators n x).2.2.1)
  have hkerdim (x : X) : Module.finrank ℂ (LinearMap.ker (θ x).toLinearMap) = d - 1 := by
    rw [hθ_kernel]
    have hdim := Submodule.finrank_add_eq_of_isCompl (hcompl x)
    rw [hrank x] at hdim
    have htdim : Module.finrank ℂ (TangentSpace (complexModel d) x) = d := by
      change Module.finrank ℂ (ComplexModel d) = d
      simp [ComplexModel]
    rw [htdim] at hdim
    omega
  have hdbarbound : ∀ᶠ n in atTop, ∀ x v,
      (p x (vectorDolbeault (sn n) x v)) ^ 2 ≤
        (A * K₀ * B) ^ 2 * ((lam ^ n)⁻¹) ^ 2 * J n x * (p x v) ^ 2 := by
    filter_upwards [hconorm] with n hn
    intro x v
    let y := hermitianBoundsIterate f n x
    let F := hermitianBoundsDerivative f n x
    obtain ⟨Un, hUn, Bn, hBn, hBnformula⟩ := (hpull n).2.2
    have hmap : (LinearMap.ker (θ x).toLinearMap).map F.toLinearMap =
        LinearMap.ker (θ y).toLinearMap := by
      ext w
      constructor
      · rintro ⟨u, hu, rfl⟩
        have he := hUn x ⟨u, hu⟩
        change (Un x ⟨u, hu⟩).val = F u at he
        change F u ∈ LinearMap.ker (θ y).toLinearMap
        rw [← he]
        exact (Un x ⟨u, hu⟩).property
      · intro hw
        refine ⟨(Un x).symm ⟨w, hw⟩, ((Un x).symm ⟨w, hw⟩).property, ?_⟩
        change F ((Un x).symm ⟨w, hw⟩) = w
        exact (hUn x ((Un x).symm ⟨w, hw⟩)).symm.trans
          (congrArg Subtype.val ((Un x).apply_symm_apply ⟨w, hw⟩))
    let hX := h x
    let hY := h y
    have hconorm' : 1 ≤ fibreNormConorm (HermitianFibreAlgebra.coreLength hX)
        (HermitianFibreAlgebra.coreLength hY) (LinearMap.ker (θ x).toLinearMap) F := by
      change 1 ≤ fibreNormConorm (hermitianBoundsNorm h x)
        (hermitianBoundsNorm h y) (LinearMap.ker (θ x).toLinearMap) F
      rw [hθ_kernel]
      exact hn x
    have hPr : Module.finrank ℂ (LinearMap.ker (θ x).toLinearMap) = d - 1 := hkerdim x
    have hQr : Module.finrank ℂ (LinearMap.ker (θ y).toLinearMap) = d - 1 := hkerdim y
    obtain ⟨bs, bt, hbs, hbt, hdet⟩ := hermitian_restricted_operator_le_det
      (V := TangentSpace (complexModel d) x) (W := TangentSpace (complexModel d) y)
      (P := LinearMap.ker (θ x).toLinearMap) (Q := LinearMap.ker (θ y).toLinearMap)
      (L := F.toLinearEquiv) (hV := h x) (hW := h y)
      (hmap := hmap) (r := d - 1)
      (hr := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 3) hd))
      (hPr := hPr) (hQr := hQr)
      (hconorm := hconorm')
    let D := ‖(LinearMap.toMatrix bs bt (F.toLinearEquiv.ofSubmodules _ _ hmap).toLinearMap).det‖
    have hdet' : fibreNormOperator (p x) (p y) (U x) F ≤ D := by
      rw [← hθ_kernel]
      exact hdet
    have hJdet : J n x = ‖μ‖ ^ (2 * n) * D ^ 2 := by
      have hj := (hJ n).2.2.2 x (Fin (d - 1)) bs bt hbs hbt
      convert hj using 2
      congr 2
      dsimp only [D]
      apply congrArg (fun z : ℂ ↦ ‖z‖)
      apply congrArg Matrix.det
      apply Matrix.ext
      intro i j
      simp only [LinearMap.toMatrix_apply, normalizedKernelMatrix]
      apply congrArg (fun u ↦ bt.repr u i)
      apply Subtype.ext
      change F (bs j) = F (bs j) - θ y (F (bs j)) • e₀ y
      have hm : F (bs j) ∈ LinearMap.ker (θ y).toLinearMap := by
        rw [← hmap]
        exact Submodule.mem_map_of_mem (bs j).property
      have hz : θ y (F (bs j)) = 0 := hm
      rw [hz, zero_smul, sub_zero]
    have hinverse (u : LinearMap.ker (θ y).toLinearMap) :
        ((Un x).symm u).val = F.symm u := by
      apply F.injective
      exact (hUn x ((Un x).symm u)).symm.trans
        ((congrArg Subtype.val ((Un x).apply_symm_apply u)).trans (F.apply_symm_apply u).symm)
    have hformula : vectorDolbeault (sn n) x v =
        μ ^ n • F.symm (vectorDolbeault e₀ y (F v)) := by
      rw [← hBn x v, hBnformula x]
      change μ ^ n • (((Un x).symm (B₀ y (F v))).val) = _
      rw [hinverse, hB₀]
    have hb := CompactHermitianAssembly.native_unit_values_bddAbove f p hp hppos n x (S x) (U y)
    have hinv := CompactHermitianBoundsScratch.pointwise_le_operator (p y) (p x) (U y)
      (F.symm.toLinearMap.restrictScalars ℝ) (hppos y) hb.2
      (show vectorDolbeault e₀ y (F v) ∈ U y from by rw [← hB₀ y (F v), ← hθ_kernel]; exact (B₀ y (F v)).property)
    have hfullb := CompactHermitianAssembly.native_unit_values_bddAbove f p hp hppos n x ⊤ (U y)
    have hfull := CompactHermitianBoundsScratch.pointwise_le_operator (p x) (p y) ⊤
      (F.toLinearMap.restrictScalars ℝ) (hppos x) hfullb.1 (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ _))
    have hi : p x (F.symm (vectorDolbeault e₀ y (F v))) ≤
        (A * (lam ^ n)⁻¹) * (K₀ * ((B * D) * p x v)) := by
      apply hinv.trans
      apply mul_le_mul
      · exact (hoperators n x).2.1
      · exact (hBbound y (F v)).trans (mul_le_mul_of_nonneg_left
          (hfull.trans (mul_le_mul_of_nonneg_right
            ((hoperators n x).2.2.2.trans (mul_le_mul_of_nonneg_left hdet' hB.le))
              (apply_nonneg (p x) v))) (zero_le_one.trans hK₀))
      · exact apply_nonneg (p y) _
      · exact mul_nonneg (zero_le_one.trans hA) (inv_nonneg.mpr (pow_nonneg (by linarith) n))
    have hnorm : p x (vectorDolbeault (sn n) x v) ≤
        ‖μ‖ ^ n * ((A * (lam ^ n)⁻¹) * (K₀ * ((B * D) * p x v))) := by
      rw [hformula]
      change HermitianFibreAlgebra.coreLength (h x) (_ • _) ≤ _
      rw [HermitianFibreAlgebra.coreLength_complex_smul, norm_pow]
      exact mul_le_mul_of_nonneg_left hi (pow_nonneg (norm_nonneg μ) n)
    calc
      _ ≤ (‖μ‖ ^ n * ((A * (lam ^ n)⁻¹) * (K₀ * ((B * D) * p x v)))) ^ 2 :=
        pow_le_pow_left₀ (apply_nonneg (p x) _) hnorm 2
      _ = _ := by rw [hJdet, pow_mul]; ring
  refine ⟨sn, fun c hc fr hfr k ↦ ⟨?_, ?_, ?_⟩⟩
  · exact fun n ↦ smooth_section_frame_coefficient (sn n) (hsmooth n) c hc fr hfr k
  · intro φ
    let : fr.IsLinear ℂ := hfr.1
    exact frame_coefficient_error_tendsto p hp hppos sn e ε hε
      (Filter.Eventually.of_forall hsnerror) c fr k φ
  · intro j φ
    let : fr.IsLinear ℂ := hfr.1
    let K := tsupport φ
    have hK : IsCompact K := φ.hasCompactSupport.isCompact
    have hKc : K ⊆ c.target := fun z hz ↦ (φ.tsupport_subset hz).1
    have hKfr : c.symm '' K ⊆ fr.baseSet := by
      rintro _ ⟨z, hz, rfl⟩
      exact (φ.tsupport_subset hz).2
    obtain ⟨Cf, hCf, hframebound⟩ := compact_frame_coefficient_bound p hp hppos fr _
      (hK.image_of_continuousOn (c.symm.continuousOn.mono hKc)) hKfr
    have hincont : ContinuousOn (fun z ↦ p (c.symm z)
        (hermitianTangentChartFrame c z j)) K := by
      have hdiag : ContinuousOn (fun z => (hermitianTangentChartCoefficient h c j j z).re) c.target :=
        Complex.continuous_re.comp_continuousOn (hh c hc j j).continuousOn
      exact (hdiag.sqrt).mono hKc
    obtain ⟨Dt, hDt⟩ := hK.bddAbove_image hincont
    let D := max 0 Dt
    have hD : 0 ≤ D := le_max_left _ _
    have hinput : ∀ z ∈ K, p (c.symm z) (hermitianTangentChartFrame c z j) ≤ D := by
      intro z hz
      exact (hDt (Set.mem_image_of_mem _ hz)).trans (le_max_right _ _)
    obtain ⟨M, hM, hmass⟩ := native_positive_jacobian_compact_chart_bound η hη c hc K hK hKc
    let C := Cf ^ 2 * (A * K₀ * B) ^ 2 * D ^ 2
    have hC : 0 ≤ C := mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
    let b := fun n z ↦ (2 : ℂ)⁻¹ *
      (fderiv ℝ (coefficient (sn n) c fr k) z (Pi.single j 1) +
        Complex.I * fderiv ℝ (coefficient (sn n) c fr k) z (Pi.single j Complex.I))
    have hbcont (n : ℕ) : ContinuousOn (b n) K := by
      have hf := ContDiffOn.continuousOn_fderiv_of_isOpen
        (smooth_section_frame_coefficient (sn n) (hsmooth n) c hc fr hfr k)
        (frameDomain c fr).isOpen (by simp)
      exact ((hf.clm_apply continuousOn_const).add
        ((hf.clm_apply continuousOn_const).const_mul Complex.I)).const_mul _ |>.mono φ.tsupport_subset
    have hJint (n : ℕ) : IntegrableOn (fun z ↦ J n (c.symm z)) K volume :=
      (((hJ n).1.continuous).comp_continuousOn
        (c.symm.continuousOn.mono hKc)).integrableOn_compact hK
    have htail : ∀ᶠ n in atTop, (∫ z in K, ‖b n z‖ ^ 2) ≤
        (C * ((lam ^ n)⁻¹) ^ 2) * M := by
      filter_upwards [hdbarbound] with n hn
      have hlocal : ∀ z ∈ K, ‖b n z‖ ^ 2 ≤ (C * ((lam ^ n)⁻¹) ^ 2) * J n (c.symm z) := by
        intro z hz
        have hsvec : ContDiffOn ℝ ∞
            (fun w ↦ fun i ↦ coefficient (sn n) c fr i w) (frameDomain c fr) :=
          contDiffOn_pi.mpr (fun i ↦ smooth_section_frame_coefficient (sn n) (hsmooth n) c hc fr hfr i)
        have hid := frame_dolbeault_scalar_coordinates (sn n)
          ((smooth_section_iff_preferred_coefficients (sn n)).mp (hsmooth n))
          c hc fr hfr z (φ.tsupport_subset hz)
          ((hsvec.contDiffAt ((frameDomain c fr).isOpen.mem_nhds
            (φ.tsupport_subset hz))).differentiableAt (by simp)) j k
        change ‖b n z‖ ^ 2 ≤ _
        dsimp only [b]
        rw [hid]
        have hfb := hframebound (c.symm z) (Set.mem_image_of_mem _ hz)
          (vectorDolbeault (sn n) (c.symm z) (hermitianTangentChartFrame c z j)) k
        calc
          _ ≤ (Cf * p (c.symm z) (vectorDolbeault (sn n) (c.symm z)
              (hermitianTangentChartFrame c z j))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hfb 2
          _ = Cf ^ 2 * (p (c.symm z) (vectorDolbeault (sn n) (c.symm z)
              (hermitianTangentChartFrame c z j))) ^ 2 := mul_pow _ _ _
          _ ≤ Cf ^ 2 * ((A * K₀ * B) ^ 2 * ((lam ^ n)⁻¹) ^ 2 * J n (c.symm z) *
              (p (c.symm z) (hermitianTangentChartFrame c z j)) ^ 2) :=
            mul_le_mul_of_nonneg_left (hn _ _) (sq_nonneg _)
          _ ≤ Cf ^ 2 * ((A * K₀ * B) ^ 2 * ((lam ^ n)⁻¹) ^ 2 * J n (c.symm z) * D ^ 2) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (apply_nonneg (p (c.symm z)) _) (hinput z hz) 2)
                (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) ((hJ n).2.1 _).le))
              (sq_nonneg _)
          _ = _ := by dsimp only [C]; ring
      calc
        _ ≤ ∫ z in K, (C * ((lam ^ n)⁻¹) ^ 2) * J n (c.symm z) :=
          setIntegral_mono_on ((hbcont n).norm.pow 2 |>.integrableOn_compact hK)
            ((hJint n).const_mul _) hK.measurableSet hlocal
        _ = (C * ((lam ^ n)⁻¹) ^ 2) * ∫ z in K, J n (c.symm z) := integral_const_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (hmass (hermitianBoundsIterate f n) (J n) (hJ n).1.continuous
            (hJ n).2.1 (hJ n).2.2.1) (mul_nonneg hC (sq_nonneg _))
    have hdecay : Tendsto (fun n : ℕ ↦ (C * ((lam ^ n)⁻¹) ^ 2) * M) atTop (𝓝 0) := by
      have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
        (inv_nonneg.mpr (by linarith : 0 ≤ lam)) (inv_lt_one_of_one_lt₀ hlam)
      simpa only [inv_pow, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] using
        ((ht.pow 2).const_mul C).mul_const M
    exact squeeze_zero' (Eventually.of_forall fun n ↦ integral_nonneg fun z ↦ sq_nonneg _) htail hdecay

end
end HolomorphicAnosov
