import HolomorphicAnosov.Analysis.Calculus.ParameterSpatialIteratedDerivative
import HolomorphicAnosov.Analysis.Distribution.FixedSupportParameterTaylorRemainder
import HolomorphicAnosov.Analysis.Distribution.FixedSupportFiniteOrderBound
import HolomorphicAnosov.Analysis.Distribution.FixedSupportSeminormRemainder
import HolomorphicAnosov.Analysis.Distribution.FixedSupportParameterDerivativeTests

/-!
# First parameter derivative of a fixed-support distribution pairing

Source: Dyatlov, *Lecture notes for 18.155* (2 October 2026), Proposition 6.3,
pp.68--69, equations (6.7)--(6.9).  This module isolates the first
Fréchet-derivative step from the higher-order induction.  The compact-support
finite-order estimate controls the Taylor remainder uniformly on the fixed
compact support, and the segment fundamental theorem of calculus identifies the
linear term with the distribution paired against the parameter derivative.

DAG node: `analysis.distribution_fixed_support_first_derivative_g10`.
-/

noncomputable section
open Set Filter
open scoped Topology _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov.Analysis

/-- The source first-derivative step for a nonempty fixed-support parameter domain.

For each parameter point, the derivative of the scalar distribution pairing is a
continuous real-linear map whose value in every direction is represented by a
fixed-support test function obtained by differentiating `H` in that direction.
This is the reusable analytic step used by the higher-order smoothness induction.
-/
theorem distribution_pairing_fixed_support_first_derivative
    {m k : ℕ} (_hm : 0 < m) (_hk : 0 < k)
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))
    (P : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)))
    (_hP : (P : Set (EuclideanSpace ℝ (Fin k))).Nonempty)
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsCompact K) (hKU : K ⊆ U)
    (H : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) → ℂ)
    (hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)))
    (hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K)
    (sections : EuclideanSpace ℝ (Fin k) → TestFunction U ℂ ⊤)
    (hSections : ∀ p ∈ P, ∀ y, sections p y = H p y) :
    ∀ p ∈ P, ∃ L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℂ,
      HasFDerivWithinAt (fun q ↦ T (sections q)) L (P : Set _) p ∧
      ∀ v, ∃ differentiatedSection : TestFunction U ℂ ⊤,
        (∀ y, differentiatedSection y =
          (fderivWithin ℝ (fun q ↦ H q y) (P : Set _) p) v) ∧
        L v = T differentiatedSection := by
  let J (i : ℕ) (z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) :=
    iteratedFDerivWithin ℝ i (H z.1) (U : Set _) z.2
  have hJ (i : ℕ) : ContDiffOn ℝ ∞ (J i) ((P : Set _) ×ˢ (U : Set _)) := by
    induction i with
    | zero =>
      exact ContDiffOn.continuousLinearMap_comp
        (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin m)) ℂ).symm.toContinuousLinearMap hH
    | succ i ih =>
      intro z hz
      have hf : ContDiffWithinAt ℝ ∞
          (Function.uncurry (fun z : EuclideanSpace ℝ (Fin k) ×
            EuclideanSpace ℝ (Fin m) ↦ fun y ↦ J i (z.1, y)))
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
  have hA (i : ℕ) : ContDiffOn ℝ ∞
      (fun z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) ↦
        fderiv ℝ (fun q ↦ J i (q,z.2)) z.1) ((P : Set _) ×ˢ (U : Set _)) := by
    intro z hz
    have hg : ContDiff ℝ ∞ (fun w :
        (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) ×
          EuclideanSpace ℝ (Fin k) ↦ (w.2,w.1.2)) :=
      contDiff_snd.prodMk contDiff_fst.snd
    have hbase : ContDiffAt ℝ ∞
        (Function.uncurry (fun w : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m) ↦
          fun q ↦ J i (q,w.2))) (z,z.1) :=
      ((hJ i).contDiffAt ((P.isOpen.prod U.isOpen).mem_nhds hz)).comp (z,z.1) hg.contDiffAt
    exact (hbase.fderiv (m := ∞) contDiffAt_fst (by simp)).contDiffWithinAt
  have hTaylor (i : ℕ) (Q : Set (EuclideanSpace ℝ (Fin k))) (hQ : IsCompact Q)
      (hcQ : Convex ℝ Q) (hQP : Q ⊆ P) :
      ∀ ε > 0, ∃ δ > 0, ∀ q ∈ Q, ∀ r ∈ Q, ∀ y ∈ K, dist r q < δ →
        ‖J i (r,y) - J i (q,y) - fderiv ℝ (fun t ↦ J i (t,y)) q (r-q)‖ ≤
          ε * ‖r-q‖ := by
    apply uniform_parameter_taylor_remainder (fun q y ↦ J i (q,y)) Q K hQ hK hcQ
    · intro q hq y hy
      have hj := (hJ i).contDiffAt (x := (q,y)) ((P.isOpen.prod U.isOpen).mem_nhds ⟨hQP hq, hKU hy⟩)
      exact (hj.comp q (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    · exact (hA i).continuousOn.mono (Set.prod_mono hQP hKU)
  have hTaylorFinite (s : Finset ℕ) (Q : Set (EuclideanSpace ℝ (Fin k)))
      (hQ : IsCompact Q) (hcQ : Convex ℝ Q) (hQP : Q ⊆ P) :
      ∀ ε > 0, ∃ δ > 0, ∀ i ∈ s, ∀ q ∈ Q, ∀ r ∈ Q, ∀ y ∈ K, dist r q < δ →
        ‖J i (r,y) - J i (q,y) - fderiv ℝ (fun t ↦ J i (t,y)) q (r-q)‖ ≤
          ε * ‖r-q‖ := by
    intro ε hε
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨δ₁, hδ₁, hb₁⟩ := hTaylor i Q hQ hcQ hQP ε hε
      obtain ⟨δ₂, hδ₂, hb₂⟩ := ih
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro j hj q hq r hr y hy hd
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hb₁ q hq r hr y hy (hd.trans_le (min_le_left _ _))
      · exact hb₂ j hj q hq r hr y hy (hd.trans_le (min_le_right _ _))
  intro p hp
  classical
  have hex (v : EuclideanSpace ℝ (Fin k)) : ∃ f : TestFunction U ℂ ⊤,
      (∀ y, f y = (fderivWithin ℝ (fun q ↦ H q y) (P : Set _) p) v) ∧
      tsupport (f : EuclideanSpace ℝ (Fin m) → ℂ) ⊆ K := by
    obtain ⟨f, hf, hs⟩ := fixed_support_parameter_derivative_test U P K hK hKU H hH hSupport
      1 (fun _ ↦ v) p hp
    refine ⟨f, ?_, hs⟩
    simpa only [iteratedFDerivWithin_one_apply (P.isOpen.uniqueDiffWithinAt (𝕜 := ℝ) hp),
      fderivWithin_of_isOpen P.isOpen hp] using hf
  choose θ hθ hsupp using hex
  have hθjet (i : ℕ) (v : EuclideanSpace ℝ (Fin k))
      (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ U) :
      iteratedFDeriv ℝ i (θ v) y = fderiv ℝ (fun q ↦ J i (q,y)) p v := by
    rw [← iteratedFDerivWithin_of_isOpen i U.isOpen hy]
    have heq : (θ v : EuclideanSpace ℝ (Fin m) → ℂ) =
        fun z ↦ fderiv ℝ (fun q ↦ H q z) p v := by
      funext z
      rw [hθ v z, fderivWithin_of_isOpen P.isOpen hp]
    rw [heq]
    exact parameter_spatial_iteratedFDerivWithin_commute (F := Function.uncurry H) P.isOpen U.isOpen hJ v i p hp y hy
  obtain ⟨s, C, hC, hboundT⟩ := distribution_fixed_support_finite_order_bound U T K hK hKU
  obtain ⟨ρ, hρ, hρP⟩ := Metric.mem_nhds_iff.mp (P.isOpen.mem_nhds hp)
  let Q := Metric.closedBall p (ρ / 2)
  have hQ : IsCompact Q := isCompact_closedBall _ _
  have hcQ : Convex ℝ Q := convex_closedBall _ _
  have hpQ : p ∈ Q := Metric.mem_closedBall_self (le_of_lt (half_pos hρ))
  have hQP : Q ⊆ P := by
    intro q hq
    apply hρP
    exact (Metric.mem_closedBall.mp hq).trans_lt (half_lt_self hρ)
  have hfiniteTaylor := hTaylorFinite s Q hQ hcQ hQP
  let D : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] TestFunction U ℂ ⊤ :=
    { toFun := θ
      map_add' := by
        intro v w
        ext y
        rw [show (θ (v+w)) y = (fderivWithin ℝ (fun q ↦ H q y) (P : Set _) p) (v+w) from hθ _ _,
          show (θ v + θ w) y = (θ v) y + (θ w) y from rfl, hθ, hθ]
        exact map_add _ _ _
      map_smul' := by
        intro c v
        ext y
        rw [show (θ (c • v)) y = (fderivWithin ℝ (fun q ↦ H q y) (P : Set _) p) (c • v) from hθ _ _,
          show ((RingHom.id ℝ) c • θ v) y = c • (θ v) y by rfl, hθ]
        exact map_smul _ _ _ }
  let L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] ℂ := (T.restrictScalars ℝ).toLinearMap.comp D
  refine ⟨⟨L, L.continuous_of_finiteDimensional⟩, ?_, ?_⟩
  · rw [hasFDerivWithinAt_iff_tendsto]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hCpos : (0 : ℝ) < C := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC)
    obtain ⟨δ,hδ,hδbound⟩ := hfiniteTaylor (ε / (2 * C)) (div_pos hε (mul_pos (by norm_num) hCpos))
    have hn : Metric.ball p (min δ (ρ / 2)) ∈ 𝓝[(P : Set _)] p :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds p (lt_min hδ (half_pos hρ)))
    filter_upwards [hn, self_mem_nhdsWithin] with q hq hqP
    have hdq : dist q p < δ := hq.trans_le (min_le_left _ _)
    have hqQ : q ∈ Q := Metric.mem_closedBall.mpr (le_of_lt (hq.trans_le (min_le_right _ _)))
    let R : TestFunction U ℂ ⊤ := sections q - sections p - θ (q-p)
    have hRzero : EqOn (R : EuclideanSpace ℝ (Fin m) → ℂ) 0 Kᶜ := by
      intro y hy
      have hqz : sections q y = 0 := (hSections q hqP y).trans
        (image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hSupport q hqP h)))
      have hpz : sections p y = 0 := (hSections p hp y).trans
        (image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hSupport p hp h)))
      have hθz : θ (q-p) y = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hy (hsupp (q-p) h))
      change sections q y - sections p y - θ (q-p) y = 0
      rw [hqz,hpz,hθz]; simp
    let R' : ContDiffMapSupportedIn (EuclideanSpace ℝ (Fin m)) ℂ ⊤ ⟨K,hK⟩ :=
      ⟨R,R.contDiff,hRzero⟩
    have hjetR (i : ℕ) (hi : i ∈ s) :
        ContDiffMapSupportedIn.seminorm ℂ _ ℂ ⊤ ⟨K,hK⟩ i R' ≤
          (ε / (2 * C)) * ‖q-p‖ := by
      apply (R'.seminorm_top_le_iff ℂ (mul_nonneg (le_of_lt (div_pos hε (mul_pos (by norm_num) hCpos))) (norm_nonneg _)) i).mpr
      intro y hy
      change ‖iteratedFDeriv ℝ i ((sections q : EuclideanSpace ℝ (Fin m) → ℂ) -
        (sections p : EuclideanSpace ℝ (Fin m) → ℂ) - (θ (q-p) : EuclideanSpace ℝ (Fin m) → ℂ)) y‖ ≤ _
      rw [iteratedFDeriv_sub_apply, iteratedFDeriv_sub_apply, hθjet i (q-p) y (hKU hy)]
      · have hsq : (sections q : EuclideanSpace ℝ (Fin m) → ℂ) = H q := funext (hSections q hqP)
        have hsp : (sections p : EuclideanSpace ℝ (Fin m) → ℂ) = H p := funext (hSections p hp)
        rw [hsq,hsp, ← iteratedFDerivWithin_of_isOpen i U.isOpen (hKU hy),
          ← iteratedFDerivWithin_of_isOpen i U.isOpen (hKU hy)]
        exact hδbound i hi p hpQ q hqQ y hy hdq
      · exact ((sections q).contDiff.of_le (by simp)).contDiffAt
      · exact ((sections p).contDiff.of_le (by simp)).contDiffAt
      · exact (((sections q).contDiff.sub (sections p).contDiff).of_le (by simp)).contDiffAt
      · exact ((θ (q-p)).contDiff.of_le (by simp)).contDiffAt
    have hscalar := distribution_pairing_fixed_support_seminorm_remainder U T K hK hKU s C hboundT R'
      ((ε / (2 * C)) * ‖q-p‖)
      (mul_nonneg (le_of_lt (div_pos hε (mul_pos (by norm_num) hCpos))) (norm_nonneg _)) hjetR
    have hvalue : T (TestFunction.ofSupportedIn hKU R') = T (sections q) - T (sections p) - L (q-p) := by
      change T (sections q - sections p - θ (q-p)) =
        T (sections q) - T (sections p) - T (θ (q-p))
      rw [map_sub,map_sub]
    rw [hvalue] at hscalar
    change dist (‖q-p‖⁻¹ * ‖T (sections q) - T (sections p) - L (q-p)‖) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))]
    by_cases hqp : q = p
    · simp [hqp,hε]
    · have hnorm : 0 < ‖q-p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hqp)
      calc
        _ ≤ ‖q-p‖⁻¹ * ((C : ℝ) * ((ε / (2 * C)) * ‖q-p‖)) :=
          mul_le_mul_of_nonneg_left hscalar (inv_nonneg.mpr (norm_nonneg _))
        _ = ε / 2 := by field_simp
        _ < ε := half_lt_self hε
  · intro v
    exact ⟨θ v, hθ v, rfl⟩

end HolomorphicAnosov.Analysis

