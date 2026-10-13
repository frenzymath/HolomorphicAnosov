import HolomorphicAnosov.Analysis.Regularity.JourneInverseHigherHolder
import HolomorphicAnosov.Analysis.Regularity.JournePlaqueHigherHolder
import HolomorphicAnosov.Analysis.Regularity.JourneApproximatesLinearImageCore
import HolomorphicAnosov.Analysis.Regularity.JourneLipschitzInverseContDiff
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set
open scoped NNReal _root_.Topology

/-- Restrict full finite Hölder bounds to a smaller domain. -/
theorem HasFiniteHolderBounds.mono
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {α K : ℝ} {S T : Set E} {f : E → F}
    (hf : HasFiniteHolderBounds n α K f S) (hTS : T ⊆ S) :
    HasFiniteHolderBounds n α K f T :=
  ⟨hf.1.mono hTS,fun j hj x hx ↦ hf.2.1 j hj x (hTS hx),
    fun x hx y hy ↦ hf.2.2 x (hTS hx) y (hTS hy)⟩

/-- Restriction to an open set preserves ordinary full Hölder bounds. -/
theorem HasFiniteHolderBounds.congr_open
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {α K : ℝ} {S : Set E} (hS : IsOpen S) {f g : E → F}
    (hf : HasFiniteHolderBounds n α K f S) (heq : EqOn g f S) :
    HasFiniteHolderBounds n α K g S := by
  have he (z : E) (hz : z ∈ S) (j : ℕ) :
      iteratedFDeriv ℝ j g z = iteratedFDeriv ℝ j f z := by
    have H : g =ᶠ[𝓝 z] f := by
      filter_upwards [hS.mem_nhds hz] with y hy
      exact heq hy
    exact (H.iteratedFDeriv ℝ j).self_of_nhds
  refine ⟨hf.1.congr heq,fun j hj z hz ↦ ?_,fun x hx y hy ↦ ?_⟩
  · rw [he z hz j]
    exact hf.2.1 j hj z hz
  · rw [he x hx n,he y hy n]
    exact hf.2.2 x hx y hy

/-- Translation of the source preserves every ordinary derivative norm and the top Hölder seminorm on a domain mapped into the original one. -/
theorem HasFiniteHolderBounds.comp_translation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {α K : ℝ} {S T : Set E} {f : E → F}
    (hf : HasFiniteHolderBounds n α K f S) (a : E)
    (hm : MapsTo (fun x ↦ a+x) T S) :
    HasFiniteHolderBounds n α K (fun x ↦ f (a+x)) T := by
  refine ⟨hf.1.comp (contDiffOn_const.add contDiffOn_id) hm,?_,?_⟩
  · intro j hj x hx
    rw [iteratedFDeriv_comp_add_left]
    exact hf.2.1 j hj _ (hm hx)
  · intro x hx y hy
    rw [iteratedFDeriv_comp_add_left,iteratedFDeriv_comp_add_left]
    simpa only [add_sub_add_left_eq_sub] using hf.2.2 _ (hm hx) _ (hm hy)

/-- A two-point bound on an open graph domain gives the same operator bound. -/
theorem graph_fderiv_bound_of_lipschitz
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set D} (hS : IsOpen S) {φ : D → E} {ε : ℝ} (hε : 0 ≤ ε)
    (hφ : ∀ u ∈ S, ∀ v ∈ S, ‖φ u-φ v‖ ≤ ε*‖u-v‖) :
    ∀ u ∈ S, ‖fderiv ℝ φ u‖ ≤ ε := by
  intro u hu
  apply norm_fderiv_le_of_lip' ℝ hε
  filter_upwards [hS.mem_nhds hu] with v hv
  exact hφ v hv u hu

/-- Subtracting the graph anchor and scaling both axes preserves its slope. -/
theorem normalized_graph_lipschitz
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set D} (φ : D → E) {ε t : ℝ} (ht : 0 < t)
    (hφ : ∀ u ∈ S, ∀ v ∈ S, ‖φ u-φ v‖ ≤ ε*‖u-v‖) :
    ∀ u, t • u ∈ S → ∀ v, t • v ∈ S →
      ‖t⁻¹ • (φ (t • u)-φ 0)-t⁻¹ • (φ (t • v)-φ 0)‖ ≤ ε*‖u-v‖ := by
  intro u hu v hv
  rw [← smul_sub,sub_sub_sub_cancel_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
  calc
    t⁻¹*‖φ (t • u)-φ (t • v)‖ ≤ t⁻¹*(ε*‖t • u-t • v‖) :=
      mul_le_mul_of_nonneg_left (hφ _ hu _ hv) (inv_nonneg.mpr ht.le)
    _ = ε*‖u-v‖ := by
      rw [← smul_sub,norm_smul,Real.norm_of_nonneg ht.le]
      field_simp

/-- A plaque whose derivative is within one quarter of the first coordinate inclusion has an invertible first projection on its source ball, a common receiving ball of radius R/4, and inverse Lipschitz constant two. (Journé, 1988) -/
theorem regraph_first_projection
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (hn : 1 ≤ n) (Q : D → D × E) (x : D) (R : ℝ) (hR : 0 < R)
    (ε : ℝ) (hε : 0 ≤ ε) (hεquarter : ε ≤ 1/4)
    (hQ : ContDiffOn ℝ n Q (Metric.ball x R))
    (hDQ : ∀ z ∈ Metric.ball x R,
      ‖fderiv ℝ Q z - ContinuousLinearMap.inl ℝ D E‖ ≤ ε) :
    ∃ e : OpenPartialHomeomorph D D,
      (e : D → D) = (fun z ↦ (Q z).1) ∧ e.source = Metric.ball x R ∧
      Metric.ball (Q x).1 (R / 4) ⊆ e.target ∧
      ContDiffOn ℝ n e.symm (Metric.ball (Q x).1 (R / 4)) ∧
      (∀ u ∈ Metric.ball (Q x).1 (R / 4), ∀ v ∈ Metric.ball (Q x).1 (R / 4),
        ‖e.symm u - e.symm v‖ ≤ 2 * ‖u-v‖) ∧
      (∀ y ∈ Metric.ball (Q x).1 (R / 4), (Q (e.symm y)).1 = y) ∧
      ∀ u ∈ Metric.ball (Q x).1 (R / 4), ∀ v ∈ Metric.ball (Q x).1 (R / 4),
        ‖(Q (e.symm u)).2 - (Q (e.symm v)).2‖ ≤ (2 * ε) * ‖u-v‖ := by
  let f : D → D := fun z ↦ (Q z).1
  let A : D ≃L[ℝ] D := ContinuousLinearEquiv.refl ℝ D
  have hdiff (z : D) (hz : z ∈ Metric.ball x R) : DifferentiableAt ℝ Q z :=
    (hQ.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt
      (by exact_mod_cast (show n ≠ 0 by omega))
  have hfd (z : D) (hz : z ∈ Metric.ball x R) :
      HasFDerivAt f ((ContinuousLinearMap.fst ℝ D E).comp (fderiv ℝ Q z)) z :=
    (ContinuousLinearMap.fst ℝ D E).hasFDerivAt.comp z (hdiff z hz).hasFDerivAt
  have hbound (z : D) (hz : z ∈ Metric.ball x R) :
      ‖((ContinuousLinearMap.fst ℝ D E).comp (fderiv ℝ Q z)) - A.toContinuousLinearMap‖ ≤
        (1 / 4 : ℝ) := by
    have heq : ((ContinuousLinearMap.fst ℝ D E).comp (fderiv ℝ Q z)) -
        A.toContinuousLinearMap = (ContinuousLinearMap.fst ℝ D E).comp
          (fderiv ℝ Q z - ContinuousLinearMap.inl ℝ D E) := by
      simp [A, ContinuousLinearMap.comp_sub]
    rw [heq]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [ContinuousLinearMap.norm_fst_le ℝ D E, hDQ z hz,
        norm_nonneg (fderiv ℝ Q z - ContinuousLinearMap.inl ℝ D E)])
  have happ : ApproximatesLinearOn f A.toContinuousLinearMap (Metric.ball x R) (1 / 4) := by
    intro u hu v hv
    exact (convex_ball x R).norm_image_sub_le_of_norm_fderiv_le'
      (fun z hz ↦ (hfd z hz).differentiableAt)
      (fun z hz ↦ by rw [(hfd z hz).fderiv]; exact hbound z hz) hv hu
  have hnorm : ‖A.symm.toContinuousLinearMap‖₊ = 1 := by simp [A]
  have hsmall : Subsingleton D ∨ (1 / 4 : ℝ≥0) < ‖A.symm.toContinuousLinearMap‖₊⁻¹ := by
    right
    rw [hnorm]
    norm_num
  obtain ⟨e, he, hs, htarget⟩ := approximates_linear_image_core f x A R hR (1 / 4) hsmall happ
  have hrecv : Metric.ball (Q x).1 (R / 4) ⊆ e.target := by
    apply Set.Subset.trans (Metric.ball_subset_ball ?_) htarget
    rw [hnorm]
    norm_num
    linarith
  have hlip : ∀ u ∈ Metric.ball (Q x).1 (R / 4),
      ∀ v ∈ Metric.ball (Q x).1 (R / 4),
        ‖e.symm u - e.symm v‖ ≤ 2 * ‖u-v‖ := by
    intro u hu v hv
    have hu' := e.map_target (hrecv hu)
    have hv' := e.map_target (hrecv hv)
    rw [hs] at hu' hv'
    have hb := (happ.antilipschitz hsmall).le_mul_dist
      ⟨e.symm u, hu'⟩ ⟨e.symm v, hv'⟩
    change dist (e.symm u) (e.symm v) ≤
      (((‖A.symm.toContinuousLinearMap‖₊⁻¹ - (1 / 4 : ℝ≥0))⁻¹ : ℝ≥0) : ℝ) *
        dist (f (e.symm u)) (f (e.symm v)) at hb
    rw [← he, e.right_inv (hrecv hu), e.right_inv (hrecv hv), hnorm] at hb
    have hquarter : (1 / 4 : ℝ≥0) ≤ 1 := by
      apply (div_le_one (by norm_num)).mpr
      norm_num
    rw [inv_one, NNReal.coe_inv, NNReal.coe_sub hquarter] at hb
    norm_num at hb
    rw [← dist_eq_norm, ← dist_eq_norm]
    nlinarith [show 0 ≤ dist u v from dist_nonneg]
  have hsmooth : ContDiffOn ℝ n e e.source := by
    rw [he, hs]
    exact contDiff_fst.comp_contDiffOn hQ
  refine ⟨e, he, hs, hrecv, ?_, hlip, ?_, ?_⟩
  · exact HolomorphicAnosov.contDiffOn_inverse_of_lipschitzOn rfl e hn hsmooth
      Metric.isOpen_ball hrecv hlip
  · intro y hy
    change f (e.symm y) = y
    rw [← he]
    exact e.right_inv (hrecv hy)
  · intro u hu v hv
    have hsd (z : D) (hz : z ∈ Metric.ball x R) :
        HasFDerivAt (fun z ↦ (Q z).2)
          ((ContinuousLinearMap.snd ℝ D E).comp (fderiv ℝ Q z)) z :=
      (ContinuousLinearMap.snd ℝ D E).hasFDerivAt.comp z (hdiff z hz).hasFDerivAt
    have hsbound (z : D) (hz : z ∈ Metric.ball x R) :
        ‖fderiv ℝ (fun z ↦ (Q z).2) z‖ ≤ ε := by
      rw [(hsd z hz).fderiv]
      have heq : (ContinuousLinearMap.snd ℝ D E).comp (fderiv ℝ Q z) =
          (ContinuousLinearMap.snd ℝ D E).comp
            (fderiv ℝ Q z - ContinuousLinearMap.inl ℝ D E) := by
        simp [ContinuousLinearMap.comp_sub]
      rw [heq]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by nlinarith [ContinuousLinearMap.norm_snd_le ℝ D E, hDQ z hz,
          norm_nonneg (fderiv ℝ Q z - ContinuousLinearMap.inl ℝ D E)])
    have hu' := e.map_target (hrecv hu)
    have hv' := e.map_target (hrecv hv)
    rw [hs] at hu' hv'
    have hb := (convex_ball x R).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz ↦ (hsd z hz).differentiableAt) hsbound hv' hu'
    have hi := hlip u hu v hv
    nlinarith



/-- Regraphing also preserves a uniform full finite Hölder bound. -/
theorem regraph_first_projection_holder
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} (hn : 1 ≤ n) {α B T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hB : 0 ≤ B) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : D → D × E) (x : D) (R : ℝ), 0 < R →
      (∀ z ∈ Metric.ball x R, ‖z‖ ≤ T) →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1/4 →
      HasFiniteHolderBounds n α B Q (Metric.ball x R) →
      (∀ z ∈ Metric.ball x R,
        ‖fderiv ℝ Q z-ContinuousLinearMap.inl ℝ D E‖ ≤ ε) →
      ∃ e : OpenPartialHomeomorph D D,
        (e : D → D) = (fun z ↦ (Q z).1) ∧ e.source = Metric.ball x R ∧
        Metric.ball (Q x).1 (R/4) ⊆ e.target ∧
        HasFiniteHolderBounds n α C (Q ∘ e.symm) (Metric.ball (Q x).1 (R/4)) ∧
        HasFiniteHolderBounds n α C e.symm (Metric.ball (Q x).1 (R/4)) ∧
        (∀ u ∈ Metric.ball (Q x).1 (R/4), ∀ v ∈ Metric.ball (Q x).1 (R/4),
          ‖e.symm u-e.symm v‖ ≤ 2*‖u-v‖) ∧
        (∀ y ∈ Metric.ball (Q x).1 (R/4), (Q (e.symm y)).1 = y) ∧
        ∀ u ∈ Metric.ball (Q x).1 (R/4), ∀ v ∈ Metric.ball (Q x).1 (R/4),
          ‖(Q (e.symm u)).2-(Q (e.symm v)).2‖ ≤ (2*ε)*‖u-v‖ := by
  obtain ⟨A,hA,HI⟩ := inverse_function_holder_bound
    (E:=D) (F:=D) n α B 2 T hα hα1 hB (by norm_num) hT
  obtain ⟨C,hC,HC⟩ := composition_holder_bound_including_zero
    (E:=D) (F:=D) (G:=D×E) n α B A 2 hα hα1 hB hA (by norm_num)
  refine ⟨max C A,hC.trans (le_max_left _ _),?_⟩
  intro Q x R hR hsource ε hε hεquarter hQ hDQ
  obtain ⟨e,he,hs,htarget,hsmooth,hlip,hfst,hsnd⟩ :=
    regraph_first_projection hn Q x R hR ε hε hεquarter hQ.1 hDQ
  have hproj : HasFiniteHolderBounds n α B e e.source := by
    rw [he,hs]
    have H := hQ.clm_comp Metric.isOpen_ball (ContinuousLinearMap.fst ℝ D E)
    exact H.mono_bound (mul_le_of_le_one_left hB (ContinuousLinearMap.norm_fst_le ℝ D E))
  have hmaps : MapsTo e.symm (Metric.ball (Q x).1 (R/4)) e.source :=
    fun y hy ↦ e.map_target (htarget hy)
  have hvalues : ∀ y ∈ Metric.ball (Q x).1 (R/4), ‖e.symm y‖ ≤ T := by
    intro y hy
    exact hsource _ (by simpa only [hs] using hmaps hy)
  obtain ⟨hin,hiH⟩ := HI e.source (Metric.ball (Q x).1 (R/4)) e.open_source
    (by rw [hs]; exact convex_ball _ _) Metric.isOpen_ball (convex_ball _ _)
    e e.symm hproj.1 hsmooth hmaps (fun z hz ↦ e.left_inv hz)
    (fun y hy ↦ e.right_inv (htarget hy)) hlip hvalues hproj.2.1 hproj.2.2
  have hresult := HC (Metric.ball (Q x).1 (R/4)) (Metric.ball x R)
    Metric.isOpen_ball (convex_ball _ _) Metric.isOpen_ball (convex_ball _ _)
    e.symm Q hsmooth hQ.1 (fun y hy ↦ by simpa only [hs] using hmaps hy)
    hlip hin hQ.2.1 hiH hQ.2.2
  have hInv : HasFiniteHolderBounds n α A e.symm (Metric.ball (Q x).1 (R/4)) :=
    ⟨hsmooth,hin,hiH⟩
  exact ⟨e,he,hs,htarget,HasFiniteHolderBounds.mono_bound hresult (le_max_left _ _),
    hInv.mono_bound (le_max_right _ _),hlip,hfst,hsnd⟩

/-- Regraph the original scalar leaf function together with the plaque. -/
theorem regraph_first_projection_with_function
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} (hn : 1 ≤ n) {α B H T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hB : 0 ≤ B) (hH : 0 ≤ H) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : D → D × E) (f : D → ℝ) (x : D) (R : ℝ), 0 < R →
      (∀ z ∈ Metric.ball x R, ‖z‖ ≤ T) → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1/4 →
      HasFiniteHolderBounds n α B Q (Metric.ball x R) →
      HasFiniteHolderBounds n α H f (Metric.ball x R) →
      (∀ z ∈ Metric.ball x R,
        ‖fderiv ℝ Q z-ContinuousLinearMap.inl ℝ D E‖ ≤ ε) →
      ∃ e : OpenPartialHomeomorph D D,
        (e : D → D) = (fun z ↦ (Q z).1) ∧ e.source = Metric.ball x R ∧
        Metric.ball (Q x).1 (R/4) ⊆ e.target ∧
        HasFiniteHolderBounds n α C (Q ∘ e.symm) (Metric.ball (Q x).1 (R/4)) ∧
        HasFiniteHolderBounds n α C (f ∘ e.symm) (Metric.ball (Q x).1 (R/4)) ∧
        (∀ y ∈ Metric.ball (Q x).1 (R/4), (Q (e.symm y)).1 = y) ∧
        ∀ u ∈ Metric.ball (Q x).1 (R/4), ∀ v ∈ Metric.ball (Q x).1 (R/4),
          ‖(Q (e.symm u)).2-(Q (e.symm v)).2‖ ≤ (2*ε)*‖u-v‖ := by
  obtain ⟨A,hA,HA⟩ := regraph_first_projection_holder (D := D) (E := E)
    hn hα hα1 hB hT
  obtain ⟨C,hC,HC⟩ := composition_holder_bound_including_zero
    (E:=D) (F:=D) (G:=ℝ) n α H A 2 hα hα1 hH hA (by norm_num)
  refine ⟨max A C,hA.trans (le_max_left _ _),?_⟩
  intro Q f x R hR hsource ε hε hεq hQ hf hDQ
  obtain ⟨e,he,hs,htarget,hgraph,hinv,hlip,hfst,hsnd⟩ :=
    HA Q x R hR hsource ε hε hεq hQ hDQ
  have hmaps : MapsTo e.symm (Metric.ball (Q x).1 (R/4)) (Metric.ball x R) := by
    intro y hy
    simpa only [← hs] using e.map_target (htarget hy)
  have hfunction := HC (Metric.ball (Q x).1 (R/4)) (Metric.ball x R)
    Metric.isOpen_ball (convex_ball _ _) Metric.isOpen_ball (convex_ball _ _)
    e.symm f hinv.1 hf.1 hmaps hlip hinv.2.1 hf.2.1 hinv.2.2 hf.2.2
  exact ⟨e,he,hs,htarget,hgraph.mono_bound (le_max_left _ _),
    HasFiniteHolderBounds.mono_bound hfunction (le_max_right _ _),hfst,hsnd⟩

/-- Regraph around a fixed common coordinate origin rather than the moving leaf basepoint. -/
theorem regraph_centered_with_function
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} (hn : 1 ≤ n) {α B H T Z : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hT : 0 ≤ T) (hZ : 0 ≤ Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : D → D × E) (f : D → ℝ) (g : D × E → ℝ)
      (x : D) (z₀ : D × E) (R : ℝ), 0 < R → ‖z₀‖ ≤ Z →
      ‖Q x-z₀‖ ≤ R/16 → (∀ z ∈ Metric.ball x R, ‖z‖ ≤ T) →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1/4 →
      HasFiniteHolderBounds n α B Q (Metric.ball x R) →
      HasFiniteHolderBounds n α H f (Metric.ball x R) →
      (∀ z ∈ Metric.ball x R, g (Q z) = f z) →
      (∀ z ∈ Metric.ball x R, ‖fderiv ℝ Q z-ContinuousLinearMap.inl ℝ D E‖ ≤ ε) →
      ∃ φ : D → E,
        φ ((Q x).1-z₀.1) = (Q x).2-z₀.2 ∧
        HasFiniteHolderBounds n α C φ (Metric.ball 0 (R/8)) ∧
        HasFiniteHolderBounds n α C (fun u ↦ g (z₀+(u,φ u))) (Metric.ball 0 (R/8)) ∧
        (∀ u ∈ Metric.ball (0:D) (R/8), ∀ v ∈ Metric.ball 0 (R/8),
          ‖φ u-φ v‖ ≤ (2*ε)*‖u-v‖) ∧
        ∀ u ∈ Metric.ball (0:D) (R/8), ∃ v ∈ Metric.ball x R, Q v = z₀+(u,φ u) := by
  obtain ⟨A,hA,HA⟩ := regraph_first_projection_with_function (D := D) (E := E)
    hn hα hα1 hB hH hT
  refine ⟨A+Z,add_nonneg hA hZ,?_⟩
  intro Q f g x z₀ R hR hz₀ hnear hsource ε hε hεq hQ hf hgf hDQ
  obtain ⟨e,he,hs,htarget,hgraph,hfun,hfst,hsnd⟩ :=
    HA Q f x R hR hsource ε hε hεq hQ hf hDQ
  have hnear₁ : ‖(Q x).1-z₀.1‖ ≤ R/16 := (le_max_left _ _).trans hnear
  have hmap : MapsTo (fun u : D ↦ z₀.1+u) (Metric.ball 0 (R/8))
      (Metric.ball (Q x).1 (R/4)) := by
    intro u hu
    have hu' : ‖u‖ < R/8 := by simpa only [Metric.mem_ball,dist_zero_right] using hu
    have hb := norm_add_le (z₀.1-(Q x).1) u
    have hrev : ‖z₀.1-(Q x).1‖ ≤ R/16 := by simpa only [norm_sub_rev] using hnear₁
    rw [Metric.mem_ball,dist_eq_norm]
    have heq : z₀.1+u-(Q x).1 = (z₀.1-(Q x).1)+u := by abel
    rw [heq]
    linarith
  let φ := fun u ↦ (Q (e.symm (z₀.1+u))).2-z₀.2
  have hparam (u : D) (hu : u ∈ Metric.ball 0 (R/8)) :
      Q (e.symm (z₀.1+u)) = z₀+(u,φ u) := by
    apply Prod.ext
    · exact hfst _ (hmap hu)
    · dsimp [φ]; abel
  have hmapsource (u : D) (hu : u ∈ Metric.ball 0 (R/8)) :
      e.symm (z₀.1+u) ∈ Metric.ball x R := by
    rw [← hs]
    exact e.map_target (htarget (hmap hu))
  have hφ : HasFiniteHolderBounds n α (A+Z) φ (Metric.ball 0 (R/8)) := by
    have H := (hgraph.clm_comp Metric.isOpen_ball (ContinuousLinearMap.snd ℝ D E)).mono_bound
      (mul_le_of_le_one_left hA (ContinuousLinearMap.norm_snd_le ℝ D E))
    have H' := (H.comp_translation z₀.1 hmap).add Metric.isOpen_ball
      (finiteHolderBounds_const n hn α (Metric.ball 0 (R/8)) (-z₀.2))
    have hz₂ : ‖-z₀.2‖ ≤ Z := by rw [norm_neg]; exact (le_max_right _ _).trans hz₀
    have H'' := H'.mono_bound (add_le_add le_rfl hz₂)
    simpa only [φ,Function.comp_apply,ContinuousLinearMap.coe_snd',sub_eq_add_neg] using H''
  have hscalar : HasFiniteHolderBounds n α (A+Z) (fun u ↦ g (z₀+(u,φ u)))
      (Metric.ball 0 (R/8)) := by
    apply ((hfun.comp_translation z₀.1 hmap).mono_bound (by linarith)).congr_open Metric.isOpen_ball
    intro u hu
    change g (z₀+(u,φ u)) = f (e.symm (z₀.1+u))
    rw [← hparam u hu]
    exact hgf _ (hmapsource u hu)
  refine ⟨φ,?_,hφ,hscalar,?_,fun u hu ↦ ⟨_,hmapsource u hu,hparam u hu⟩⟩
  · have hx : x ∈ e.source := by rw [hs]; exact Metric.mem_ball_self hR
    have hc : e x = (Q x).1 := congrFun he x
    dsimp [φ]
    rw [add_sub_cancel,← hc,e.left_inv hx]
  · intro u hu v hv
    have H := hsnd _ (hmap hu) _ (hmap hv)
    simpa only [φ,sub_sub_sub_cancel_right,add_sub_add_left_eq_sub] using H

/-- Interchanging the coordinate factors preserves full bounds and converts closeness to the second inclusion into closeness to the first inclusion. -/
theorem regraph_swap_bounds
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (hn : 1 ≤ n) {α B ε : ℝ} (hB : 0 ≤ B)
    {S : Set E} (hS : IsOpen S) (Q : E → D × E)
    (hQ : HasFiniteHolderBounds n α B Q S)
    (hD : ∀ z ∈ S, ‖fderiv ℝ Q z-ContinuousLinearMap.inr ℝ D E‖ ≤ ε) :
    HasFiniteHolderBounds n α B (fun z ↦ (Q z).swap) S ∧
      ∀ z ∈ S, ‖fderiv ℝ (fun z ↦ (Q z).swap) z-
        ContinuousLinearMap.inl ℝ E D‖ ≤ ε := by
  let T := (LinearIsometryEquiv.prodComm ℝ D E).toContinuousLinearEquiv.toContinuousLinearMap
  have hT : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖(LinearIsometryEquiv.prodComm ℝ D E) z‖ ≤ 1*‖z‖
    rw [one_mul]
    exact (LinearIsometryEquiv.prodComm ℝ D E).norm_map z |>.le
  have hfull := (hQ.clm_comp hS T).mono_bound (mul_le_of_le_one_left hB hT)
  refine ⟨hfull,?_⟩
  intro z hz
  have hdQ := (hQ.1.contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp; omega)
  have he : fderiv ℝ (fun z ↦ (Q z).swap) z = T.comp (fderiv ℝ Q z) :=
    (T.hasFDerivAt.comp z hdQ.hasFDerivAt).fderiv
  have hin : T.comp (ContinuousLinearMap.inr ℝ D E) = ContinuousLinearMap.inl ℝ E D := by
    ext x <;> rfl
  rw [he,← hin,← ContinuousLinearMap.comp_sub]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hT).trans (hD z hz))

end HolomorphicAnosov.JourneLeafPolynomialApproximation
