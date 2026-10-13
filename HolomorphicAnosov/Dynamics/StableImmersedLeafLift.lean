import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.ENNReal.Lemmas
import HolomorphicAnosov.Geometry.ContinuousOriginalNorm
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Pointed covering lifts of stable tangent immersions, using nullhomotopy of their ambient loop
images (Lee, §11, pp. 275–279; Hatcher, Prop. 1.33). -/

noncomputable section
open Set Filter Bundle Manifold
open scoped ContDiff Topology ENNReal NNReal
namespace HolomorphicAnosov

variable {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- A smooth map from an open Euclidean domain has locally bounded derivative in a specified ambient
Riemannian norm. -/
theorem euclidean_to_riemannian_derivative_locally_bounded
    (h : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x))
    {U : Set V} (hU : IsOpen U) (g : V → M) (hg : ContMDiffOn 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ g U)
    {x : V} (hx : x ∈ U) :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ,E) y) := ⟨h.toRiemannianMetric⟩
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace 𝓘(ℝ,V) y,
      ‖mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) g y v‖ ≤ C * ‖v‖ := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ,E) y) := ⟨h.toRiemannianMetric⟩
  let A (y : U) : V →L[ℝ] TangentSpace 𝓘(ℝ,E) (g y) :=
    mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) g y
  have himage : Continuous (fun p : U × V ↦ ‖A p.1 p.2‖) := by
    apply FixedBlockEstimates.Native.continuous_original_norm h
      (fun p : U × V ↦ g p.1) (fun p ↦ A p.1 p.2)
    have ht := hg.continuousOn_tangentMapWithin (by simp)
      (hU.uniqueMDiffOn (I := 𝓘(ℝ,V)))
    have hin : Continuous (fun p : U × V ↦
        (⟨p.1.val,p.2⟩ : TangentBundle 𝓘(ℝ,V) V)) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ,V)).symm.continuous.comp
        (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd)
    have ht' := ht.comp_continuous hin (fun p ↦ p.1.property)
    convert ht' using 1
    funext p
    apply congrArg (fun v ↦ (⟨g p.1,v⟩ : TangentBundle 𝓘(ℝ,E) M))
    dsimp [A, tangentMapWithin]
    rw [mfderivWithin_of_isOpen hU p.1.property]
    rfl
  let C : ℝ := ‖A ⟨x,hx⟩‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have he := moving_operator_norm_eventually_lt (fun _ : U ↦ LinearEquiv.refl ℝ V)
    A continuous_snd.norm himage (⟨x,hx⟩ : U) (lt_add_one _)
  refine ⟨C,hC,?_⟩
  have he' : ∀ᶠ y in 𝓝 (⟨x,hx⟩ : U), ∀ v : V, ‖A y v‖ ≤ C * ‖v‖ :=
    he.mono fun y hy v ↦ (A y).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right hy.le (norm_nonneg v))
  rw [← map_nhds_subtype_coe_eq_nhds hx (hU.mem_nhds hx)]
  exact he'

omit [FiniteDimensional ℝ V] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A derivative bound on a convex open domain bounds the ambient Riemannian distance between image
points by the corresponding multiple of Euclidean distance. -/
theorem riemannianEDist_le_mul_edist_of_convex
    [RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ,E) y)]
    {U : Set V} (hU : IsOpen U) (hconv : Convex ℝ U)
    (g : V → M) (hg : ContMDiffOn 𝓘(ℝ,V) 𝓘(ℝ,E) 1 g U)
    (K : ℝ≥0)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace 𝓘(ℝ,V) x,
      ‖mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) g x v‖ₑ ≤ (K : ℝ≥0∞) * ‖v‖ₑ)
    {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    Manifold.riemannianEDist 𝓘(ℝ,E) (g x) (g y) ≤ (K : ℝ≥0∞) * edist x y := by
  let η := ContinuousAffineMap.lineMap (R := ℝ) x y
  have hη : MapsTo η (Icc 0 1) U := by
    rw [mapsTo_iff_image_subset,ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap]
    exact hconv.segment_subset hx hy
  have hs : ContMDiff 𝓘(ℝ) 𝓘(ℝ,V) 1 η := by
    rw [contMDiff_iff_contDiff]
    exact η.contDiff
  have hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ,E) 1 (g ∘ η) (Icc 0 1) :=
    hg.comp hs.contMDiffOn hη
  apply (Manifold.riemannianEDist_le_pathELength hγ (by simp [η,ContinuousAffineMap.coe_lineMap_eq])
    (by simp [η,ContinuousAffineMap.coe_lineMap_eq]) zero_le_one).trans
  rw [← lintegral_fderiv_lineMap_eq_edist,
    Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  calc
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, (K : ℝ≥0∞) *
        ‖fderivWithin ℝ η (Icc 0 1) t 1‖ₑ := by
      apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hdiff := (hg _ (hη ht)).contMDiffAt (hU.mem_nhds (hη ht))
        |>.mdifferentiableAt one_ne_zero
      rw [mfderivWithin_comp t (hdiff.mdifferentiableWithinAt (s := univ))
        (hs.mdifferentiable one_ne_zero t).mdifferentiableWithinAt
        (show Icc (0:ℝ) 1 ⊆ η ⁻¹' univ from fun _ _ ↦ trivial) (by
          rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc zero_lt_one t ht), mfderivWithin_univ]
      convert hbound _ (hη ht) ((mfderivWithin 𝓘(ℝ) 𝓘(ℝ,V) η (Icc 0 1) t) 1) using 1
      · rfl
      · rw [mfderivWithin_eq_fderivWithin]; rfl
    _ = _ := by rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top]

/-- A family of smooth ambient maps with derivative bounds on an immersed tangent distribution has
uniform local distance bounds on the intrinsic leaf. -/
theorem smooth_tangent_family_local_distance_bound
    {L : Type*} [TopologicalSpace L] [ChartedSpace V L] [IsManifold 𝓘(ℝ,V) ∞ L]
    (h : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x))
    (inc : L → M) (hi : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ inc)
    (D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ,E) x))
    (htan : ∀ x v, mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) inc x v ∈ D (inc x))
    (g : ℕ → M → M) (hg : ∀ n, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (g n))
    (w : ℕ → ℝ≥0)
    (hbound : letI : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ,E) y) :=
        ⟨h.toRiemannianMetric⟩
      ∀ n x v, v ∈ D x → ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (g n) x v‖ ≤ w n * ‖v‖)
    (x : L) :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ,E) y) := ⟨h.toRiemannianMetric⟩
    ∃ U : Set L, IsOpen U ∧ x ∈ U ∧ ∃ B : ℝ≥0,
      ∀ y ∈ U, ∀ n,
        Manifold.riemannianEDist 𝓘(ℝ,E) (g n (inc x)) (g n (inc y)) ≤
          (w n : ℝ≥0∞) * B := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace 𝓘(ℝ,E) y) := ⟨h.toRiemannianMetric⟩
  let c := chartAt V x
  let φ := inc ∘ c.symm
  have hc : ContMDiffOn 𝓘(ℝ,V) 𝓘(ℝ,V) ∞ c.symm c.target :=
    contMDiffOn_chart_symm
  have hφ : ContMDiffOn 𝓘(ℝ,V) 𝓘(ℝ,E) ∞ φ c.target := hi.comp_contMDiffOn hc
  obtain ⟨C,hC,hlocal⟩ := euclidean_to_riemannian_derivative_locally_bounded
    h c.open_target φ hφ (c.map_source (mem_chart_source V x))
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (c.open_target.mem_nhds (c.map_source (mem_chart_source V x))) hlocal)
  let U := c.source ∩ c ⁻¹' Metric.ball (c x) r
  have hU : IsOpen U := c.isOpen_inter_preimage Metric.isOpen_ball
  have hxU : x ∈ U := ⟨mem_chart_source V x,Metric.mem_ball_self hr⟩
  refine ⟨U,hU,hxU,NNReal.mk (C*r) (mul_nonneg hC.le hr.le),?_⟩
  intro y hy n
  have hderiv : ∀ z ∈ Metric.ball (c x) r, ∀ v : TangentSpace 𝓘(ℝ,V) z,
      ‖mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) (g n ∘ φ) z v‖ₑ ≤
        ENNReal.ofReal ((w n:ℝ)*C) * ‖v‖ₑ := by
    intro z hz v
    have hzt := (hrsub hz).1
    have hφd := (hφ z hzt).contMDiffAt (c.open_target.mem_nhds hzt)
    have hcd := (hc z hzt).contMDiffAt (c.open_target.mem_nhds hzt)
    have hv : mfderiv 𝓘(ℝ,V) 𝓘(ℝ,E) φ z v ∈ D (φ z) := by
      dsimp [φ]
      rw [mfderiv_comp z (hi.mdifferentiableAt (by simp))
        (hcd.mdifferentiableAt (by simp))]
      exact htan _ _
    rw [mfderiv_comp z ((hg n).mdifferentiableAt (by simp))
      (hφd.mdifferentiableAt (by simp))]
    have hb := (hbound n (φ z) _ hv).trans
      (mul_le_mul_of_nonneg_left ((hrsub hz).2 v) (w n).coe_nonneg)
    have hb' := ENNReal.ofReal_le_ofReal hb
    simp only [ENNReal.ofReal_mul (w n).coe_nonneg, ENNReal.ofReal_mul hC.le,
      ofReal_norm, mul_assoc] at hb' ⊢
    convert hb' using 1; rfl
  have hdist := riemannianEDist_le_mul_edist_of_convex Metric.isOpen_ball
    (convex_ball _ _) (g n ∘ φ)
    (((hg n).comp_contMDiffOn hφ).of_le (by simp) |>.mono (fun z hz ↦ (hrsub hz).1))
    (NNReal.mk ((w n:ℝ)*C) (mul_nonneg (w n).coe_nonneg hC.le)) (by
      simpa only [ENNReal.ofReal_eq_coe_nnreal (mul_nonneg (w n).coe_nonneg hC.le)] using hderiv)
    (Metric.mem_ball_self hr) hy.2
  have hxφ : φ (c x) = inc x := congrArg inc (c.left_inv (mem_chart_source V x))
  have hyφ : φ (c y) = inc y := congrArg inc (c.left_inv hy.1)
  simp only [Function.comp_apply,hxφ,hyφ] at hdist
  rw [← ENNReal.ofReal_eq_coe_nnreal (mul_nonneg (w n).coe_nonneg hC.le)] at hdist
  rw [← ENNReal.ofReal_eq_coe_nnreal (mul_nonneg hC.le hr.le)]
  apply hdist.trans
  have he : edist (c x) (c y) ≤ ENNReal.ofReal r := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (by simpa only [dist_comm] using (Metric.mem_ball.mp hy.2).le)
  calc
    _ ≤ ENNReal.ofReal ((w n:ℝ)*C) * ENNReal.ofReal r :=
      mul_le_mul_right he _
    _ = _ := by
      change ENNReal.ofReal ((w n:ℝ)*C) * ENNReal.ofReal r =
        (w n : ℝ≥0∞) * ENNReal.ofReal (C*r)
      rw [ENNReal.ofReal_mul (w n).coe_nonneg, ENNReal.ofReal_mul hC.le,
        ENNReal.ofReal_coe_nnreal, mul_assoc]

end HolomorphicAnosov

open Set Filter Topology
open scoped ENNReal NNReal
namespace HolomorphicAnosov

/-- For a family of maps with weighted local distance bounds on a connected space, the distance from
a fixed point has a uniform weighted bound on every compact subset. -/
theorem compact_uniform_bound_of_local
    {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X] [PseudoEMetricSpace Y]
    (g : ℕ → X → Y) (w : ℕ → ℝ≥0∞)
    (hloc : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ B : ℝ≥0, ∀ y ∈ U, ∀ n, edist (g n x) (g n y) ≤ w n * B)
    (x₀ : X) {K : Set X} (hK : IsCompact K) :
    ∃ B : ℝ≥0, ∀ y ∈ K, ∀ n, edist (g n x₀) (g n y) ≤ w n * B := by
  classical
  let R : Set X := {y | ∃ B : ℝ≥0, ∀ n, edist (g n x₀) (g n y) ≤ w n * B}
  have trans_bound {x y z : X} {B C : ℝ≥0}
      (hx : ∀ n, edist (g n x) (g n y) ≤ w n * B)
      (hy : ∀ n, edist (g n y) (g n z) ≤ w n * C) :
      ∀ n, edist (g n x) (g n z) ≤ w n * (B + C : ℝ≥0) := by
    intro n
    calc
      _ ≤ edist (g n x) (g n y) + edist (g n y) (g n z) := edist_triangle ..
      _ ≤ w n * B + w n * C := add_le_add (hx n) (hy n)
      _ = _ := by rw [ENNReal.coe_add, mul_add]
  have hopen : IsOpen R := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨B,hB⟩
    obtain ⟨U,hU,hx,C,hC⟩ := hloc x
    exact ⟨U,fun y hy ↦ ⟨B+C,trans_bound hB (hC y hy)⟩,hU,hx⟩
  have hclosed : IsClosed R := by
    rw [← isOpen_compl_iff,isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨U,hU,hxU,C,hC⟩ := hloc x
    refine ⟨U,?_,hU,hxU⟩
    rintro y hy ⟨B,hB⟩
    apply hx
    exact ⟨B+C,trans_bound hB (fun n ↦ by simpa only [edist_comm] using hC y hy n)⟩
  have hR : R = univ := (IsClopen.eq_univ ⟨hclosed,hopen⟩ ⟨x₀,0,by simp⟩)
  have hall (x : X) : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ B : ℝ≥0, ∀ y ∈ U, ∀ n, edist (g n x₀) (g n y) ≤ w n * B := by
    obtain ⟨B,hB⟩ : x ∈ R := by rw [hR]; trivial
    obtain ⟨U,hU,hx,C,hC⟩ := hloc x
    exact ⟨U,hU,hx,B+C,fun y hy ↦ trans_bound hB (hC y hy)⟩
  choose U hU hx B hB using hall
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover U hU
    (fun x _ ↦ mem_iUnion.mpr ⟨x,hx x⟩)
  refine ⟨∑ x ∈ t, B x,?_⟩
  intro y hy n
  obtain ⟨x,hxt,hyU⟩ := mem_iUnion₂.mp (ht hy)
  exact (hB x y hyU n).trans (mul_le_mul_right (by
    exact_mod_cast (Finset.single_le_sum (fun z _ ↦ (zero_le : (0:ℝ≥0) ≤ B z)) hxt)) _)

end HolomorphicAnosov

open Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section
namespace HolomorphicAnosov

/-- Every point of a boundaryless charted manifold has an open simply connected neighborhood. -/
theorem charted_simply_connected_neighborhood
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] [ChartedSpace V X] (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsSimplyConnected U := by
  let c := chartAt V x
  obtain ⟨r,hr,hrsub⟩ := Metric.isOpen_iff.mp c.open_target (c x)
    (c.map_source (mem_chart_source V x))
  let b := c.symm.restrOpen (Metric.ball (c x) r) Metric.isOpen_ball
  have hb : b.source = Metric.ball (c x) r := inter_eq_right.mpr hrsub
  have hball : ContractibleSpace b.source := by
    rw [hb]
    exact (convex_ball (c x) r).contractibleSpace ⟨c x,Metric.mem_ball_self hr⟩
  let := hball
  refine ⟨b.target,b.open_target,?_,?_⟩
  · have hx : c x ∈ b.source := by rw [hb]; exact Metric.mem_ball_self hr
    have ht := b.map_source hx
    simpa [b,c,mem_chart_source] using ht
  · exact b.toHomeomorphSourceTarget.symm.toHomotopyEquiv.simplyConnectedSpace

/-- A compact boundaryless emetric manifold has a positive radius such that every loop contained in
a ball of that radius is nullhomotopic. -/
theorem compact_charted_uniform_nullhomotopy_radius
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [EMetricSpace X] [ChartedSpace V X] [CompactSpace X] :
    ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ x : X, ∀ γ : Path x x,
      (∀ t, edist (γ t) x < ε) → γ.Homotopic (Path.refl x) := by
  classical
  choose U hU hx hsim using (charted_simply_connected_neighborhood (V := V) :
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsSimplyConnected U)
  obtain ⟨ε,hε,hcover⟩ := lebesgue_number_lemma_of_emetric isCompact_univ hU
    (show (univ : Set X) ⊆ ⋃ x, U x from fun x _ ↦ mem_iUnion.mpr ⟨x,hx x⟩)
  refine ⟨ε,hε,?_⟩
  intro x γ hγ
  obtain ⟨y,hy⟩ := hcover x (mem_univ x)
  obtain ⟨H,-⟩ := (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp
    (hsim y)).2 x γ (fun t ↦ hy (hγ t))
  exact ⟨H⟩

end HolomorphicAnosov
namespace HolomorphicAnosov
open Set Filter _root_.Topology Bundle
open scoped ContDiff ENNReal NNReal Manifold
attribute [local instance] complex_isManifold_real

/-- Every intrinsic loop in a stable tangent immersion into a compact Anosov manifold has
nullhomotopic ambient image. -/
theorem stable_tangent_immersion_loops_nullhomotopic
    {d r : ℕ} {M L : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ,Fin r → ℝ) ∞ L] [PreconnectedSpace L]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (inc : L → M) (hi : ContMDiff 𝓘(ℝ,Fin r → ℝ) (realModel d) ∞ inc)
    (htan : ∀ x v, mfderiv 𝓘(ℝ,Fin r → ℝ) (realModel d) inc x v ∈
      a.splitting.stable.toDistribution (inc x))
    (x : L) (γ : Path x x) : (γ.map hi.continuous).Homotopic (Path.refl (inc x)) := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace (realModel d) y) :=
    ⟨a.metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (ComplexModel d)
      (fun y : M ↦ TangentSpace (realModel d) y) :=
    ⟨a.metric.inner,a.metric.contMDiff.continuous,fun _ _ _ ↦ rfl⟩
  let : RegularSpace M := inferInstance
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (realModel d) M
  obtain ⟨C,rate,hC,hrate,hrate1,hs,-⟩ := fixed_block_uniform_anosov_estimates f a
  let w (n : ℕ) : ℝ≥0 := NNReal.mk (C*rate^n) (mul_nonneg hC.le (pow_nonneg hrate.le _))
  have hlocal := smooth_tangent_family_local_distance_bound a.metric inc hi
    a.splitting.stable.toDistribution htan
    (fun n ↦ (f : M → M)^[n])
    (fun n ↦ f.toReal.contMDiff.iterate n) w hs
  have hlocal' : ∀ z : L, ∃ U : Set L, IsOpen U ∧ z ∈ U ∧
      ∃ B : ℝ≥0, ∀ y ∈ U, ∀ n,
        edist (((f:M→M)^[n]) (inc z)) (((f:M→M)^[n]) (inc y)) ≤ (w n:ℝ≥0∞)*B := hlocal
  obtain ⟨B,hB⟩ := compact_uniform_bound_of_local
    (fun n z ↦ ((f:M→M)^[n]) (inc z)) (fun n ↦ (w n:ℝ≥0∞)) hlocal' x
    (isCompact_range γ.continuous)
  obtain ⟨ε,hε,hsmall⟩ := compact_charted_uniform_nullhomotopy_radius
    (V := ComplexModel d) (X := M)
  have hw : Tendsto (fun n ↦ (w n:ℝ≥0∞)*B) atTop (𝓝 0) := by
    have hwreal : Tendsto (fun n : ℕ ↦ C*rate^n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hrate.le hrate1).const_mul C
    have hw' : Tendsto (fun n ↦ (w n:ℝ≥0∞)) atTop (𝓝 0) := by
      simpa only [w,ENNReal.ofReal_eq_coe_nnreal (mul_nonneg hC.le (pow_nonneg hrate.le _)),
        ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hwreal
    simpa using ENNReal.Tendsto.mul_const hw' (Or.inr ENNReal.coe_ne_top)
  obtain ⟨n,hn⟩ := (hw.eventually (gt_mem_nhds hε)).exists
  let δ : Path (((f:M→M)^[n]) (inc x)) (((f:M→M)^[n]) (inc x)) :=
    (γ.map hi.continuous).map (f.continuous.iterate n)
  have hδ : δ.Homotopic (Path.refl _) := hsmall _ δ (fun t ↦ by
    rw [edist_comm]
    exact (hB (γ t) ⟨t,rfl⟩ n).trans_lt hn)
  have hback := hδ.map ⟨(f.symm:M→M)^[n],f.symm.continuous.iterate n⟩
  have hinv : Function.LeftInverse ((f.symm:M→M)^[n]) ((f:M→M)^[n]) :=
    f.left_inv.iterate n
  have hback' := hback.pathCast (hinv (inc x)).symm (hinv (inc x)).symm
  convert hback' using 1
  · apply Path.ext
    funext t
    exact (hinv (inc (γ t))).symm
  · apply Path.ext
    funext t
    exact (hinv (inc x)).symm

/-- An injective stable tangent immersion admits a continuous injective lift through a
covering with a prescribed value at a basepoint. -/
theorem stable_tangent_immersion_pointed_lift
    {d r : ℕ} {M L E : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ,Fin r → ℝ) ∞ L] [ConnectedSpace L]
    [TopologicalSpace E]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (inc : L → M) (hi : ContMDiff 𝓘(ℝ,Fin r → ℝ) (realModel d) ∞ inc)
    (hinj : Function.Injective inc)
    (htan : ∀ x v, mfderiv 𝓘(ℝ,Fin r → ℝ) (realModel d) inc x v ∈
      a.splitting.stable.toDistribution (inc x))
    {p : E → M} (hp : IsCoveringMap p) (x : L) (e : E) (he : p e = inc x) :
    ∃ lift : C(L,E), Function.Injective lift ∧ lift x = e ∧
      ∀ z, p (lift z) = inc z := by
  let : LocallyPathConnectedSpace L := ChartedSpace.locallyPathConnectedSpace (Fin r → ℝ) L
  let : PathConnectedSpace L := (pathConnectedSpace_iff_connectedSpace).mpr inferInstance
  let j : C(L,M) := ⟨inc,hi.continuous⟩
  have hzero (γ : FundamentalGroup L x) : FundamentalGroup.map j x γ = 1 := by
    induction γ using Quotient.ind with
    | _ γ =>
      change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk γ) j =
        Path.Homotopic.Quotient.mk (Path.refl (inc x))
      rw [← Path.Homotopic.Quotient.mk_map]
      exact Path.Homotopic.Quotient.eq.mpr
        (stable_tangent_immersion_loops_nullhomotopic f a inc hi htan x γ)
  obtain ⟨lift,⟨hpoint,hproj⟩,-⟩ := hp.existsUnique_continuousMap_lifts_of_range_le
    (f := j) he (by
      rintro z ⟨γ,rfl⟩
      rw [hzero]
      exact ⟨1,map_one _⟩)
  refine ⟨lift,?_,hpoint,congrFun hproj⟩
  intro u v huv
  apply hinj
  exact (congrFun hproj u).symm.trans ((congrArg p huv).trans (congrFun hproj v))


end HolomorphicAnosov
