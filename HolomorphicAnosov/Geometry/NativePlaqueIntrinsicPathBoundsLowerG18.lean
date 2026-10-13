import HolomorphicAnosov.Geometry.ImmersionRiemannianMetric
import HolomorphicAnosov.Geometry.IntrinsicPiecewiseC1RiemannianEDist
import Mathlib.Geometry.Manifold.Riemannian.Basic
import HolomorphicAnosov.Geometry.IntrinsicChartFirstExit
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalSmoothRealMetricInner
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import HolomorphicAnosov.Geometry.HermitianLeafPathDistance

set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Manifold Bundle MeasureTheory
open scoped ContDiff Manifold _root_.Topology ENNReal
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
/-- The pullback Hermitian path-length infimum along a smooth immersion defines an extended metric
inducing the intrinsic leaf topology. (Lee, §11, pp.275–279) -/
theorem hermitian_pullback_emetric
    {r d : ℕ} {L M : Type*} [TopologicalSpace L] [T2Space L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (hi : ∀ z, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z)) :
    ∃ m : EMetricSpace L,
      m.toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace L) ∧
      ∀ x y : L, @edist L m.toEDist x y = intrinsicHermitianLeafEDist (r := r) inc h x y := by
  obtain ⟨gL, hgL⟩ := immersion_riemannianMetric_exists
    (StableFoliationsSupport.originalSmoothRealMetric h hh) inc hinc hi
  let : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, Fin r → ℝ) : L → Type _) :=
    ⟨gL.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (Fin r → ℝ)
      (TangentSpace 𝓘(ℝ, Fin r → ℝ) : L → Type _) :=
    ⟨gL.inner, gL.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : LocallyCompactSpace L := ChartedSpace.locallyCompactSpace (Fin r → ℝ) L
  let m : EMetricSpace L := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, Fin r → ℝ) L
  refine ⟨m, rfl, ?_⟩
  intro x y
  change Manifold.riemannianEDist 𝓘(ℝ, Fin r → ℝ) x y = _
  rw [intrinsicPiecewiseC1Path_riemannianEDist (r := r) (L := L) x y]
  unfold intrinsicHermitianLeafEDist IntrinsicPiecewiseC1Path.length
  congr 1
  funext p
  apply Finset.sum_congr rfl
  intro k hk
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [← ofReal_norm (p.velocity k t), norm_eq_sqrt_real_inner]
  change ENNReal.ofReal (Real.sqrt (gL.inner _ _ _)) = _
  rw [hgL, StableFoliationsSupport.originalSmoothRealMetric_inner]
  rfl

/-- Strict balls for the intrinsic Hermitian path distance are open in the intrinsic leaf topology.
(Lee, Prop. 11.20) -/
theorem intrinsicHermitianLeafEDist_ball_isOpen
    {r d : ℕ} {L M : Type*} [TopologicalSpace L] [T2Space L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (hi : ∀ z, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z))
    (x : L) (R : ℝ≥0∞) :
    IsOpen {y | intrinsicHermitianLeafEDist (r := r) inc h x y < R} := by
  obtain ⟨m, hm, he⟩ := hermitian_pullback_emetric h hh inc hinc hi
  let B : Set L := {y | intrinsicHermitianLeafEDist (r := r) inc h x y < R}
  let : EMetricSpace L := m
  have ho := @Metric.isOpen_eball L x m.toPseudoEMetricSpace R
  have hs : @Metric.eball L m.toEDist x R =
      {y | intrinsicHermitianLeafEDist (r := r) inc h x y < R} := by
    ext y
    change (@edist L m.toEDist y x < R) ↔ _
    rw [@edist_comm L m.toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (EMetricSpace.toWeakEMetricSpace L).toWeakPseudoEMetricSpace y x, he]
    rfl
  rw [hs] at ho
  exact Eq.mp (congrArg (fun τ : TopologicalSpace L ↦
    @IsOpen L τ B) hm) ho

/-- The intrinsic Hermitian path distance satisfies the triangle inequality. (Lee, §11, pp.275–279) -/
theorem intrinsicHermitianLeafEDist_triangle
    {r d : ℕ} {L M : Type*} [TopologicalSpace L] [T2Space L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (hi : ∀ z, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z))
    (x y z : L) :
    intrinsicHermitianLeafEDist (r := r) inc h x z ≤
      intrinsicHermitianLeafEDist (r := r) inc h x y +
        intrinsicHermitianLeafEDist (r := r) inc h y z := by
  obtain ⟨m, _, he⟩ := hermitian_pullback_emetric h hh inc hinc hi
  rw [← he, ← he, ← he]
  let : EMetricSpace L := m
  exact @edist_triangle L m.toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace
    (EMetricSpace.toWeakEMetricSpace L).toWeakPseudoEMetricSpace x y z


/-- The derivative of the included plaque parametrization cancels the derivative of its intrinsic
chart. -/
theorem native_plaque_chart_derivative_cancel
    {r d : ℕ} {L M : Type*}
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : L → M)
    (e : OpenPartialHomeomorph L (Fin r → ℝ))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ L)
    (q : (Fin r → ℝ) → M) (D : Set (Fin r → ℝ)) (hD : IsOpen D)
    (hq : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ q D)
    (hqi : ∀ v ∈ D, q v = inc (e.symm v))
    {z : L} (hz : z ∈ e.source) (hez : e z ∈ D)
    (w : TangentSpace 𝓘(ℝ, Fin r → ℝ) z) :
    mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q (e z)
      (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) e z w) =
    mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z w := by
  have hs : IsOpen (e.source ∩ e ⁻¹' D) :=
    e.continuousOn.isOpen_inter_preimage e.open_source hD
  have heq : q ∘ e =ᶠ[𝓝 z] inc := by
    filter_upwards [hs.mem_nhds ⟨hz,hez⟩] with y hy
    simp only [Function.comp_apply, hqi _ hy.2, e.left_inv hy.1]
  have hd := (contMDiffOn_of_mem_maximalAtlas he).contMDiffAt (e.open_source.mem_nhds hz)
    |>.mdifferentiableAt (by simp)
  have hqd := hq.contMDiffAt (hD.mem_nhds hez) |>.mdifferentiableAt (by simp)
  have hc := mfderiv_comp z hqd hd
  rw [heq.mfderiv_eq] at hc
  exact congrArg (fun A ↦ A w) hc.symm

/-- A positive lower speed bound on a buffered native plaque confines sufficiently small intrinsic
Hermitian distance balls to that plaque. -/
theorem native_plaque_intrinsic_ball_confinement
    {r d : ℕ} {L M : Type*}
    [TopologicalSpace L] [T2Space L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : L → M)
    (e : OpenPartialHomeomorph L (Fin r → ℝ))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ L)
    (q : (Fin r → ℝ) → M) (δ R m : ℝ)
    (hR : 0 < R) (hRδ : R < δ) (hm : 0 < m)
    (hbuffer : ball (0 : Fin r → ℝ) δ ⊆ e.target)
    (hq : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ q (ball 0 δ))
    (hqi : ∀ v ∈ ball (0 : Fin r → ℝ) δ, q v = inc (e.symm v))
    (hbound : ∀ u ∈ ball (0 : Fin r → ℝ) δ, ∀ w : Fin r → ℝ,
      m * ‖w‖ ≤ Real.sqrt
        ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner (q u)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q u w)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q u w)))
    {x y : L} (hx : x ∈ e.source) (he0 : e x = 0)
    (hd : intrinsicHermitianLeafEDist (r := r) inc h x y < ENNReal.ofReal (m * R)) :
    y ∈ e.source ∧ e y ∈ ball (0 : Fin r → ℝ) R := by
  let eδ := e.trans (OpenPartialHomeomorph.ofSet (ball (0 : Fin r → ℝ) δ) isOpen_ball)
  have heδ : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) 1 eδ eδ.source :=
    ((contMDiffOn_of_mem_maximalAtlas he).of_le (by simp)).mono inter_subset_left
  have hbufδ : closedBall (0 : Fin r → ℝ) R ⊆ eδ.target := by
    intro v hv
    have hvδ := closedBall_subset_ball hRδ hv
    exact ⟨hvδ,hbuffer hvδ⟩
  have hxδ : x ∈ eδ.source := ⟨hx, by
    change e x ∈ ball (0 : Fin r → ℝ) δ
    rw [he0]
    exact mem_ball_self (hR.trans hRδ)⟩
  have hb : ∀ z ∈ eδ.source, ∀ w : TangentSpace 𝓘(ℝ, Fin r → ℝ) z,
      m * ‖(tangentSpaceCastModel 𝓘(ℝ, Fin r → ℝ) (eδ z))
        (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) eδ z w)‖ ≤
      leafPullbackHermitianNorm inc h z w := by
    intro z hz w
    have hc := native_plaque_chart_derivative_cancel inc e he q (ball 0 δ)
      isOpen_ball hq hqi hz.1 hz.2 w
    have hb := hbound (e z) hz.2
      (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) e z w)
    rw [StableFoliationsSupport.originalSmoothRealMetric_inner, hc,
      hqi (e z) (show e z ∈ ball 0 δ from hz.2), e.left_inv hz.1] at hb
    exact hb
  have hy := intrinsic_chart_ball_of_length_inf_lt eδ heδ 0 R hR hbufδ
    (leafPullbackHermitianNorm inc h) m hm hb hxδ he0 hd
  exact ⟨hy.1.1,hy.2⟩

end HolomorphicAnosov

noncomputable section
open Set MeasureTheory Manifold Bundle
open scoped Manifold ContDiff ENNReal
namespace HolomorphicAnosov

variable {r d : ℕ} {L M : Type*}
  [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
  [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (realModel d) ∞ M]

/-- The Hermitian speed of an intrinsic piecewise C1 path equals the ambient Riemannian norm of its
included velocity when the real tangent pairings agree. (Ghys, pp.588–589; Lee, §11, pp.275–279) -/
theorem IntrinsicPiecewiseC1Path.speed_eq_ambient_norm
    (inclusion : L → M)
    (hinc : ContMDiff (modelWithCornersSelf ℝ (Fin r → ℝ)) (realModel d) 1 inclusion)
    (h : HermitianTangentMetricCore d M)
    (g : ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (hpair : ∀ x v w, g.inner x v w = hermitianTangentRealPairing h x v w)
    {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y)
    (i : Fin (p.n + 1)) {t : ℝ} (ht : t ∈ p.pieceInterval i) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨g.toRiemannianMetric⟩
    p.speed inclusion h i t =
      ‖mfderivWithin 𝓘(ℝ) (realModel d) (inclusion ∘ p.piece i)
        (p.pieceInterval i) t 1‖ := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  have hd := mfderiv_comp_mfderivWithin t
    ((hinc (p.piece i t)).mdifferentiableAt (by simp))
    ((p.piece_c1 i).mdifferentiableOn (by simp) t ht)
    (((uniqueDiffOn_Icc (p.time_strictMono Fin.castSucc_lt_succ)).uniqueMDiffOn) t ht)
  simp only [IntrinsicPiecewiseC1Path.pieceInterval]
  rw [hd]
  rw [norm_eq_sqrt_real_inner]
  change Real.sqrt (hermitianTangentRealPairing h _ _ _) =
    Real.sqrt (g.inner _ _ _)
  rw [hpair]
  rfl

/-- The Hermitian length of an intrinsic piecewise C1 path equals the sum of the ambient Riemannian
lengths of its included pieces when the real tangent pairings agree. -/
theorem IntrinsicPiecewiseC1Path.length_eq_sum_ambient_pathELength
    (inclusion : L → M)
    (hinc : ContMDiff (modelWithCornersSelf ℝ (Fin r → ℝ)) (realModel d) 1 inclusion)
    (h : HermitianTangentMetricCore d M)
    (g : ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (hpair : ∀ x v w, g.inner x v w = hermitianTangentRealPairing h x v w)
    {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨g.toRiemannianMetric⟩
    p.length inclusion h = ∑ i : Fin (p.n + 1),
      pathELength (realModel d) (inclusion ∘ p.piece i)
        (p.time i.castSucc) (p.time i.succ) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  unfold IntrinsicPiecewiseC1Path.length
  apply Finset.sum_congr rfl
  intro i _
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  change ENNReal.ofReal (p.speed inclusion h i t) = _
  exact (congrArg ENNReal.ofReal
    (p.speed_eq_ambient_norm inclusion hinc h g hpair i ht)).trans (ofReal_norm _)

/-- The single-piece intrinsic path associated with a C1 curve on `[0,1]`. (Lee, §11, pp.275–279) -/
def IntrinsicPiecewiseC1Path.ofCurve
    (γ : ℝ → L)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Fin r → ℝ) 1 γ (Icc 0 1)) :
    IntrinsicPiecewiseC1Path (r := r) (γ 0) (γ 1) where
  n := 0
  time := fun i ↦ (i.val : ℝ)
  time_strictMono := by
    intro i j hij
    change (i.val : ℝ) < (j.val : ℝ)
    exact_mod_cast (show i.val < j.val from hij)
  time_zero := by norm_num
  time_one := by norm_num
  piece := fun _ ↦ γ
  piece_c1 := fun i ↦ by
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simpa using hγ
  source := rfl
  target := rfl
  junction := fun i ↦ Fin.elim0 i

/-- The intrinsic Hermitian distance between the endpoints of a C1 curve is bounded by the ambient
Riemannian length of its inclusion. -/
theorem intrinsicHermitianLeafEDist_le_included_curve
    (inclusion : L → M)
    (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) 1 inclusion)
    (h : HermitianTangentMetricCore d M)
    (g : ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (hpair : ∀ x v w, g.inner x v w = hermitianTangentRealPairing h x v w)
    (γ : ℝ → L)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Fin r → ℝ) 1 γ (Icc 0 1)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨g.toRiemannianMetric⟩
    intrinsicHermitianLeafEDist (r := r) inclusion h (γ 0) (γ 1) ≤
      pathELength (realModel d) (inclusion ∘ γ) 0 1 := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  let p := IntrinsicPiecewiseC1Path.ofCurve γ hγ
  have hp := p.length_eq_sum_ambient_pathELength inclusion hinc h g hpair
  have hi : intrinsicHermitianLeafEDist (r := r) inclusion h (γ 0) (γ 1) ≤
      p.length inclusion h := iInf_le _ p
  apply hi.trans_eq
  change p.length inclusion h = ∑ i : Fin 1,
    pathELength (realModel d) (inclusion ∘ γ) (i.val : ℝ) ((i.val + 1 : ℕ) : ℝ) at hp
  simpa only [Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, Nat.zero_add, Nat.cast_one] using hp

/-- A uniform ambient speed bound for an included intrinsic C1 curve on `[0,1]` bounds the intrinsic
Hermitian distance between its endpoints. -/
theorem intrinsicHermitianLeafEDist_le_curve_speed_bound
    (inclusion : L → M)
    (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) 1 inclusion)
    (h : HermitianTangentMetricCore d M)
    (g : ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (hpair : ∀ x v w, g.inner x v w = hermitianTangentRealPairing h x v w)
    (γ : ℝ → L)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Fin r → ℝ) 1 γ (Icc 0 1))
    (B : ℝ) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨g.toRiemannianMetric⟩
    (∀ t ∈ Icc (0 : ℝ) 1,
      ‖mfderivWithin 𝓘(ℝ) (realModel d) (inclusion ∘ γ) (Icc 0 1) t 1‖ ≤ B) →
    intrinsicHermitianLeafEDist (r := r) inclusion h (γ 0) (γ 1) ≤
      ENNReal.ofReal B := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  intro hB
  apply (intrinsicHermitianLeafEDist_le_included_curve inclusion hinc h g hpair γ hγ).trans
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  calc
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal B := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB t ht)
    _ = _ := by simp

end HolomorphicAnosov
namespace HolomorphicAnosov
open Set Filter Manifold Bundle
open scoped _root_.Topology
attribute [local instance] complex_isManifold_real

/-- The intrinsic Hermitian distance along a straight segment in a native chart is at most the
parameter displacement times a uniform metric speed bound. -/
theorem raw_plaque_intrinsic_segment_bound
    {r d : ℕ} {L M : Type*}
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : L → M) (hi : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (e : OpenPartialHomeomorph L (Fin r → ℝ))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ L)
    (q : (Fin r → ℝ) → M) (δ B : ℝ)
    (hbuffer : Metric.ball (0 : Fin r → ℝ) δ ⊆ e.target)
    (hq : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ q (Metric.ball 0 δ))
    (hqi : ∀ v ∈ Metric.ball (0 : Fin r → ℝ) δ, q v = inc (e.symm v))
    (hbound : ∀ u ∈ Metric.ball (0 : Fin r → ℝ) δ, ∀ w : Fin r → ℝ,
      Real.sqrt ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner (q u)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q u w)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q u w)) ≤ B * ‖w‖)
    (a v : Fin r → ℝ) (ha : a ∈ Metric.ball 0 δ) (hv : v ∈ Metric.ball 0 δ) :
    intrinsicHermitianLeafEDist (r := r) inc h (e.symm a) (e.symm v) ≤
      ENNReal.ofReal (B * ‖v-a‖) := by
  let g := StableFoliationsSupport.originalSmoothRealMetric h hh
  let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) := ⟨g.toRiemannianMetric⟩
  let η : ℝ →ᵃ[ℝ] (Fin r → ℝ) := AffineMap.lineMap a v
  have hη : ContMDiff 𝓘(ℝ) 𝓘(ℝ, Fin r → ℝ) ∞ η :=
    contMDiff_iff_contDiff.mpr (AffineMap.contDiff_lineMap _ _)
  have hmem (t : ℝ) (ht : t ∈ Icc 0 1) : η t ∈ Metric.ball (0 : Fin r → ℝ) δ :=
    (convex_ball _ _).mapsTo_lineMap ha hv ht
  have hcurve : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Fin r → ℝ) 1 (e.symm ∘ η) (Icc 0 1) :=
    ((contMDiffOn_symm_of_mem_maximalAtlas he).comp hη.contMDiffOn
      (fun t ht ↦ hbuffer (hmem t ht))).of_le (by simp)
  have hb := intrinsicHermitianLeafEDist_le_included_curve inc (hi.of_le (by simp))
    h g (StableFoliationsSupport.originalSmoothRealMetric_inner h hh) (e.symm ∘ η) hcurve
  simp only [Function.comp_apply, η, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] at hb
  apply hb.trans
  have hpath : pathELength (realModel d) (inc ∘ (e.symm ∘ η)) 0 1 =
      pathELength (realModel d) (q ∘ η) 0 1 := by
    apply pathELength_congr
    intro t ht
    exact (hqi (η t) (hmem t ht)).symm
  rw [hpath, pathELength_eq_lintegral_mfderivWithin_Icc]
  calc
    _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1, ENNReal.ofReal (B * ‖v-a‖) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hd := mfderiv_comp_mfderivWithin t
        ((hq.contMDiffAt (Metric.isOpen_ball.mem_nhds (hmem t ht))).mdifferentiableAt (by simp))
        (hη.contMDiffOn.mdifferentiableOn (by simp) t ht)
        ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)
      rw [hd]
      have hvη : mfderivWithin 𝓘(ℝ) 𝓘(ℝ, Fin r → ℝ) η (Icc 0 1) t 1 = v-a := by
        rw [mfderivWithin_eq_fderivWithin,
          AffineMap.hasDerivWithinAt_lineMap.hasFDerivWithinAt.fderivWithin
            (uniqueDiffOn_Icc zero_lt_one t ht)]
        change (1 : ℝ) • (v-a) = v-a
        exact one_smul ℝ (v-a)
      change ‖mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q (η t)
        (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, Fin r → ℝ) η (Icc 0 1) t 1)‖ₑ ≤ _
      rw [hvη, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      exact hbound (η t) (hmem t ht) (v-a)
    _ = _ := by simp


/-- A radial displacement in a moving plaque stays in a fixed buffered intrinsic plaque when its
starting-point distance plus its radial length bound is below the first-exit cost. (Lee, §11,
pp.275–279) -/
theorem native_plaque_radial_transfer_confinement_g18
    {r d : ℕ} {L M : Type*}
    [TopologicalSpace L] [T2Space L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : L → M) (hi : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (hinj : ∀ z, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z))
    (e₀ e₁ : OpenPartialHomeomorph L (Fin r → ℝ))
    (he₀ : e₀ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ L)
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ L)
    (q₀ q₁ : (Fin r → ℝ) → M) (δ₀ δ₁ R m A B : ℝ)
    (hR : 0 < R) (hRδ : R < δ₀) (hm : 0 < m) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbuf₀ : ball (0 : Fin r → ℝ) δ₀ ⊆ e₀.target)
    (hbuf₁ : ball (0 : Fin r → ℝ) δ₁ ⊆ e₁.target)
    (hq₀ : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ q₀ (ball 0 δ₀))
    (hq₁ : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ q₁ (ball 0 δ₁))
    (heq₀ : ∀ v ∈ ball (0 : Fin r → ℝ) δ₀, q₀ v = inc (e₀.symm v))
    (heq₁ : ∀ v ∈ ball (0 : Fin r → ℝ) δ₁, q₁ v = inc (e₁.symm v))
    (hlo : ∀ u ∈ ball (0 : Fin r → ℝ) δ₀, ∀ w : Fin r → ℝ,
      m * ‖w‖ ≤ Real.sqrt
        ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner (q₀ u)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q₀ u w)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q₀ u w)))
    (hup : ∀ u ∈ ball (0 : Fin r → ℝ) δ₁, ∀ w : Fin r → ℝ,
      Real.sqrt ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner (q₁ u)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q₁ u w)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q₁ u w)) ≤ B * ‖w‖)
    (x : L) (hx : x ∈ e₀.source) (he0 : e₀ x = 0)
    (a v : Fin r → ℝ) (ha : a ∈ ball 0 δ₁) (hv : v ∈ ball 0 δ₁)
    (hanchor : intrinsicHermitianLeafEDist (r := r) inc h x (e₁.symm a) ≤
      ENNReal.ofReal A)
    (hbudget : A + B * ‖v - a‖ < m * R) :
    e₁.symm v ∈ e₀.source ∧ e₀ (e₁.symm v) ∈ ball (0 : Fin r → ℝ) R := by
  apply native_plaque_intrinsic_ball_confinement h hh inc e₀ he₀ q₀ δ₀ R m
    hR hRδ hm hbuf₀ hq₀ heq₀ hlo hx he0
  have hrad := raw_plaque_intrinsic_segment_bound h hh inc hi e₁ he₁ q₁ δ₁ B
    hbuf₁ hq₁ heq₁ hup a v ha hv
  calc
    intrinsicHermitianLeafEDist (r := r) inc h x (e₁.symm v) ≤
        intrinsicHermitianLeafEDist (r := r) inc h x (e₁.symm a) +
        intrinsicHermitianLeafEDist (r := r) inc h (e₁.symm a) (e₁.symm v) :=
      intrinsicHermitianLeafEDist_triangle h hh inc hi hinj _ _ _
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal (B * ‖v - a‖) := add_le_add hanchor hrad
    _ = ENNReal.ofReal (A + B * ‖v - a‖) :=
      (ENNReal.ofReal_add hA (mul_nonneg hB (norm_nonneg _))).symm
    _ < ENNReal.ofReal (m * R) := (ENNReal.ofReal_lt_ofReal_iff (mul_pos hm hR)).mpr hbudget

/-- Endpoints at uniformly small intrinsic distance from an intrinsically continuous moving anchor
remain in a fixed buffered chart near the original anchor. (Lee, §11) -/
theorem native_plaque_moving_endpoint_confinement_g18
    {r d : ℕ} {L M P : Type*}
    [TopologicalSpace P] [TopologicalSpace L] [T2Space L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : L → M) (hi : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (hinj : ∀ z, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z))
    (e : OpenPartialHomeomorph L (Fin r → ℝ))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ L)
    (q : (Fin r → ℝ) → M) (δ R m ε : ℝ)
    (hR : 0 < R) (hRδ : R < δ) (hm : 0 < m) (hε : 0 ≤ ε) (hsmall : ε < m * R)
    (hbuf : ball (0 : Fin r → ℝ) δ ⊆ e.target)
    (hq : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ q (ball 0 δ))
    (heq : ∀ v ∈ ball (0 : Fin r → ℝ) δ, q v = inc (e.symm v))
    (hlo : ∀ u ∈ ball (0 : Fin r → ℝ) δ, ∀ w : Fin r → ℝ,
      m * ‖w‖ ≤ Real.sqrt
        ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner (q u)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q u w)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q u w)))
    (anchor endpoint : P → L) (p₀ : P) (hc : ContinuousAt anchor p₀)
    (hx : anchor p₀ ∈ e.source) (he0 : e (anchor p₀) = 0)
    (hclose : ∀ᶠ p in 𝓝 p₀,
      intrinsicHermitianLeafEDist (r := r) inc h (anchor p) (endpoint p) ≤ ENNReal.ofReal ε) :
    ∀ᶠ p in 𝓝 p₀, endpoint p ∈ e.source ∧ e (endpoint p) ∈ ball (0 : Fin r → ℝ) R := by
  let A : ℝ := (m * R - ε) / 2
  have hA : 0 < A := by dsimp [A]; linarith
  have hbudget : A + ε < m * R := by dsimp [A]; linarith
  have hself : intrinsicHermitianLeafEDist (r := r) inc h (anchor p₀) (anchor p₀) = 0 := by
    obtain ⟨em, _, hem⟩ := hermitian_pullback_emetric h hh inc hi hinj
    rw [← hem]
    exact @edist_self L em.toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (EMetricSpace.toWeakEMetricSpace L).toWeakPseudoEMetricSpace _
  have hball := intrinsicHermitianLeafEDist_ball_isOpen h hh inc hi hinj (anchor p₀)
    (ENNReal.ofReal A)
  have hnear : ∀ᶠ p in 𝓝 p₀,
      intrinsicHermitianLeafEDist (r := r) inc h (anchor p₀) (anchor p) < ENNReal.ofReal A :=
    hc (hball.mem_nhds (by simpa only [Set.mem_ofPred_eq, hself, ENNReal.ofReal_pos] using hA))
  filter_upwards [hnear, hclose] with p hp hpclose
  apply native_plaque_intrinsic_ball_confinement h hh inc e he q δ R m
    hR hRδ hm hbuf hq heq hlo hx he0
  calc
    intrinsicHermitianLeafEDist (r := r) inc h (anchor p₀) (endpoint p) ≤
        intrinsicHermitianLeafEDist (r := r) inc h (anchor p₀) (anchor p) +
        intrinsicHermitianLeafEDist (r := r) inc h (anchor p) (endpoint p) :=
      intrinsicHermitianLeafEDist_triangle h hh inc hi hinj _ _ _
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal ε := add_le_add hp.le hpclose
    _ = ENNReal.ofReal (A + ε) := (ENNReal.ofReal_add hA.le hε).symm
    _ < ENNReal.ofReal (m * R) := (ENNReal.ofReal_lt_ofReal_iff (mul_pos hm hR)).mpr hbudget

end HolomorphicAnosov


