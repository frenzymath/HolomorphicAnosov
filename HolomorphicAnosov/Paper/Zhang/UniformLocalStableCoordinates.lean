import HolomorphicAnosov.Geometry.NativePlaqueIntrinsicPathBoundsLowerG18
import HolomorphicAnosov.Geometry.ParallelCoordinatePairsAffineGermG5
import HolomorphicAnosov.Geometry.NormalizedLocalCoordinateContinuousG5
import HolomorphicAnosov.Geometry.NativeComplexStableLeafDatum
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinate
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HolomorphicAnosov.Analysis.ParametricInverseNeighborhoodG2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import HolomorphicAnosov.Analysis.MetricPullbackCompactLowerBound
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import HolomorphicAnosov.Geometry.ImmersionRiemannianMetric
import HolomorphicAnosov.Geometry.IntrinsicPiecewiseC1RiemannianEDist
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalSmoothRealMetricInner
import HolomorphicAnosov.Geometry.IntrinsicChartFirstExit
import Mathlib.Geometry.Manifold.Riemannian.Basic
import HolomorphicAnosov.Geometry.HermitianLeafPathDistance
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import Mathlib.Topology.Separation.Regular
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Basic.Real.Basic
import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinateAffineGerm
import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Analysis.Calculus.MeanValue
import HolomorphicAnosov.Geometry.Riemannian.MovingPathLength
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.ContinuousOn
import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinateDerivative
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.StableCoordinateDerivativeInvertible
import HolomorphicAnosov.Geometry.NativeComplexStableLeafRank
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Topology.Metrizable.Uniformity
import HolomorphicAnosov.Geometry.DiffeomorphOfExhaustion


noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov
open Manifold Bundle
attribute [local instance] complex_isManifold_real
/-- Jointly continuous coordinate first jets of a plaque family define a continuous family of
tangent vectors in any compatible ambient chart. -/
private theorem moving_plaque_tangent_continuous
    {P E H M : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold 𝓘(ℝ,H) ∞ M]
    (V : Set P) (D : Set E) (hD : IsOpen D)
    (q : P → E → M) (a : OpenPartialHomeomorph M H)
    (ha : ContMDiffOn 𝓘(ℝ,H) 𝓘(ℝ,H) 1 a.symm a.target)
    (hqa : ∀ x ∈ V, ∀ v ∈ D, q x v ∈ a.source)
    (hc : ContinuousOn (fun z : P × E ↦ a (q z.1 z.2)) (V ×ˢ D))
    (hδ : ContinuousOn (fun z : P × E ↦ fderiv ℝ (fun v ↦ a (q z.1 v)) z.2)
      (V ×ˢ D))
    (hd : ∀ x ∈ V, ∀ v ∈ D, DifferentiableAt ℝ (fun w ↦ a (q x w)) v) :
    Continuous (fun z : (V × D) × E ↦
      (⟨q z.1.1 z.1.2, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,H) (q z.1.1) z.1.2 z.2⟩ :
        TangentBundle 𝓘(ℝ,H) M)) := by
  let j : (V × D) × E → P × E := fun z ↦ (z.1.1.val,z.1.2.val)
  have hj : Continuous j := by fun_prop
  have hjmem z : j z ∈ V ×ˢ D := ⟨z.1.1.property,z.1.2.property⟩
  let k : (V × D) × E → TangentBundle 𝓘(ℝ,H) H := fun z ↦
    ⟨a (q z.1.1 z.1.2), fderiv ℝ (fun v ↦ a (q z.1.1 v)) z.1.2 z.2⟩
  have hk : Continuous k :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ,H)).symm.continuous.comp
      ((hc.comp_continuous hj hjmem).prodMk
        ((hδ.comp_continuous hj hjmem).clm_apply continuous_snd))
  have hcont := (ha.continuousOn_tangentMapWithin le_rfl
    a.open_target.uniqueMDiffOn).comp_continuous hk
    (fun z ↦ a.map_source (hqa _ z.1.1.property _ z.1.2.property))
  apply hcont.congr
  intro z
  have hmem := hqa _ z.1.1.property _ z.1.2.property
  have he : (q z.1.1.val) =ᶠ[𝓝 z.1.2.val]
      (a.symm ∘ fun v ↦ a (q z.1.1.val v)) := by
    filter_upwards [hD.mem_nhds z.1.2.property] with v hv
    exact (a.left_inv (hqa _ z.1.1.property v hv)).symm
  have hai := (ha _ (a.map_source hmem)).contMDiffAt
    (a.open_target.mem_nhds (a.map_source hmem)) |>.mdifferentiableAt one_ne_zero
  have hder := he.mfderiv_eq (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,H))
  rw [mfderiv_comp (f := fun v : E ↦ a (q z.1.1.val v)) (g := a.symm) _ hai
      ((hd _ z.1.1.property _ z.1.2.property).mdifferentiableAt),
    mfderiv_eq_fderiv] at hder
  symm
  apply TotalSpace.ext (a.left_inv hmem).symm
  apply heq_of_eq
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,H) (q z.1.1.val) z.1.2.val z.2 =
    mfderivWithin 𝓘(ℝ,H) 𝓘(ℝ,H) a.symm a.target
      (a (q z.1.1.val z.1.2.val))
        (fderiv ℝ (fun v ↦ a (q z.1.1.val v)) z.1.2.val z.2)
  rw [mfderivWithin_of_isOpen a.open_target (a.map_source hmem), hder]
  rfl

/-- A compact continuous family of injective finite-dimensional linear maps has uniform positive
lower and finite upper bounds in a continuous tangent metric. -/
private theorem compact_injective_tangent_bounds
    {X E H M : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold 𝓘(ℝ,H) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,H) ∞ H
      (fun x : M ↦ TangentSpace 𝓘(ℝ,H) x))
    (b : X → M) (Q : ∀ x, E →L[ℝ] TangentSpace 𝓘(ℝ,H) (b x))
    (hQ : Continuous (fun z : X × E ↦
      (⟨b z.1, Q z.1 z.2⟩ : TangentBundle 𝓘(ℝ,H) M)))
    (hinj : ∀ x, Function.Injective (Q x)) :
    let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,H) x) :=
      ⟨g.toRiemannianMetric⟩
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ x w, c * ‖w‖ ≤ ‖Q x w‖ ∧ ‖Q x w‖ ≤ C * ‖w‖ := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,H) x) :=
    ⟨g.toRiemannianMetric⟩
  let T := Metric.sphere (0 : E) 1
  let : CompactSpace T := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  obtain ⟨c,hc0,hc⟩ := Analysis.exists_uniform_metric_pullback_lower_bound g b Q hQ hinj
  have hlower (x : X) (w : E) : c * ‖w‖ ≤ ‖Q x w‖ := hc x w
  have hnorm := FixedBlockEstimates.Native.continuous_original_norm g
    (fun z : X × T ↦ b z.1) (fun z ↦ Q z.1 z.2.val)
    (hQ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hnorm.continuousOn
  refine ⟨c,max C 0,hc0,le_max_right _ _,?_⟩
  intro x w
  by_cases hw : w = 0
  · simp [hw]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let u : T := ⟨‖w‖⁻¹ • w, by
    simp only [T, Metric.mem_sphere, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']⟩
  have hu := hC (x,u) (mem_univ _)
  have he : ‖Q x u.val‖ = ‖w‖⁻¹ * ‖Q x w‖ := by
    simp only [u, map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  simp only [norm_norm] at hu
  rw [he] at hu
  constructor
  · exact hlower x w
  · have ht := mul_le_mul_of_nonneg_left hu hn.le
    have hnC : C ≤ max C 0 := le_max_left _ _
    have hb := mul_le_mul_of_nonneg_right hnC hn.le
    have ht' : ‖Q x w‖ ≤ C * ‖w‖ := by
      simpa only [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul, mul_comm] using ht
    exact ht'.trans hb



/-- Composing a family with jointly continuous first jets with a `C¹` map preserves joint continuity
of the first jets. -/
private theorem composed_first_jet_family
    {P E A B : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (q : P → E → A) (D : P × E → E →L[ℝ] A)
    (Ω : Set (P × E)) (U : Set A) (hU : IsOpen U)
    (hq : ContinuousOn (fun p : P × E ↦ q p.1 p.2) Ω)
    (hD : ContinuousOn D Ω)
    (hqd : ∀ p ∈ Ω, HasFDerivAt (q p.1) (D p) p.2)
    (hqU : ∀ p ∈ Ω, q p.1 p.2 ∈ U)
    (t : A → B) (ht : ContDiffOn ℝ 1 t U) :
    ContinuousOn (fun p : P × E ↦ t (q p.1 p.2)) Ω ∧
    ContinuousOn (fun p : P × E ↦ fderiv ℝ (fun v ↦ t (q p.1 v)) p.2) Ω ∧
    ∀ p ∈ Ω, HasFDerivAt (fun v ↦ t (q p.1 v))
      ((fderiv ℝ t (q p.1 p.2)).comp (D p)) p.2 := by
  have hd p (hp : p ∈ Ω) : HasFDerivAt (fun v ↦ t (q p.1 v))
      ((fderiv ℝ t (q p.1 p.2)).comp (D p)) p.2 := by
    have ht' := (ht.differentiableOn one_ne_zero (q p.1 p.2) (hqU p hp)).differentiableAt
      (hU.mem_nhds (hqU p hp))
    exact ht'.hasFDerivAt.comp p.2 (hqd p hp)
  refine ⟨ht.continuousOn.comp hq hqU, ?_, hd⟩
  exact (((ht.continuousOn_fderiv_of_isOpen hU le_rfl).comp hq hqU).clm_comp hD).congr
    (fun p hp ↦ (hd p hp).fderiv)

/-- A holomorphic scalar transverse coordinate maps a plaque family with continuous ambient first
jets to a family with jointly continuous scalar first jets. -/
private theorem scalar_native_first_jets
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (V W : Set M) (hW : IsOpen W)
    (a : OpenPartialHomeomorph M (ComplexModel d))
    (ha : a ∈ IsManifold.maximalAtlas (complexModel d) ∞ M)
    (r : ℝ) (q : M → (Fin 2 → ℝ) → M)
    (hqa : ∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) r, q x v ∈ a.source)
    (hqW : ∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) r, q x v ∈ W)
    (hq : ContinuousOn (fun xv : M × (Fin 2 → ℝ) ↦ a (q xv.1 xv.2))
      (V ×ˢ Metric.ball 0 r))
    (hD : ContinuousOn (fun xv : M × (Fin 2 → ℝ) ↦
      fderiv ℝ (fun v ↦ a (q xv.1 v)) xv.2) (V ×ˢ Metric.ball 0 r))
    (hqd : ∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) r,
      HasFDerivAt (fun w ↦ a (q x w)) (fderiv ℝ (fun w ↦ a (q x w)) v) v)
    (t : M → ℂ) (ht : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ t W) :
    ContinuousOn (fun xv : M × (Fin 2 → ℝ) ↦ t (q xv.1 xv.2))
      (V ×ˢ Metric.ball 0 r) ∧
    ContinuousOn (fun xv : M × (Fin 2 → ℝ) ↦
      fderiv ℝ (fun v ↦ t (q xv.1 v)) xv.2) (V ×ˢ Metric.ball 0 r) ∧
    ∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) r,
      HasFDerivAt (fun w ↦ t (q x w)) (fderiv ℝ (fun w ↦ t (q x w)) v) v := by
  let C : Set (ComplexModel d) := a.target ∩ a.symm ⁻¹' W
  have hC : IsOpen C := a.symm.continuousOn.isOpen_inter_preimage a.open_target hW
  have htA : ContDiffOn ℝ 1 (t ∘ a.symm) C := by
    have hs : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ (t ∘ a.symm) C :=
      ht.comp ((contMDiffOn_symm_of_mem_maximalAtlas ha).mono inter_subset_left)
        (fun z hz ↦ hz.2)
    exact hs.contDiffOn.restrict_scalars ℝ |>.of_le (by simp)
  have hqC : ∀ p ∈ V ×ˢ Metric.ball (0 : Fin 2 → ℝ) r,
      a (q p.1 p.2) ∈ C := by
    intro p hp
    exact ⟨a.map_source (hqa p.1 hp.1 p.2 hp.2), by
      simpa only [mem_preimage, a.left_inv (hqa p.1 hp.1 p.2 hp.2)] using hqW p.1 hp.1 p.2 hp.2⟩
  obtain ⟨hc, hd, hder⟩ := composed_first_jet_family
    (fun x v ↦ a (q x v))
    (fun p : M × (Fin 2 → ℝ) ↦ fderiv ℝ (fun v ↦ a (q p.1 v)) p.2)
    (V ×ˢ Metric.ball 0 r) C hC hq hD
    (fun p hp ↦ hqd p.1 hp.1 p.2 hp.2) hqC (t ∘ a.symm) htA
  have heq (x : M) (hx : x ∈ V) (v : Fin 2 → ℝ) (hv : v ∈ Metric.ball 0 r) :
      (fun w ↦ t (q x w)) =ᶠ[𝓝 v] (fun w ↦ (t ∘ a.symm) (a (q x w))) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hv] with w hw
    simp only [Function.comp_apply, a.left_inv (hqa x hx w hw)]
  refine ⟨hc.congr (fun p hp ↦ ?_), hd.congr (fun p hp ↦ ?_), ?_⟩
  · simp only [Function.comp_apply, a.left_inv (hqa p.1 hp.1 p.2 hp.2)]
  · exact (heq p.1 hp.1 p.2 hp.2).fderiv_eq
  · intro x hx v hv
    exact ((hder (x, v) ⟨hx, hv⟩).congr_of_eventuallyEq (heq x hx v hv)).differentiableAt.hasFDerivAt

/-- A jointly continuous centered plaque family lies in any prescribed open neighborhood of its
center after shrinking the parameter neighborhood and plaque radius. -/
private theorem moving_plaque_range_shrink
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    (V : Set M) (hV : IsOpen V) (p : M) (hpV : p ∈ V)
    (a : OpenPartialHomeomorph M (ComplexModel d))
    (r : ℝ) (hr : 0 < r) (q : M → (Fin 2 → ℝ) → M) (hq0 : q p 0 = p)
    (hqa : ∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) r, q x v ∈ a.source)
    (hq : ContinuousOn (fun xv : M × (Fin 2 → ℝ) ↦ a (q xv.1 xv.2))
      (V ×ˢ Metric.ball 0 r))
    (W : Set M) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ V' : Set M, IsOpen V' ∧ p ∈ V' ∧ V' ⊆ V ∧
      ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧
        ∀ x ∈ V', ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) r', q x v ∈ W := by
  have hc : ContinuousOn (fun xv : M × (Fin 2 → ℝ) ↦ q xv.1 xv.2)
      (V ×ˢ Metric.ball 0 r) := by
    exact (a.symm.continuousOn.comp hq
      (fun xv hxv ↦ a.map_source (hqa xv.1 hxv.1 xv.2 hxv.2))).congr
      (fun xv hxv ↦ (a.left_inv (hqa xv.1 hxv.1 xv.2 hxv.2)).symm)
  have hat : ContinuousAt (fun xv : M × (Fin 2 → ℝ) ↦ q xv.1 xv.2) (p, 0) :=
    hc.continuousAt ((hV.prod Metric.isOpen_ball).mem_nhds ⟨hpV, Metric.mem_ball_self hr⟩)
  have hev : (fun xv : M × (Fin 2 → ℝ) ↦ q xv.1 xv.2) ⁻¹' W ∈ 𝓝 (p, 0) :=
    hat.preimage_mem_nhds (hW.mem_nhds (by simpa only [hq0] using hpW))
  obtain ⟨V₀, hV₀, D, hD, hprod⟩ := mem_nhds_prod_iff.mp hev
  obtain ⟨V₁, hV₁sub, hV₁, hpV₁⟩ := mem_nhds_iff.mp hV₀
  obtain ⟨δ, hδ, hδD⟩ := Metric.mem_nhds_iff.mp hD
  refine ⟨V₁ ∩ V, hV₁.inter hV, ⟨hpV₁, hpV⟩, inter_subset_right,
    min δ r, lt_min hδ hr, min_le_right _ _, ?_⟩
  intro x hx v hv
  exact hprod (show (x, v) ∈ V₀ ×ˢ D from
    ⟨hV₁sub hx.1, hδD (Metric.ball_subset_ball (min_le_left δ r) hv)⟩)

end HolomorphicAnosov

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- A plaque parametrization represented by an intrinsic leaf chart has injective derivative with
the same tangent image as the leaf inclusion. -/
private theorem plaque_chart_derivative
    {r d : ℕ} {M L : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    (inc : L → M) (hi : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (hinj : ∀ y, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc y))
    (c : OpenPartialHomeomorph L (Fin r → ℝ))
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ L)
    (q : (Fin r → ℝ) → M) (R : ℝ)
    (hR : Metric.ball (0 : Fin r → ℝ) R ⊆ c.target)
    (hq : ∀ v ∈ Metric.ball (0 : Fin r → ℝ) R, q v = inc (c.symm v))
    (v : Fin r → ℝ) (hv : v ∈ Metric.ball 0 R) :
    Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q v) ∧
    (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q v).range =
      (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc (c.symm v)).range := by
  have hd : c.MDifferentiable 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩
  have he : q =ᶠ[𝓝 v] (inc ∘ c.symm) :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hv) (fun w hw ↦ hq w hw)
  have heD := he.mfderiv_eq (I := 𝓘(ℝ, Fin r → ℝ)) (I' := realModel d)
  rw [mfderiv_comp v (hi.mdifferentiable (by simp) _)
    (hd.mdifferentiableAt_symm (hR hv))] at heD
  rw [heD]
  exact ⟨(hinj _).comp (hd.symm.mfderiv_injective (hR hv)),
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (hd.symm.mfderiv_surjective (hR hv)))⟩

/-- A transverse scalar coordinate with invertible stable restriction has bijective real derivative
on a rank-two real plaque tangent to the stable subspace. -/
private theorem scalar_plaque_derivative_bijective
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (q : (Fin 2 → ℝ) → M) (v : Fin 2 → ℝ)
    (hq : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) (realModel d) q v)
    (hqi : Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) q v))
    (hqr : (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) q v).range =
      ((S (q v)).restrictScalars ℝ).map
        (complexTangentToReal d (q v)).toLinearEquiv.toLinearMap)
    (t : M → ℂ)
    (htc : MDifferentiableAt (complexModel d) 𝓘(ℂ) t (q v))
    (htr : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) t (q v))
    (hB : (localStableCoordinateDerivative S t (q v)).IsInvertible) :
    Function.Bijective (fderiv ℝ (t ∘ q) v) := by
  have hrestrict : mfderiv (realModel d) 𝓘(ℝ, ℂ) t (q v) =
      (mfderiv (complexModel d) 𝓘(ℂ) t (q v)).restrictScalars ℝ := by
    ext w
    rw [htr.mfderiv_abuse, htc.mfderiv_abuse]
    have hd := htc.differentiableWithinAt_writtenInExtChartAt
    change (fderivWithin ℝ (writtenInExtChartAt (complexModel d) 𝓘(ℂ) (q v) t)
      (Set.range (complexModel d)) ((extChartAt (complexModel d) (q v)) (q v))) w =
      (fderivWithin ℂ (writtenInExtChartAt (complexModel d) 𝓘(ℂ) (q v) t)
        (Set.range (complexModel d)) ((extChartAt (complexModel d) (q v)) (q v))) w
    exact congrArg (fun A ↦ A w) (hd.restrictScalars_fderivWithin ℝ (by simp)).symm
  have hchain : fderiv ℝ (t ∘ q) v =
      (mfderiv (realModel d) 𝓘(ℝ, ℂ) t (q v)).comp
        (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) q v) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp v htr hq
  have hinj : Function.Injective (fderiv ℝ (t ∘ q) v) := by
    apply (injective_iff_map_eq_zero (fderiv ℝ (t ∘ q) v)).mpr
    intro w hw
    change TangentSpace 𝓘(ℝ, Fin 2 → ℝ) v at w
    change w = (0 : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) v)
    apply hqi
    rw [map_zero]
    have hm : (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) q v) w ∈
        ((S (q v)).restrictScalars ℝ).map
          (complexTangentToReal d (q v)).toLinearEquiv.toLinearMap := by
      rw [← hqr]
      exact ⟨w, rfl⟩
    obtain ⟨u, hu, he⟩ := hm
    have hz : localStableCoordinateDerivative S t (q v) ⟨u, hu⟩ = 0 := by
      rw [hchain, hrestrict] at hw
      change (mfderiv (complexModel d) 𝓘(ℂ) t (q v))
        ((mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) q v) w) = 0 at hw
      rw [← he] at hw
      exact hw
    have hu0 : (⟨u, hu⟩ : S (q v)) = 0 := hB.injective (hz.trans (map_zero _).symm)
    have huu : u = 0 := congrArg Subtype.val hu0
    rw [← he, huu, map_zero]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Complex.finrank_real_complex] : Module.finrank ℝ (Fin 2 → ℝ) = Module.finrank ℝ ℂ)).mp hinj⟩

end HolomorphicAnosov

noncomputable section
open Set Filter TopologicalSpace _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov

/-- A continuous family of scalar maps with jointly continuous plaque derivatives and bijective
derivative at a marked point has a local inverse preserving the parameter. -/
private theorem scalar_parameter_inverse_neighborhood
    {P : Type*} [TopologicalSpace P]
    (G : P → (Fin 2 → ℝ) → ℂ)
    (δ : P × (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℂ)
    (S : Set (P × (Fin 2 → ℝ))) (hS : IsOpen S)
    (p : P) (hp : (p, 0) ∈ S)
    (hG : ContinuousOn (fun x : P × (Fin 2 → ℝ) ↦ G x.1 x.2) S)
    (hδ : ContinuousOn δ S)
    (hder : ∀ x ∈ S, HasFDerivAt (G x.1) (δ x) x.2)
    (hzero : G p 0 = 0) (hb : Function.Bijective (δ (p, 0))) :
    ∃ A : (Fin 2 → ℝ) ≃L[ℝ] ℂ, A.toContinuousLinearMap = δ (p, 0) ∧
    ∃ V : Opens P, ∃ hpV : p ∈ V, ∃ r : ℝ, 0 < r ∧
      let U : Set (V × (Fin 2 → ℝ)) := {x | x.2 ∈ Metric.ball 0 r ∧
        A.symm (G x.1.1 x.2) ∈ Metric.ball 0 (r / 8)}
      IsOpen U ∧ (⟨p, hpV⟩, 0) ∈ U ∧
      (∀ x : U, (x.1.1.1, x.1.2) ∈ S) ∧
      ∃ c : U ≃ₜ (Metric.ball (0 : Fin 2 → ℝ) (r / 8) × V),
        ∀ x : U, ((c x).1 : Fin 2 → ℝ) = A.symm (G x.1.1.1 x.1.2) ∧
          (c x).2 = x.1.1 := by
  let A : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (δ (p, 0)).toLinearMap hb).toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = δ (p, 0) := by ext v; rfl
  refine ⟨A, hA, ?_⟩
  apply Analysis.parametric_inverse_neighborhood
    (fun x v ↦ A.symm (G x v))
    (fun x ↦ A.symm.toContinuousLinearMap.comp (δ x)) S hS p hp
  · exact A.symm.continuous.comp_continuousOn hG
  · exact continuousOn_const.clm_comp hδ
  · intro x hx
    exact A.symm.toContinuousLinearMap.hasFDerivAt.comp x.2 (hder x hx)
  · rw [hzero, map_zero]
  · rw [← hA]
    apply ContinuousLinearMap.ext
    intro v
    exact A.symm_apply_apply v

end HolomorphicAnosov

noncomputable section
open Set Filter TopologicalSpace _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
universe u

/-- A scalar transverse coordinate on a moving stable plaque family admits a local inverse
preserving the base point, with uniform lower and upper plaque metric bounds. -/
private theorem native_scalar_inverse_metric_family
    {d : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {S : ContinuousComplexTangentSubbundle (complexModel d) M}
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f S ι L)
    (W : Set M) (hW : IsOpen W) (t : M → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ t W)
    (hB : ∀ x ∈ W, (localStableCoordinateDerivative S.toDistribution t x).IsInvertible)
    (p : M) (hpW : p ∈ W) :
    ∃ (V₀ : Set M) (ρ : ℝ) (q : M → (Fin 2 → ℝ) → M),
      IsOpen V₀ ∧ p ∈ V₀ ∧ V₀ ⊆ W ∧ 0 < ρ ∧
      (∀ x ∈ V₀, q x 0 = x) ∧
      (∀ x ∈ V₀, ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) ρ, q x v ∈ W) ∧
      (∀ x ∈ V₀, ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) (realModel d) ∞
        (q x) (Metric.ball 0 ρ)) ∧
      (∀ x ∈ V₀, ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) ρ,
        Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) (q x) v)) ∧
      Continuous (fun z : (V₀ × Metric.ball (0 : Fin 2 → ℝ) ρ) × (Fin 2 → ℝ) ↦
        (⟨q z.1.1 z.1.2, mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d)
          (q z.1.1) z.1.2 z.2⟩ : TangentBundle (realModel d) M)) ∧
      (∀ x ∈ V₀, ∃ (i : ι) (e : OpenPartialHomeomorph (L i) (Fin 2 → ℝ)),
        e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i) ∧
        Metric.ball (0 : Fin 2 → ℝ) ρ ⊆ e.target ∧
        ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) ρ,
          q x v = (F.partition.leaf i).inclusion (e.symm v)) ∧
      ∃ A : (Fin 2 → ℝ) ≃L[ℝ] ℂ,
      ∃ V : Opens M, ∃ hpV : p ∈ V, ∃ r : ℝ, 0 < r ∧
        let U : Set (V × (Fin 2 → ℝ)) := {x | x.2 ∈ Metric.ball 0 r ∧
          A.symm (t (q x.1.1 x.2) - t x.1.1) ∈ Metric.ball 0 (r / 8)}
        IsOpen U ∧ (⟨p, hpV⟩, 0) ∈ U ∧
        (∀ x : U, (x.1.1.1, x.1.2) ∈ V₀ ×ˢ Metric.ball 0 ρ) ∧
        ∃ c : U ≃ₜ (Metric.ball (0 : Fin 2 → ℝ) (r / 8) × V),
          ∀ x : U,
            ((c x).1 : Fin 2 → ℝ) = A.symm (t (q x.1.1.1 x.1.2) - t x.1.1.1) ∧
            (c x).2 = x.1.1 := by
  obtain ⟨Vj, a, R, q, hVj, hpVj, hVja, ha, hR, hq0, hqa, hqs, hqe,
    hcharts, hderiv, hcont, hjet⟩ := F.local_first_jets p
  obtain ⟨V₀, hV₀, hpV₀, hV₀j, ρ, hρ, hρR, hqW⟩ :=
    moving_plaque_range_shrink Vj hVj p hpVj a R hR q (hq0 p hpVj) hqa hcont W hW hpW
  have hsmall : Metric.ball (0 : Fin 2 → ℝ) ρ ⊆ Metric.ball 0 R := Metric.ball_subset_ball hρR
  have hV₀W : V₀ ⊆ W := by
    intro x hx
    simpa only [hq0 x (hV₀j hx)] using hqW x hx 0 (Metric.mem_ball_self hρ)
  have hprod : V₀ ×ˢ Metric.ball (0 : Fin 2 → ℝ) ρ ⊆ Vj ×ˢ Metric.ball 0 R :=
    Set.prod_mono hV₀j hsmall
  have hscalar := scalar_native_first_jets V₀ W hW a ha ρ q
    (fun x hx v hv ↦ hqa x (hV₀j hx) v (hsmall hv)) hqW
    (hcont.mono hprod) (hjet.mono hprod)
    (fun x hx v hv ↦ hderiv x (hV₀j hx) v (hsmall hv)) t ht
  let G : M → (Fin 2 → ℝ) → ℂ := fun x v ↦ t (q x v) - t x
  let D : M × (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℂ :=
    fun xv ↦ fderiv ℝ (fun v ↦ t (q xv.1 v)) xv.2
  have hG : ContinuousOn (fun xv : M × (Fin 2 → ℝ) ↦ G xv.1 xv.2)
      (V₀ ×ˢ Metric.ball 0 ρ) :=
    hscalar.1.sub (ht.continuousOn.comp continuous_fst.continuousOn
      (fun xv hxv ↦ hV₀W hxv.1))
  have hGD : ∀ xv ∈ V₀ ×ˢ Metric.ball (0 : Fin 2 → ℝ) ρ,
      HasFDerivAt (G xv.1) (D xv) xv.2 := by
    intro xv hxv
    exact (hscalar.2.2 xv.1 hxv.1 xv.2 hxv.2).sub_const (t xv.1)
  have hzero : G p 0 = 0 := by simp only [G, hq0 p hpVj, sub_self]
  have hb : Function.Bijective (D (p, 0)) := by
    obtain ⟨i, e, he, hball, hqleaf⟩ := hcharts p hpVj
    have h0 : (0 : Fin 2 → ℝ) ∈ Metric.ball 0 R := Metric.mem_ball_self hR
    have hqdiff := ((hqs p hpVj).contMDiffAt (Metric.isOpen_ball.mem_nhds h0)).mdifferentiableAt (by simp)
    obtain ⟨hinj, hrange⟩ := plaque_chart_derivative (F.partition.leaf i).inclusion
      (F.partition.leaf i).immersion.contMDiff
      ((F.partition.leaf i).immersion.mfderiv_injective (by simp)) e he (q p) R hball hqleaf 0 h0
    have hqr : (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) (q p) 0).range =
        ((S.toDistribution (q p 0)).restrictScalars ℝ).map
          (complexTangentToReal d (q p 0)).toLinearEquiv.toLinearMap := by
      rw [hrange, (F.partition.leaf i).tangent]
      rw [hqleaf 0 h0]
      rfl
    have htc : MDifferentiableAt (complexModel d) 𝓘(ℂ) t (q p 0) :=
      ((ht p hpW).contMDiffAt (hW.mem_nhds hpW)).mdifferentiableAt (by simp) |>
        fun hh ↦ (hq0 p hpVj).symm ▸ hh
    have htr : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) t (q p 0) := by
      have htc' := (ht p hpW).contMDiffAt (hW.mem_nhds hpW)
      have hr : ContMDiffAt (realModel d) 𝓘(ℝ, ℂ) ∞ t p := by
        rw [contMDiffAt_iff] at htc' ⊢
        exact ⟨htc'.1, htc'.2.restrict_scalars ℝ⟩
      simpa only [hq0 p hpVj] using hr.mdifferentiableAt (by simp)
    exact scalar_plaque_derivative_bijective S.toDistribution (q p) 0 hqdiff hinj hqr
      t htc htr (by rw [hq0 p hpVj]; exact hB p hpW)
  obtain ⟨A, hA, V, hpV, r, hr, hU, hpin, hdom, c, hc⟩ :=
    scalar_parameter_inverse_neighborhood G D (V₀ ×ˢ Metric.ball 0 ρ)
      (hV₀.prod Metric.isOpen_ball) p ⟨hpV₀, Metric.mem_ball_self hρ⟩
      hG hscalar.2.1 hGD hzero hb
  have hqinj : ∀ x ∈ V₀, ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) ρ,
      Function.Injective (mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) (q x) v) := by
    intro x hx v hv
    obtain ⟨i,e,he,hball,hqi⟩ := hcharts x (hV₀j hx)
    exact (plaque_chart_derivative (F.partition.leaf i).inclusion
      (F.partition.leaf i).immersion.contMDiff
      ((F.partition.leaf i).immersion.mfderiv_injective (by simp)) e he (q x) R
      hball hqi v (hsmall hv)).1
  have har : ContMDiffOn (realModel d) (realModel d) 1 a.symm a.target := by
    intro v hv
    have hc := contMDiffOn_symm_of_mem_maximalAtlas ha v hv
    rw [contMDiffWithinAt_iff] at hc ⊢
    refine ⟨hc.1, ?_⟩
    exact (hc.2.restrict_scalars ℝ).of_le (by simp)
  have htan := moving_plaque_tangent_continuous V₀ (Metric.ball 0 ρ) Metric.isOpen_ball
    q a har (fun x hx v hv ↦ hqa x (hV₀j hx) v (hsmall hv))
    (hcont.mono hprod) (hjet.mono hprod)
    (fun x hx v hv ↦ (hderiv x (hV₀j hx) v (hsmall hv)).differentiableAt)
  refine ⟨V₀, ρ, q, hV₀, hpV₀, hV₀W, hρ, fun x hx ↦ hq0 x (hV₀j hx), hqW,
    fun x hx ↦ (hqs x (hV₀j hx)).mono hsmall, hqinj, htan, ?_, A, V, hpV, r, hr,
    hU, hpin, hdom, c, hc⟩
  intro x hx
  obtain ⟨i, e, he, hball, heq⟩ := hcharts x (hV₀j hx)
  exact ⟨i, e, he, hsmall.trans hball, fun v hv ↦ heq v (hsmall hv)⟩

end HolomorphicAnosov

noncomputable section
open Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff ENNReal Bundle
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real


end HolomorphicAnosov
noncomputable section
open Set Filter Metric Manifold Bundle
open scoped ContDiff Manifold _root_.Topology
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
end HolomorphicAnosov

noncomputable section
open Set Filter
open scoped Manifold ContDiff _root_.Topology
namespace HolomorphicAnosov

/-- A holomorphic open partial homeomorphism from a one-dimensional complex manifold to `ℂ` has a
holomorphic inverse. -/
private theorem product_curve_holomorphic_inverse
    {L : Type*} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    [IsManifold (complexModel 1) ∞ L]
    (e : OpenPartialHomeomorph L ℂ)
    (he : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ e e.source) :
    ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ e.symm e.target := by
  let A : ComplexModel 1 ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  intro y hy
  let a := chartAt (ComplexModel 1) (e.symm y)
  let c := a.trans A.toHomeomorph.toOpenPartialHomeomorph
  have hci : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ c.symm c.target :=
    contMDiffOn_chart_symm.comp A.symm.contDiff.contMDiff.contMDiffOn (fun _ hx ↦ hx.2)
  have hx : e.symm y ∈ c.source := ⟨ChartedSpace.mem_chart_source _,mem_univ _⟩
  let k := c.symm.trans e
  have hky : y ∈ k.target := ⟨hy,hx⟩
  have hk : DifferentiableOn ℂ k k.source :=
    (he.comp (hci.mono inter_subset_left) (fun _ hz ↦ hz.2)).contDiffOn.differentiableOn (by simp)
  have hki : DifferentiableOn ℂ k.symm k.target := by
    intro z hz
    exact (Analysis.Complex.coordinateInverseDeriv k hk hz).2.differentiableAt.differentiableWithinAt
  have hkis : ContDiffOn ℂ ∞ k.symm k.target := hki.contDiffOn k.open_target
  have hksy : k.symm y ∈ c.target := (k.map_target hky).1
  have hcAt := (hci _ hksy).contMDiffAt (c.open_target.mem_nhds hksy)
  have hh := hcAt.comp y ((hkis.contDiffAt (k.open_target.mem_nhds hky)).contMDiffAt)
  apply (hh.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [k.open_target.mem_nhds hky] with z hz
  change e.symm z = c.symm (c (e.symm z))
  exact (c.left_inv hz.2).symm

end HolomorphicAnosov
namespace HolomorphicAnosov
open Set Filter Metric Manifold Bundle
open scoped ContDiff Manifold _root_.Topology
attribute [local instance] complex_isManifold_real

/-- Uniform lower and upper plaque speed bounds give a biholomorphic scalar chart on a sufficiently
small intrinsic distance ball, whose image contains a scalar disk. -/
private theorem exact_intrinsic_scalar_chart
    {r d : ℕ} {L M : Type*}
    [TopologicalSpace L] [T2Space L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [ChartedSpace (ComplexModel 1) L] [IsManifold (complexModel 1) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : L → M) (hi : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (hinj : ∀ z, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z))
    (e : OpenPartialHomeomorph L (Fin r → ℝ))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ L)
    (q : (Fin r → ℝ) → M) (δ R m B ε : ℝ)
    (hR : 0 < R) (hRδ : R < δ) (hm : 0 < m)
    (hbuffer : ball (0 : Fin r → ℝ) δ ⊆ e.target)
    (hq : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ q (ball 0 δ))
    (hqi : ∀ v ∈ ball (0 : Fin r → ℝ) δ, q v = inc (e.symm v))
    (hbound : ∀ u ∈ ball (0 : Fin r → ℝ) δ, ∀ w : Fin r → ℝ,
      m * ‖w‖ ≤ Real.sqrt
        ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner (q u)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q u w)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q u w)) ∧
      Real.sqrt ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner (q u)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q u w)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q u w)) ≤ B * ‖w‖)
    (x : L) (hx : x ∈ e.source) (he0 : e x = 0)
    (t : M → ℂ)
    (ht : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ (t ∘ inc)
      (e.source ∩ e ⁻¹' ball 0 δ))
    (k : OpenPartialHomeomorph (Fin r → ℝ) ℂ)
    (hk : ball (0 : Fin r → ℝ) δ ⊆ k.source)
    (hkfun : ∀ v ∈ ball (0 : Fin r → ℝ) δ, k v = t (q v) - t (inc x))
    (hsmall : ∀ w ∈ ball (0 : ℂ) ε,
      w ∈ k.target ∧ k.symm w ∈ ball (0 : Fin r → ℝ) δ ∧ B * ‖k.symm w‖ < m*R) :
    let W : Set L := {y | intrinsicHermitianLeafEDist (r := r) inc h x y < ENNReal.ofReal (m*R)}
    ∃ c : OpenPartialHomeomorph L ℂ,
      c.source = W ∧ (∀ y ∈ W, c y = t (inc y) - t (inc x)) ∧
      ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ c W ∧
      ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ c.symm c.target ∧
      ball (0 : ℂ) ε ⊆ c.target := by
  let W : Set L := {y | intrinsicHermitianLeafEDist (r := r) inc h x y < ENNReal.ofReal (m*R)}
  have hW : IsOpen W := intrinsicHermitianLeafEDist_ball_isOpen h hh inc hi hinj x _
  let eδ := e.trans (OpenPartialHomeomorph.ofSet (ball (0 : Fin r → ℝ) δ) isOpen_ball)
  let j := eδ.trans k
  have hconf (y : L) (hy : y ∈ W) : y ∈ e.source ∧ e y ∈ ball (0 : Fin r → ℝ) R :=
    native_plaque_intrinsic_ball_confinement h hh inc e he q δ R m hR hRδ hm hbuffer hq hqi
      (fun u hu w ↦ (hbound u hu w).1) hx he0 hy
  have hWj : W ⊆ j.source := by
    intro y hy
    have hc := hconf y hy
    have hv := ball_subset_ball hRδ.le hc.2
    exact ⟨⟨hc.1,hv⟩,hk hv⟩
  let c := j.restrOpen W hW
  have hsource : c.source = W := inter_eq_right.mpr hWj
  have hformula (y : L) (hy : y ∈ W) : c y = t (inc y) - t (inc x) := by
    have hc := hconf y hy
    change k (e y) = _
    rw [hkfun _ (ball_subset_ball hRδ.le hc.2), hqi _ (ball_subset_ball hRδ.le hc.2), e.left_inv hc.1]
  have hhol : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ c W := by
    apply ((ht.mono (fun y hy ↦ ⟨(hconf y hy).1,ball_subset_ball hRδ.le (hconf y hy).2⟩)).sub
      contMDiffOn_const).congr
    intro y hy
    exact hformula y hy
  refine ⟨c,hsource,hformula,hhol,?_,?_⟩
  · apply product_curve_holomorphic_inverse c
    rw [hsource]
    exact hhol
  · intro w hw
    obtain ⟨hwk,hwδ,hwB⟩ := hsmall w hw
    have hz := e.map_target (hbuffer hwδ)
    have hjt : w ∈ j.target := ⟨hwk,hwδ,hbuffer hwδ⟩
    have hzero : e.symm 0 = x := by rw [← he0,e.left_inv hx]
    have hdist := raw_plaque_intrinsic_segment_bound h hh inc hi e he q δ B hbuffer hq hqi
      (fun u hu v ↦ (hbound u hu v).2) 0 (k.symm w)
      (mem_ball_self (hR.trans hRδ)) hwδ
    rw [hzero,sub_zero] at hdist
    have hleaf : e.symm (k.symm w) ∈ W :=
      hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hm hR)).mpr hwB)
    exact ⟨hjt,hleaf⟩

end HolomorphicAnosov
noncomputable section
open Set Filter
open scoped _root_.Topology
namespace HolomorphicAnosov

/-- An open neighborhood of a zero-section point contains a product of a parameter neighborhood and
a closed model ball of positive radius. -/
private theorem open_product_closed_ball
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E]
    {U : Set (P × E)} (hU : IsOpen U) {p : P} (hp : (p,0) ∈ U) :
    ∃ V : Set P, IsOpen V ∧ p ∈ V ∧ ∃ δ : ℝ, 0 < δ ∧
      V ×ˢ Metric.closedBall (0 : E) δ ⊆ U := by
  obtain ⟨V,hV,D,hD,hsub⟩ := mem_nhds_prod_iff.mp (hU.mem_nhds hp)
  obtain ⟨V',hV'V,hV',hpV'⟩ := mem_nhds_iff.mp hV
  obtain ⟨r,hr,hDr⟩ := Metric.mem_nhds_iff.mp hD
  refine ⟨V',hV',hpV',r/2,by positivity,?_⟩
  exact (Set.prod_mono hV'V
    ((Metric.closedBall_subset_ball (by linarith : r/2 < r)).trans hDr)).trans hsub

/-- A local inverse preserving the parameter admits common source and target balls over a compact
neighborhood of its zero-section mark. -/
private theorem parameter_inverse_common_core
    {P E : Type*} [TopologicalSpace P] [LocallyCompactSpace P] [RegularSpace P]
    [NormedAddCommGroup E]
    (G : P → E → E) (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (U : Set (P × E))
    (hU : IsOpen U)
    (hUdef : ∀ z, z ∈ U ↔ z.2 ∈ Metric.ball 0 r ∧ G z.1 z.2 ∈ Metric.ball 0 R)
    (hG0 : ∀ p, G p 0 = 0)
    (c : U ≃ₜ (Metric.ball (0 : E) R × P))
    (hc : ∀ z : U, ((c z).1 : E) = G z.1.1 z.1.2 ∧ (c z).2 = z.1.1)
    (p : P) :
    ∃ K : Set P, IsCompact K ∧ p ∈ interior K ∧
      ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧ ε < R ∧
        K ×ˢ Metric.closedBall (0 : E) δ ⊆ U ∧
        ∀ x ∈ K, ∀ v : Metric.ball (0 : E) R,
          ‖(v : E)‖ < ε → (c.symm (v,x)).1.2 ∈ Metric.ball (0 : E) (δ/2) := by
  have hpU : (p,0) ∈ U := (hUdef _).mpr
    ⟨Metric.mem_ball_self hr, by rw [hG0]; exact Metric.mem_ball_self hR⟩
  obtain ⟨V,hV,hpV,δ,hδ,hVδ⟩ := open_product_closed_ball hU hpU
  let z0 : U := ⟨(p,0),hpU⟩
  let v0 : Metric.ball (0 : E) R := ⟨0,Metric.mem_ball_self hR⟩
  have hcz : c z0 = (v0,p) := by
    apply Prod.ext
    · apply Subtype.ext
      exact (hc z0).1.trans (hG0 p)
    · exact (hc z0).2
  have hinv0 : (c.symm (v0,p)).1.2 = 0 := by rw [← hcz, c.symm_apply_apply]
  have hi : Continuous (fun z : Metric.ball (0 : E) R × P ↦ (c.symm z).1.2) :=
    continuous_snd.comp (continuous_subtype_val.comp c.symm.continuous)
  have hn := hi.continuousAt.preimage_mem_nhds
    (Metric.isOpen_ball.mem_nhds (show (c.symm (v0,p)).1.2 ∈ Metric.ball 0 (δ/2) by
      rw [hinv0]; exact Metric.mem_ball_self (by positivity)))
  obtain ⟨T,hT,B,hB,hTB⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨ε,hε,hεT⟩ := Metric.mem_nhds_iff.mp hT
  obtain ⟨B',hB'B,hB',hpB'⟩ := mem_nhds_iff.mp hB
  obtain ⟨K,hK,hpK,hKsub⟩ := exists_compact_subset (hV.inter hB') ⟨hpV,hpB'⟩
  refine ⟨K,hK,hpK,δ,min (ε/2) (R/2),hδ,by positivity,?_,?_,?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  · exact (Set.prod_mono (hKsub.trans inter_subset_left) subset_rfl).trans hVδ
  · intro x hx v hv
    apply hTB
    refine ⟨hεT ?_, hB'B (hKsub hx).2⟩
    change dist v v0 < ε
    change dist (v : E) (0 : E) < ε
    rw [dist_zero_right]
    exact hv.trans_le ((min_le_left _ _).trans (by linarith))

/-- A continuous inverse vanishing at a marked zero-section point maps a common target ball into any
prescribed source ball over a sufficiently small parameter neighborhood. -/
private theorem continuous_inverse_small_target
    {P E F : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (R : ℝ) (hR : 0 < R)
    (I : Metric.ball (0 : E) R × P → F) (hI : Continuous I)
    (p : P) (hI0 : I (⟨0,Metric.mem_ball_self hR⟩,p) = 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ B : Set P, IsOpen B ∧ p ∈ B ∧ ∃ ε : ℝ,
      0 < ε ∧ ε < R ∧ ∀ x ∈ B, ∀ v : Metric.ball (0 : E) R,
        ‖(v : E)‖ < ε → ‖I (v,x)‖ < η := by
  let v0 : Metric.ball (0 : E) R := ⟨0,Metric.mem_ball_self hR⟩
  have hn := hI.continuousAt.preimage_mem_nhds
    (Metric.isOpen_ball.mem_nhds (show I (v0,p) ∈ Metric.ball 0 η by
      rw [hI0]; exact Metric.mem_ball_self hη))
  obtain ⟨T,hT,B,hB,hTB⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨ε,hε,hεT⟩ := Metric.mem_nhds_iff.mp hT
  obtain ⟨B',hB'B,hB',hpB'⟩ := mem_nhds_iff.mp hB
  refine ⟨B',hB',hpB',min (ε/2) (R/2),by positivity,
    lt_of_le_of_lt (min_le_right _ _) (by linarith),?_⟩
  intro x hx v hv
  have hh : I (v,x) ∈ Metric.ball 0 η := by
    apply hTB
    refine ⟨hεT ?_, hB'B hx⟩
    change dist (v : E) (0 : E) < ε
    rw [dist_zero_right]
    exact hv.trans_le ((min_le_left _ _).trans (by linarith))
  simpa only [Metric.mem_ball, dist_zero_right] using hh

end HolomorphicAnosov
noncomputable section
open Set Filter
open scoped _root_.Topology
namespace HolomorphicAnosov

/-- Each parameter slice of a product-preserving homeomorphism defines an open partial homeomorphism
between the corresponding fibres. -/
private theorem parameter_inverse_slice
    {P E F : Type*} [TopologicalSpace P] [TopologicalSpace E] [TopologicalSpace F]
    [Nonempty E]
    (G : P → E → F) (U : Set (P × E)) (T : Set F)
    (hU : IsOpen U) (hT : IsOpen T)
    (c : U ≃ₜ (T × P))
    (hc : ∀ z : U, ((c z).1 : F) = G z.1.1 z.1.2 ∧ (c z).2 = z.1.1)
    (p : P) :
    ∃ e : OpenPartialHomeomorph E F,
      e.source = {v | (p,v) ∈ U} ∧ e.target = T ∧
      (∀ v, e v = G p v) ∧
      ∀ v : T, e.symm v = (c.symm (v,p)).1.2 := by
  classical
  let S : Set E := {v | (p,v) ∈ U}
  let inv : F → E := fun v ↦ if hv : v ∈ T then (c.symm (⟨v,hv⟩,p)).1.2 else Classical.choice ‹Nonempty E›
  have hbase (v : T) : (c.symm (v,p)).1.1 = p := by
    have hb := (hc (c.symm (v,p))).2
    rw [c.apply_symm_apply] at hb
    exact hb.symm
  have hval (v : T) : G p (c.symm (v,p)).1.2 = v := by
    have hv := (hc (c.symm (v,p))).1
    rw [c.apply_symm_apply] at hv
    rw [hbase] at hv
    exact hv.symm
  have hinv (v : T) : inv v = (c.symm (v,p)).1.2 := dite_eq_left v.property
  have hsource (v : T) : (p,(c.symm (v,p)).1.2) ∈ U := by
    have hh := (c.symm (v,p)).property
    change ((c.symm (v,p)).1.1,(c.symm (v,p)).1.2) ∈ U at hh
    simpa only [hbase] using hh
  have hleft (v : E) (hv : v ∈ S) : inv (G p v) = v := by
    let z : U := ⟨(p,v),hv⟩
    have hg : G p v ∈ T := (hc z).1 ▸ (c z).1.property
    rw [show inv (G p v) = (c.symm (⟨G p v,hg⟩,p)).1.2 from dite_eq_left hg]
    have hcz : c z = (⟨G p v,hg⟩,p) :=
      Prod.ext (Subtype.ext (hc z).1) (hc z).2
    rw [← hcz,c.symm_apply_apply]
  have hforward : ContinuousOn (G p) S := by
    have hz : Continuous (fun v : S ↦ (⟨(p,v.val),v.property⟩ : U)) :=
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact ((continuous_subtype_val.comp continuous_fst).comp (c.continuous.comp hz)).congr
      (fun v ↦ (hc ⟨(p,v.val),v.property⟩).1)
  have hinverse : ContinuousOn inv T := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_snd.comp (continuous_subtype_val.comp
      (c.symm.continuous.comp (continuous_id.prodMk continuous_const)))).congr
        (fun v ↦ (hinv v).symm)
  let e : OpenPartialHomeomorph E F := {
    toFun := G p
    invFun := inv
    source := S
    target := T
    map_source' := fun v hv ↦ (hc ⟨(p,v),hv⟩).1 ▸ (c ⟨(p,v),hv⟩).1.property
    map_target' := fun v hv ↦ by
      change (p,inv v) ∈ U
      rw [show inv v = (c.symm (⟨v,hv⟩,p)).1.2 from dite_eq_left hv]
      exact hsource ⟨v,hv⟩
    left_inv' := hleft
    right_inv' := fun v hv ↦ by
      rw [show inv v = (c.symm (⟨v,hv⟩,p)).1.2 from dite_eq_left hv]
      exact hval ⟨v,hv⟩
    open_source := hU.preimage (continuous_const.prodMk continuous_id)
    open_target := hT
    continuousOn_toFun := hforward
    continuousOn_invFun := hinverse }
  exact ⟨e,rfl,rfl,fun _ ↦ rfl,hinv⟩

end HolomorphicAnosov
namespace HolomorphicAnosov
universe u
private theorem first_jet_chart_at_mark {d : ℕ} {M : Type u} [MetricSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : M ≃ₜ M) (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (ι : Type u) (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f S ι L)
    (q : (Fin 2 → ℝ) → M) (r : ℝ) (hr : 0 < r)
    (i : ι) (z : L i) (hq0 : q 0 = (F.partition.leaf i).inclusion z)
    (hc : ∃ (j : ι) (c : OpenPartialHomeomorph (L j) (Fin 2 → ℝ)),
        c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin 2 → ℝ) ∞ (L j) ∧
        Metric.ball (0 : Fin 2 → ℝ) r ⊆ c.target ∧
        ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) r,
          q v = (F.partition.leaf j).inclusion (c.symm v)) :
    ∃ c : OpenPartialHomeomorph (L i) (Fin 2 → ℝ),
      c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i) ∧
      Metric.ball (0 : Fin 2 → ℝ) r ⊆ c.target ∧ z ∈ c.source ∧ c z = 0 ∧
      ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) r,
        q v = (F.partition.leaf i).inclusion (c.symm v) := by
  obtain ⟨j, c, hcat, htarget, hreal⟩ := hc
  have h0 : (0 : Fin 2 → ℝ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have hinc := (hreal 0 h0).symm.trans hq0
  have hji : j = i := F.partition.disjoint j i (c.symm 0) z hinc
  subst j
  have hcz : c.symm 0 = z := (F.partition.leaf i).injective hinc
  refine ⟨c, hcat, htarget, ?_, ?_, hreal⟩
  · exact hcz ▸ c.map_target (htarget h0)
  · rw [← hcz, c.right_inv (htarget h0)]


end HolomorphicAnosov

namespace HolomorphicAnosov
open Set Filter Metric Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold _root_.Topology
attribute [local instance] complex_isManifold_real
universe u

/-- A continuous inverse vanishing along a compact zero section maps a common sufficiently small
target ball into any prescribed positive source ball. -/
private theorem continuous_inverse_small_target_compact
    {P E F : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (R : ℝ) (hR : 0 < R)
    (I : Metric.ball (0 : E) R × P → F) (hI : Continuous I)
    (K : Set P) (hK : IsCompact K)
    (hI0 : ∀ x ∈ K, I (⟨0,Metric.mem_ball_self hR⟩,x) = 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < R ∧ ∀ x ∈ K, ∀ v : Metric.ball (0 : E) R,
      ‖(v : E)‖ < ε → ‖I (v,x)‖ < η := by
  let v0 : Metric.ball (0 : E) R := ⟨0,Metric.mem_ball_self hR⟩
  have hsub : ({v0} : Set (Metric.ball (0 : E) R)) ×ˢ K ⊆ I ⁻¹' Metric.ball 0 η := by
    rintro ⟨v,x⟩ ⟨hv,hx⟩
    have hv' : v = v0 := hv
    subst v
    change I (v0,x) ∈ Metric.ball 0 η
    rw [hI0 x hx]
    exact Metric.mem_ball_self hη
  obtain ⟨T,B,hT,hB,hvT,hKB,hTB⟩ := generalized_tube_lemma isCompact_singleton hK
    (Metric.isOpen_ball.preimage hI) hsub
  obtain ⟨ε,hε,hεT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds (hvT (mem_singleton v0)))
  refine ⟨min (ε/2) (R/2),by positivity,
    lt_of_le_of_lt (min_le_right _ _) (by linarith),?_⟩
  intro x hx v hv
  have hh : I (v,x) ∈ Metric.ball 0 η := by
    apply hTB
    refine ⟨hεT ?_,hKB hx⟩
    change dist (v : E) (0 : E) < ε
    rw [dist_zero_right]
    exact hv.trans_le ((min_le_left _ _).trans (by linarith))
  simpa only [Metric.mem_ball,dist_zero_right] using hh

/-- Scalar coordinates give biholomorphic charts on sufficiently small intrinsic Hermitian balls,
with a common target disk over a neighborhood of the base point. -/
private theorem local_uniform_intrinsic_scalar_all_radii
    {d : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {S : ContinuousComplexTangentSubbundle (complexModel d) M}
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f S ι L)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (W : Set M) (hW : IsOpen W) (t : M → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ t W)
    (hB : ∀ x ∈ W, (localStableCoordinateDerivative S.toDistribution t x).IsInvertible)
    (p : M) (hpW : p ∈ W) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ W ∧
      ∃ rMax : ℝ, 0 < rMax ∧ ∀ r : ℝ, 0 < r → r ≤ rMax →
      ∃ ε : ℝ, 0 < ε ∧ ∀ i (z : L i),
        (F.partition.leaf i).inclusion z ∈ V →
        let D : Set (L i) := {y | intrinsicHermitianLeafEDist (r := 2)
          (F.partition.leaf i).inclusion h z y < ENNReal.ofReal r}
        letI := (F.complexUpgrade i).charts
        ∃ e : OpenPartialHomeomorph (L i) ℂ,
          e.source = D ∧ D ⊆ (F.partition.leaf i).inclusion ⁻¹' W ∧
          (∀ y ∈ D, e y = t ((F.partition.leaf i).inclusion y) -
            t ((F.partition.leaf i).inclusion z)) ∧
          ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ e D ∧
          ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ e.symm e.target ∧
          ball (0 : ℂ) ε ⊆ e.target := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel d) M
  obtain ⟨V₀,ρ,q,hV₀,hpV₀,hV₀W,hρ,hq0,hqW,hqs,hqinj,htan,hcharts,
    A,V,hpV,s,hs,hU,hpin,hdom,c,hc⟩ :=
    native_scalar_inverse_metric_family F W hW t ht hB p hpW
  let U : Set (V × (Fin 2 → ℝ)) := {x | x.2 ∈ ball 0 s ∧
    A.symm (t (q x.1.1 x.2) - t x.1.1) ∈ ball 0 (s/8)}
  let G : V → (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
    fun x v ↦ A.symm (t (q x.val v) - t x.val)
  have hVV₀ (x : V) : x.val ∈ V₀ := by
    let v0 : ball (0 : Fin 2 → ℝ) (s/8) := ⟨0,mem_ball_self (by positivity)⟩
    have hhdom := (hdom (c.symm (v0,x))).1
    have hbase := (hc (c.symm (v0,x))).2
    rw [c.apply_symm_apply] at hbase
    have hv := congrArg Subtype.val hbase
    exact hv ▸ hhdom
  have hG0 (x : V) : G x 0 = 0 := by simp only [G,hq0 x.val (hVV₀ x),sub_self,map_zero]
  let : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  obtain ⟨K,hK,hpK,δ,ε₀,hδ,hε₀,hε₀s,hKδ,hsmall₀⟩ :=
    parameter_inverse_common_core G s (s/8) hs (by positivity) U hU (fun _ ↦ Iff.rfl)
      hG0 c hc ⟨p,hpV⟩
  let X := K × closedBall (0 : Fin 2 → ℝ) δ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : CompactSpace (closedBall (0 : Fin 2 → ℝ) δ) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : Nonempty X := ⟨(⟨⟨p,hpV⟩,interior_subset hpK⟩,⟨0,mem_closedBall_self hδ.le⟩)⟩
  have hXdom (z : X) : (z.1.val.val,z.2.val) ∈ V₀ ×ˢ ball (0 : Fin 2 → ℝ) ρ :=
    hdom ⟨(z.1.val,z.2.val),hKδ ⟨z.1.property,z.2.property⟩⟩
  let b : X → M := fun z ↦ q z.1.val.val z.2.val
  let Q (z : X) : (Fin 2 → ℝ) →L[ℝ] TangentSpace (realModel d) (b z) :=
    mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) (q z.1.val.val) z.2.val
  let input : X × (Fin 2 → ℝ) → (V₀ × ball (0 : Fin 2 → ℝ) ρ) × (Fin 2 → ℝ) :=
    fun z ↦ ((⟨z.1.1.val.val,(hXdom z.1).1⟩,⟨z.1.2.val,(hXdom z.1).2⟩),z.2)
  have hinput : Continuous input := by
    dsimp only [input, X]
    fun_prop
  obtain ⟨m,B,hm,hB0,hbounds⟩ := compact_injective_tangent_bounds
    (StableFoliationsSupport.originalSmoothRealMetric h hh) b Q (htan.comp hinput)
    (fun z ↦ hqinj _ (hXdom z).1 _ (hXdom z).2)
  let rMax : ℝ := m*(δ/4)
  have hrMax : 0 < rMax := mul_pos hm (by positivity)
  let Vout : Set M := (Subtype.val : V → M) '' interior K
  have hVout : IsOpen Vout := V.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_interior
  have hpout : p ∈ Vout := ⟨⟨p,hpV⟩,hpK,rfl⟩
  refine ⟨Vout,hVout,hpout,?_,rMax,hrMax,?_⟩
  · rintro x ⟨v,hv,rfl⟩
    exact hV₀W (hVV₀ v)
  intro r hr hrrMax
  have hRm : 0 < r/m := div_pos hr hm
  have hRδ : r/m < δ/2 := by
    apply (div_lt_iff₀ hm).mpr
    dsimp only [rMax] at hrrMax
    nlinarith
  have hmr : m*(r/m) = r := mul_div_cancel₀ r hm.ne'
  let η : ℝ := min (δ/4) (r/(B+1))
  have hη : 0 < η := lt_min (by positivity) (div_pos hr (by linarith))
  let I : ball (0 : Fin 2 → ℝ) (s/8) × V → (Fin 2 → ℝ) := fun z ↦ (c.symm z).1.2
  have hI : Continuous I := continuous_snd.comp (continuous_subtype_val.comp c.symm.continuous)
  have hI0 (x : V) : I (⟨0,mem_ball_self (by positivity)⟩,x) = 0 := by
    have hxU : (x,0) ∈ U := ⟨mem_ball_self hs,by change G x 0 ∈ ball 0 (s/8); rw [hG0]; exact mem_ball_self (by positivity)⟩
    have heq : c ⟨(x,0),hxU⟩ = (⟨0,mem_ball_self (by positivity)⟩,x) := by
      apply Prod.ext
      · apply Subtype.ext
        exact (hc _).1.trans (hG0 x)
      · exact (hc _).2
    change (c.symm _).1.2 = 0
    rw [← heq,c.symm_apply_apply]
  obtain ⟨ε₁,hε₁,hε₁s,hsmall⟩ :=
    continuous_inverse_small_target_compact (s/8) (by positivity) I hI K hK
      (fun x _ ↦ hI0 x) η hη
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp
    (A.symm.continuous.continuousAt.preimage_mem_nhds
      (Metric.ball_mem_nhds (A.symm (0 : ℂ)) hε₁))
  have hεA (w : ℂ) (hw : w ∈ ball 0 ε) : ‖A.symm w‖ < ε₁ := by
    simpa only [mem_preimage,mem_ball,map_zero,dist_zero_right] using hεsub hw
  refine ⟨ε,hε,?_⟩
  intro i z hz
  obtain ⟨x,hx,hxz⟩ := hz
  have hxK : x ∈ K := interior_subset hx
  have hxV₀ := hVV₀ x
  have hδρ : ball (0 : Fin 2 → ℝ) (δ/2) ⊆ ball 0 ρ := by
    intro v hv
    have hvδ : v ∈ closedBall (0 : Fin 2 → ℝ) δ :=
      ball_subset_closedBall (ball_subset_ball (by linarith) hv)
    exact (hdom ⟨(x,v),hKδ ⟨hxK,hvδ⟩⟩).2
  obtain ⟨e,he,het,hze,hez,hqi⟩ := first_jet_chart_at_mark f S ι L F
    (q x.val) ρ hρ i z (by rw [hq0 x.val hxV₀,hxz]) (hcharts x.val hxV₀)
  obtain ⟨k₀,hk₀s,hk₀t,hk₀f,hk₀i⟩ := parameter_inverse_slice G U
    (ball (0 : Fin 2 → ℝ) (s/8)) hU isOpen_ball c hc x
  let k := k₀.trans A.toHomeomorph.toOpenPartialHomeomorph
  have hk : ball (0 : Fin 2 → ℝ) (δ/2) ⊆ k.source := by
    intro v hv
    refine ⟨?_,mem_univ _⟩
    change v ∈ k₀.source
    rw [hk₀s]
    exact hKδ ⟨hxK,ball_subset_closedBall (ball_subset_ball (by linarith) hv)⟩
  have hkf (v : Fin 2 → ℝ) (hv : v ∈ ball 0 (δ/2)) :
      k v = t (q x.val v) - t ((F.partition.leaf i).inclusion z) := by
    change A (k₀ v) = _
    rw [hk₀f]
    change A (A.symm _) = _
    rw [A.apply_symm_apply,hxz]
  let : T2Space (L i) := (F.partition.leaf i).hausdorff
  let := (F.complexUpgrade i).charts
  let := (F.complexUpgrade i).complex_manifold
  have hmetric (u : Fin 2 → ℝ) (hu : u ∈ ball 0 (δ/2)) (w : Fin 2 → ℝ) :=
    hbounds (⟨x,hxK⟩,⟨u,ball_subset_closedBall (ball_subset_ball (by linarith) hu)⟩) w
  have hsc : ∀ w ∈ ball (0 : ℂ) ε,
      w ∈ k.target ∧ k.symm w ∈ ball (0 : Fin 2 → ℝ) (δ/2) ∧ B*‖k.symm w‖ < m*(r/m) := by
    intro w hw
    have hnorm := hεA w hw
    have hws : A.symm w ∈ ball (0 : Fin 2 → ℝ) (s/8) :=
      mem_ball_zero_iff.mpr (hnorm.trans hε₁s)
    have hwt : w ∈ k.target := ⟨mem_univ _,by rw [hk₀t]; exact hws⟩
    have hki : k.symm w = I (⟨A.symm w,hws⟩,x) := hk₀i ⟨A.symm w,hws⟩
    have hsmallw := hsmall x hxK ⟨A.symm w,hws⟩ hnorm
    rw [← hki] at hsmallw
    refine ⟨hwt,mem_ball_zero_iff.mpr (hsmallw.trans ?_),?_⟩
    · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · have hlt : ‖k.symm w‖ < r/(B+1) := hsmallw.trans_le (min_le_right _ _)
      have hh := (lt_div_iff₀ (by linarith : 0 < B+1)).mp hlt
      rw [hmr]
      nlinarith [norm_nonneg (k.symm w)]
  have htleaf : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞
      (t ∘ (F.partition.leaf i).inclusion) (e.source ∩ e ⁻¹' ball 0 (δ/2)) :=
    ht.comp (F.complexUpgrade i).inclusion_holomorphic.contMDiffOn (by
      intro y hy
      have hmem := hqW x.val hxV₀ (e y) (hδρ hy.2)
      rw [hqi _ (hδρ hy.2),e.left_inv hy.1] at hmem
      exact hmem)
  obtain ⟨e',hes,hef,hehol,heinv,hetarget⟩ := exact_intrinsic_scalar_chart h hh
    (F.partition.leaf i).inclusion (F.partition.leaf i).immersion.contMDiff
    ((F.partition.leaf i).immersion.mfderiv_injective (by simp)) e he (q x.val)
    (δ/2) (r/m) m B ε hRm hRδ hm
    (hδρ.trans het) ((hqs x.val hxV₀).mono hδρ)
    (fun v hv ↦ hqi v (hδρ hv)) hmetric z hze hez t htleaf k hk hkf hsc
  rw [hmr] at hes hef hehol
  refine ⟨e',hes,?_,hef,hehol,heinv,hetarget⟩
  intro y hy
  have hconf := native_plaque_intrinsic_ball_confinement h hh
    (F.partition.leaf i).inclusion e he (q x.val) (δ/2) (r/m) m
    hRm hRδ hm (hδρ.trans het) ((hqs x.val hxV₀).mono hδρ)
    (fun v hv ↦ hqi v (hδρ hv)) (fun u hu w ↦ (hmetric u hu w).1) hze hez (by rw [hmr]; exact hy)
  have hmem := hqW x.val hxV₀ (e y) (hδρ (ball_subset_ball (by linarith) hconf.2))
  rwa [hqi _ (hδρ (ball_subset_ball (by linarith) hconf.2)),e.left_inv hconf.1] at hmem

end HolomorphicAnosov
open Set Bundle Filter
open scoped Manifold ContDiff _root_.Topology
noncomputable section
namespace HolomorphicAnosov
universe u
/-- A nonvanishing stable scalar differential gives a local uniform lower bound for the ratio of the
Hermitian norm of a stable vector to the norm of its scalar image. -/
private theorem local_stable_scalar_metric_bound
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (V : Set M) (hV : IsOpen V) (t : M → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ t V)
    (hB : ∀ x ∈ V, (localStableCoordinateDerivative S.toDistribution t x).IsInvertible)
    (p : M) (hpV : p ∈ V) :
    ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ O ⊆ V ∧ ∃ c : ℝ, 0 < c ∧
      ∀ x ∈ O, ∀ v : S.toDistribution x,
        c * ‖localStableCoordinateDerivative S.toDistribution t x v‖ ≤
          Real.sqrt ((h x).inner v.val v.val).re := by
  classical
  obtain ⟨r, hr⟩ := S.locally_trivial p
  let : TopologicalSpace (TotalSpace (Fin r → ℂ) (fun x ↦ ↥(S.toDistribution x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  obtain ⟨e, hxe, he⟩ := hr
  let := he
  let B := fun x ↦ localStableCoordinateDerivative S.toDistribution t x
  obtain ⟨A, hA⟩ := hB p hpV
  let w0 : Fin r → ℂ := e.linearEquivAt ℂ p hxe (A.symm 1)
  have hw0 : w0 ≠ 0 := by
    intro h
    have ha : A.symm 1 = 0 := (e.linearEquivAt ℂ p hxe).map_eq_zero_iff.mp h
    have hz := congrArg A ha
    exact one_ne_zero (by simpa only [A.apply_symm_apply, map_zero] using hz)
  let O : Set M := e.baseSet ∩ V
  have hO : IsOpen O := e.open_baseSet.inter hV
  have hxo : p ∈ O := ⟨hxe, hpV⟩
  let w : ∀ x, S.toDistribution x := fun x ↦ e.symm x w0
  have hframe : Continuous (fun x : O ↦
      (⟨x.val, (w x.val).val⟩ : TangentBundle (complexModel d) M)) := by
    have hc : Continuous (fun x : O ↦
        (⟨x.val, w x.val⟩ : TotalSpace (Fin r → ℂ) (fun x ↦ ↥(S.toDistribution x)))) :=
      e.continuousOn_symm.comp_continuous
        (continuous_subtype_val.prodMk continuous_const) (fun x ↦ ⟨x.property.1, mem_univ _⟩)
    exact continuous_induced_dom.comp hc
  have hw (x : O) : w x.val ≠ 0 := by
    change (e.linearEquivAt ℂ x.val x.property.1).symm w0 ≠ 0
    exact fun h ↦ hw0 ((e.linearEquivAt ℂ x.val x.property.1).symm.map_eq_zero_iff.mp h)
  have hBw (x : O) : B x.val (w x.val) ≠ 0 := by
    obtain ⟨C, hC⟩ := hB x.val x.property.2
    change localStableCoordinateDerivative S.toDistribution t x.val (w x.val) ≠ 0
    rw [← hC]
    exact fun h ↦ hw x (C.map_eq_zero_iff.mp h)
  have hscalar : Continuous (fun x : O ↦ B x.val (w x.val)) := by
    have hc := (ht.continuousOn_tangentMapWithin (by simp) hV.uniqueMDiffOn).comp_continuous
      hframe (fun x ↦ x.property.2)
    have hs := (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℂ) (n := ∞)).continuous.comp hc
    apply hs.congr
    intro x
    change mfderivWithin (complexModel d) 𝓘(ℂ) t V x.val (w x.val).val = _
    rw [mfderivWithin_of_isOpen hV x.property.2]
    rfl
  let ratio : O → ℝ := fun x ↦
    hermitianBoundsNorm h x.val (w x.val).val / ‖B x.val (w x.val)‖
  have hratio : Continuous ratio :=
    ((Preparation.continuous_hermitian_tangent_norm h hh).comp hframe).div
      hscalar.norm (fun x ↦ norm_ne_zero_iff.mpr (hBw x))
  have hpos (x : O) : 0 < ratio x := by
    apply div_pos
    · exact HermitianFibreAlgebra.coreLength_pos (h x.val)
        (fun hv ↦ hw x (Subtype.ext hv))
    · exact norm_pos_iff.mpr (hBw x)
  let c : ℝ := ratio ⟨p,hxo⟩ / 2
  have hc : 0 < c := half_pos (hpos ⟨p,hxo⟩)
  let O' : Set O := {x | c < ratio x}
  have hO' : IsOpen O' := isOpen_lt continuous_const hratio
  have hpO' : (⟨p,hxo⟩ : O) ∈ O' := by
    change ratio ⟨p,hxo⟩ / 2 < ratio ⟨p,hxo⟩
    linarith [hpos ⟨p,hxo⟩]
  refine ⟨(Subtype.val : O → M) '' O',hO.isOpenEmbedding_subtypeVal.isOpenMap _ hO',
    ⟨⟨p,hxo⟩,hpO',rfl⟩,?_,c,hc,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    exact y.property.2
  · rintro x ⟨y,hy,rfl⟩ v
    have hv : v = (B y.val v / B y.val (w y.val)) • w y.val := by
      obtain ⟨A',hA'⟩ := hB y.val y.property.2
      apply A'.injective
      change (A' : S.toDistribution y.val →L[ℂ] ℂ) v =
        (A' : S.toDistribution y.val →L[ℂ] ℂ) _
      rw [hA',map_smul]
      change B y.val v = (B y.val v / B y.val (w y.val)) * B y.val (w y.val)
      exact (div_mul_cancel₀ _ (hBw y)).symm
    have heq : hermitianBoundsNorm h y.val v.val =
        ‖B y.val v‖ * ratio y := by
      have hvv := congrArg Subtype.val hv
      rw [hvv]
      change HermitianFibreAlgebra.coreLength (h y.val)
        ((B y.val v / B y.val (w y.val)) • (w y.val).val) = _
      rw [HermitianFibreAlgebra.coreLength_complex_smul,norm_div]
      dsimp only [ratio,hermitianBoundsNorm,HermitianFibreAlgebra.coreLength]
      ring
    change c * ‖B y.val v‖ ≤ hermitianBoundsNorm h y.val v.val
    rw [heq,mul_comm]
    exact mul_le_mul_of_nonneg_left (le_of_lt hy) (norm_nonneg _)

end HolomorphicAnosov
namespace HolomorphicAnosov
open Set Filter Metric Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold _root_.Topology
attribute [local instance] complex_isManifold_real
universe u

/-- Normalized stable coordinates give biholomorphic charts on small intrinsic Hermitian balls with
a uniform Hermitian ball in their images over a base neighborhood. -/
private theorem local_uniform_normalized_coordinates
    {d : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {S : ContinuousComplexTangentSubbundle (complexModel d) M}
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f S ι L)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (W : Set M) (hW : IsOpen W) (t : M → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ t W)
    (hB : ∀ x ∈ W, (localStableCoordinateDerivative S.toDistribution t x).IsInvertible)
    (p : M) (hpW : p ∈ W) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ W ∧
      ∃ rMax : ℝ, 0 < rMax ∧ ∀ r : ℝ, 0 < r → r ≤ rMax →
      ∃ ε : ℝ, 0 < ε ∧ ∀ i (z : L i),
        (F.partition.leaf i).inclusion z ∈ V →
        let x := (F.partition.leaf i).inclusion z
        let D : Set (L i) := {y | intrinsicHermitianLeafEDist (r := 2)
          (F.partition.leaf i).inclusion h z y < ENNReal.ofReal r}
        letI := (F.complexUpgrade i).charts
        ∃ c : S.toDistribution x ≃L[ℂ] ℂ,
        ∃ e : OpenPartialHomeomorph (L i) (S.toDistribution x),
          e.source = D ∧ D ⊆ (F.partition.leaf i).inclusion ⁻¹' W ∧
          (∀ y ∈ D, e y = normalizedLocalStableCoordinate S.toDistribution t x
            ((F.partition.leaf i).inclusion y)) ∧
          ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ (c ∘ e) D ∧
          ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ (e.symm ∘ c.symm)
            (c.symm ⁻¹' e.target) ∧
          (∀ v : S.toDistribution x,
            Real.sqrt ((h x).inner v.val v.val).re < ε → v ∈ e.target) := by
  obtain ⟨V₀,hV₀,hpV₀,hV₀W,rMax,hrMax,hcharts⟩ :=
    local_uniform_intrinsic_scalar_all_radii F h hh W hW t ht hB p hpW
  obtain ⟨O,hO,hpO,hOW,m,hm,hmetric⟩ :=
    local_stable_scalar_metric_bound S h hh W hW t ht hB p hpW
  refine ⟨V₀ ∩ O,hV₀.inter hO,⟨hpV₀,hpO⟩,inter_subset_left.trans hV₀W,
    rMax,hrMax,?_⟩
  intro r hr hrr
  obtain ⟨ε,hε,hcharts⟩ := hcharts r hr hrr
  refine ⟨m*ε,mul_pos hm hε,?_⟩
  intro i z hz
  obtain ⟨e₀,he₀s,he₀W,he₀f,he₀h,he₀i,he₀t⟩ := hcharts i z hz.1
  let := (F.complexUpgrade i).charts
  let := (F.complexUpgrade i).complex_manifold
  let x := (F.partition.leaf i).inclusion z
  obtain ⟨c,hc⟩ := hB x (hV₀W hz.1)
  let e := e₀.trans c.symm.toHomeomorph.toOpenPartialHomeomorph
  have hes : e.source = e₀.source := by
    ext y
    change (y ∈ e₀.source ∧ e₀ y ∈ univ) ↔ y ∈ e₀.source
    simp only [mem_univ,and_true]
  have hforward : (c ∘ e : L i → ℂ) = e₀ := by
    funext y
    exact c.apply_symm_apply (e₀ y)
  have hinverse : (e.symm ∘ c.symm : ℂ → L i) = e₀.symm := by
    funext y
    change e₀.symm (c (c.symm y)) = e₀.symm y
    rw [c.apply_symm_apply]
  have htarget : c.symm ⁻¹' e.target = e₀.target := by
    ext y
    change (c.symm y ∈ univ ∧ c (c.symm y) ∈ e₀.target) ↔ y ∈ e₀.target
    simp only [mem_univ,true_and,c.apply_symm_apply]
  refine ⟨c,e,hes.trans he₀s,he₀W,?_,?_,?_,?_⟩
  · intro y hy
    change c.symm (e₀ y) = (localStableCoordinateDerivative S.toDistribution t x).inverse _
    rw [← hc,ContinuousLinearMap.inverse_equiv,he₀f y hy]
    rfl
  · rw [hforward]
    exact he₀h
  · rw [hinverse,htarget]
    exact he₀i
  · intro v hv
    refine ⟨mem_univ _,he₀t ?_⟩
    change c v ∈ ball (0 : ℂ) ε
    rw [mem_ball,dist_zero_right]
    have hh := hmetric x hz.2 v
    have hcv : c v = localStableCoordinateDerivative S.toDistribution t x v :=
      congrArg (fun B ↦ B v) hc
    rw [← hcv] at hh
    exact (mul_lt_mul_iff_right₀ hm).mp (hh.trans_lt hv)

end HolomorphicAnosov
noncomputable section
open Set
namespace HolomorphicAnosov

/-- On a compact parameter space, local chart estimates valid for all sufficiently small source
radii yield common positive source and target radii. -/
private theorem compact_uniform_two_radii
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (C : X → ℝ → ℝ → Prop)
    (hmono : ∀ x r ε ε', ε' ≤ ε → C x r ε → C x r ε')
    (hloc : ∀ x : X, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∃ rMax : ℝ, 0 < rMax ∧ ∀ r : ℝ, 0 < r → r ≤ rMax →
        ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ V, C y r ε) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧ ∀ x, C x r ε := by
  classical
  by_cases hX : Nonempty X
  · let := hX
    choose V hVo hxV R hR hc using hloc
    obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover V hVo
      (fun x _ ↦ mem_iUnion.mpr ⟨x,hxV x⟩)
    have hsn : s.Nonempty := by
      obtain ⟨x,hx,hmem⟩ := mem_iUnion₂.mp (hs (mem_univ (Classical.choice hX)))
      exact ⟨x,hx⟩
    let r := s.inf' hsn R
    have hr : 0 < r := (Finset.lt_inf'_iff _).mpr (fun x _ ↦ hR x)
    have hrr (x : s) : r ≤ R x.val := Finset.inf'_le R x.property
    choose ε hε hcharts using fun x : s ↦ hc x.val r hr (hrr x)
    let : Nonempty s := ⟨⟨hsn.choose,hsn.choose_spec⟩⟩
    let e := Finset.univ.inf' Finset.univ_nonempty ε
    have he : 0 < e := (Finset.lt_inf'_iff _).mpr (fun x _ ↦ hε x)
    refine ⟨r,e,hr,he,?_⟩
    intro x
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact hmono x r (ε ⟨y,hy⟩) e (Finset.inf'_le ε (Finset.mem_univ _))
      (hcharts ⟨y,hy⟩ x hxy)
  · refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro x
    exact (hX ⟨x⟩).elim

end HolomorphicAnosov
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u
/-- Normalized coordinates from two parallel transverse pairs have the same germ at every point of
their common domain. (Zhang, equation (15)) -/
private theorem normalized_parallel_coordinate_pairs_germ
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (nabla : QuotientLineConnection.Connection U)
    (V W : TopologicalSpace.Opens M)
    (σ σ' : ∀ x : M, QuotientLineConnection.Fibre U x) (t t' : M → ℂ)
    (hσ : QuotientLineConnection.IsHolomorphicSection U V σ)
    (hσ' : QuotientLineConnection.IsHolomorphicSection U W σ')
    (hnσ : ∀ x ∈ V, σ x ≠ 0) (hnσ' : ∀ x ∈ W, σ' x ≠ 0)
    (hpσ : QuotientLineConnection.IsParallelOn nabla V σ)
    (hpσ' : QuotientLineConnection.IsParallelOn nabla W σ')
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (ht' : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t' W)
    (hformula : ∀ y ∈ V, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v = transverseScalarDifferential t y v • σ y)
    (hformula' : ∀ y ∈ W, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v = transverseScalarDifferential t' y v • σ' y)
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (x : M) (hx : x ∈ V) (hxW : x ∈ W) :
    normalizedLocalStableCoordinate S t' x =ᶠ[nhds x]
      normalizedLocalStableCoordinate S t x := by
  obtain ⟨c, b, N, hN, hxN, hsub, heq⟩ := parallel_coordinate_pairs_affine_germ
    U nabla V W σ σ' t t' hσ hσ' hnσ hnσ' hpσ hpσ' ht ht'
    hformula hformula' x hx hxW
  exact normalizedLocalStableCoordinate_affine_germ S t t' x c b
    (((ht x hx).contMDiffAt (V.isOpen.mem_nhds hx)).mdifferentiableAt (by simp))
    (Filter.eventually_of_mem (hN.mem_nhds hxN) heq)
end
end HolomorphicAnosov.Paper.Zhang

namespace HolomorphicAnosov
open Set Filter _root_.Topology TopologicalSpace
open scoped ContDiff Manifold ENNReal
noncomputable section
universe u
variable {d : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]

/-- A nonvanishing parallel holomorphic quotient section and a holomorphic transverse coordinate
satisfying `π = dt ⊗ σ` on an open set. (Zhang, equation (14)) -/
private structure ParallelPair
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (nabla : QuotientLineConnection.Connection U) where
  V : TopologicalSpace.Opens M
  σ : ∀ x, QuotientLineConnection.Fibre U x
  t : M → ℂ
  holσ : QuotientLineConnection.IsHolomorphicSection U V σ
  nonzero : ∀ x ∈ V, σ x ≠ 0
  parallel : QuotientLineConnection.IsParallelOn nabla V σ
  holt : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ t V
  formula : ∀ x ∈ V, ∀ v : TangentSpace (complexModel d) x,
    QuotientLineConnection.projection U x v = Paper.Zhang.transverseScalarDifferential t x v • σ x

variable {f : M ≃ₜ M} {S : ContinuousComplexTangentSubbundle (complexModel d) M}
  {ι : Type u} {L : ι → Type u}
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]

/-- The normalized stable coordinate is a biholomorphic chart on the intrinsic radius ball at a
marked point, with image containing a prescribed Hermitian ball. -/
private def NativeUniformChartAt
    (F : NativeComplexStableLeafDatum f S ι L)
    (h : HermitianTangentMetricCore d M) (x : M) (t : M → ℂ) (W : Set M)
    (r ε : ℝ) : Prop :=
  ∀ i (z : L i), (F.partition.leaf i).inclusion z = x →
    let D : Set (L i) := {y | intrinsicHermitianLeafEDist (r := 2)
      (F.partition.leaf i).inclusion h z y < ENNReal.ofReal r}
    letI := (F.complexUpgrade i).charts
    ∃ c : S.toDistribution x ≃L[ℂ] ℂ,
    ∃ e : OpenPartialHomeomorph (L i) (S.toDistribution x),
      e.source = D ∧ D ⊆ (F.partition.leaf i).inclusion ⁻¹' W ∧
      (∀ y ∈ D, e y = normalizedLocalStableCoordinate S.toDistribution t x
        ((F.partition.leaf i).inclusion y)) ∧
      ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ (c ∘ e) D ∧
      ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ (e.symm ∘ c.symm)
        (c.symm ⁻¹' e.target) ∧
      (∀ v : S.toDistribution x,
        Real.sqrt ((h x).inner v.val v.val).re < ε → v ∈ e.target)

/-- Chosen normalized coordinates agree as ambient germs with the normalized coordinates of every
parallel transverse pair. -/
private theorem chosen_parallel_coordinates_germ
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (nabla : QuotientLineConnection.Connection U)
    (P : M → ParallelPair U nabla) (hP : ∀ x, x ∈ (P x).V)
    (Q : ParallelPair U nabla) (x : M) (hxQ : x ∈ Q.V) :
    normalizedLocalStableCoordinate S.toDistribution (P x).t x =ᶠ[nhds x]
      normalizedLocalStableCoordinate S.toDistribution Q.t x := by
  exact Paper.Zhang.normalized_parallel_coordinate_pairs_germ U nabla
    Q.V (P x).V Q.σ (P x).σ Q.t (P x).t Q.holσ (P x).holσ
    Q.nonzero (P x).nonzero Q.parallel (P x).parallel Q.holt (P x).holt
    Q.formula (P x).formula S.toDistribution x hxQ (hP x)

end
end HolomorphicAnosov
noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Manifold ContDiff ENNReal
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- Points at intrinsic Hermitian distance less than a radius are joined by a `C¹` path lying in
that ball and having ambient Hermitian length less than the radius. -/
private theorem hermitian_short_path_in_ball
    {r d : ℕ} {L M : Type*} [TopologicalSpace L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (hi : ∀ z, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z))
    (x y : L) (R : ℝ≥0∞)
    (hxy : intrinsicHermitianLeafEDist (r := r) inc h x y < R) :
    let g := StableFoliationsSupport.originalSmoothRealMetric h hh
    let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨g.toRiemannianMetric⟩
    ∃ γ : ℝ → L, γ 0 = x ∧ γ 1 = y ∧
      ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Fin r → ℝ) 1 γ (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, intrinsicHermitianLeafEDist (r := r) inc h x (γ t) < R) ∧
      pathELength (realModel d) (inc ∘ γ) 0 1 < R := by
  let g := StableFoliationsSupport.originalSmoothRealMetric h hh
  let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨gL, hgL⟩ := immersion_riemannianMetric_exists g inc hinc hi
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, Fin r → ℝ) : L → Type _) :=
    ⟨gL.toRiemannianMetric⟩
  have he : ∀ x y : L, riemannianEDist 𝓘(ℝ, Fin r → ℝ) x y =
      intrinsicHermitianLeafEDist (r := r) inc h x y := by
    intro x y
    rw [intrinsicPiecewiseC1Path_riemannianEDist]
    unfold intrinsicHermitianLeafEDist IntrinsicPiecewiseC1Path.length
    congr 1
    funext p
    apply Finset.sum_congr rfl
    intro k hk
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [← ofReal_norm (p.velocity k t), norm_eq_sqrt_real_inner]
    change ENNReal.ofReal (Real.sqrt (gL.inner _ _ _)) = _
    rw [hgL, StableFoliationsSupport.originalSmoothRealMetric_inner]
    rfl
  rw [← he] at hxy
  obtain ⟨γ,hγ0,hγ1,hγ,hlen⟩ := exists_lt_of_riemannianEDist_lt hxy
  refine ⟨γ,hγ0,hγ1,hγ,?_,?_⟩
  · intro t ht
    rw [← he]
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
    exact (riemannianEDist_le_pathELength (hγ.mono hsub) hγ0 rfl ht.1).trans_lt
      ((pathELength_mono (I := 𝓘(ℝ,Fin r → ℝ)) (γ := γ) le_rfl ht.2).trans_lt hlen)
  · have heq : pathELength (realModel d) (inc ∘ γ) 0 1 =
        pathELength 𝓘(ℝ,Fin r → ℝ) γ 0 1 := by
      rw [pathELength_eq_lintegral_mfderivWithin_Icc,
        pathELength_eq_lintegral_mfderivWithin_Icc]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only
      rw [mfderiv_comp_mfderivWithin t
        (hinc.mdifferentiable (by simp) (γ t))
        (hγ.mdifferentiableOn one_ne_zero t ht)
        ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)]
      simp only [ContinuousLinearMap.comp_apply, ←ofReal_norm]
      rw [norm_eq_sqrt_real_inner,norm_eq_sqrt_real_inner]
      change ENNReal.ofReal (Real.sqrt (g.inner _ _ _)) =
        ENNReal.ofReal (Real.sqrt (gL.inner _ _ _))
      rw [hgL]
      rfl
    rw [heq]
    exact hlen
end HolomorphicAnosov
noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Manifold Topology ENNReal
namespace HolomorphicAnosov

/-- The Riemannian length of a fixed `C¹` coordinate path varies continuously in a plaque family
with continuous tangent maps. -/
private theorem raw_moving_plaque_length_continuous
    {P E H M : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold 𝓘(ℝ,H) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,H) ∞ H
      (fun x : M ↦ TangentSpace 𝓘(ℝ,H) x))
    (D : Set E) (hD : IsOpen D) (q : P → E → M)
    (hq : ∀ p, ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,H) 1 (q p) D)
    (hT : Continuous (fun z : (P × D) × E ↦
      (⟨q z.1.1 z.1.2, mfderiv 𝓘(ℝ,E) 𝓘(ℝ,H) (q z.1.1) z.1.2 z.2⟩ :
        TangentBundle 𝓘(ℝ,H) M)))
    (γ : ℝ → E) (hγ : ContDiffOn ℝ 1 γ (Icc 0 1))
    (hγD : MapsTo γ (Icc 0 1) D) :
    let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,H) x) :=
      ⟨g.toRiemannianMetric⟩
    Continuous (fun p ↦ pathELength 𝓘(ℝ,H) (q p ∘ γ) 0 1) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,H) x) :=
    ⟨g.toRiemannianMetric⟩
  let vel : Icc (0 : ℝ) 1 → E := fun t ↦ fderivWithin ℝ γ (Icc 0 1) t 1
  have hv : Continuous vel :=
    ((hγ.continuousOn_fderivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl).domRestrict).clm_apply
      continuous_const
  let point : Icc (0 : ℝ) 1 → D := fun t ↦ ⟨γ t,hγD t.property⟩
  have hp : Continuous point := hγ.continuousOn.domRestrict.subtype_mk _
  let tangent : P × Icc (0 : ℝ) 1 → TangentBundle 𝓘(ℝ,H) M := fun z ↦
    ⟨q z.1 (γ z.2), mfderiv 𝓘(ℝ,E) 𝓘(ℝ,H) (q z.1) (γ z.2) (vel z.2)⟩
  have ht : Continuous tangent := hT.comp
    ((continuous_fst.prodMk (hp.comp continuous_snd)).prodMk (hv.comp continuous_snd))
  let speed : P × Icc (0 : ℝ) 1 → ℝ := fun z ↦ ‖(tangent z).snd‖
  have hs : Continuous speed := FixedBlockEstimates.Native.continuous_original_norm g
    (fun z : P × Icc (0 : ℝ) 1 ↦ q z.1 (γ z.2))
    (fun z : P × Icc (0 : ℝ) 1 ↦ mfderiv 𝓘(ℝ,E) 𝓘(ℝ,H) (q z.1) (γ z.2) (vel z.2)) ht
  have hc := continuous_lintegral_compact_interval_speed zero_le_one speed hs
    (fun _ ↦ norm_nonneg _)
  apply hc.congr
  intro p
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  have hd := mfderiv_comp_mfderivWithin t
    ((((hq p) (γ t) (hγD ht)).contMDiffAt (hD.mem_nhds (hγD ht))).mdifferentiableAt
      one_ne_zero)
    (hγ.contMDiffOn.mdifferentiableOn one_ne_zero t ht)
    ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)
  dsimp only
  rw [hd, mfderivWithin_eq_fderivWithin, ←ofReal_norm]
  simp only [speed,tangent,vel,projIcc_of_mem zero_le_one ht]
  rfl

end HolomorphicAnosov
noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace HolomorphicAnosov

/-- Intrinsic distance has open strict sublevels when short paths can be transported continuously
and nearby endpoints admit uniformly short connectors. -/
private theorem transported_length_sublevel_open
    {P E A : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] (D : Set E)
    (d : P → D → ℝ≥0∞) (length : A → P → ℝ≥0∞)
    (endpoint : A → D) (B : ℝ) (R : ℝ≥0∞)
    (hlen : ∀ a, Continuous (length a))
    (hbound : ∀ a p, d p (endpoint a) ≤ length a p)
    (hconnector : ∀ p (v w : D), d p w ≤ d p v + ENNReal.ofReal (B * ‖w.val-v.val‖))
    (hwitness : ∀ p (v : D), d p v < R →
      ∃ a, endpoint a = v ∧ length a p < R) :
    IsOpen {z : P × D | d z.1 z.2 < R} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨a,ha,hlenz⟩ := hwitness z.1 z.2 hz
  let f : P × D → ℝ≥0∞ := fun w ↦ length a w.1 + ENNReal.ofReal (B * dist w.2.val z.2.val)
  have hf : Continuous f := (hlen a).comp continuous_fst |>.add
    (ENNReal.continuous_ofReal.comp
      (continuous_const.mul ((continuous_subtype_val.comp continuous_snd).dist continuous_const)))
  have hfz : f z < R := by
    simpa only [f,dist_self,mul_zero,ENNReal.ofReal_zero,add_zero] using hlenz
  have hn := (isOpen_lt hf continuous_const).mem_nhds hfz
  apply Filter.mem_of_superset hn
  intro w hw
  change d w.1 w.2 < R
  apply (hconnector w.1 z.2 w.2).trans_lt
  have hb : d w.1 z.2 ≤ length a w.1 := ha ▸ hbound a w.1
  have hsum : d w.1 z.2 + ENNReal.ofReal (B * ‖w.2.val-z.2.val‖) ≤
      length a w.1 + ENNReal.ofReal (B * ‖w.2.val-z.2.val‖) := add_le_add hb le_rfl
  exact hsum.trans_lt (by simpa only [mem_ofPred_eq,f,dist_eq_norm] using hw)

end HolomorphicAnosov
namespace HolomorphicAnosov
open Set Filter Manifold Bundle Metric MeasureTheory
open scoped ContDiff Manifold Topology ENNReal
attribute [local instance] complex_isManifold_real

/-- The intrinsic radius domain is open in a continuous family of buffered plaque charts with
uniform metric bounds. -/
private theorem native_moving_ball_open
    {r d : ℕ} {P M : Type*} [TopologicalSpace P]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (L : P → Type*) [∀ p, TopologicalSpace (L p)] [∀ p, T2Space (L p)]
    [∀ p, ChartedSpace (Fin r → ℝ) (L p)]
    [∀ p, IsManifold 𝓘(ℝ,Fin r → ℝ) ∞ (L p)]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : ∀ p, L p → M)
    (hinc : ∀ p, ContMDiff 𝓘(ℝ,Fin r → ℝ) (realModel d) ∞ (inc p))
    (hi : ∀ p z, Function.Injective (mfderiv 𝓘(ℝ,Fin r → ℝ) (realModel d) (inc p) z))
    (e : ∀ p, OpenPartialHomeomorph (L p) (Fin r → ℝ))
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓘(ℝ,Fin r → ℝ) ∞ (L p))
    (q : P → (Fin r → ℝ) → M) (δ R m B radius : ℝ)
    (hR : 0 < R) (hRδ : R < δ) (hm : 0 < m) (hradius : radius ≤ m * R)
    (hbuffer : ∀ p, ball (0 : Fin r → ℝ) δ ⊆ (e p).target)
    (hq : ∀ p, ContMDiffOn 𝓘(ℝ,Fin r → ℝ) (realModel d) ∞ (q p) (ball 0 δ))
    (hqi : ∀ p v, v ∈ ball (0 : Fin r → ℝ) δ → q p v = inc p ((e p).symm v))
    (hbound : ∀ p u, u ∈ ball (0 : Fin r → ℝ) δ → ∀ w : Fin r → ℝ,
      m * ‖w‖ ≤ Real.sqrt
        ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner (q p u)
          (mfderiv 𝓘(ℝ,Fin r → ℝ) (realModel d) (q p) u w)
          (mfderiv 𝓘(ℝ,Fin r → ℝ) (realModel d) (q p) u w)) ∧
      Real.sqrt ((StableFoliationsSupport.originalSmoothRealMetric h hh).inner (q p u)
          (mfderiv 𝓘(ℝ,Fin r → ℝ) (realModel d) (q p) u w)
          (mfderiv 𝓘(ℝ,Fin r → ℝ) (realModel d) (q p) u w)) ≤ B * ‖w‖)
    (hT : Continuous (fun z : (P × ball (0 : Fin r → ℝ) δ) × (Fin r → ℝ) ↦
      (⟨q z.1.1 z.1.2, mfderiv 𝓘(ℝ,Fin r → ℝ) (realModel d) (q z.1.1) z.1.2 z.2⟩ :
        TangentBundle (realModel d) M))) :
    IsOpen {z : P × ball (0 : Fin r → ℝ) δ |
      intrinsicHermitianLeafEDist (r := r) (inc z.1) h
        ((e z.1).symm 0) ((e z.1).symm z.2) < ENNReal.ofReal radius} := by
  let g := StableFoliationsSupport.originalSmoothRealMetric h hh
  let : RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  let D := ball (0 : Fin r → ℝ) δ
  let A := {γ : ℝ → (Fin r → ℝ) //
    ContDiffOn ℝ 1 γ (Icc 0 1) ∧ MapsTo γ (Icc 0 1) D ∧ γ 0 = 0}
  let length : A → P → ℝ≥0∞ := fun γ p ↦ pathELength (realModel d) (q p ∘ γ.val) 0 1
  let endpoint : A → D := fun γ ↦ ⟨γ.val 1,γ.property.2.1 (right_mem_Icc.mpr zero_le_one)⟩
  let distance : P → D → ℝ≥0∞ := fun p v ↦
    intrinsicHermitianLeafEDist (r := r) (inc p) h ((e p).symm 0) ((e p).symm v)
  have hlen : ∀ γ, Continuous (length γ) := fun γ ↦
    raw_moving_plaque_length_continuous g D isOpen_ball q
      (fun p ↦ (hq p).of_le (by simp)) hT γ.val γ.property.1 γ.property.2.1
  have hdist : ∀ γ p, distance p (endpoint γ) ≤ length γ p := by
    intro γ p
    have hcurve : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ,Fin r → ℝ) 1
        ((e p).symm ∘ γ.val) (Icc 0 1) :=
      ((contMDiffOn_symm_of_mem_maximalAtlas (he p)).of_le (by simp)).comp
        γ.property.1.contMDiffOn (fun t ht ↦ hbuffer p (γ.property.2.1 ht))
    have hb := intrinsicHermitianLeafEDist_le_included_curve (inc p)
      ((hinc p).of_le (by simp)) h g
      (StableFoliationsSupport.originalSmoothRealMetric_inner h hh)
      ((e p).symm ∘ γ.val) hcurve
    simp only [Function.comp_apply, γ.property.2.2] at hb
    apply hb.trans_eq
    apply pathELength_congr
    intro t ht
    exact (hqi p (γ.val t) (γ.property.2.1 ht)).symm
  have hconn : ∀ p (v w : D), distance p w ≤ distance p v + ENNReal.ofReal (B * ‖w.val-v.val‖) := by
    intro p v w
    apply (intrinsicHermitianLeafEDist_triangle h hh (inc p) (hinc p) (hi p)
      ((e p).symm 0) ((e p).symm v) ((e p).symm w)).trans
    apply add_le_add le_rfl
    exact raw_plaque_intrinsic_segment_bound h hh (inc p) (hinc p) (e p) (he p)
      (q p) δ B (hbuffer p) (hq p) (hqi p) (fun u hu w ↦ (hbound p u hu w).2)
      v w v.property w.property
  apply transported_length_sublevel_open D distance length endpoint B
    (ENNReal.ofReal radius) hlen hdist hconn
  intro p v hv
  obtain ⟨γ,hγ0,hγ1,hγ,hγball,hγlen⟩ := hermitian_short_path_in_ball h hh
    (inc p) (hinc p) (hi p) ((e p).symm 0) ((e p).symm v) (ENNReal.ofReal radius) hv
  have hzero : (0 : Fin r → ℝ) ∈ (e p).target :=
    hbuffer p (mem_ball_self (hR.trans hRδ))
  have hconf (t : ℝ) (ht : t ∈ Icc 0 1) :
      γ t ∈ (e p).source ∧ e p (γ t) ∈ ball (0 : Fin r → ℝ) R :=
    native_plaque_intrinsic_ball_confinement h hh (inc p) (e p) (he p) (q p) δ R m
      hR hRδ hm (hbuffer p) (hq p) (hqi p) (fun u hu w ↦ (hbound p u hu w).1)
      ((e p).map_target hzero) ((e p).right_inv hzero)
      ((hγball t ht).trans_le (ENNReal.ofReal_le_ofReal hradius))
  let η : A := ⟨(e p) ∘ γ, by
    refine ⟨?_,?_,?_⟩
    · exact contMDiffOn_iff_contDiffOn.mp
        (((contMDiffOn_of_mem_maximalAtlas (he p)).of_le (by simp)).comp hγ
          (fun t ht ↦ (hconf t ht).1))
    · exact fun t ht ↦ ball_subset_ball hRδ.le (hconf t ht).2
    · change e p (γ 0) = 0
      rw [hγ0,(e p).right_inv hzero]⟩
  refine ⟨η,?_,?_⟩
  · apply Subtype.ext
    change e p (γ 1) = v.val
    rw [hγ1,(e p).right_inv (hbuffer p v.property)]
  · change pathELength (realModel d) (q p ∘ ((e p) ∘ γ)) 0 1 < _
    have heq : pathELength (realModel d) (q p ∘ ((e p) ∘ γ)) 0 1 =
        pathELength (realModel d) (inc p ∘ γ) 0 1 := by
      apply pathELength_congr
      intro t ht
      change q p (e p (γ t)) = inc p (γ t)
      rw [hqi p _ (ball_subset_ball hRδ.le (hconf t ht).2),
        (e p).left_inv (hconf t ht).1]
    rw [heq]
    exact hγlen

end HolomorphicAnosov
noncomputable section
open Set Topology
namespace HolomorphicAnosov

/-- A product inverse preserving the parameter maps open restricted sources to open targets and has
continuous inverse evaluation there. -/
private theorem product_inverse_open_image
    {P E F M : Type*} [TopologicalSpace P] [TopologicalSpace E]
    [TopologicalSpace F] [TopologicalSpace M]
    (U J : Set (P × E)) (T : Set F) (hJ : IsOpen J) (hJU : J ⊆ U) (hT : IsOpen T)
    (c : U ≃ₜ (T × P)) (g : P × E → P × F)
    (hg : ∀ z : U, g z = ((c z).2,((c z).1 : F)))
    (q : P × E → M) (hq : ContinuousOn q U) :
    IsOpen (g '' J) ∧ ∃ I : (g '' J) → M, Continuous I ∧
      ∀ z (hz : z ∈ J), I ⟨g z,mem_image_of_mem g hz⟩ = q z := by
  let embed : T × P → P × F := fun z ↦ (z.2,z.1.val)
  have hembed : IsOpenEmbedding embed :=
    (Homeomorph.prodComm F P).isOpenEmbedding.comp
      (hT.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id)
  have hEq : g '' J = embed '' (c '' ((Subtype.val : U → P × E) ⁻¹' J)) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨c ⟨z,hJU hz⟩,⟨⟨z,hJU hz⟩,hz,rfl⟩,?_⟩
      exact (hg ⟨z,hJU hz⟩).symm
    · rintro ⟨w,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨z.val,hz,hg z⟩
  have hopen : IsOpen (g '' J) := by
    rw [hEq]
    exact hembed.isOpenMap _ (c.isOpenMap _ (hJ.preimage continuous_subtype_val))
  have hmem (z : g '' J) : z.val.2 ∈ T := by
    obtain ⟨w,hw,hwz⟩ := z.property
    have heq := hg ⟨w,hJU hw⟩
    rw [hwz] at heq
    have hs := congrArg Prod.snd heq
    rw [hs]
    exact (c ⟨w,hJU hw⟩).1.property
  let lift : (g '' J) → T × P := fun z ↦ (⟨z.val.2,hmem z⟩,z.val.1)
  have hlift : Continuous lift :=
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_fst.comp continuous_subtype_val)
  let I : (g '' J) → M := fun z ↦ q (c.symm (lift z)).val
  have hI : Continuous I := hq.domRestrict.comp (c.symm.continuous.comp hlift)
  refine ⟨hopen,I,hI,?_⟩
  intro z hz
  have heq : lift ⟨g z,mem_image_of_mem g hz⟩ = c ⟨z,hJU hz⟩ := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.snd (hg ⟨z,hJU hz⟩)
    · exact congrArg Prod.fst (hg ⟨z,hJU hz⟩)
  change q (c.symm (lift _)).val = q z
  rw [heq,c.symm_apply_apply]

end HolomorphicAnosov
open Set Topology
noncomputable section
namespace HolomorphicAnosov

/-- An open embedding transports an open inverse domain and its continuous evaluation map. -/
private theorem open_image_inverse_transport
    {X Y M : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
    (j : X → Y) (hj : IsOpenEmbedding j) (O : Set X) (hO : IsOpen O)
    (I : O → M) (hI : Continuous I) :
    IsOpen (j '' O) ∧ ∃ J : (j '' O) → M, Continuous J ∧
      ∀ x : O, J ⟨j x.val,mem_image_of_mem j x.property⟩ = I x := by
  let e : O ≃ₜ (j '' O) := hj.isEmbedding.homeomorphImage O
  refine ⟨hj.isOpenMap O hO,I ∘ e.symm,hI.comp e.symm.continuous,?_⟩
  intro x
  change I (e.symm (e x)) = I x
  rw [e.symm_apply_apply]
end HolomorphicAnosov
namespace HolomorphicAnosov
open Set Filter Metric Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold _root_.Topology ENNReal
attribute [local instance] complex_isManifold_real
noncomputable section
universe u
variable {d : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  {f : M ≃ₜ M} {S : ContinuousComplexTangentSubbundle (complexModel d) M}
  {ι : Type u} {L : ι → Type u}
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ,Fin 2 → ℝ) ∞ (L i)]
/-- Pairs of points on a common stable leaf at intrinsic distance less than `r`, with the first
point in `N`. -/
private def native_radius_pairs (F : NativeComplexStableLeafDatum f S ι L)
    (h : HermitianTangentMetricCore d M) (r : ℝ) (N : Set M) : Set (M × M) :=
  {xp | xp.1 ∈ N ∧ ∃ i, ∃ z y : L i,
    (F.partition.leaf i).inclusion z = xp.1 ∧ (F.partition.leaf i).inclusion y = xp.2 ∧
    intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf i).inclusion h z y < ENNReal.ofReal r}
/-- The centered scalar coordinate map `(x, p) ↦ (x, t p - t x)`. -/
private def scalar_pair_map (t : M → ℂ) (xp : M × M) : M × ℂ := (xp.1,t xp.2-t xp.1)

/-- For every sufficiently small radius, the scalar image of intrinsic radius pairs has an open
product domain and continuous inverse evaluation locally in the base point. -/
private theorem local_scalar_inverse_intrinsic_domain
    {d : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {S : ContinuousComplexTangentSubbundle (complexModel d) M}
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f S ι L)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (W : Set M) (hW : IsOpen W) (t : M → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ t W)
    (hB : ∀ x ∈ W, (localStableCoordinateDerivative S.toDistribution t x).IsInvertible)
    (p : M) (hpW : p ∈ W) :
    ∃ N : Set M, IsOpen N ∧ p ∈ N ∧ N ⊆ W ∧
      ∃ rMax : ℝ, 0 < rMax ∧ ∀ r : ℝ, 0 < r → r ≤ rMax →
      IsOpen (scalar_pair_map t '' native_radius_pairs F h r N) ∧
      ∃ I : (scalar_pair_map t '' native_radius_pairs F h r N) → M, Continuous I ∧
        ∀ xp (hxp : xp ∈ native_radius_pairs F h r N),
          I ⟨scalar_pair_map t xp,mem_image_of_mem _ hxp⟩ = xp.2 := by
  classical
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel d) M
  obtain ⟨V₀,ρ,q,hV₀,hpV₀,hV₀W,hρ,hq0,hqW,hqs,hqinj,htan,hcharts,
    A,V,hpV,s,hs,hU,hpin,hdom,c,hc⟩ :=
    native_scalar_inverse_metric_family F W hW t ht hB p hpW
  let U : Set (V × (Fin 2 → ℝ)) := {x | x.2 ∈ ball 0 s ∧
    A.symm (t (q x.1.1 x.2) - t x.1.1) ∈ ball 0 (s/8)}
  let G : V → (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
    fun x v ↦ A.symm (t (q x.val v) - t x.val)
  have hVV₀ (x : V) : x.val ∈ V₀ := by
    let v0 : ball (0 : Fin 2 → ℝ) (s/8) := ⟨0,mem_ball_self (by positivity)⟩
    have hhdom := (hdom (c.symm (v0,x))).1
    have hbase := (hc (c.symm (v0,x))).2
    rw [c.apply_symm_apply] at hbase
    have hv := congrArg Subtype.val hbase
    exact hv ▸ hhdom
  have hG0 (x : V) : G x 0 = 0 := by simp only [G,hq0 x.val (hVV₀ x),sub_self,map_zero]
  let : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  obtain ⟨K,hK,hpK,δ,ε₀,hδ,hε₀,hε₀s,hKδ,hsmall₀⟩ :=
    parameter_inverse_common_core G s (s/8) hs (by positivity) U hU (fun _ ↦ Iff.rfl)
      hG0 c hc ⟨p,hpV⟩
  let X := K × closedBall (0 : Fin 2 → ℝ) δ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : CompactSpace (closedBall (0 : Fin 2 → ℝ) δ) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : Nonempty X := ⟨(⟨⟨p,hpV⟩,interior_subset hpK⟩,⟨0,mem_closedBall_self hδ.le⟩)⟩
  have hXdom (z : X) : (z.1.val.val,z.2.val) ∈ V₀ ×ˢ ball (0 : Fin 2 → ℝ) ρ :=
    hdom ⟨(z.1.val,z.2.val),hKδ ⟨z.1.property,z.2.property⟩⟩
  let b : X → M := fun z ↦ q z.1.val.val z.2.val
  let Q (z : X) : (Fin 2 → ℝ) →L[ℝ] TangentSpace (realModel d) (b z) :=
    mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) (q z.1.val.val) z.2.val
  let input : X × (Fin 2 → ℝ) → (V₀ × ball (0 : Fin 2 → ℝ) ρ) × (Fin 2 → ℝ) :=
    fun z ↦ ((⟨z.1.1.val.val,(hXdom z.1).1⟩,⟨z.1.2.val,(hXdom z.1).2⟩),z.2)
  have hinput : Continuous input := by
    dsimp only [input, X]
    fun_prop
  obtain ⟨m,B,hm,hB0,hbounds⟩ := compact_injective_tangent_bounds
    (StableFoliationsSupport.originalSmoothRealMetric h hh) b Q (htan.comp hinput)
    (fun z ↦ hqinj _ (hXdom z).1 _ (hXdom z).2)
  let rMax : ℝ := m*(δ/4)
  have hrMax : 0 < rMax := mul_pos hm (by positivity)
  let Vout : Set M := (Subtype.val : V → M) '' interior K
  have hVout : IsOpen Vout := V.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ isOpen_interior
  have hpout : p ∈ Vout := ⟨⟨p,hpV⟩,hpK,rfl⟩
  let N := interior K
  have hN : IsOpen N := isOpen_interior
  have hN_K (x : N) : (x : V) ∈ K := interior_subset x.property
  have hsmall (x : N) : ball (0 : Fin 2 → ℝ) (δ/2) ⊆ ball 0 ρ := by
    intro v hv
    exact (hdom ⟨(x.val,v),hKδ ⟨hN_K x,
      ball_subset_closedBall (ball_subset_ball (by linarith) hv)⟩⟩).2
  choose idx e he het hqe using fun x : N ↦ hcharts x.val.val (hVV₀ x.val)
  let inc := fun x : N ↦ (F.partition.leaf (idx x)).inclusion
  have hinc0 (x : N) : inc x ((e x).symm 0) = x.val.val :=
    (hqe x 0 (mem_ball_self hρ)).symm.trans (hq0 _ (hVV₀ x.val))
  have he0 (x : N) : (e x) ((e x).symm 0) = 0 :=
    (e x).right_inv (het x (mem_ball_self hρ))
  let : ∀ x : N, T2Space (L (idx x)) := fun x ↦ (F.partition.leaf (idx x)).hausdorff
  have hmet (x : N) (u : Fin 2 → ℝ) (hu : u ∈ ball 0 (δ/2)) (w : Fin 2 → ℝ) :=
    hbounds (⟨x.val,hN_K x⟩,⟨u,ball_subset_closedBall (ball_subset_ball (by linarith) hu)⟩) w
  have htansmall : Continuous (fun z : (N × ball (0 : Fin 2 → ℝ) (δ/2)) × (Fin 2 → ℝ) ↦
      (⟨q z.1.1.val.val z.1.2, mfderiv 𝓘(ℝ,Fin 2 → ℝ) (realModel d)
        (q z.1.1.val.val) z.1.2 z.2⟩ : TangentBundle (realModel d) M)) := by
    let j : (N × ball (0 : Fin 2 → ℝ) (δ/2)) × (Fin 2 → ℝ) →
        (V₀ × ball (0 : Fin 2 → ℝ) ρ) × (Fin 2 → ℝ) := fun z ↦
      ((⟨z.1.1.val.val,hVV₀ z.1.1.val⟩,⟨z.1.2.val,hsmall z.1.1 z.1.2.property⟩),z.2)
    have hj : Continuous j := by dsimp only [j]; fun_prop
    exact htan.comp hj
  have hqc : ContinuousOn (fun z : V × (Fin 2 → ℝ) ↦ q z.1.val z.2) U := by
    let j : U → (V₀ × ball (0 : Fin 2 → ℝ) ρ) × (Fin 2 → ℝ) := fun z ↦
      ((⟨z.val.1.val,(hdom z).1⟩,⟨z.val.2,(hdom z).2⟩),0)
    have hj : Continuous j := by dsimp only [j]; fun_prop
    exact continuousOn_iff_continuous_domRestrict.mpr
      ((FiberBundle.continuous_proj (ComplexModel d) (fun x : M ↦ TangentSpace (realModel d) x)).comp
        (htan.comp hj))
  refine ⟨Vout,hVout,hpout,?_,rMax,hrMax,?_⟩
  · rintro x ⟨v,hv,rfl⟩
    exact hV₀W (hVV₀ v)
  intro r hr hrr
  let J₀ := {z : N × ball (0 : Fin 2 → ℝ) (δ/2) |
    intrinsicHermitianLeafEDist (r := 2) (inc z.1) h
      ((e z.1).symm 0) ((e z.1).symm z.2) < ENNReal.ofReal r}
  have hJ₀ : IsOpen J₀ := native_moving_ball_open (fun x : N ↦ L (idx x)) h hh inc
    (fun x ↦ (F.partition.leaf (idx x)).immersion.contMDiff)
    (fun x ↦ (F.partition.leaf (idx x)).immersion.mfderiv_injective (by simp))
    e he (fun x : N ↦ q x.val.val) (δ/2) (δ/4) m B r (by positivity) (by linarith) hm hrr
    (fun x ↦ (hsmall x).trans (het x))
    (fun x ↦ (hqs _ (hVV₀ x.val)).mono (hsmall x))
    (fun x v hv ↦ hqe x v (hsmall x hv)) hmet htansmall
  let emb : N × ball (0 : Fin 2 → ℝ) (δ/2) → V × (Fin 2 → ℝ) :=
    fun z ↦ (z.1.val,z.2.val)
  have hemb : Topology.IsOpenEmbedding emb :=
    hN.isOpenEmbedding_subtypeVal.prodMap isOpen_ball.isOpenEmbedding_subtypeVal
  let J := emb '' J₀
  have hJ : IsOpen J := hemb.isOpenMap _ hJ₀
  have hJU : J ⊆ U := by
    rintro z ⟨⟨x,v⟩,hd,rfl⟩
    exact hKδ ⟨hN_K x,ball_subset_closedBall (ball_subset_ball (by linarith) v.property)⟩
  let g : V × (Fin 2 → ℝ) → V × (Fin 2 → ℝ) := fun z ↦ (z.1,G z.1 z.2)
  have hcg : ∀ z : U, g z = ((c z).2,((c z).1 : Fin 2 → ℝ)) := by
    intro z
    exact Prod.ext (hc z).2.symm (hc z).1.symm
  obtain ⟨hO,I,hI,hIeq⟩ := product_inverse_open_image U J (ball (0 : Fin 2 → ℝ) (s/8))
    hJ hJU isOpen_ball c g hcg (fun z ↦ q z.1.val z.2) hqc
  let out : V × (Fin 2 → ℝ) → M × ℂ := fun z ↦ (z.1.val,A z.2)
  have hout : Topology.IsOpenEmbedding out :=
    V.isOpen.isOpenEmbedding_subtypeVal.prodMap A.toHomeomorph.isOpenEmbedding
  obtain ⟨hO',I',hI',hI'eq⟩ := open_image_inverse_transport out hout (g '' J) hO I hI
  have hformula (z : V × (Fin 2 → ℝ)) :
      out (g z) = scalar_pair_map t (z.1.val,q z.1.val z.2) := by
    change (z.1.val,A (A.symm _)) = _
    rw [A.apply_symm_apply]
    rfl
  have hforward (z : V × (Fin 2 → ℝ)) (hz : z ∈ J) :
      (z.1.val,q z.1.val z.2) ∈ native_radius_pairs F h r Vout := by
    obtain ⟨⟨x,v⟩,hd,rfl⟩ := hz
    refine ⟨⟨x.val,x.property,rfl⟩,idx x,(e x).symm 0,(e x).symm v,hinc0 x,?_,hd⟩
    exact (hqe x v (hsmall x v.property)).symm
  have hback (xp : M × M) (hxp : xp ∈ native_radius_pairs F h r Vout) :
      ∃ z : V × (Fin 2 → ℝ), z ∈ J ∧ out (g z) = scalar_pair_map t xp ∧
        q z.1.val z.2 = xp.2 := by
    obtain ⟨⟨x,hx,hxx⟩,i,z,y,hz,hy,hd⟩ := hxp
    let xN : N := ⟨x,hx⟩
    have hi : idx xN = i := F.partition.disjoint _ _ ((e xN).symm 0) z
      ((hinc0 xN).trans (hxx.trans hz.symm))
    subst i
    have hz0 : z = (e xN).symm 0 := (F.partition.leaf (idx xN)).injective
      (hz.trans (hxx.symm.trans (hinc0 xN).symm))
    rw [hz0] at hd
    have hyconf := native_plaque_intrinsic_ball_confinement h hh (inc xN) (e xN) (he xN)
      (q x.val) (δ/2) (δ/4) m (by positivity) (by linarith) hm
      ((hsmall xN).trans (het xN)) ((hqs _ (hVV₀ x)).mono (hsmall xN))
      (fun v hv ↦ hqe xN v (hsmall xN hv)) (fun u hu w ↦ (hmet xN u hu w).1)
      ((e xN).map_target (het xN (mem_ball_self hρ))) (he0 xN)
      (hd.trans_le (ENNReal.ofReal_le_ofReal hrr))
    let v : ball (0 : Fin 2 → ℝ) (δ/2) :=
      ⟨e xN y,ball_subset_ball (by linarith) hyconf.2⟩
    have hvdist : (xN,v) ∈ J₀ := by
      change intrinsicHermitianLeafEDist (inc xN) h ((e xN).symm 0) ((e xN).symm (e xN y)) < _
      rw [(e xN).left_inv hyconf.1]
      exact hd
    have hqv : q x.val v.val = xp.2 := by
      rw [hqe xN v (hsmall xN v.property),(e xN).left_inv hyconf.1]
      exact hy
    refine ⟨(x,v.val),⟨(xN,v),hvdist,rfl⟩,?_,hqv⟩
    rw [hformula,hqv,hxx]
  have hsets : out '' (g '' J) = scalar_pair_map t '' native_radius_pairs F h r Vout := by
    ext w
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨(z.1.val,q z.1.val z.2),hforward z hz,(hformula z).symm⟩
    · rintro ⟨xp,hxp,rfl⟩
      obtain ⟨z,hz,heq,hqz⟩ := hback xp hxp
      exact ⟨g z,mem_image_of_mem g hz,heq⟩
  refine ⟨hsets ▸ hO',?_⟩
  let eO := Homeomorph.setCongr hsets
  let Iout : (scalar_pair_map t '' native_radius_pairs F h r Vout) → M := I' ∘ eO.symm
  refine ⟨Iout,hI'.comp eO.symm.continuous,?_⟩
  intro xp hxp
  obtain ⟨z,hz,heq,hqz⟩ := hback xp hxp
  have hi' := hI'eq (⟨g z,mem_image_of_mem g hz⟩ : g '' J)
  have heq' : eO.symm ⟨scalar_pair_map t xp,mem_image_of_mem _ hxp⟩ =
      ⟨out (g z),mem_image_of_mem out (mem_image_of_mem g hz)⟩ :=
    Subtype.ext heq.symm
  change I' (eO.symm _) = xp.2
  rw [heq',hi',hIeq z hz,hqz]

end
end HolomorphicAnosov
namespace HolomorphicAnosov
open Set Filter _root_.Topology
open scoped Manifold ContDiff ENNReal
noncomputable section
universe u
variable {d : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  {f : M ≃ₜ M} {S : ContinuousComplexTangentSubbundle (complexModel d) M}
  {ι : Type u} {L : ι → Type u}
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ,Fin 2 → ℝ) ∞ (L i)]

/-- The scalar image of intrinsic radius pairs is open and admits continuous inverse evaluation on
its entire image. -/
private def ScalarInverseOn (F : NativeComplexStableLeafDatum f S ι L)
    (h : HermitianTangentMetricCore d M) (t : M → ℂ) (r : ℝ) (N : Set M) : Prop :=
  IsOpen (scalar_pair_map t '' native_radius_pairs F h r N) ∧
  ∃ I : (scalar_pair_map t '' native_radius_pairs F h r N) → M, Continuous I ∧
    ∀ xp (hxp : xp ∈ native_radius_pairs F h r N),
      I ⟨scalar_pair_map t xp,mem_image_of_mem _ hxp⟩ = xp.2

/-- Restricting the base to an open subset preserves openness of the scalar inverse domain and
continuity of inverse evaluation. -/
private theorem scalar_inverse_on_restrict
    (F : NativeComplexStableLeafDatum f S ι L) (h : HermitianTangentMetricCore d M)
    (t : M → ℂ) (r : ℝ) (N N' : Set M) (hN' : IsOpen N') (hsub : N' ⊆ N)
    (hI : ScalarInverseOn F h t r N) : ScalarInverseOn F h t r N' := by
  obtain ⟨hO,I,hIc,hIe⟩ := hI
  have hD : native_radius_pairs F h r N' ⊆ native_radius_pairs F h r N :=
    fun xp hxp ↦ ⟨hsub hxp.1,hxp.2⟩
  have heq : scalar_pair_map t '' native_radius_pairs F h r N' =
      (scalar_pair_map t '' native_radius_pairs F h r N) ∩ Prod.fst ⁻¹' N' := by
    ext w
    constructor
    · rintro ⟨xp,hxp,rfl⟩
      exact ⟨mem_image_of_mem _ (hD hxp),hxp.1⟩
    · rintro ⟨⟨xp,hxp,rfl⟩,hx⟩
      exact ⟨xp,⟨hx,hxp.2⟩,rfl⟩
  have hsmall : scalar_pair_map t '' native_radius_pairs F h r N' ⊆
      scalar_pair_map t '' native_radius_pairs F h r N := image_mono hD
  let inc : (scalar_pair_map t '' native_radius_pairs F h r N') →
      (scalar_pair_map t '' native_radius_pairs F h r N) := fun w ↦ ⟨w.val,hsmall w.property⟩
  refine ⟨heq ▸ hO.inter (hN'.preimage continuous_fst),I ∘ inc,?_,?_⟩
  · exact hIc.comp (continuous_subtype_val.subtype_mk _)
  · intro xp hxp
    exact hIe xp (hD hxp)
end
end HolomorphicAnosov
namespace HolomorphicAnosov
open Set Filter _root_.Topology TopologicalSpace
open scoped ContDiff Manifold ENNReal
noncomputable section
universe u
variable {d : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]

variable {f : M ≃ₜ M} {S : ContinuousComplexTangentSubbundle (complexModel d) M}
  {ι : Type u} {L : ι → Type u}
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]

/-- A finite cover admits normalized charts and open inverse domains at one common positive
intrinsic radius. -/
private theorem global_complete_coordinate_neighborhoods [CompactSpace M]
    (F : NativeComplexStableLeafDatum f S ι L)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (nabla : QuotientLineConnection.Connection U)
    (hcover : ∀ x : M, ∃ P : ParallelPair U nabla, x ∈ P.V ∧
      ∀ y ∈ P.V, (localStableCoordinateDerivative S.toDistribution P.t y).IsInvertible) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ∃ (P : M → ParallelPair U nabla) (N : M → Set M), ∀ x,
        IsOpen (N x) ∧ x ∈ N x ∧ N x ⊆ (P x).V ∧
        (∀ y ∈ (P x).V, (localStableCoordinateDerivative S.toDistribution (P x).t y).IsInvertible) ∧
        (∀ y ∈ N x, NativeUniformChartAt F h y (P x).t (P x).V r ε) ∧
        ScalarInverseOn F h (P x).t r (N x) := by
  let C : M → ℝ → ℝ → Prop := fun x r ε ↦
    ∃ (P : ParallelPair U nabla) (N : Set M), IsOpen N ∧ x ∈ N ∧ N ⊆ P.V ∧
      (∀ y ∈ P.V, (localStableCoordinateDerivative S.toDistribution P.t y).IsInvertible) ∧
      (∀ y ∈ N, NativeUniformChartAt F h y P.t P.V r ε) ∧ ScalarInverseOn F h P.t r N
  have hmono : ∀ x r ε ε', ε' ≤ ε → C x r ε → C x r ε' := by
    rintro x r ε ε' hε ⟨P,N,hN,hxN,hNP,hB,hcharts,hI⟩
    refine ⟨P,N,hN,hxN,hNP,hB,?_,hI⟩
    intro y hy i z hz
    obtain ⟨c,e,hs,hW,hf,hh,hi,ht⟩ := hcharts y hy i z hz
    exact ⟨c,e,hs,hW,hf,hh,hi,fun v hv ↦ ht v (hv.trans_le hε)⟩
  have hloc : ∀ x, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∃ rMax : ℝ, 0 < rMax ∧ ∀ r : ℝ, 0 < r → r ≤ rMax →
        ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ V, C y r ε := by
    intro x
    obtain ⟨P,hxP,hB⟩ := hcover x
    obtain ⟨V,hV,hxV,hVP,R,hR,hcharts⟩ :=
      local_uniform_normalized_coordinates F h hh P.V P.V.isOpen P.t P.holt hB x hxP
    obtain ⟨V',hV',hxV',hV'P,R',hR',hinverse⟩ :=
      local_scalar_inverse_intrinsic_domain F h hh P.V P.V.isOpen P.t P.holt hB x hxP
    refine ⟨V ∩ V',hV.inter hV',⟨hxV,hxV'⟩,min R R',lt_min hR hR',?_⟩
    intro r hr hrR
    obtain ⟨ε,hε,hcharts⟩ := hcharts r hr (hrR.trans (min_le_left _ _))
    have hI : ScalarInverseOn F h P.t r (V ∩ V') :=
      scalar_inverse_on_restrict F h P.t r V' (V ∩ V') (hV.inter hV') inter_subset_right
        (hinverse r hr (hrR.trans (min_le_right _ _)))
    refine ⟨ε,hε,?_⟩
    intro y hy
    refine ⟨P,V ∩ V',hV.inter hV',hy,inter_subset_left.trans hVP,hB,?_,hI⟩
    intro w hw i z hz
    subst w
    exact hcharts i z hw.1
  obtain ⟨r,ε,hr,hε,hcharts⟩ := compact_uniform_two_radii C hmono hloc
  choose P N hP using hcharts
  exact ⟨r,ε,hr,hε,P,N,hP⟩

end
end HolomorphicAnosov
noncomputable section
open Set Manifold Bundle
open scoped Manifold ContDiff ENNReal
namespace HolomorphicAnosov

/-- Strict balls for the Riemannian path-length distance are path connected. -/
private theorem riemannian_ball_pathConnected
    {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace L] [ChartedSpace E L] [IsManifold 𝓘(ℝ,E) 1 L]
    [RiemannianBundle (fun x : L ↦ TangentSpace 𝓘(ℝ,E) x)]
    (x : L) (R : ℝ≥0∞) (hR : 0 < R) :
    IsPathConnected {y | riemannianEDist 𝓘(ℝ,E) x y < R} := by
  refine ⟨x,?_,?_⟩
  · simpa only [mem_ofPred_eq,riemannianEDist_self] using hR
  intro y hy
  obtain ⟨γ,hγ0,hγ1,hγ,hγlen⟩ := exists_lt_of_riemannianEDist_lt hy
  let p : Path x y := ⟨⟨fun t ↦ γ t,
    hγ.continuousOn.comp_continuous continuous_subtype_val (fun t ↦ t.property)⟩,hγ0,hγ1⟩
  refine ⟨p,?_⟩
  intro t
  change riemannianEDist 𝓘(ℝ,E) x (γ t) < R
  have hsub : Icc (0 : ℝ) (t : ℝ) ⊆ Icc 0 1 := Icc_subset_Icc le_rfl t.property.2
  exact (riemannianEDist_le_pathELength (hγ.mono hsub) hγ0 rfl t.property.1).trans_lt
    ((pathELength_mono (I := 𝓘(ℝ,E)) (γ := γ) le_rfl t.property.2).trans_lt hγlen)


attribute [local instance] complex_isManifold_real

/-- Strict balls for the intrinsic Hermitian path-length distance are path connected. -/
private theorem intrinsic_hermitian_ball_pathConnected
    {r d : ℕ} {L M : Type*} [TopologicalSpace L] [T2Space L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (hi : ∀ z, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z))
    (x : L) (R : ℝ≥0∞) (hR : 0 < R) :
    IsPathConnected {y | intrinsicHermitianLeafEDist (r := r) inc h x y < R} := by
  obtain ⟨gL, hgL⟩ := immersion_riemannianMetric_exists
    (StableFoliationsSupport.originalSmoothRealMetric h hh) inc hinc hi
  let : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, Fin r → ℝ) : L → Type _) :=
    ⟨gL.toRiemannianMetric⟩
  have he : ∀ x y : L, Manifold.riemannianEDist 𝓘(ℝ, Fin r → ℝ) x y =
      intrinsicHermitianLeafEDist (r := r) inc h x y := by
    intro x y
    rw [intrinsicPiecewiseC1Path_riemannianEDist]
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
  simp_rw [← he]
  exact riemannian_ball_pathConnected x R hR

end HolomorphicAnosov
namespace HolomorphicAnosov
open Set Filter
open scoped Manifold ContDiff Topology ENNReal
attribute [local instance] complex_isManifold_real

/-- Holomorphic maps into a complex line on an intrinsic Hermitian ball agree everywhere if their
germs at the center agree. -/
private theorem intrinsic_ball_coordinates_eq_of_germ
    {r d : ℕ} {L M E : Type*} [TopologicalSpace L] [T2Space L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    [ChartedSpace (ComplexModel 1) L] [IsManifold (complexModel 1) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : L → M) (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (hi : ∀ z, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z))
    (x : L) (R : ℝ≥0∞) (hR : 0 < R)
    (f g : L → E) (c c' : E ≃L[ℂ] ℂ)
    (hf : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ (c ∘ f)
      {y | intrinsicHermitianLeafEDist (r := r) inc h x y < R})
    (hg : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ (c' ∘ g)
      {y | intrinsicHermitianLeafEDist (r := r) inc h x y < R})
    (heq : f =ᶠ[𝓝 x] g) :
    EqOn f g {y | intrinsicHermitianLeafEDist (r := r) inc h x y < R} := by
  have hpath := intrinsic_hermitian_ball_pathConnected h hh inc hinc hi x R hR
  have hopen := intrinsicHermitianLeafEDist_ball_isOpen h hh inc hinc hi x R
  have hx : x ∈ {y | intrinsicHermitianLeafEDist (r := r) inc h x y < R} := by
    obtain ⟨m,_,hm⟩ := hermitian_pullback_emetric h hh inc hinc hi
    rw [mem_ofPred_eq, ←hm]
    let : EMetricSpace L := m
    have he := @edist_self L m.toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (EMetricSpace.toWeakEMetricSpace L).toWeakPseudoEMetricSpace x
    simpa only [he] using hR
  have hf' : ContMDiffOn (complexModel 1) 𝓘(ℂ,E) ∞ f
      {y | intrinsicHermitianLeafEDist (r := r) inc h x y < R} := by
    have hc := c.symm.contDiff.contMDiff.comp_contMDiffOn hf
    simpa only [Function.comp_def, c.symm_apply_apply] using hc
  have hg' : ContMDiffOn (complexModel 1) 𝓘(ℂ,E) ∞ g
      {y | intrinsicHermitianLeafEDist (r := r) inc h x y < R} := by
    have hc := c'.symm.contDiff.contMDiff.comp_contMDiffOn hg
    simpa only [Function.comp_def, c'.symm_apply_apply] using hc
  exact line_holomorphic_eqOn_of_germ
    (c.trans (ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)).symm)
    f g hopen hpath.isConnected.isPreconnected hx hf' hg' heq
end HolomorphicAnosov
namespace HolomorphicAnosov
open Set Filter _root_.Topology
open scoped ContDiff Manifold ENNReal
noncomputable section
universe u

/-- Normalized stable charts with the same ambient germ agree on their entire common intrinsic ball. -/
private theorem native_normalized_chart_overlap
    {d : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {S : ContinuousComplexTangentSubbundle (complexModel d) M}
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ,Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f S ι L)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (r ε ε' : ℝ) (hr : 0 < r) (x : M) (t t' : M → ℂ) (W W' : Set M)
    (hf : NativeUniformChartAt F h x t W r ε)
    (hg : NativeUniformChartAt F h x t' W' r ε')
    (hgerm : normalizedLocalStableCoordinate S.toDistribution t x =ᶠ[nhds x]
      normalizedLocalStableCoordinate S.toDistribution t' x)
    (i : ι) (z : L i) (hz : (F.partition.leaf i).inclusion z = x) :
    ∀ y, intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf i).inclusion h z y < ENNReal.ofReal r →
      normalizedLocalStableCoordinate S.toDistribution t x ((F.partition.leaf i).inclusion y) =
        normalizedLocalStableCoordinate S.toDistribution t' x ((F.partition.leaf i).inclusion y) := by
  let : T2Space (L i) := (F.partition.leaf i).hausdorff
  let := (F.complexUpgrade i).charts
  let := (F.complexUpgrade i).complex_manifold
  let inc := (F.partition.leaf i).inclusion
  have hinc := (F.partition.leaf i).immersion.contMDiff
  have hinj := (F.partition.leaf i).immersion.mfderiv_injective (by simp)
  let D := {y | intrinsicHermitianLeafEDist (r := 2) inc h z y < ENNReal.ofReal r}
  have hD : IsOpen D := intrinsicHermitianLeafEDist_ball_isOpen h hh inc hinc hinj z _
  have hzD : z ∈ D := by
    obtain ⟨m,_,hm⟩ := hermitian_pullback_emetric h hh inc hinc hinj
    change intrinsicHermitianLeafEDist inc h z z < ENNReal.ofReal r
    rw [←hm]
    let : EMetricSpace (L i) := m
    have he := @edist_self (L i) m.toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (EMetricSpace.toWeakEMetricSpace (L i)).toWeakPseudoEMetricSpace z
    simpa only [he] using (ENNReal.ofReal_pos.mpr hr)
  obtain ⟨c,e,hes,heW,hef,heh,hei,het⟩ := hf i z hz
  obtain ⟨c',e',hes',heW',hef',heh',hei',het'⟩ := hg i z hz
  have heq : (e : L i → S.toDistribution x) =ᶠ[nhds z] e' := by
    have hgg := hgerm.comp_tendsto (hz ▸ hinc.continuous.continuousAt.tendsto)
    filter_upwards [hD.mem_nhds hzD,hgg] with y hy hyy
    rw [hef y hy,hef' y hy]
    exact hyy
  have hgg : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ (c ∘ e') D := by
    have hc := (c'.symm.trans c).contDiff.contMDiff.comp_contMDiffOn heh'
    simpa only [Function.comp_def,ContinuousLinearEquiv.trans_apply,c'.symm_apply_apply] using hc
  have hall := intrinsic_ball_coordinates_eq_of_germ h hh inc hinc hinj z
    (ENNReal.ofReal r) (ENNReal.ofReal_pos.mpr hr) (c ∘ e) (c ∘ e')
    (ContinuousLinearEquiv.refl ℂ ℂ) (ContinuousLinearEquiv.refl ℂ ℂ)
    heh hgg (heq.fun_comp c)
  intro y hy
  rw [←hef y hy,←hef' y hy]
  exact c.injective (hall hy)

end
end HolomorphicAnosov

namespace HolomorphicAnosov
open Set Filter _root_.Topology
open scoped ContDiff Manifold ENNReal
noncomputable section
universe u

/-- The chosen normalized coordinates vary continuously on the intrinsic radius domain. -/
private theorem chosen_coordinate_continuous_on_intrinsic_domain
    {d : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {S : ContinuousComplexTangentSubbundle (complexModel d) M}
    {ι : Type u} {L : ι → Type u}
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ,Fin 2 → ℝ) ∞ (L i)]
    (F : NativeComplexStableLeafDatum f S ι L)
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (nabla : QuotientLineConnection.Connection U)
    (r ε : ℝ) (hr : 0 < r)
    (P : M → ParallelPair U nabla) (N : M → Set M)
    (hN : ∀ x, IsOpen (N x) ∧ x ∈ N x ∧ N x ⊆ (P x).V ∧
      ∀ y ∈ N x, NativeUniformChartAt F h y (P x).t (P x).V r ε)
    (hB : ∀ x y, y ∈ (P x).V →
      (localStableCoordinateDerivative S.toDistribution (P x).t y).IsInvertible) :
    let K := fun x ↦ normalizedLocalStableCoordinate S.toDistribution (P x).t x
    let D : Set (M × M) := {xp | ∃ i, ∃ z y : L i,
      (F.partition.leaf i).inclusion z = xp.1 ∧
      (F.partition.leaf i).inclusion y = xp.2 ∧
      intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf i).inclusion h z y < ENNReal.ofReal r}
    ContinuousOn (fun xp : M × M ↦
      (⟨xp.1,(K xp.1 xp.2).val⟩ : TangentBundle (complexModel d) M)) D := by
  let K := fun x ↦ normalizedLocalStableCoordinate S.toDistribution (P x).t x
  let D : Set (M × M) := {xp | ∃ i, ∃ z y : L i,
      (F.partition.leaf i).inclusion z = xp.1 ∧
      (F.partition.leaf i).inclusion y = xp.2 ∧
      intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf i).inclusion h z y < ENNReal.ofReal r}
  have hP (x : M) : x ∈ (P x).V := (hN x).2.2.1 (hN x).2.1
  have heq (a : M) (xp : M × M) (hx : xp.1 ∈ N a) (hxp : xp ∈ D) :
      K xp.1 xp.2 = normalizedLocalStableCoordinate S.toDistribution (P a).t xp.1 xp.2 := by
    obtain ⟨i,z,y,hz,hy,hd⟩ := hxp
    have hf := (hN xp.1).2.2.2 xp.1 (hN xp.1).2.1
    have hg := (hN a).2.2.2 xp.1 hx
    have hgg := chosen_parallel_coordinates_germ (S := S) U nabla P hP (P a) xp.1
      ((hN a).2.2.1 hx)
    simpa only [hy,K] using native_normalized_chart_overlap F h hh r ε ε hr
      xp.1 (P xp.1).t (P a).t (P xp.1).V (P a).V hf hg hgg i z hz y hd
  have htarget (a : M) (xp : M × M) (hx : xp.1 ∈ N a) (hxp : xp ∈ D) :
      xp.2 ∈ (P a).V := by
    obtain ⟨i,z,y,hz,hy,hd⟩ := hxp
    obtain ⟨c,e,hs,hW,hf,hh,hi,ht⟩ := (hN a).2.2.2 xp.1 hx i z hz
    rw [←hy]
    exact hW hd
  change ContinuousOn (fun xp : M × M ↦
    (⟨xp.1,(K xp.1 xp.2).val⟩ : TangentBundle (complexModel d) M)) D
  intro xp hxp
  have hx := (hN xp.1).2.1
  have hy := htarget xp.1 xp hx hxp
  have hc := (normalized_local_coordinate_continuous S (P xp.1).t (P xp.1).V
    (P xp.1).V.isOpen (P xp.1).holt (hB xp.1)).continuousAt
      (((P xp.1).V.isOpen.prod (P xp.1).V.isOpen).mem_nhds ⟨hP xp.1,hy⟩)
  apply hc.continuousWithinAt.congr_of_eventuallyEq
  have hn : ∀ᶠ w in nhdsWithin xp D, w.1 ∈ N xp.1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (((hN xp.1).1.preimage continuous_fst).mem_nhds hx)
  filter_upwards [hn,self_mem_nhdsWithin] with w hw hwD
  exact congrArg (fun v : S.toDistribution w.1 ↦
    (⟨w.1,v.val⟩ : TangentBundle (complexModel d) M)) (heq xp.1 w hw hwD)
  rfl

end
end HolomorphicAnosov
open Set Bundle _root_.Topology
open scoped Manifold ContDiff
noncomputable section
namespace HolomorphicAnosov
universe u
set_option maxHeartbeats 800000
/-- The inverse stable scalar differential is continuous as a map into the tangent bundle. (Zhang,
Lemma 2.5, p.8, equation (14)) -/
private theorem stable_scalar_inverse_continuous
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (V : Set M) (hV : IsOpen V) (t : M → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ t V)
    (hB : ∀ x ∈ V, (localStableCoordinateDerivative S.toDistribution t x).IsInvertible) :
    ContinuousOn (fun xp : M × ℂ ↦
      (⟨xp.1, ((localStableCoordinateDerivative S.toDistribution t xp.1).inverse xp.2).val⟩ :
        TangentBundle (complexModel d) M)) (V ×ˢ univ) := by
  classical
  intro xp hxp
  obtain ⟨r, hr⟩ := S.locally_trivial xp.1
  let : TopologicalSpace (TotalSpace (Fin r → ℂ) (fun x ↦ ↥(S.toDistribution x))) :=
    TopologicalSpace.induced
      (fun z ↦ (⟨z.proj, z.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  obtain ⟨e, hxe, he⟩ := hr
  let := he
  let B := fun x ↦ localStableCoordinateDerivative S.toDistribution t x
  obtain ⟨A, hA⟩ := hB xp.1 hxp.1
  let w0 : Fin r → ℂ := e.linearEquivAt ℂ xp.1 hxe (A.symm 1)
  have hw0 : w0 ≠ 0 := by
    intro h
    have ha : A.symm 1 = 0 := (e.linearEquivAt ℂ xp.1 hxe).map_eq_zero_iff.mp h
    have hz := congrArg A ha
    exact one_ne_zero (by simpa only [A.apply_symm_apply, map_zero] using hz)
  let O : Set M := e.baseSet ∩ V
  have hO : IsOpen O := e.open_baseSet.inter hV
  have hxo : xp.1 ∈ O := ⟨hxe, hxp.1⟩
  let w : ∀ x, S.toDistribution x := fun x ↦ e.symm x w0
  have hframe : Continuous (fun x : O ↦
      (⟨x.val, (w x.val).val⟩ : TangentBundle (complexModel d) M)) := by
    have hc : Continuous (fun x : O ↦
        (⟨x.val, w x.val⟩ : TotalSpace (Fin r → ℂ) (fun x ↦ ↥(S.toDistribution x)))) :=
      e.continuousOn_symm.comp_continuous
        (continuous_subtype_val.prodMk continuous_const) (fun x ↦ ⟨x.property.1, mem_univ _⟩)
    exact continuous_induced_dom.comp hc
  have hw (x : O) : w x.val ≠ 0 := by
    change (e.linearEquivAt ℂ x.val x.property.1).symm w0 ≠ 0
    exact fun h ↦ hw0 ((e.linearEquivAt ℂ x.val x.property.1).symm.map_eq_zero_iff.mp h)
  have hBw (x : O) : B x.val (w x.val) ≠ 0 := by
    obtain ⟨C, hC⟩ := hB x.val x.property.2
    change localStableCoordinateDerivative S.toDistribution t x.val (w x.val) ≠ 0
    rw [← hC]
    exact fun h ↦ hw x (C.map_eq_zero_iff.mp h)
  have hscalar : Continuous (fun x : O ↦ B x.val (w x.val)) := by
    have hc := (ht.continuousOn_tangentMapWithin (by simp) hV.uniqueMDiffOn).comp_continuous
      hframe (fun x ↦ x.property.2)
    have hs := (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℂ) (n := ∞)).continuous.comp hc
    apply hs.congr
    intro x
    change mfderivWithin (complexModel d) 𝓘(ℂ) t V x.val (w x.val).val = _
    rw [mfderivWithin_of_isOpen hV x.property.2]
    rfl
  let Q : Set (M × ℂ) := O ×ˢ univ
  have hQ : IsOpen Q := hO.prod isOpen_univ
  have hxpQ : xp ∈ Q := ⟨hxo, hxp.2⟩
  have hfirst : Continuous (fun z : Q ↦ (⟨z.val.1, z.property.1⟩ : O)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hdiff : Continuous (fun z : Q ↦ z.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hratio : Continuous (fun z : Q ↦ z.val.2 / B z.val.1 (w z.val.1)) :=
    hdiff.div (hscalar.comp hfirst) (fun z ↦ hBw ⟨z.val.1, z.property.1⟩)
  have hc : Continuous (fun z : Q ↦
      (⟨z.val.1, e.symm z.val.1 ((z.val.2 /
        B z.val.1 (w z.val.1)) • w0)⟩ :
          TotalSpace (Fin r → ℂ) (fun x ↦ ↥(S.toDistribution x)))) :=
    e.continuousOn_symm.comp_continuous
      ((continuous_fst.comp continuous_subtype_val).prodMk (hratio.smul continuous_const))
      (fun z ↦ ⟨z.property.1.1, mem_univ _⟩)
  have hnorm (z : Q) : (localStableCoordinateDerivative S.toDistribution t z.val.1).inverse z.val.2 =
      e.symm z.val.1 ((z.val.2 / B z.val.1 (w z.val.1)) • w0) := by
    change (B z.val.1).inverse _ = _
    apply (hB z.val.1 z.property.1.2).inverse_apply_eq.mpr
    rw [show e.symm z.val.1 = (e.linearEquivAt ℂ z.val.1 z.property.1.1).symm from rfl,
      map_smul, map_smul]
    change _ = _ * B z.val.1 (w z.val.1)
    exact (div_mul_cancel₀ _ (hBw ⟨z.val.1, z.property.1⟩)).symm
  have hcont : Continuous (fun z : Q ↦
      (⟨z.val.1, ((localStableCoordinateDerivative S.toDistribution t z.val.1).inverse z.val.2).val⟩ :
        TangentBundle (complexModel d) M)) := by
    apply (continuous_induced_dom.comp hc).congr
    intro z
    exact congrArg (fun v : S.toDistribution z.val.1 ↦
      (⟨z.val.1, v.val⟩ : TangentBundle (complexModel d) M)) (hnorm z).symm
  exact ((continuousOn_iff_continuous_domRestrict.mpr hcont).continuousAt
    (hQ.mem_nhds hxpQ)).continuousWithinAt
end HolomorphicAnosov
namespace HolomorphicAnosov
open Set Bundle _root_.Topology
open scoped Manifold ContDiff
noncomputable section

/-- The stable scalar differential defines a homeomorphism from the stable bundle over a transverse
coordinate neighborhood to the product with `ℂ`. -/
private theorem stable_scalar_bundle_chart
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (V : Set M) (hV : IsOpen V) (t : M → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ t V)
    (hB : ∀ x ∈ V, (localStableCoordinateDerivative S.toDistribution t x).IsInvertible) :
    letI : TopologicalSpace (TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))) :=
      TopologicalSpace.induced
        (fun w ↦ (⟨w.proj,w.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    ∃ c : {w : TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) | w.proj ∈ V} ≃ₜ (V × ℂ),
      (∀ w, (c w).1.val = w.val.proj ∧
        (c w).2 = localStableCoordinateDerivative S.toDistribution t w.val.proj w.val.snd) ∧
      (∀ z, (c.symm z).val = ⟨z.1.val,
        (localStableCoordinateDerivative S.toDistribution t z.1.val).inverse z.2⟩) := by
  let B := fun x ↦ localStableCoordinateDerivative S.toDistribution t x
  let : TopologicalSpace (TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))) :=
    TopologicalSpace.induced
      (fun w ↦ (⟨w.proj,w.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  let T := {w : TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) | w.proj ∈ V}
  let F : T → V × ℂ := fun w ↦ (⟨w.val.proj,w.property⟩,B w.val.proj w.val.snd)
  let G : V × ℂ → T := fun z ↦ ⟨⟨z.1.val,(B z.1.val).inverse z.2⟩,z.1.property⟩
  have hinc : Continuous (fun w : T ↦
      (⟨w.val.proj,w.val.snd.val⟩ : TangentBundle (complexModel d) M)) :=
    (show Continuous (fun w : TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) ↦
      (⟨w.proj,w.snd.val⟩ : TangentBundle (complexModel d) M)) from
      continuous_induced_dom).comp continuous_subtype_val
  have hbase : Continuous (fun w : T ↦ w.val.proj) :=
    (FiberBundle.continuous_proj (ComplexModel d) (fun x : M ↦ TangentSpace (complexModel d) x)).comp hinc
  have hscalar : Continuous (fun w : T ↦ B w.val.proj w.val.snd) := by
    have hc := (ht.continuousOn_tangentMapWithin (by simp) hV.uniqueMDiffOn).comp_continuous
      hinc (fun w ↦ w.property)
    have hs := (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℂ) (n := ∞)).continuous.comp hc
    apply hs.congr
    intro w
    change mfderivWithin (complexModel d) 𝓘(ℂ) t V w.val.proj w.val.snd.val = _
    rw [mfderivWithin_of_isOpen hV w.property]
    rfl
  have hF : Continuous F := (hbase.subtype_mk _).prodMk hscalar
  have hG : Continuous G := by
    apply Continuous.subtype_mk
    apply continuous_induced_rng.mpr
    exact (stable_scalar_inverse_continuous S V hV t ht hB).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z ↦ ⟨z.1.property,mem_univ _⟩)
  let c : T ≃ₜ (V × ℂ) := {
    toEquiv := {
      toFun := F
      invFun := G
      left_inv := by
        intro w
        apply Subtype.ext
        apply TotalSpace.ext (show (G (F w)).val.proj = w.val.proj from rfl)
        apply heq_of_eq
        obtain ⟨A,hA⟩ := hB w.val.proj w.property
        change (localStableCoordinateDerivative S.toDistribution t w.val.proj).inverse
          (localStableCoordinateDerivative S.toDistribution t w.val.proj w.val.snd) = w.val.snd
        rw [←hA,ContinuousLinearMap.inverse_equiv]
        exact A.symm_apply_apply _
      right_inv := by
        intro z
        apply Prod.ext (show (F (G z)).1 = z.1 from rfl)
        obtain ⟨A,hA⟩ := hB z.1.val z.1.property
        change localStableCoordinateDerivative S.toDistribution t z.1.val
          ((localStableCoordinateDerivative S.toDistribution t z.1.val).inverse z.2) = z.2
        rw [←hA,ContinuousLinearMap.inverse_equiv]
        exact A.apply_symm_apply _ }
    continuous_toFun := hF
    continuous_invFun := hG }
  exact ⟨c,fun _ ↦ ⟨rfl,rfl⟩,fun _ ↦ rfl⟩

end
end HolomorphicAnosov
namespace HolomorphicAnosov
open Set Filter Bundle _root_.Topology
open scoped ContDiff Manifold
noncomputable section

/-- The inverse stable differential transfers an open scalar inverse domain and continuous inverse
evaluation to the stable tangent bundle. -/
private theorem scalar_inverse_to_stable_bundle
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (V : Set M) (hV : IsOpen V) (t : M → ℂ)
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ) ∞ t V)
    (hB : ∀ x ∈ V, (localStableCoordinateDerivative S.toDistribution t x).IsInvertible)
    (D : Set (M × M)) (hDV : ∀ xp ∈ D, xp.1 ∈ V)
    (hO : IsOpen ((fun xp : M × M ↦ (xp.1,t xp.2-t xp.1)) '' D))
    (I : ((fun xp : M × M ↦ (xp.1,t xp.2-t xp.1)) '' D) → M)
    (hI : Continuous I)
    (hIe : ∀ xp (hxp : xp ∈ D), I ⟨(xp.1,t xp.2-t xp.1),mem_image_of_mem _ hxp⟩ = xp.2) :
    letI : TopologicalSpace (TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))) :=
      TopologicalSpace.induced
        (fun w ↦ (⟨w.proj,w.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
    let k : M × M → TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) :=
      fun xp ↦ ⟨xp.1,normalizedLocalStableCoordinate S.toDistribution t xp.1 xp.2⟩
    IsOpen (k '' D) ∧ ∃ J : (k '' D) → M, Continuous J ∧
      ∀ xp (hxp : xp ∈ D), J ⟨k xp,mem_image_of_mem _ hxp⟩ = xp.2 := by
  let : TopologicalSpace (TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))) :=
    TopologicalSpace.induced
      (fun w ↦ (⟨w.proj,w.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  let k : M × M → TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) :=
    fun xp ↦ ⟨xp.1,normalizedLocalStableCoordinate S.toDistribution t xp.1 xp.2⟩
  let O := (fun xp : M × M ↦ (xp.1,t xp.2-t xp.1)) '' D
  let Osub : Set (V × ℂ) := {z | (z.1.val,z.2) ∈ O}
  have hOsub : IsOpen Osub := hO.preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let Isub : Osub → M := fun z ↦ I ⟨(z.val.1.val,z.val.2),z.property⟩
  have hIsub : Continuous Isub := hI.comp
    ((((continuous_subtype_val.comp continuous_fst).comp continuous_subtype_val).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
  obtain ⟨c,hcf,hci⟩ := stable_scalar_bundle_chart S V hV t ht hB
  have hproj : Continuous (fun w : TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) ↦
      w.proj) :=
    (FiberBundle.continuous_proj (ComplexModel d) (fun x : M ↦ TangentSpace (complexModel d) x)).comp
      (show Continuous (fun w : TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) ↦
        (⟨w.proj,w.snd.val⟩ : TangentBundle (complexModel d) M)) from continuous_induced_dom)
  let j : V × ℂ → TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) :=
    fun z ↦ (c.symm z).val
  have hj : Topology.IsOpenEmbedding j :=
    (hV.preimage hproj).isOpenEmbedding_subtypeVal.comp c.symm.isOpenEmbedding
  obtain ⟨hJO,J,hJ,hJe⟩ := open_image_inverse_transport j hj Osub hOsub Isub hIsub
  have hmap (xp : M × M) (hxp : xp ∈ D) :
      j (⟨xp.1,hDV xp hxp⟩,t xp.2-t xp.1) = k xp := hci _
  have hsets : j '' Osub = k '' D := by
    ext w
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨xp,hxp,heq⟩ := hz
      have hx := congrArg Prod.fst heq
      have hy := congrArg Prod.snd heq
      dsimp only at hx hy
      refine ⟨xp,hxp,?_⟩
      change k xp = (c.symm z).val
      rw [hci z]
      change (⟨xp.1,(localStableCoordinateDerivative S.toDistribution t xp.1).inverse
        (t xp.2-t xp.1)⟩ : TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))) = _
      rw [hy,hx]
    · rintro ⟨xp,hxp,rfl⟩
      exact ⟨(⟨xp.1,hDV xp hxp⟩,t xp.2-t xp.1),mem_image_of_mem _ hxp,hmap xp hxp⟩
  let eO := Homeomorph.setCongr hsets
  refine ⟨hsets ▸ hJO,J ∘ eO.symm,hJ.comp eO.symm.continuous,?_⟩
  intro xp hxp
  let z : Osub := ⟨(⟨xp.1,hDV xp hxp⟩,t xp.2-t xp.1),mem_image_of_mem _ hxp⟩
  have heq : eO.symm ⟨k xp,mem_image_of_mem _ hxp⟩ =
      ⟨j z.val,mem_image_of_mem j z.property⟩ := Subtype.ext (hmap xp hxp).symm
  change J (eO.symm _) = _
  rw [heq,hJe z]
  exact hIe xp hxp

end
end HolomorphicAnosov
noncomputable section
open Set Filter Topology
open scoped Topology
namespace HolomorphicAnosov

/-- Local continuous inverse evaluations for a base-preserving map glue to a continuous inverse
evaluation on its full open image. -/
private theorem glue_local_inverse_evaluation
    {B M Y : Type*} [TopologicalSpace B] [TopologicalSpace M] [TopologicalSpace Y]
    (D : Set (B × M)) (k : B × M → Y) (baseProj : Y → B) (fallback : Y → M)
    (hbaseProj : ∀ z ∈ D, baseProj (k z) = z.1)
    (hlocal : ∀ b : B, ∃ N : Set B, b ∈ N ∧
      IsOpen (k '' (D ∩ Prod.fst ⁻¹' N)) ∧
      ∃ I : (k '' (D ∩ Prod.fst ⁻¹' N)) → M, Continuous I ∧
        ∀ z (hz : z ∈ D ∩ Prod.fst ⁻¹' N),
          I ⟨k z,mem_image_of_mem _ hz⟩ = z.2) :
    IsOpen (k '' D) ∧ ∃ inverse : Y → M, ContinuousOn inverse (k '' D) ∧
      (∀ z ∈ D, inverse (k z) = z.2) ∧
      ∀ y ∈ k '' D, (baseProj y,inverse y) ∈ D ∧ k (baseProj y,inverse y) = y := by
  classical
  let O := k '' D
  have choice (y : O) : ∃ z : B × M, z ∈ D ∧ k z = y.val := y.property
  let pick : O → B × M := fun y ↦ Classical.choose (choice y)
  have hpick (y : O) : pick y ∈ D ∧ k (pick y) = y.val := Classical.choose_spec (choice y)
  let inverse : Y → M := fun y ↦ if hy : y ∈ O then (pick ⟨y,hy⟩).2 else fallback y
  have hinverse (z : B × M) (hz : z ∈ D) : inverse (k z) = z.2 := by
    let y : O := ⟨k z,mem_image_of_mem k hz⟩
    obtain ⟨N,hzN,hN,I,hIc,hIe⟩ := hlocal z.1
    have hb : (pick y).1 = z.1 := (hbaseProj _ (hpick y).1).symm.trans
      ((congrArg baseProj (hpick y).2).trans (hbaseProj z hz))
    have hpD : pick y ∈ D ∩ Prod.fst ⁻¹' N := ⟨(hpick y).1,by change (pick y).1 ∈ N; rw [hb]; exact hzN⟩
    have hzD : z ∈ D ∩ Prod.fst ⁻¹' N := ⟨hz,hzN⟩
    have heq : (⟨k (pick y),mem_image_of_mem k hpD⟩ : k '' (D ∩ Prod.fst ⁻¹' N)) =
        ⟨k z,mem_image_of_mem k hzD⟩ := Subtype.ext (hpick y).2
    have hv := congrArg I heq
    rw [hIe _ hpD,hIe _ hzD] at hv
    change (if hy : k z ∈ O then (pick ⟨k z,hy⟩).2 else fallback (k z)) = _
    rw [dite_eq_left (mem_image_of_mem k hz)]
    exact hv
  have hopen : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨z,hz,rfl⟩
    obtain ⟨N,hzN,hN,I,hIc,hIe⟩ := hlocal z.1
    exact Filter.mem_of_superset (hN.mem_nhds (mem_image_of_mem k ⟨hz,hzN⟩))
      (image_mono inter_subset_left)
  have hcont : ContinuousOn inverse O := by
    rintro y ⟨z,hz,rfl⟩
    obtain ⟨N,hzN,hN,I,hIc,hIe⟩ := hlocal z.1
    have heq : ∀ y : k '' (D ∩ Prod.fst ⁻¹' N), I y = inverse y.val := by
      rintro ⟨y,w,hw,rfl⟩
      exact (hIe w hw).trans (hinverse w hw.1).symm
    have hc : ContinuousOn inverse (k '' (D ∩ Prod.fst ⁻¹' N)) :=
      continuousOn_iff_continuous_domRestrict.mpr (hIc.congr heq)
    exact (hc.continuousAt (hN.mem_nhds (mem_image_of_mem k ⟨hz,hzN⟩))).continuousWithinAt
  refine ⟨hopen,inverse,hcont,hinverse,?_⟩
  rintro y ⟨z,hz,rfl⟩
  rw [hbaseProj z hz,hinverse z hz]
  exact ⟨hz,rfl⟩
end HolomorphicAnosov
open Set
noncomputable section
namespace HolomorphicAnosov
/-- Maps agreeing on a source have the same image and continuous inverse evaluation laws. -/
private theorem inverse_image_eqOn_transport
    {X Y M : Type*} [TopologicalSpace Y] [TopologicalSpace M]
    (D : Set X) (f g : X → Y) (endpoint : X → M) (heq : EqOn f g D)
    (hO : IsOpen (f '' D)) (I : (f '' D) → M) (hI : Continuous I)
    (hIe : ∀ x (hx : x ∈ D), I ⟨f x,mem_image_of_mem _ hx⟩ = endpoint x) :
    IsOpen (g '' D) ∧ ∃ J : (g '' D) → M, Continuous J ∧
      ∀ x (hx : x ∈ D), J ⟨g x,mem_image_of_mem _ hx⟩ = endpoint x := by
  have hs : f '' D = g '' D := image_congr heq
  let e := Homeomorph.setCongr hs
  refine ⟨hs ▸ hO,I ∘ e.symm,hI.comp e.symm.continuous,?_⟩
  intro x hx
  have hh : e.symm ⟨g x,mem_image_of_mem _ hx⟩ = ⟨f x,mem_image_of_mem _ hx⟩ :=
    Subtype.ext (heq hx).symm
  change I (e.symm _) = _
  rw [hh,hIe x hx]
end HolomorphicAnosov

/-! Uniform normalized holomorphic coordinates on intrinsic stable balls, with continuous inverse
evaluation on open stable bundle domains. (Zhang, Lemma 2.5, p.8, equation (15), and equation
(14), p.7) -/

attribute [local instance] HolomorphicAnosov.complex_isManifold_real

open Set _root_.Topology TopologicalSpace
open scoped ContDiff Manifold ENNReal

noncomputable section

namespace HolomorphicAnosov.Paper.Zhang

universe u


/-- For a compact complex manifold of dimension at least three with a holomorphic Anosov
diffeomorphism and one-dimensional stable bundle, normalized stable coordinates give
biholomorphisms on intrinsic Hermitian balls of a common radius, fixing the center with identity
derivative and containing a common Hermitian ball in each image. The coordinates agree as germs
with every parallel transverse pair and vary continuously with their inverses on open bundle
image domains. (Zhang, Lemma 2.5, p.8, equation (15), and equation (14), p.7) -/
theorem uniform_local_stable_coordinates
    {d : ℕ} (hd : 3 ≤ d) (M : Type u)
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (hS : ∀ x, ((S.toDistribution x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.stable.toDistribution x)
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (hU : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hU_invariant : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (nabla : QuotientLineConnection.Connection U)
    (hcontinuous : QuotientLineConnection.IsContinuous nabla)
    (hcompatible : QuotientLineConnection.IsCompatible nabla)
    (hinvariant : QuotientLineConnection.IsInvariant nabla f hU_invariant)
    (ι : Type u) (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h) :
    letI : MetrizableSpace M := Manifold.metrizableSpace (realModel d) M
    letI : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
    ∀ F : NativeComplexStableLeafDatum f.toHomeomorph S ι L,
    ∃ (r ε : ℝ) (K : ∀ x : M, M → S.toDistribution x)
      (inverse : Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) → M),
      0 < r ∧ 0 < ε ∧
      (∀ x, K x x = 0) ∧
      (∀ (V : TopologicalSpace.Opens M)
        (σ : ∀ y : M, QuotientLineConnection.Fibre U y) (t : M → ℂ),
        QuotientLineConnection.IsHolomorphicSection U V σ →
        (∀ y ∈ V, σ y ≠ 0) → QuotientLineConnection.IsParallelOn nabla V σ →
        ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V →
        (∀ y ∈ V, ∀ v : TangentSpace (complexModel d) y,
          QuotientLineConnection.projection U y v =
            ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t y)).toContinuousLinearMap.comp
              (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t y)) v • σ y) →
        ∀ i (z : L i), (F.partition.leaf i).inclusion z ∈ V →
        ∃ W : Set (L i), IsOpen W ∧ z ∈ W ∧
          W ⊆ (F.partition.leaf i).inclusion ⁻¹' (V : Set M) ∧
          ∀ p ∈ W,
            K ((F.partition.leaf i).inclusion z) ((F.partition.leaf i).inclusion p) =
              normalizedLocalStableCoordinate S.toDistribution t
                ((F.partition.leaf i).inclusion z) ((F.partition.leaf i).inclusion p)) ∧
      (∀ i (z : L i),
        let x := (F.partition.leaf i).inclusion z
        let W : Set (L i) := {p | intrinsicHermitianLeafEDist (r := 2)
          (F.partition.leaf i).inclusion h z p < ENNReal.ofReal r}
        letI := (F.complexUpgrade i).charts
        ∃ c : S.toDistribution x ≃L[ℂ] ℂ,
        ∃ e : OpenPartialHomeomorph (L i) (S.toDistribution x),
          e.source = W ∧
          (∀ p ∈ W, e p = K x ((F.partition.leaf i).inclusion p)) ∧
          ContMDiffOn (complexModel 1) 𝓘(ℂ, ℂ) ∞ (c ∘ e) W ∧
          ContMDiffOn 𝓘(ℂ, ℂ) (complexModel 1) ∞ (e.symm ∘ c.symm)
            (c.symm ⁻¹' e.target) ∧
          (∀ v : S.toDistribution x,
            Real.sqrt ((h x).inner v.val v.val).re < ε → v ∈ e.target) ∧
          (S.toDistribution x).subtypeL.comp
            (c.symm.toContinuousLinearMap.comp
              ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (c (K x x))).toContinuousLinearMap.comp
                (mfderiv (complexModel 1) 𝓘(ℂ, ℂ)
                  (fun p : L i ↦ c (K x ((F.partition.leaf i).inclusion p))) z))) =
            mfderiv (complexModel 1) (complexModel d) (F.partition.leaf i).inclusion z) ∧
      (let D : Set (M × M) := {xp | ∃ i, ∃ z p : L i,
          (F.partition.leaf i).inclusion z = xp.1 ∧
          (F.partition.leaf i).inclusion p = xp.2 ∧
          intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf i).inclusion h z p < ENNReal.ofReal r}
       letI : TopologicalSpace
           (Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))) :=
         TopologicalSpace.induced
           (fun w ↦ (⟨w.proj, w.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
       let O : Set (Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))) :=
         (fun xp : M × M ↦ ⟨xp.1, K xp.1 xp.2⟩) '' D
       ContinuousOn (fun xp : M × M ↦
         (⟨xp.1, K xp.1 xp.2⟩ :
           Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)))) D ∧
       IsOpen O ∧ ContinuousOn inverse O ∧
       (∀ xp ∈ D, inverse ⟨xp.1, K xp.1 xp.2⟩ = xp.2) ∧
       (∀ w ∈ O, (w.proj, inverse w) ∈ D ∧ K w.proj (inverse w) = w.snd)) := by
  let : MetrizableSpace M := Manifold.metrizableSpace (realModel d) M
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  intro F
  have hstable : HasComplexRankOne a.splitting.stable.toDistribution := by
    intro x
    exact ⟨S.toDistribution x, F.finrank x, hS x⟩
  suffices hremaining :
    ∃ (r ε : ℝ) (K : ∀ x : M, M → S.toDistribution x)
      (inverse : Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) → M),
      0 < r ∧ 0 < ε ∧
      (∀ (V : TopologicalSpace.Opens M)
        (σ : ∀ y : M, QuotientLineConnection.Fibre U y) (t : M → ℂ),
        QuotientLineConnection.IsHolomorphicSection U V σ →
        (∀ y ∈ V, σ y ≠ 0) → QuotientLineConnection.IsParallelOn nabla V σ →
        ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V →
        (∀ y ∈ V, ∀ v : TangentSpace (complexModel d) y,
          QuotientLineConnection.projection U y v =
            ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t y)).toContinuousLinearMap.comp
              (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t y)) v • σ y) →
        ∀ i (z : L i), (F.partition.leaf i).inclusion z ∈ V →
        ∃ W : Set (L i), IsOpen W ∧ z ∈ W ∧
          W ⊆ (F.partition.leaf i).inclusion ⁻¹' (V : Set M) ∧
          ∀ p ∈ W,
            K ((F.partition.leaf i).inclusion z) ((F.partition.leaf i).inclusion p) =
              normalizedLocalStableCoordinate S.toDistribution t
                ((F.partition.leaf i).inclusion z) ((F.partition.leaf i).inclusion p)) ∧
      (∀ i (z : L i),
        let x := (F.partition.leaf i).inclusion z
        let W : Set (L i) := {p | intrinsicHermitianLeafEDist (r := 2)
          (F.partition.leaf i).inclusion h z p < ENNReal.ofReal r}
        letI := (F.complexUpgrade i).charts
        ∃ c : S.toDistribution x ≃L[ℂ] ℂ,
        ∃ e : OpenPartialHomeomorph (L i) (S.toDistribution x),
          e.source = W ∧
          (∀ p ∈ W, e p = K x ((F.partition.leaf i).inclusion p)) ∧
          ContMDiffOn (complexModel 1) 𝓘(ℂ, ℂ) ∞ (c ∘ e) W ∧
          ContMDiffOn 𝓘(ℂ, ℂ) (complexModel 1) ∞ (e.symm ∘ c.symm)
            (c.symm ⁻¹' e.target) ∧
          (∀ v : S.toDistribution x,
            Real.sqrt ((h x).inner v.val v.val).re < ε → v ∈ e.target)) ∧
      (let D : Set (M × M) := {xp | ∃ i, ∃ z p : L i,
          (F.partition.leaf i).inclusion z = xp.1 ∧
          (F.partition.leaf i).inclusion p = xp.2 ∧
          intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf i).inclusion h z p < ENNReal.ofReal r}
       letI : TopologicalSpace
           (Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))) :=
         TopologicalSpace.induced
           (fun w ↦ (⟨w.proj, w.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
       let O : Set (Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))) :=
         (fun xp : M × M ↦ ⟨xp.1, K xp.1 xp.2⟩) '' D
       ContinuousOn (fun xp : M × M ↦
         (⟨xp.1, K xp.1 xp.2⟩ :
           Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)))) D ∧
       IsOpen O ∧ ContinuousOn inverse O ∧
       (∀ xp ∈ D, inverse ⟨xp.1, K xp.1 xp.2⟩ = xp.2) ∧
       (∀ w ∈ O, (w.proj, inverse w) ∈ D ∧ K w.proj (inverse w) = w.snd)) by
    obtain ⟨r, ε, K, inverse, hr, hε, hgerm, hleaf, hinverse⟩ := hremaining
    refine ⟨r, ε, K, inverse, hr, hε, ?_, hgerm, ?_, hinverse⟩
    · intro x
      obtain ⟨V, hxV, σ, t, hσ, hnz, hparallel, ht, hsub, hformula⟩ :=
        transverse_parallel_coordinates hd M f a hstable U hU hU_invariant
          nabla hcontinuous hcompatible hinvariant x
      obtain ⟨i, z, rfl⟩ := F.partition.cover x
      obtain ⟨W, hWopen, hzW, hWV, hKeq⟩ :=
        hgerm V σ t hσ hnz hparallel ht (fun y hy v ↦ (hformula y hy).1 v)
          i z hxV
      simpa only [normalizedLocalStableCoordinate, sub_self, map_zero] using hKeq z hzW
    · intro i z
      let := (F.complexUpgrade i).charts
      obtain ⟨c, e, heW, heK, hehol, heinv, hetarget⟩ := hleaf i z
      refine ⟨c, e, heW, heK, hehol, heinv, hetarget, ?_⟩
      let x := (F.partition.leaf i).inclusion z
      obtain ⟨V, hxV, σ, t, hσ, hnz, hparallel, ht, hsub, hformula⟩ :=
        transverse_parallel_coordinates hd M f a hstable U hU hU_invariant
          nabla hcontinuous hcompatible hinvariant x
      obtain ⟨W, hWopen, hzW, hWV, hKeq⟩ :=
        hgerm V σ t hσ hnz hparallel ht (fun y hy v ↦ (hformula y hy).1 v)
          i z hxV
      have hB := localLinearization_stable_coordinate_derivative_invertible
        f a S hS U hU t x (F.finrank x) (hformula x hxV).2
      have heq : (fun p : L i ↦ c (K x ((F.partition.leaf i).inclusion p)))
          =ᶠ[nhds z] (fun p : L i ↦ c (normalizedLocalStableCoordinate
            S.toDistribution t x ((F.partition.leaf i).inclusion p))) := by
        filter_upwards [hWopen.mem_nhds hzW] with p hp
        rw [hKeq p hp]
      have heqd := heq.mfderiv_eq (I := complexModel 1) (I' := 𝓘(ℂ, ℂ))
      have hd := normalizedLocalStableCoordinate_derivative S.toDistribution
        (F.partition.leaf i).inclusion t z
        ((F.complexUpgrade i).inclusion_holomorphic.mdifferentiable (by simp) z)
        (((ht x hxV).contMDiffAt (V.isOpen.mem_nhds hxV)).mdifferentiableAt (by simp))
        (F.complex_tangent i z).le hB c
      ext v
      have hdv := congrArg (fun T ↦ T v) hd
      have hkv := congrArg (fun T ↦ (c.symm (T v)).val) heqd
      exact hkv.trans hdv

  classical
  have hpairs : ∀ x : M, ∃ P : ParallelPair U nabla, x ∈ P.V ∧
      ∀ y ∈ P.V, (localStableCoordinateDerivative S.toDistribution P.t y).IsInvertible := by
    intro x
    obtain ⟨V,hxV,σ,t,hσ,hnz,hpar,ht,hsub,hformula⟩ :=
      transverse_parallel_coordinates hd M f a hstable U hU hU_invariant
        nabla hcontinuous hcompatible hinvariant x
    let P : ParallelPair U nabla := ⟨V,σ,t,hσ,hnz,hpar,ht,fun y hy ↦ (hformula y hy).1⟩
    refine ⟨P,hxV,?_⟩
    intro y hy
    exact localLinearization_stable_coordinate_derivative_invertible f a S hS U hU
      t y (F.finrank y) (hformula y hy).2
  obtain ⟨r,ε,hr,hε,P,N,hNfull⟩ := global_complete_coordinate_neighborhoods F h hh U nabla hpairs
  have hN : ∀ x, IsOpen (N x) ∧ x ∈ N x ∧ N x ⊆ (P x).V ∧
      ∀ y ∈ N x, NativeUniformChartAt F h y (P x).t (P x).V r ε :=
    fun x ↦ ⟨(hNfull x).1,(hNfull x).2.1,(hNfull x).2.2.1,(hNfull x).2.2.2.2.1⟩
  have hB : ∀ x y, y ∈ (P x).V →
      (localStableCoordinateDerivative S.toDistribution (P x).t y).IsInvertible :=
    fun x ↦ (hNfull x).2.2.2.1
  have hP (x : M) : x ∈ (P x).V := (hN x).2.2.1 (hN x).2.1
  let K : ∀ x : M, M → S.toDistribution x :=
    fun x ↦ normalizedLocalStableCoordinate S.toDistribution (P x).t x
  let D : Set (M × M) := {xp | ∃ i, ∃ z y : L i,
      (F.partition.leaf i).inclusion z = xp.1 ∧
      (F.partition.leaf i).inclusion y = xp.2 ∧
      intrinsicHermitianLeafEDist (r := 2) (F.partition.leaf i).inclusion h z y < ENNReal.ofReal r}
  let : TopologicalSpace (Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))) :=
    TopologicalSpace.induced
      (fun w ↦ (⟨w.proj,w.snd.val⟩ : TangentBundle (complexModel d) M)) inferInstance
  let k : M × M → Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x)) :=
    fun xp ↦ ⟨xp.1,K xp.1 xp.2⟩
  have heq (b : M) (xp : M × M) (hx : xp.1 ∈ N b) (hxp : xp ∈ D) :
      K xp.1 xp.2 = normalizedLocalStableCoordinate S.toDistribution (P b).t xp.1 xp.2 := by
    obtain ⟨i,z,y,hz,hy,hd⟩ := hxp
    have hf := (hN xp.1).2.2.2 xp.1 (hN xp.1).2.1
    have hg := (hN b).2.2.2 xp.1 hx
    have hgg := chosen_parallel_coordinates_germ (S := S) U nabla P hP (P b) xp.1
      ((hN b).2.2.1 hx)
    simpa only [hy,K] using native_normalized_chart_overlap F h hh r ε ε hr
      xp.1 (P xp.1).t (P b).t (P xp.1).V (P b).V hf hg hgg i z hz y hd
  have hlocal : ∀ b : M, ∃ N' : Set M, b ∈ N' ∧
      IsOpen (k '' (D ∩ Prod.fst ⁻¹' N')) ∧
      ∃ I : (k '' (D ∩ Prod.fst ⁻¹' N')) → M, Continuous I ∧
        ∀ xp (hxp : xp ∈ D ∩ Prod.fst ⁻¹' N'),
          I ⟨k xp,mem_image_of_mem _ hxp⟩ = xp.2 := by
    intro b
    refine ⟨N b,(hN b).2.1,?_⟩
    have hsets : native_radius_pairs F h r (N b) = D ∩ Prod.fst ⁻¹' N b := by
      ext xp
      exact and_comm
    obtain ⟨ho,I,hIc,hIe⟩ := (hNfull b).2.2.2.2.2
    change IsOpen (scalar_pair_map (P b).t '' native_radius_pairs F h r (N b)) at ho
    have hresult := scalar_inverse_to_stable_bundle S (P b).V (P b).V.isOpen
      (P b).t (P b).holt (hB b) (native_radius_pairs F h r (N b))
      (fun xp hxp ↦ (hN b).2.2.1 hxp.1) ho I hIc hIe
    rw [hsets] at hresult
    obtain ⟨hbo,J,hJ,hJe⟩ := hresult
    apply inverse_image_eqOn_transport (D ∩ Prod.fst ⁻¹' N b)
      (fun xp : M × M ↦ (⟨xp.1,normalizedLocalStableCoordinate S.toDistribution
        (P b).t xp.1 xp.2⟩ : Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))))
      k Prod.snd ?_ hbo J hJ hJe
    intro xp hxp
    exact congrArg (fun v : S.toDistribution xp.1 ↦
      (⟨xp.1,v⟩ : Bundle.TotalSpace (ComplexModel d) (fun x ↦ ↥(S.toDistribution x))))
      (heq b xp hxp.2 hxp.1).symm
  obtain ⟨hO,inverse,hIc,hIl,hIr⟩ := glue_local_inverse_evaluation D k
    (fun w ↦ w.proj) (fun w ↦ w.proj) (fun _ _ ↦ rfl) hlocal
  refine ⟨r,ε,K,inverse,hr,hε,?_,?_,?_⟩
  · intro V σ t hσ hnσ hpσ ht hf i z hz
    let Q : ParallelPair U nabla := ⟨V,σ,t,hσ,hnσ,hpσ,ht,hf⟩
    have he := chosen_parallel_coordinates_germ (S := S) U nabla P hP Q
      ((F.partition.leaf i).inclusion z) hz
    have hl := he.comp_tendsto (F.partition.leaf i).immersion.contMDiff.continuous.continuousAt.tendsto
    obtain ⟨W,hW,hWo,hzW⟩ := eventually_nhds_iff.mp hl
    let W' := W ∩ (F.partition.leaf i).inclusion ⁻¹' (V : Set M)
    refine ⟨W',hWo.inter (V.isOpen.preimage (F.partition.leaf i).immersion.contMDiff.continuous),
      ⟨hzW,hz⟩,inter_subset_right,?_⟩
    intro y hy
    exact hW y hy.1
  · intro i z
    let x := (F.partition.leaf i).inclusion z
    obtain ⟨c,e,hes,heW,hef,heh,hei,het⟩ := (hN x).2.2.2 x (hN x).2.1 i z rfl
    exact ⟨c,e,hes,hef,heh,hei,het⟩
  · refine ⟨?_,hO,hIc,hIl,?_⟩
    · have hc := chosen_coordinate_continuous_on_intrinsic_domain F h hh U nabla r ε hr P N hN hB
      apply continuousOn_iff_continuous_domRestrict.mpr
      apply continuous_induced_rng.mpr
      exact continuousOn_iff_continuous_domRestrict.mp hc
    · intro w hw
      have hh := hIr w hw
      refine ⟨hh.1,?_⟩
      exact (Bundle.TotalSpace.mk_injective w.proj) hh.2

end HolomorphicAnosov.Paper.Zhang

