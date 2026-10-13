import HolomorphicAnosov.Geometry.Holonomy.NativeStablePlaqueProducts
import HolomorphicAnosov.Analysis.Complex.AffineHolonomyFamilySchwarzian
import HolomorphicAnosov.Dynamics.Anosov.StablePathIterateLength
import HolomorphicAnosov.Analysis.Complex.HolomorphicSliceSchwarzianContinuous
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Paper.Ghys.SchwarzianAffineCurveCalculus
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import HolomorphicAnosov.Topology.ParallelPathsConvexOpen
import HolomorphicAnosov.Topology.FiniteClosedCoverVariation


/-!
The Schwarzian derivative of stable holonomy vanishes in complete affine unstable coordinates.
(Ghys, Prop. 4.1 and §4, pp.594–597)
-/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold ENNReal NNReal BigOperators
open MeasureTheory
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

/-- For an invariant, stable-holonomy-continuous family of complete affine unstable structures,
the Schwarzian of every holomorphic stable holonomy representative vanishes near its marked point
in affine coordinates. (Ghys, §4, pp.594–597; HPS, §7, pp.115–116) -/
theorem proposition_4_1_schwarzian_vanishing
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (P : AnosovIntrinsicFoliationPresentation f a) :
    let _ := P.realCharts
    letI : ∀ w : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf w) :=
      fun w ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition w)
    letI : ∀ w : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf w) :=
      fun w ↦ P.complexLeaves.complex_manifold
        (Quotient.mk P.foliations.unstablePartition w)
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves)
    (_hAct : A.ActsAffinely P.foliations P.complexLeaves f)
    (_hCont : A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves)
    (_hComplete :
      ∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        ComplexAffineStructure.Complete
          (IntrinsicFoliationLeaf P.foliations.unstablePartition q) (A.structureAt q))
    (q : Quotient P.foliations.stablePartition)
      (x y : IntrinsicFoliationLeaf P.foliations.stablePartition q) (γ : Path x y)
      (H : PathHolonomyRepresentative P.foliations γ 0 1)
      (c : OpenPartialHomeomorph (P.foliations.ULeaf (γ 0).val) ℂ)
      (e : OpenPartialHomeomorph (P.foliations.ULeaf (γ 1).val) ℂ),
      (letI := P.complexLeaves.charts
          (Quotient.mk P.foliations.unstablePartition (γ 0).val);
        c ∈ ComplexAffineStructure.maximalAtlas _
          (A.atPoint
            P.foliations P.complexLeaves (γ 0).val)) →
      (letI := P.complexLeaves.charts
          (Quotient.mk P.foliations.unstablePartition (γ 1).val);
        e ∈ ComplexAffineStructure.maximalAtlas _
          (A.atPoint
            P.foliations P.complexLeaves (γ 1).val)) →
      P.foliations.uPoint (γ 0).val ∈ c.source →
      P.foliations.uPoint (γ 1).val ∈ e.source →
      IsHolomorphicCurveLocalMap H.map →
      ∀ᶠ w in 𝓝 (c (P.foliations.uPoint (γ 0).val)),
        schwarzian (affineLocalMapExpression c H.map e) w = 0 := by
  classical
  let := P.realCharts
  let : ∀ w : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf w) :=
    fun w ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition w)
  let : ∀ w : M, IsManifold (complexModel 1) ∞ (P.foliations.ULeaf w) :=
    fun w ↦ P.complexLeaves.complex_manifold
      (Quotient.mk P.foliations.unstablePartition w)
  dsimp only
  intro A hAct hCont hComplete q x y γ H c e hc he hxc hye hhol
  obtain ⟨N, C, hcover⟩ := anosov_finite_native_stable_source_cover f a P
  let w₀ : FoliationCoordinateDisk 2 := ⟨0, by simp⟩
  have hsource (i : Fin N) :=
    (C i).complete_scalar_family hRank A hAct hCont hComplete w₀
  choose coordinate transport scalar bound hcoordinate hsource_all htarget_all
    htransport hscalar hrepresents hcompact hbound_nonneg hbound using hsource
  let χ (i : Fin N) := fun t ↦ coordinate i ((C i).unstableAnchor w₀ t)
  let budget : ℝ≥0∞ := ∑ i, ENNReal.ofReal (bound i) *
    MeasureTheory.volume (χ i '' (C i).transverseCore)
  have hbudget : budget ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hcompact i).measure_lt_top.ne
  let : Bundle.RiemannianBundle (fun z : M ↦ TangentSpace (realModel d) z) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨m, hmTop, hmLength⟩ := anosov_exists_full_length_metric f a
  have hreceiving (b : P.foliations.boxIndex)
      (s₀ : FoliationCoordinateDisk (2*d-2)) (wr : FoliationCoordinateDisk 2) :=
    completePlaqueScalarFamily_nonempty f a hRank P A hAct hCont hComplete b s₀ wr
  have hdensity (b : P.foliations.boxIndex)
      (s₀ : FoliationCoordinateDisk (2*d-2)) (wr : FoliationCoordinateDisk 2)
      (D : CompletePlaqueScalarFamily P.foliations
        (A.atPoint P.foliations P.complexLeaves) b s₀ wr)
      (n : ℕ) (K₁ : Set M) (hK₁ : IsCompact K₁)
      (hKbox : K₁ ⊆ (P.foliations.box b).image) (i : Fin N) :
      ∃ B : ℂ → ℝ≥0∞, Measurable B ∧
        (∫⁻ z, B z ∂MeasureTheory.volume) ≤
          ENNReal.ofReal (bound i) * MeasureTheory.volume (χ i '' (C i).transverseCore) ∧
        ∀ z (roots : Finset (C i).transversal),
          (∀ t, t ∈ roots ↔ t ∈ (C i).transverseCore ∧
            ((f : M → M)^[n]) ((C i).anchor t).val ∈ K₁ ∧
            D.projection (((f : M → M)^[n]) ((C i).anchor t).val) = z) →
          B z = ∑ t ∈ roots, ENNReal.ofReal (bound i) /
            ENNReal.ofReal (‖deriv (fun v ↦ D.projection
              (((f : M → M)^[n]) ((coordinate i).symm v).val)) (χ i t)‖ ^ 2) := by
    let xi := ((P.foliations.box (C i).box).chart ((C i).stableCoordinate,w₀)).val
    obtain ⟨E,hE⟩ := intrinsic_unstable_iterate_biholomorph_g17 f a P n xi
    have hcalc := receiving_projection_scalar_calculus f a hRank P A
      ((f : M → M)^[n]) (f.continuous.iterate n) xi (((f : M → M)^[n]) xi)
      E hE (coordinate i) (hcoordinate i) b s₀ wr D.transport D.transport_meta
      D.coordinate D.coordinate_mem D.source_eq D.projection D.projection_box
    exact (C i).root_density_budget w₀ (coordinate i) (hsource_all i) n K₁ hK₁ b
      hKbox D.projection hcalc.2.1 hcalc.2.2 (ENNReal.ofReal (bound i))
  have htotal_density (b : P.foliations.boxIndex)
      (s₀ : FoliationCoordinateDisk (2*d-2)) (wr : FoliationCoordinateDisk 2)
      (D : CompletePlaqueScalarFamily P.foliations
        (A.atPoint P.foliations P.complexLeaves) b s₀ wr)
      (n : ℕ) (K₁ : Set M) (hK₁ : IsCompact K₁)
      (hKbox : K₁ ⊆ (P.foliations.box b).image) :
      ∃ B : ℂ → ℝ≥0∞, Measurable B ∧
        (∫⁻ z, B z ∂MeasureTheory.volume) ≤ budget ∧
        ∀ z (roots : ∀ i : Fin N, Finset (C i).transversal),
          (∀ i t, t ∈ roots i ↔ t ∈ (C i).transverseCore ∧
            ((f : M → M)^[n]) ((C i).anchor t).val ∈ K₁ ∧
            D.projection (((f : M → M)^[n]) ((C i).anchor t).val) = z) →
          B z = ∑ i, ∑ t ∈ roots i, ENNReal.ofReal (bound i) /
            ENNReal.ofReal (‖deriv (fun v ↦ D.projection
              (((f : M → M)^[n]) ((coordinate i).symm v).val)) (χ i t)‖ ^ 2) := by
    choose B hB hBbudget hBroots using hdensity b s₀ wr D n K₁ hK₁ hKbox
    refine ⟨fun z ↦ ∑ i, B i z, Finset.measurable_sum _ (fun i _ ↦ hB i),?_,?_⟩
    · rw [MeasureTheory.lintegral_finsetSum _ (fun i _ ↦ hB i)]
      exact Finset.sum_le_sum (fun i _ ↦ hBbudget i)
    · intro z roots hroots
      exact Finset.sum_congr rfl (fun i _ ↦ hBroots i z (roots i) (hroots i))
  have hrootcover (b : P.foliations.boxIndex)
      (s₀ : FoliationCoordinateDisk (2*d-2)) (wr : FoliationCoordinateDisk 2)
      (D : CompletePlaqueScalarFamily P.foliations
        (A.atPoint P.foliations P.complexLeaves) b s₀ wr)
      (K₀ K₁ : Set M) (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
      (h₀ : K₀ ⊆ interior K₁) (h₁ : K₁ ⊆ (P.foliations.box b).image) :=
    native_source_cores_eventual_root_cover f a P C hcover m hmTop hmLength b K₀ K₁
      D.projection D.label D.open_label.injective hK₀ hK₁ h₀ h₁
      D.continuous_projection D.projection_coordinate
  have hpoint_pullback (b : P.foliations.boxIndex)
      (s₀ : FoliationCoordinateDisk (2*d-2)) (wr : FoliationCoordinateDisk 2)
      (D : CompletePlaqueScalarFamily P.foliations
        (A.atPoint P.foliations P.complexLeaves) b s₀ wr)
      (n : ℕ) (i : Fin N) (t : (C i).transversal)
      (v : Metric.closedBall (0 : Fin (C i).dimension → ℝ) (C i).radius)
      (hbox : ∀ w : Metric.closedBall (0 : Fin (C i).dimension → ℝ) (C i).radius,
        ((f : M → M)^[n]) ((C i).closedEvaluation (t,w)) ∈ (P.foliations.box b).image) :
      let G := fun z ↦ D.projection (((f : M → M)^[n]) ((coordinate i).symm z).val)
      let st := (P.foliations.box b).chart.symm
        ⟨((f : M → M)^[n]) ((C i).closedEvaluation (t,v)),hbox v⟩
      scalar i (χ i t,(C i).closedStableParameter t v) =
        schwarzian G (χ i t) + D.value (G (χ i t),st.1) * deriv G (χ i t) ^ 2 := by
    intro G st
    let sv := (C i).closedStableParameter t v
    let xi := ((P.foliations.box (C i).box).chart ((C i).stableCoordinate,w₀)).val
    let yi := ((P.foliations.box (C i).box).chart (sv,w₀)).val
    let yr := ((P.foliations.box b).chart (st.1,wr)).val
    let p₀ := (C i).unstableAnchor w₀ t
    let p₁ := (transport i sv).map p₀
    have hp₀ : p₀ ∈ (transport i sv).map.source := by
      rw [(htransport i sv).2.2.2.2]
      exact ⟨t.val,rfl⟩
    have hp₁ : p₁.val = (C i).closedEvaluation (t,v) := by
      have hh := (transport i sv).coordinate_map p₀ t.val hp₀ (by
        rw [(htransport i sv).1,(htransport i sv).2.1]
        rfl)
      rw [(htransport i sv).1,(htransport i sv).2.2.1] at hh
      exact hh.trans ((C i).closed_source_coordinates t v)
    obtain ⟨E,hE⟩ := intrinsic_unstable_iterate_biholomorph_g17 f a P n yi
    have hst : ((P.foliations.box b).chart (st.1,st.2)).val =
        ((f : M → M)^[n]) p₁.val := by
      rw [hp₁]
      exact congrArg Subtype.val ((P.foliations.box b).chart.apply_symm_apply _)
    have hlabel : Quotient.mk P.foliations.unstablePartition yr =
        Quotient.mk P.foliations.unstablePartition (((f : M → M)^[n]) yi) := by
      calc
        _ = P.foliations.unstableLabel b st.1 := P.foliations.unstable_label b st.1 wr
        _ = Quotient.mk P.foliations.unstablePartition (((f : M → M)^[n]) p₁.val) :=
          (P.foliations.unstable_label b st.1 st.2).symm.trans
            (congrArg (Quotient.mk P.foliations.unstablePartition) hst)
        _ = _ := by rw [← hE p₁]; exact (E p₁).property
    let E' := E.trans (unstableLeafLabelBiholomorph_g17 f a P _ _ hlabel.symm)
    have hE' (z) : (E' z).val = ((f : M → M)^[n]) z.val :=
      (unstableLeafLabelBiholomorph_g17_val f a P _ _ hlabel.symm (E z)).trans (hE z)
    let k := D.transport st.1
    have htarget : k.map.target = {z | ∃ w : FoliationCoordinateDisk 2,
        ((P.foliations.box b).chart (st.1,w)).val = z.val} := by
      have ht := local_plaque_transport_full_target_g17 P.foliations k (by
        rw [(D.transport_meta st.1).1,(D.transport_meta st.1).2.1]
        exact (D.transport_meta st.1).2.2.2.2)
      change (D.transport st.1).map.target =
        {z | ∃ w : FoliationCoordinateDisk 2,
          ((P.foliations.box (D.transport st.1).box).chart ((D.transport st.1).second,w)).val = z.val} at ht
      rw [(D.transport_meta st.1).2.2.1] at ht
      rw [(D.transport_meta st.1).1] at ht
      exact ht
    have hpk : E' p₁ ∈ k.map.target := by
      rw [htarget]
      exact ⟨st.2,hst.trans (hE' p₁).symm⟩
    obtain ⟨ec,hec,hpec⟩ := affine_chart_at_g12
      (A.atPoint P.foliations P.complexLeaves yr) (E' p₁)
    have hproj : D.projection (E' p₁).val = G (χ i t) := by
      have hh := ((C i).iterate_projection_germ n b D.projection D.label
        D.projection_coordinate t v hbox w₀ yi (transport i sv)
        (htransport i sv).1 (htransport i sv).2.1 (htransport i sv).2.2.1 hp₀).eq_of_nhds
      have hpc : p₀ ∈ (coordinate i).source := by rw [hsource_all i]; trivial
      change D.projection (E' p₁).val =
        D.projection (((f : M → M)^[n]) ((coordinate i).symm ((coordinate i) p₀)).val)
      rw [(coordinate i).left_inv hpc,hE']
      exact hh
    have hpR : k.map.symm (E' p₁) ∈ D.coordinate.source := by rw [D.source_eq]; trivial
    have hinv : D.coordinate.symm (G (χ i t)) = k.map.symm (E' p₁) := by
      rw [← hproj,D.projection_inverse st.1 (E' p₁) hpk,D.coordinate.left_inv hpR]
    have hRsource : D.coordinate.symm (G (χ i t)) ∈ k.map.source := by
      rw [hinv]
      exact k.map.map_target hpk
    have hRtarget : k.map (D.coordinate.symm (G (χ i t))) = E' p₁ := by
      rw [hinv,k.map.right_inv hpk]
    have hDdom : G (χ i t) ∈ range D.label := by
      refine ⟨st.2,?_⟩
      rw [← hproj,hE' p₁,← hst,D.projection_box]
    have hDs := D.domain_eq_range_label ▸ hDdom
    have hDrep := D.represents (G (χ i t),st.1) ⟨hDs,mem_univ _⟩ ec hec
      (hRtarget ▸ hpec)
    have hsrc := (C i).iterate_scalar_schwarzian A hAct n b D.projection D.label
      D.projection_coordinate t v hbox w₀ yi yr
      (((P.foliations.box b).chart (s₀,wr)).val) (transport i sv)
      (htransport i sv).1 (htransport i sv).2.1 (htransport i sv).2.2.1 hp₀
      E' hE' k.map (coordinate i) D.coordinate ec (hsource_all i) D.source_eq hec
      (D.projection_inverse st.1) hpk hpec
    have hχtarget : χ i t ∈ (coordinate i).target := by rw [htarget_all i]; trivial
    have hχinv : (coordinate i).symm (χ i t) = p₀ :=
      (coordinate i).left_inv (by rw [hsource_all i]; trivial)
    have hsrcdom : (χ i t,sv) ∈ ((coordinate i).target ∩ (coordinate i).symm ⁻¹'
        {z | ∃ w : FoliationCoordinateDisk 2,
          ((P.foliations.box (C i).box).chart ((C i).stableCoordinate,w)).val = z.val}) ×ˢ univ := by
      refine ⟨⟨hχtarget,?_⟩,mem_univ _⟩
      change ∃ w : FoliationCoordinateDisk 2,
        ((P.foliations.box (C i).box).chart ((C i).stableCoordinate,w)).val =
          ((coordinate i).symm (χ i t)).val
      rw [hχinv]
      exact ⟨t.val,rfl⟩
    have hSrep := hrepresents i (χ i t,sv) hsrcdom
      (E'.toHomeomorph.toOpenPartialHomeomorph.trans ec) hsrc.1 (by
        simpa only [hχinv] using hsrc.2.1)
    rw [hSrep,hsrc.2.2, hDrep]
    obtain ⟨E₀,hE₀⟩ := intrinsic_unstable_iterate_biholomorph_g17 f a P n xi
    have hcalcG := receiving_projection_scalar_calculus f a hRank P A
      ((f : M → M)^[n]) (f.continuous.iterate n) xi (((f : M → M)^[n]) xi)
      E₀ hE₀ (coordinate i) (hcoordinate i) b s₀ wr D.transport D.transport_meta
      D.coordinate D.coordinate_mem D.source_eq D.projection D.projection_box
    have hanchorbox : ((f : M → M)^[n]) p₀.val ∈ (P.foliations.box b).image := by
      let zero : Metric.closedBall (0 : Fin (C i).dimension → ℝ) (C i).radius :=
        ⟨0,Metric.mem_closedBall_self (C i).radius_pos.le⟩
      have hz := hbox zero
      have heval : (C i).closedEvaluation (t,zero) = p₀.val :=
        ((C i).family.plaque ((C i).anchor t)).centered
      rwa [heval] at hz
    have hΩz : χ i t ∈ (coordinate i).target ∩
        (fun z ↦ ((f : M → M)^[n]) ((coordinate i).symm z).val) ⁻¹'
          (P.foliations.box b).image := by
      refine ⟨hχtarget,?_⟩
      change ((f : M → M)^[n]) ((coordinate i).symm (χ i t)).val ∈
        (P.foliations.box b).image
      rw [hχinv]
      exact hanchorbox
    have hkhol := intrinsicPresentation_plaque_holomorphic f a hRank P _ _ k
    have hcalcH := affine_local_map_schwarzian_calculus
      (A.atPoint P.foliations P.complexLeaves (((P.foliations.box b).chart (s₀,wr)).val))
      (A.atPoint P.foliations P.complexLeaves yr)
      (A.atPoint P.foliations P.complexLeaves yr)
      k.map hkhol D.coordinate ec D.coordinate_mem hec
      (D.coordinate.symm (G (χ i t))) (D.coordinate.map_target hDs.1)
      hRsource (hRtarget ▸ hpec)
    have hTz : G (χ i t) ∈ affineLocalMapDomain D.coordinate k.map ec := by
      refine ⟨⟨hDs.1,hRsource⟩,?_⟩
      change k.map (D.coordinate.symm (G (χ i t))) ∈ ec.source
      rw [hRtarget]
      exact hpec
    exact Analysis.Complex.schwarzian_chain_rule
      (hcalcG.2.1.continuousOn.isOpen_inter_preimage hcalcG.1 hcalcH.1) hcalcH.1
      (hcalcG.2.1.mono inter_subset_left) hcalcH.2.1 (fun _ hz ↦ hz.2)
      ⟨hΩz,hTz⟩ (hcalcG.2.2 _ hΩz) (hcalcH.2.2.1 _ hTz)
  have hroot_variation (b : P.foliations.boxIndex)
      (s₀ : FoliationCoordinateDisk (2*d-2)) (wr : FoliationCoordinateDisk 2)
      (D : CompletePlaqueScalarFamily P.foliations
        (A.atPoint P.foliations P.complexLeaves) b s₀ wr)
      (n : ℕ) (i : Fin N) (t : (C i).transversal) (ht : t ∈ (C i).transverseCore)
      (hbox : ∀ w : Metric.closedBall (0 : Fin (C i).dimension → ℝ) (C i).radius,
        ((f : M → M)^[n]) ((C i).closedEvaluation (t,w)) ∈ (P.foliations.box b).image)
      (v v' : Metric.closedBall (0 : Fin (C i).dimension → ℝ) (C i).radius) :
      let G := fun z ↦ D.projection (((f : M → M)^[n]) ((coordinate i).symm z).val)
      let st := fun w ↦ (P.foliations.box b).chart.symm
        ⟨((f : M → M)^[n]) ((C i).closedEvaluation (t,w)),hbox w⟩
      dist (D.value (G (χ i t),(st v).1)) (D.value (G (χ i t),(st v').1)) ≤
        bound i / ‖deriv G (χ i t)‖ ^ 2 := by
    intro G st
    let pv (w : Metric.closedBall (0 : Fin (C i).dimension → ℝ) (C i).radius) :
        (C i).parameterDomain × (C i).transversal :=
      (⟨w.val,Metric.closedBall_subset_ball (C i).radius_lt w.property⟩,t)
    have hpcore (w) : pv w ∈ (C i).parameterCore := by
      refine ⟨?_,ht⟩
      exact mem_closedBall_zero_iff.mp w.property
    have hb := hbound i (pv v) (hpcore v) (pv v') (hpcore v')
    change dist (scalar i (χ i t,(C i).closedStableParameter t v))
      (scalar i (χ i t,(C i).closedStableParameter t v')) ≤ bound i at hb
    rw [hpoint_pullback b s₀ wr D n i t v hbox,hpoint_pullback b s₀ wr D n i t v' hbox] at hb
    change dist (schwarzian G (χ i t) + D.value (G (χ i t),(st v).1) * deriv G (χ i t)^2)
      (schwarzian G (χ i t) + D.value (G (χ i t),(st v').1) * deriv G (χ i t)^2) ≤ bound i at hb
    rw [dist_eq_norm] at hb ⊢
    have heq : (schwarzian G (χ i t) + D.value (G (χ i t),(st v).1) * deriv G (χ i t)^2) -
        (schwarzian G (χ i t) + D.value (G (χ i t),(st v').1) * deriv G (χ i t)^2) =
        (D.value (G (χ i t),(st v).1) - D.value (G (χ i t),(st v').1)) * deriv G (χ i t)^2 := by
      ring
    rw [heq,norm_mul,norm_pow] at hb
    let xi := ((P.foliations.box (C i).box).chart ((C i).stableCoordinate,w₀)).val
    obtain ⟨E,hE⟩ := intrinsic_unstable_iterate_biholomorph_g17 f a P n xi
    have hcalc := receiving_projection_scalar_calculus f a hRank P A
      ((f : M → M)^[n]) (f.continuous.iterate n) xi (((f : M → M)^[n]) xi)
      E hE (coordinate i) (hcoordinate i) b s₀ wr D.transport D.transport_meta
      D.coordinate D.coordinate_mem D.source_eq D.projection D.projection_box
    have hanchorbox : ((f : M → M)^[n]) ((C i).anchor t).val ∈ (P.foliations.box b).image := by
      let zero : Metric.closedBall (0 : Fin (C i).dimension → ℝ) (C i).radius :=
        ⟨0,Metric.mem_closedBall_self (C i).radius_pos.le⟩
      have hz := hbox zero
      have heval : (C i).closedEvaluation (t,zero) = ((C i).anchor t).val :=
        ((C i).family.plaque ((C i).anchor t)).centered
      rwa [heval] at hz
    have hnz : deriv G (χ i t) ≠ 0 := by
      apply hcalc.2.2
      refine ⟨by rw [htarget_all i]; trivial,?_⟩
      change ((f : M → M)^[n]) ((coordinate i).symm ((coordinate i)
        ((C i).unstableAnchor w₀ t))).val ∈ (P.foliations.box b).image
      rw [(coordinate i).left_inv (by rw [hsource_all i]; trivial)]
      exact hanchorbox
    exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hnz))).mpr hb
  have hwhole (b : P.foliations.boxIndex) (K₁ : Set M) (hK₁ : IsCompact K₁)
      (hKbox : K₁ ⊆ (P.foliations.box b).image) :
      ∀ᶠ n : ℕ in atTop, ∀ i : Fin N, ∀ t : (C i).transversal,
        t ∈ (C i).transverseCore → ((f : M → M)^[n]) ((C i).anchor t).val ∈ K₁ →
        ∀ v : Metric.closedBall (0 : Fin (C i).dimension → ℝ) (C i).radius,
          ((f : M → M)^[n]) ((C i).closedEvaluation (t,v)) ∈ (P.foliations.box b).image := by
    let : MetricSpace M := m.replaceTopology hmTop.symm
    obtain ⟨ε,hε,hbuffer⟩ := hK₁.exists_thickening_subset_open
      (P.foliations.box b).isOpen_image hKbox
    have hsmall := Filter.eventually_all.mpr (fun i : Fin N ↦
      (C i).uniform_shrinking m hmLength ε hε)
    filter_upwards [hsmall] with n hn
    intro i t ht hk v
    apply hbuffer
    apply Metric.mem_thickening_iff.mpr
    refine ⟨((f : M → M)^[n]) ((C i).anchor t).val,hk,?_⟩
    let v' : (C i).parameterDomain :=
      ⟨v.val,Metric.closedBall_subset_ball (C i).radius_lt v.property⟩
    exact hn i (v',t) ⟨mem_closedBall_zero_iff.mp v.property,ht⟩
  have hhit_variation (b : P.foliations.boxIndex)
      (s₀ : FoliationCoordinateDisk (2*d-2)) (wr : FoliationCoordinateDisk 2)
      (D : CompletePlaqueScalarFamily P.foliations
        (A.atPoint P.foliations P.complexLeaves) b s₀ wr)
      (n : ℕ) (i : Fin N) (t : (C i).transversal) (ht : t ∈ (C i).transverseCore)
      (hbox : ∀ w : Metric.closedBall (0 : Fin (C i).dimension → ℝ) (C i).radius,
        ((f : M → M)^[n]) ((C i).closedEvaluation (t,w)) ∈ (P.foliations.box b).image)
      (z : ℂ) (hroot : D.projection (((f : M → M)^[n]) ((C i).anchor t).val) = z) :
      let Q : M → ℂ := fun p ↦ if hp : p ∈ (P.foliations.box b).image then
        D.value (z,((P.foliations.box b).chart.symm ⟨p,hp⟩).1) else 0
      ∀ p ∈ range (fun v ↦ ((f : M → M)^[n]) ((C i).closedEvaluation (t,v))),
        ∀ p' ∈ range (fun v ↦ ((f : M → M)^[n]) ((C i).closedEvaluation (t,v))),
          dist (Q p) (Q p') ≤ bound i /
            ‖deriv (fun v ↦ D.projection (((f : M → M)^[n]) ((coordinate i).symm v).val))
              (χ i t)‖ ^ 2 := by
    intro Q p hp p' hp'
    obtain ⟨v,rfl⟩ := hp
    obtain ⟨v',rfl⟩ := hp'
    have hGroot : D.projection (((f : M → M)^[n]) ((coordinate i).symm (χ i t)).val) = z := by
      change D.projection (((f : M → M)^[n]) ((coordinate i).symm
        ((coordinate i) ((C i).unstableAnchor w₀ t))).val) = z
      rw [(coordinate i).left_inv (by rw [hsource_all i]; trivial)]
      exact hroot
    have hv := hroot_variation b s₀ wr D n i t ht hbox v v'
    simpa only [Q,dite_eq_left (hbox v),dite_eq_left (hbox v'),hGroot] using hv
  have hpacking (b : P.foliations.boxIndex)
      (s₀ : FoliationCoordinateDisk (2*d-2)) (wr : FoliationCoordinateDisk 2)
      (D : CompletePlaqueScalarFamily P.foliations
        (A.atPoint P.foliations P.complexLeaves) b s₀ wr)
      (n : ℕ) (K₀ K₁ : Set M) (z : ℂ)
      (roots : ∀ i : Fin N, Finset (C i).transversal)
      (hroots : ∀ i t, t ∈ roots i ↔ t ∈ (C i).transverseCore ∧
        ((f : M → M)^[n]) ((C i).anchor t).val ∈ K₁ ∧
        D.projection (((f : M → M)^[n]) ((C i).anchor t).val) = z)
      (hclosed : ∀ i t, t ∈ roots i → IsCompact ({p ∈ K₀ | D.projection p = z} ∩
        range (fun v ↦ ((f : M → M)^[n]) ((C i).closedEvaluation (t,v)))))
      (hcovers : ∀ p ∈ K₀, D.projection p = z → ∃ i t, t ∈ roots i ∧
        p ∈ range (fun v ↦ ((f : M → M)^[n]) ((C i).closedEvaluation (t,v))))
      (hbox : ∀ i t, t ∈ roots i →
        ∀ v : Metric.closedBall (0 : Fin (C i).dimension → ℝ) (C i).radius,
          ((f : M → M)^[n]) ((C i).closedEvaluation (t,v)) ∈ (P.foliations.box b).image)
      (L : ℕ) (paths : Fin L → Set M) (hpre : ∀ j, IsPreconnected (paths j))
      (hin : ∀ j, paths j ⊆ {p ∈ K₀ | D.projection p = z})
      (honly : ∀ i t, t ∈ roots i → ∀ j k,
        (paths j ∩ range (fun v ↦ ((f : M → M)^[n]) ((C i).closedEvaluation (t,v)))).Nonempty →
        (paths k ∩ range (fun v ↦ ((f : M → M)^[n]) ((C i).closedEvaluation (t,v)))).Nonempty → j = k)
      (ends₀ ends₁ : Fin L → M) (he₀ : ∀ j, ends₀ j ∈ paths j)
      (he₁ : ∀ j, ends₁ j ∈ paths j) (η : ℝ)
      (hgap : ∀ j, η ≤ dist
        (if hp : ends₀ j ∈ (P.foliations.box b).image then
          D.value (z,((P.foliations.box b).chart.symm ⟨ends₀ j,hp⟩).1) else 0)
        (if hp : ends₁ j ∈ (P.foliations.box b).image then
          D.value (z,((P.foliations.box b).chart.symm ⟨ends₁ j,hp⟩).1) else 0)) :
      (L : ℝ≥0∞) * ENNReal.ofReal η ≤
        ∑ i, ∑ t ∈ roots i, ENNReal.ofReal (bound i) /
          ENNReal.ofReal (‖deriv (fun v ↦ D.projection
            (((f : M → M)^[n]) ((coordinate i).symm v).val)) (χ i t)‖ ^ 2) := by
    let R := Σ i : Fin N, {t // t ∈ roots i}
    let piece (r : R) := {p ∈ K₀ | D.projection p = z} ∩
      range (fun v ↦ ((f : M → M)^[n]) ((C r.1).closedEvaluation (r.2.val,v)))
    let weight (r : R) := bound r.1 /
      ‖deriv (fun v ↦ D.projection (((f : M → M)^[n]) ((coordinate r.1).symm v).val))
        (χ r.1 r.2.val)‖ ^ 2
    let Q : M → ℂ := fun p ↦ if hp : p ∈ (P.foliations.box b).image then
      D.value (z,((P.foliations.box b).chart.symm ⟨p,hp⟩).1) else 0
    have hw (r : R) : 0 ≤ weight r := div_nonneg (hbound_nonneg r.1) (sq_nonneg _)
    have hv (r : R) : ∀ p ∈ piece r, ∀ p' ∈ piece r,
        dist (Q p) (Q p') ≤ weight r := by
      intro p hp p' hp'
      exact hhit_variation b s₀ wr D n r.1 r.2.val ((hroots _ _).mp r.2.property).1
        (hbox _ _ r.2.property) z ((hroots _ _).mp r.2.property).2.2 p hp.2 p' hp'.2
    have hcov (j : Fin L) : paths j ⊆ ⋃ r : R, piece r := by
      intro p hp
      obtain ⟨i,t,ht,hp'⟩ := hcovers p (hin j hp).1 (hin j hp).2
      exact mem_iUnion.mpr ⟨⟨i,⟨t,ht⟩⟩,hin j hp,hp'⟩
    have honly' (r : R) (j k : Fin L) (hj : (paths j ∩ piece r).Nonempty)
        (hk : (paths k ∩ piece r).Nonempty) : j = k := by
      exact honly r.1 r.2.val r.2.property j k
        (hj.mono (fun _ hp ↦ ⟨hp.1,hp.2.2⟩)) (hk.mono (fun _ hp ↦ ⟨hp.1,hp.2.2⟩))
    have hp := finite_closed_cover_packing_variation paths piece Q weight
      (fun r ↦ (hclosed r.1 r.2.val r.2.property).isClosed) hpre hcov hw hv honly'
      ends₀ ends₁ he₀ he₁ η hgap
    have hpen := ENNReal.ofReal_le_ofReal hp
    simp only [Fintype.card_fin,ENNReal.ofReal_mul (Nat.cast_nonneg L),
      ENNReal.ofReal_natCast] at hpen
    apply hpen.trans
    rw [ENNReal.ofReal_sum_of_nonneg (fun r _ ↦ hw r)]
    calc
      ∑ r : R, ENNReal.ofReal (weight r) ≤ ∑ r : R,
          ENNReal.ofReal (bound r.1) / ENNReal.ofReal
            (‖deriv (fun v ↦ D.projection (((f : M → M)^[n]) ((coordinate r.1).symm v).val))
              (χ r.1 r.2.val)‖ ^ 2) :=
        Finset.sum_le_sum (fun _ _ ↦ ENNReal.ofReal_div_le (sq_nonneg _))
      _ = _ := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.sum_subtype (p := fun t ↦ t ∈ roots i) (roots i) (fun _ ↦ Iff.rfl)
          (fun t ↦ ENNReal.ofReal (bound i) / ENNReal.ofReal
            (‖deriv (fun v ↦ D.projection (((f : M → M)^[n]) ((coordinate i).symm v).val))
              (χ i t)‖ ^ 2))).symm
  have hlocal (b : P.foliations.boxIndex)
      (s₀ : FoliationCoordinateDisk (2*d-2)) (wr : FoliationCoordinateDisk 2)
      (D : CompletePlaqueScalarFamily P.foliations
        (A.atPoint P.foliations P.complexLeaves) b s₀ wr) :
      ∀ z ∈ range D.label, ∀ s, D.value (z,s) = 0 := by
    intro z₀ hz₀ s₁
    by_contra hnzero
    have hdim : 1 < 2*d-2 := by
      by_contra hh
      have he : 2*d-2 = 0 := by omega
      have : Subsingleton (FoliationCoordinateDisk (2*d-2)) := by rw [he]; infer_instance
      exact hnzero ((congrArg (fun t ↦ D.value (z₀,t)) (Subsingleton.elim s₁ s₀)).trans
        (D.value_self z₀ hz₀))
    let E := Fin (2*d-2) → ℝ
    let θ : E ≃ₜ FoliationCoordinateDisk (2*d-2) := Homeomorph.unitBall
    let S : ℂ × E → ℂ := fun p ↦ D.value (p.1,θ p.2)
    have hS : ContinuousOn S (range D.label ×ˢ univ) := by
      have hc := D.continuous_value
      rw [D.domain_eq_range_label] at hc
      exact hc.comp (continuous_fst.prodMk (θ.continuous.comp continuous_snd)).continuousOn
        (fun p hp ↦ ⟨hp.1,mem_univ _⟩)
    have hgap₀ : 0 < dist (S (z₀,θ.symm s₀)) (S (z₀,θ.symm s₁)) := by
      simp only [S,θ.apply_symm_apply,D.value_self z₀ hz₀,dist_zero_left]
      exact norm_pos_iff.mpr hnzero
    obtain ⟨r,η,hr,hT, hη,hpaths⟩ := continuous_family_parallel_paths_uniform_gap
      (E := E) (by simpa [E] using hdim) (range D.label) univ
      D.open_label.isOpen_range isOpen_univ (convex_univ : Convex ℝ (univ : Set E))
      S hS z₀ hz₀ (θ.symm s₀) (θ.symm s₁) (mem_univ _) (mem_univ _) hgap₀
    let T := Metric.closedBall z₀ r
    have hTc : IsCompact T := isCompact_closedBall _ _
    have hTpos : volume T ≠ 0 := (Metric.measure_closedBall_pos volume z₀ hr).ne'
    let : Nonempty (FoliationCoordinateDisk 2) := ⟨w₀⟩
    let δ := D.open_label.toOpenPartialHomeomorph D.label
    have hδtarget : δ.target = range D.label := by simp [δ]
    let Φ : ℂ × E → M := fun p ↦ ((P.foliations.box b).chart (θ p.2,δ.symm p.1)).val
    have hΦcont : ContinuousOn Φ (range D.label ×ˢ univ) := by
      apply continuous_subtype_val.comp_continuousOn
      apply (P.foliations.box b).chart.continuous.comp_continuousOn
      exact ((θ.continuous.comp continuous_snd).continuousOn).prodMk
        (δ.symm.continuousOn.comp continuous_fst.continuousOn
          (fun _ hp ↦ by change _ ∈ δ.target; rw [hδtarget]; exact hp.1))
    have hΦbox (z : ℂ) (v : E) : Φ (z,v) ∈ (P.foliations.box b).image :=
      ((P.foliations.box b).chart (θ v,δ.symm z)).property
    have hΦproj (z : ℂ) (hz : z ∈ range D.label) (v : E) : D.projection (Φ (z,v)) = z := by
      rw [show Φ (z,v) = ((P.foliations.box b).chart (θ v,δ.symm z)).val from rfl,D.projection_box]
      exact D.open_label.toOpenPartialHomeomorph_right_inv D.label hz
    have hΦslice (z : ℂ) : Continuous (fun v : E ↦ Φ (z,v)) :=
      continuous_subtype_val.comp ((P.foliations.box b).chart.continuous.comp
        (θ.continuous.prodMk (show Continuous (fun _ : E ↦ δ.symm z) from continuous_const)))
    have hΦinj (z : ℂ) : Function.Injective (fun v : E ↦ Φ (z,v)) := by
      intro v w he
      exact θ.injective (congrArg Prod.fst ((P.foliations.box b).chart.injective (Subtype.ext he)))
    let : MetricSpace M := m.replaceTopology hmTop.symm
    apply Analysis.Complex.finite_integral_budget_excludes_packing volume T hTc.measurableSet hTpos
      (ENNReal.ofReal η) budget (ENNReal.ofReal_ne_zero_iff.mpr hη) hbudget
    intro L
    obtain ⟨ends₀,ends₁,γs,hγin,hγdisj,hγgap⟩ := hpaths L
    let Kstable : Set E := ⋃ j : Fin L, range (γs j)
    have hKstable : IsCompact Kstable := isCompact_iUnion (fun j ↦ isCompact_range (γs j).continuous)
    let K₀ := Φ '' (T ×ˢ Kstable)
    have hK₀ : IsCompact K₀ := (hTc.prod hKstable).image_of_continuousOn
      (hΦcont.mono (fun _ hp ↦ ⟨hT hp.1,mem_univ _⟩))
    have hKbox : K₀ ⊆ (P.foliations.box b).image := by
      rintro _ ⟨p,hp,rfl⟩
      exact hΦbox p.1 p.2
    obtain ⟨K₁,hK₁,hinside,houter⟩ := exists_compact_between hK₀
      (P.foliations.box b).isOpen_image hKbox
    let paths (z : ℂ) (j : Fin L) := (fun v : E ↦ Φ (z,v)) '' range (γs j)
    have hseparate (j k : Fin L) : ∀ᶠ n : ℕ in atTop,
        ∀ z ∈ T, ∀ i : Fin N, ∀ t : (C i).transversal, t ∈ (C i).transverseCore →
          (paths z j ∩ range (fun v ↦ ((f : M → M)^[n]) ((C i).closedEvaluation (t,v)))).Nonempty →
          (paths z k ∩ range (fun v ↦ ((f : M → M)^[n]) ((C i).closedEvaluation (t,v)))).Nonempty → j = k := by
      by_cases hjk : j = k
      · exact Filter.Eventually.of_forall (fun _ _ _ _ _ _ _ _ ↦ hjk)
      obtain ⟨ε,hε,hsep⟩ := compact_fiberwise_uniform_separation T univ univ hTc
        isCompact_univ isCompact_univ
        (fun p : ℂ × unitInterval ↦ Φ (p.1,γs j p.2))
        (fun p : ℂ × unitInterval ↦ Φ (p.1,γs k p.2))
        (hΦcont.comp (continuous_fst.prodMk ((γs j).continuous.comp continuous_snd)).continuousOn
          (fun p hp ↦ ⟨hT hp.1,mem_univ _⟩))
        (hΦcont.comp (continuous_fst.prodMk ((γs k).continuous.comp continuous_snd)).continuousOn
          (fun p hp ↦ ⟨hT hp.1,mem_univ _⟩)) (by
          intro z hz v hv w hw he
          exact (Set.disjoint_left.mp (hγdisj hjk)) (mem_range_self v)
            (hΦinj z he ▸ mem_range_self w))
      have hs := Filter.eventually_all.mpr (fun i : Fin N ↦
        (C i).uniform_shrinking m hmLength (ε/2) (half_pos hε))
      filter_upwards [hs] with n hn
      intro z hz i t ht hj hk
      obtain ⟨p,⟨v,⟨a,ha⟩,hvp⟩,⟨v',hv'p⟩⟩ := hj
      obtain ⟨q,⟨w,⟨c,hc⟩,hwq⟩,⟨w',hw'q⟩⟩ := hk
      have hpdist : dist p (((f : M → M)^[n]) ((C i).anchor t).val) < ε/2 := by
        rw [← hv'p]
        exact hn i (⟨v'.val,Metric.closedBall_subset_ball (C i).radius_lt v'.property⟩,t)
          ⟨mem_closedBall_zero_iff.mp v'.property,ht⟩
      have hqdist : dist q (((f : M → M)^[n]) ((C i).anchor t).val) < ε/2 := by
        rw [← hw'q]
        exact hn i (⟨w'.val,Metric.closedBall_subset_ball (C i).radius_lt w'.property⟩,t)
          ⟨mem_closedBall_zero_iff.mp w'.property,ht⟩
      have hdist : dist p q < ε := by
        have hh := dist_triangle p (((f : M → M)^[n]) ((C i).anchor t).val) q
        rw [dist_comm (((f : M → M)^[n]) ((C i).anchor t).val) q] at hh
        linarith
      have hfar := hsep z hz a (mem_univ _) c (mem_univ _)
      change ε < dist (Φ (z,γs j a)) (Φ (z,γs k c)) at hfar
      rw [ha,hc] at hfar
      change Φ (z,v) = p at hvp
      change Φ (z,w) = q at hwq
      rw [hvp,hwq] at hfar
      exact (not_lt_of_ge hdist.le hfar).elim
    have hsepall := Filter.eventually_all.mpr (fun j ↦ Filter.eventually_all.mpr (hseparate j))
    obtain ⟨n,hncover,hnwhole,hnsep⟩ := ((hrootcover b s₀ wr D K₀ K₁ hK₀ hK₁ hinside houter).and
      ((hwhole b K₁ hK₁ houter).and hsepall)).exists
    obtain ⟨B,hB,hBbudget,hBsum⟩ := htotal_density b s₀ wr D n K₁ hK₁ houter
    refine ⟨B,(MeasureTheory.lintegral_mono' Measure.restrict_le_self (le_refl B)).trans hBbudget,?_⟩
    intro z hz
    let roots (i : Fin N) := ((hncover z).1 i).toFinset
    have hroots (i : Fin N) (t : (C i).transversal) : t ∈ roots i ↔
        t ∈ (C i).transverseCore ∧ ((f : M → M)^[n]) ((C i).anchor t).val ∈ K₁ ∧
          D.projection (((f : M → M)^[n]) ((C i).anchor t).val) = z :=
      Set.Finite.mem_toFinset _
    rw [hBsum z roots hroots]
    apply hpacking b s₀ wr D n K₀ K₁ z roots hroots
      (fun i t ht ↦ (hncover z).2.1 i t ((hroots i t).mp ht).1 ((hroots i t).mp ht).2.1)
      (fun p hp hpz ↦ by
        obtain ⟨i,t,ht,hpt⟩ := (hncover z).2.2 p hp hpz
        exact ⟨i,t,(hroots i t).mpr ht,hpt⟩)
      (fun i t ht ↦ hnwhole i t ((hroots i t).mp ht).1 ((hroots i t).mp ht).2.1)
      L (paths z)
      (fun j ↦ (isPreconnected_range (γs j).continuous).image _ (hΦslice z).continuousOn)
      (fun j p hp ↦ by
        obtain ⟨v,hv,rfl⟩ := hp
        exact ⟨⟨(z,v),⟨hz,mem_iUnion.mpr ⟨j,hv⟩⟩,rfl⟩,hΦproj z (hT hz) v⟩)
      (fun i t ht j k ↦ hnsep j k z hz i t ((hroots i t).mp ht).1)
      (fun j ↦ Φ (z,ends₀ j)) (fun j ↦ Φ (z,ends₁ j))
      (fun j ↦ ⟨ends₀ j,⟨0,(γs j).source⟩,rfl⟩)
      (fun j ↦ ⟨ends₁ j,⟨1,(γs j).target⟩,rfl⟩) η
    intro j
    simpa only [dite_eq_left (hΦbox z (ends₀ j)),dite_eq_left (hΦbox z (ends₁ j)),
      Φ,Subtype.coe_eta,(P.foliations.box b).chart.symm_apply_apply] using hγgap z hz j
  have hsingle (x₁ y₁ : M) (k : LocalPlaqueTransport P.foliations x₁ y₁)
      (p : P.foliations.ULeaf x₁) (hp : p ∈ k.map.source)
      (c₁ : OpenPartialHomeomorph (P.foliations.ULeaf x₁) ℂ)
      (e₁ : OpenPartialHomeomorph (P.foliations.ULeaf y₁) ℂ)
      (hc₁ : c₁ ∈ (A.atPoint P.foliations P.complexLeaves x₁).maximalAtlas _)
      (he₁ : e₁ ∈ (A.atPoint P.foliations P.complexLeaves y₁).maximalAtlas _)
      (hpc : p ∈ c₁.source) (hpe : k.map p ∈ e₁.source) :
      schwarzianQuadraticAt c₁ k.map e₁ p = 0 := by
    rcases k with ⟨⟨k,hmark,himage⟩,b,s₀,s₁,wr,hfirst,hsecond,hsource,hmap⟩
    subst x₁
    subst y₁
    let k₀ : LocalPlaqueTransport P.foliations
        ((P.foliations.box b).chart (s₀,wr)).val
        ((P.foliations.box b).chart (s₁,wr)).val :=
      ⟨⟨k,hmark,himage⟩,b,s₀,s₁,wr,rfl,rfl,hsource,hmap⟩
    obtain ⟨D⟩ := hreceiving b s₀ wr
    have hpD : p ∈ D.coordinate.source := by rw [D.source_eq]; trivial
    have hpk : p ∈ (D.transport s₁).map.source := by
      rw [(D.transport_meta s₁).2.2.2.2]
      exact hsource p hp
    have heq : k =ᶠ[𝓝 p] (D.transport s₁).map := by
      filter_upwards [k.open_source.mem_nhds hp,
        (D.transport s₁).map.open_source.mem_nhds hpk] with v hv hvD
      obtain ⟨w,hw⟩ := hsource v hv
      apply Subtype.ext
      rw [hmap v w hv hw]
      have hh := ((D.transport s₁).coordinate_map v w hvD (by
        rw [(D.transport_meta s₁).1,(D.transport_meta s₁).2.1]
        exact hw)).symm
      rw [(D.transport_meta s₁).1,(D.transport_meta s₁).2.2.1] at hh
      exact hh
    have hpeD : (D.transport s₁).map p ∈ e₁.source := heq.eq_of_nhds ▸ hpe
    have hpdom : D.coordinate p ∈ D.coordinate.target ∩ D.coordinate.symm ⁻¹'
        {v | ∃ w : FoliationCoordinateDisk 2,
          ((P.foliations.box b).chart (s₀,w)).val = v.val} := by
      refine ⟨D.coordinate.map_source hpD,?_⟩
      simpa only [Set.mem_preimage,Set.mem_ofPred_eq,D.coordinate.left_inv hpD] using hsource p hp
    have hz := hlocal b s₀ wr D (D.coordinate p)
      (D.domain_eq_range_label ▸ hpdom) s₁
    have hr := D.represents (D.coordinate p,s₁) ⟨hpdom,mem_univ _⟩ e₁ he₁
      (by simpa only [D.coordinate.left_inv hpD] using hpeD)
    have hscalar : schwarzian (affineLocalMapExpression D.coordinate k e₁)
        (D.coordinate p) = 0 := by
      have ht : Tendsto D.coordinate.symm (𝓝 (D.coordinate p)) (𝓝 p) := by
        simpa only [D.coordinate.left_inv hpD] using
          (D.coordinate.symm.continuousAt (D.coordinate.map_source hpD)).tendsto
      have he : affineLocalMapExpression D.coordinate k e₁ =ᶠ[𝓝 (D.coordinate p)]
          affineLocalMapExpression D.coordinate (D.transport s₁).map e₁ :=
        (ht.eventually heq).mono (fun _ hh ↦ congrArg e₁ hh)
      unfold schwarzian
      rw [he.deriv_eq,he.deriv.deriv_eq,he.deriv.deriv.deriv_eq]
      exact hr.symm.trans hz
    rw [schwarzian_quadratic_coordinate_independent
      (A.atPoint P.foliations P.complexLeaves _) (A.atPoint P.foliations P.complexLeaves _)
      k (intrinsicPresentation_plaque_holomorphic f a hRank P _ _ k₀)
      c₁ D.coordinate e₁ e₁ hc₁ D.coordinate_mem he₁ he₁ p hpc hpD hp hpe hpe]
    simp only [schwarzianQuadraticAt,hscalar,zero_smul]
  have hchain (t₀ t₁ : unitInterval)
      (k : OpenPartialHomeomorph (P.foliations.ULeaf (γ t₀).val)
        (P.foliations.ULeaf (γ t₁).val)) (hk : PlaqueChainAlong P.foliations γ t₀ t₁ k) :
      ∀ (p : P.foliations.ULeaf (γ t₀).val), p ∈ k.source →
      ∀ (c₁ : OpenPartialHomeomorph (P.foliations.ULeaf (γ t₀).val) ℂ)
        (e₁ : OpenPartialHomeomorph (P.foliations.ULeaf (γ t₁).val) ℂ),
      c₁ ∈ (A.atPoint P.foliations P.complexLeaves (γ t₀).val).maximalAtlas _ →
      e₁ ∈ (A.atPoint P.foliations P.complexLeaves (γ t₁).val).maximalAtlas _ →
      p ∈ c₁.source → k p ∈ e₁.source → schwarzianQuadraticAt c₁ k e₁ p = 0 := by
    induction hk with
    | single t₀ t₁ hle k hsegment => exact hsingle _ _ k
    | @compose t₀ tm t₁ k k' hle hle' left right ih ih' =>
      intro p hp c₁ e₁ hc₁ he₁ hpc hpe
      obtain ⟨cm,hcm,hpcm⟩ := affine_chart_at_g12
        (A.atPoint P.foliations P.complexLeaves (γ tm).val) (k p)
      have khol := intrinsic_holonomy_chain_holomorphic P.foliations P.complexLeaves
        (intrinsicPresentation_plaque_holomorphic f a hRank P) q x y γ t₀ tm k left
      have k'hol := intrinsic_holonomy_chain_holomorphic P.foliations P.complexLeaves
        (intrinsicPresentation_plaque_holomorphic f a hRank P) q x y γ tm t₁ k' right
      have hs := (affine_local_map_schwarzian_calculus
        (A.atPoint P.foliations P.complexLeaves (γ t₀).val)
        (A.atPoint P.foliations P.complexLeaves (γ tm).val)
        (A.atPoint P.foliations P.complexLeaves (γ t₁).val)
        k khol c₁ cm hc₁ hcm p hpc hp.1 hpcm).2.2.2.2
        k' e₁ k'hol he₁ hp.2 hpe
      ext v
      rw [hs.2 v, ih p hp.1 c₁ cm hc₁ hcm hpc hpcm,
        ih' (k p) hp.2 cm e₁ hcm he₁ hpcm hpe]
      simp
  have hΩ := (affine_local_map_schwarzian_calculus
    (A.atPoint P.foliations P.complexLeaves (γ 0).val)
    (A.atPoint P.foliations P.complexLeaves (γ 1).val)
    (A.atPoint P.foliations P.complexLeaves (γ 1).val)
    H.map hhol c e hc he (P.foliations.uPoint (γ 0).val) hxc H.source_point
    (by simpa only [H.map_point] using hye)).1
  have hcx : c (P.foliations.uPoint (γ 0).val) ∈ affineLocalMapDomain c H.map e := by
    refine ⟨⟨c.map_source hxc,?_⟩,?_⟩ <;>
      simp only [Set.mem_preimage,c.left_inv hxc,H.map_point]
    · exact H.source_point
    · exact hye
  filter_upwards [hΩ.mem_nhds hcx] with z hz
  let p := c.symm z
  have hpc : p ∈ c.source := c.map_target hz.1.1
  have hzero := hchain 0 1 H.map H.chain p hz.1.2 c e hc he hpc hz.2
  have hdiff : c.MDifferentiable (complexModel 1) 𝓘(ℂ) :=
    ⟨hc.1.1.mdifferentiableOn (by simp),hc.1.2.mdifferentiableOn (by simp)⟩
  obtain ⟨v,hv⟩ := (hdiff.mfderiv hpc).surjective (1 : ℂ)
  have hform : schwarzianQuadraticAt c H.map e p =
      schwarzian (affineLocalMapExpression c H.map e) (c p) •
        ((QuadraticMap.sq (R := ℂ) (A := ℂ)).comp
          (mvfderiv (complexModel 1) c p).toLinearMap) := by
    unfold schwarzianQuadraticAt
    rfl
  have hzv := congrArg (fun Q : QuadraticForm ℂ (TangentSpace (complexModel 1) p) ↦ Q v) hzero
  rw [hform] at hzv
  simp only [smul_apply, QuadraticMap.comp_apply,
    QuadraticMap.sq_apply] at hzv
  change schwarzian (affineLocalMapExpression c H.map e) (c p) *
      ((mvfderiv (complexModel 1) c p) v * (mvfderiv (complexModel 1) c p) v) = 0 at hzv
  have hvd : (mvfderiv (complexModel 1) c p) v = 1 := by
    change (NormedSpace.fromTangentSpace (c p))
      ((mfderiv (complexModel 1) 𝓘(ℂ) c p) v) = 1
    have hhv := congrArg (NormedSpace.fromTangentSpace (c p)) hv
    have hraw : (mfderiv (complexModel 1) 𝓘(ℂ) c p) v =
        (hdiff.mfderiv hpc) v := by rfl
    rw [hraw]
    exact hhv.trans (by rfl)
  rw [hvd] at hzv
  have hcpz : c p = z := by simp [p, c.right_inv hz.1.1]
  rw [hcpz] at hzv
  simpa only [one_pow, mul_one, one_mul] using hzv


end HolomorphicAnosov.Ghys

