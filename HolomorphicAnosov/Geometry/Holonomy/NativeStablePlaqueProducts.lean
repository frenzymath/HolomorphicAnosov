import HolomorphicAnosov.Analysis.Complex.FiniteInverseBranchBudget
import HolomorphicAnosov.Geometry.Holonomy.ImmersedLeafLiftLocalDiffeomorph
import HolomorphicAnosov.Geometry.Holonomy.ConnectedRangeInBox
import HolomorphicAnosov.Dynamics.Anosov.StablePathIterateLength
import HolomorphicAnosov.Geometry.NativePlaqueFamilyCoordinateJet
import HolomorphicAnosov.Dynamics.Anosov.GlobalLaminationTensorMetric
import HolomorphicAnosov.Geometry.StableLeafTransportG9
import HolomorphicAnosov.Topology.CompactLocalInjectiveBranches
import HolomorphicAnosov.Paper.Ghys.SchwarzianLeafCocycleNativeProvider
import HolomorphicAnosov.Analysis.Complex.AffineHolonomyFamilySchwarzian

/-! Native stable plaque products and compact source cores. (HPS) (Ghys, Proposition 4.1) -/

noncomputable section
open Set Filter TopologicalSpace _root_.Topology Manifold
open scoped ContDiff Manifold Bundle ENNReal _root_.Topology
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real

/-- Restrict only the common open radius of a native family.  All original parametrizations, frames, coordinate derivatives, and receiving chart are retained. -/
def NativePlaqueFamily.restrictRadius
    {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ,E) x)} {center : M}
    (F : NativePlaqueFamily 𝓘(ℝ,E) (V := V) D center)
    (R : ℝ) (hR : 0 < R) (hRF : R ≤ F.radius) :
    NativePlaqueFamily 𝓘(ℝ,E) (V := V) D center where
  centerDomain := F.centerDomain
  centerDomain_open := F.centerDomain_open
  center_mem := F.center_mem
  radius := R
  radius_pos := hR
  plaque p := {
    finiteDimensional := (F.plaque p).finiteDimensional
    domain := Metric.ball 0 R
    domain_open := Metric.isOpen_ball
    zero_mem := Metric.mem_ball_self hR
    param := (F.plaque p).param
    centered := (F.plaque p).centered
    smooth := (F.plaque p).smooth.mono (by rw [F.domain_eq]; exact Metric.ball_subset_ball hRF)
    embedded := (F.plaque p).embedded.comp
      (IsEmbedding.inclusion (by rw [F.domain_eq]; exact Metric.ball_subset_ball hRF))
    immersed := fun u hu ↦ (F.plaque p).immersed u (by
      rw [F.domain_eq]; exact Metric.ball_subset_ball hRF hu)
    tangent := fun u hu ↦ (F.plaque p).tangent u (by
      rw [F.domain_eq]; exact Metric.ball_subset_ball hRF hu) }
  domain_eq _ := rfl
  frame := F.frame
  frame_continuous := F.frame_continuous
  receivingAnchor := F.receivingAnchor
  receiving_domain p u hu := F.receiving_domain p u (Metric.ball_subset_ball hRF hu)
  jointly_continuous := F.jointly_continuous.comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk
      (fun p ↦ Metric.ball_subset_ball hRF p.2.property)))
  coordinate_smooth p := (F.coordinate_smooth p).mono (Metric.ball_subset_ball hRF)
  jointly_continuous_derivative := F.jointly_continuous_derivative.comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk
      (fun p ↦ Metric.ball_subset_ball hRF p.2.property)))
  compact_C1 K hK hKR := F.compact_C1 K hK (hKR.trans (Metric.ball_subset_ball hRF))

/-- Actual native stable plaques anchored on a receiving unstable transversal form an ambient open product whenever they stay inside that receiving box.  Original contraction supplies membership in the supplied P stable classes; the countable-plaque criterion supplies intrinsic continuity, tangencies give open intrinsic lifts, and compact boundary persistence gives product openness. (HPS) -/
theorem anosov_native_stable_family_product_open
    {d r : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : Ghys.AnosovIntrinsicFoliationPresentation f a) {center : M}
    (F : NativePlaqueFamily (realModel d) (V := Fin r → ℝ)
      a.splitting.stable.toDistribution center) :
    letI := P.realCharts
    ∀ (b : P.foliations.boxIndex) (s₀ : FoliationCoordinateDisk (2*d-2))
      (T : Opens (FoliationCoordinateDisk 2))
      (hcenter : ∀ t : T, ((P.foliations.box b).chart (s₀,t.val)).val ∈ F.centerDomain),
      let U : Opens (Fin r → ℝ) := ⟨Metric.ball 0 F.radius,Metric.isOpen_ball⟩
      let J : U × T → M := fun p ↦
        (F.plaque ⟨((P.foliations.box b).chart (s₀,p.2.val)).val,hcenter p.2⟩).param p.1.val
      (∀ p, J p ∈ (P.foliations.box b).image) → IsOpenEmbedding J := by
  let := P.realCharts
  intro b s₀ T hcenter
  dsimp only
  let U : Opens (Fin r → ℝ) := ⟨Metric.ball 0 F.radius,Metric.isOpen_ball⟩
  let anchor : T → F.centerDomain := fun t ↦
    ⟨((P.foliations.box b).chart (s₀,t.val)).val,hcenter t⟩
  let J : U × T → M := fun p ↦ (F.plaque (anchor p.2)).param p.1.val
  intro hbox
  have hanchor : Continuous anchor :=
    (continuous_subtype_val.comp ((P.foliations.box b).chart.continuous.comp
      (continuous_const.prodMk continuous_subtype_val))).subtype_mk _
  have hJ : Continuous J := F.jointly_continuous.comp
    ((hanchor.comp continuous_snd).prodMk continuous_fst)
  have hleaf (t : T) (v : U) :
      Quotient.mk P.foliations.stablePartition (J (v,t)) = P.foliations.stableLabel b t.val := by
    have h := anosov_native_plaque_in_presentation_stable_class f a P F (anchor t) v.val v.property
    exact (Quotient.sound (P.foliations.stablePartition.symm h)).trans
      (P.foliations.stable_label b s₀ t.val)
  have hlift (t : T) :
      letI := P.foliations.stableTopology (P.foliations.stableLabel b t.val)
      ∃ g : U → IntrinsicFoliationLeaf P.foliations.stablePartition (P.foliations.stableLabel b t.val),
        IsOpenEmbedding g ∧ ∀ v, (g v).val = J (v,t) := by
    let := P.foliations.stableTopology (P.foliations.stableLabel b t.val)
    let := P.foliations.stableCharts (P.foliations.stableLabel b t.val)
    have hh := native_stable_plaque_open_lift f a P (F.plaque (anchor t))
      (P.foliations.stableLabel b t.val) (fun v hv ↦ hleaf t ⟨v,by rwa [F.domain_eq] at hv⟩)
    obtain ⟨g,hg,ho,_⟩ := hh
    let e : U ≃ₜ (⟨(F.plaque (anchor t)).domain,(F.plaque (anchor t)).domain_open⟩ :
        Opens (Fin r → ℝ)) := Homeomorph.setCongr (F.domain_eq (anchor t)).symm
    exact ⟨g ∘ e,ho.comp e.isOpenEmbedding,fun v ↦ hg (e v)⟩
  have hcoord (p : U × T) :
      ((P.foliations.box b).chart.symm ⟨J p,hbox p⟩).2 = p.2.val := by
    let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp
      (convex_ball (0 : Fin r → ℝ) F.radius).isPreconnected
    let q := P.foliations.stableLabel b p.2.val
    let := P.foliations.stableTopology q
    let := P.foliations.stableCharts q
    let := P.stableSmooth q
    let := (P.stableNative q).countable
    let z : U := ⟨0,Metric.mem_ball_self F.radius_pos⟩
    have hc := stable_connected_range_in_box P.foliations b q
      (fun v : U ↦ J (v,p.2)) (hJ.comp (continuous_id.prodMk continuous_const))
      (fun v ↦ hbox (v,p.2)) (hleaf p.2) inferInstance p.1 z
    have hzero : J (z,p.2) = ((P.foliations.box b).chart (s₀,p.2.val)).val :=
      (F.plaque (anchor p.2)).centered
    have he : (⟨J (z,p.2),hbox (z,p.2)⟩ : (P.foliations.box b).image) =
        (P.foliations.box b).chart (s₀,p.2.val) := Subtype.ext hzero
    exact hc.trans (congrArg Prod.snd ((congrArg (P.foliations.box b).chart.symm he).trans
      ((P.foliations.box b).chart.symm_apply_apply _)))
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  exact stable_plaque_product_open_embedding P.foliations b T J hJ hbox hcoord hlift

/-- Every marked native stable family admits a smaller actual source product inside a supplied receiving box through its center.  The image is open by the preceding theorem and contains the marked center at zero parameter. -/
theorem anosov_native_stable_family_local_product
    {d r : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : Ghys.AnosovIntrinsicFoliationPresentation f a) {center : M}
    (F : NativePlaqueFamily (realModel d) (V := Fin r → ℝ)
      a.splitting.stable.toDistribution center) :
    letI := P.realCharts
    ∀ (b : P.foliations.boxIndex) (s₀ : FoliationCoordinateDisk (2*d-2))
      (t₀ : FoliationCoordinateDisk 2),
      ((P.foliations.box b).chart (s₀,t₀)).val = center →
      ∃ R : ℝ, 0 < R ∧ R < F.radius ∧
      ∃ T : Opens (FoliationCoordinateDisk 2), t₀ ∈ T ∧
      ∃ hcenter : ∀ t : T,
        ((P.foliations.box b).chart (s₀,t.val)).val ∈ F.centerDomain,
      let U : Opens (Fin r → ℝ) := ⟨Metric.ball 0 R,Metric.isOpen_ball⟩
      let J : U × T → M := fun p ↦
        (F.plaque ⟨((P.foliations.box b).chart (s₀,p.2.val)).val,hcenter p.2⟩).param p.1.val
      (∀ p, J p ∈ (P.foliations.box b).image) ∧ IsOpenEmbedding J := by
  let := P.realCharts
  intro b s₀ t₀ hmark
  let p₀ : F.centerDomain := ⟨center,F.center_mem⟩
  have hcm : center ∈ (P.foliations.box b).image :=
    hmark ▸ ((P.foliations.box b).chart (s₀,t₀)).property
  have hn : (fun z : F.centerDomain × (Fin r → ℝ) ↦ (F.plaque z.1).param z.2) ⁻¹'
      (P.foliations.box b).image ∈ 𝓝 (p₀,0) :=
    F.continuousAt_centered_param ((P.foliations.box b).isOpen_image.mem_nhds
      (by
        change (F.plaque p₀).param 0 ∈ _
        rw [(F.plaque p₀).centered]
        exact hcm))
  obtain ⟨N,W,hN,hpN,hW,h0W,hNW⟩ := mem_nhds_prod_iff'.mp hn
  obtain ⟨η,hη,hηW⟩ := Metric.isOpen_iff.mp hW 0 h0W
  let R := min (η/2) (F.radius/2)
  have hR : 0 < R := lt_min (half_pos hη) (half_pos F.radius_pos)
  have hRη : R < η := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hη)
  have hRF : R < F.radius := lt_of_le_of_lt (min_le_right _ _) (half_lt_self F.radius_pos)
  let β : FoliationCoordinateDisk 2 → M := fun t ↦ ((P.foliations.box b).chart (s₀,t)).val
  have hβ : Continuous β := continuous_subtype_val.comp
    ((P.foliations.box b).chart.continuous.comp (continuous_const.prodMk continuous_id))
  let T : Opens (FoliationCoordinateDisk 2) :=
    ⟨β ⁻¹' (Subtype.val '' N),
      (F.centerDomain_open.isOpenMap_subtype_val N hN).preimage hβ⟩
  have ht₀ : t₀ ∈ T := ⟨p₀,hpN,hmark.symm⟩
  have hcenter (t : T) : β t.val ∈ F.centerDomain := by
    obtain ⟨q,_,hq⟩ := t.property
    exact hq ▸ q.property
  let U : Opens (Fin r → ℝ) := ⟨Metric.ball 0 R,Metric.isOpen_ball⟩
  have hbox (p : U × T) :
      (F.plaque ⟨β p.2.val,hcenter p.2⟩).param p.1.val ∈ (P.foliations.box b).image := by
    obtain ⟨q,hq,hqval⟩ := p.2.property
    have he : (⟨β p.2.val,hcenter p.2⟩ : F.centerDomain) = q := Subtype.ext hqval.symm
    rw [he]
    have hv : p.1.val ∈ W := hηW (Metric.ball_subset_ball hRη.le p.1.property)
    exact @hNW (q,p.1.val) ⟨hq,hv⟩
  refine ⟨R,hR,hRF,T,ht₀,hcenter,hbox,?_⟩
  exact anosov_native_stable_family_product_open f a P (F.restrictRadius R hR hRF.le)
    b s₀ T hcenter hbox

/-- Extract the actual finite-C¹ stable family at every original center from HPS's tensor-metric lamination theorem, using the original all-iterate bounds. -/
theorem anosov_native_stable_family_exists
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f) (x : M) :
    ∃ r : ℕ, Nonempty (NativePlaqueFamily (realModel d) (V := Fin r → ℝ)
      a.splitting.stable.toDistribution x) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨C,rate,hC,hr,hr1,hs,hu⟩ := fixed_block_uniform_anosov_estimates f a
  have hi (x : M) (v w : TangentSpace (realModel d) x) :
      inner ℝ v w = a.metric.inner x v w := rfl
  have hb : Nonempty (TensorAnosovBounds f.toReal a.splitting a.metric) := by
    refine ⟨⟨C,rate,hC,hr,hr1,?_,?_⟩⟩
    · intro n x v hv
      have he : (realIterate (realModel d) f.toReal n : M → M) = (f : M → M)^[n] := rfl
      rw [he]
      simpa only [norm_eq_sqrt_real_inner,hi] using hs n x v hv
    · intro n x v hv
      have he : (realIterate (realModel d) f.toReal.symm n : M → M) =
          (f.symm : M → M)^[n] := rfl
      rw [he]
      simpa only [norm_eq_sqrt_real_inner,hi] using hu n x v hv
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨hS,_⟩ := HPS.anosov_global_lamination_tensor_metric f.toReal a.splitting a.metric hb
  obtain ⟨ι,L,r,top,charts,smooth,S,boxes,invariant,families,coherent,extra⟩ := hS
  exact ⟨families.dimension x,⟨(families.family x).family⟩⟩

section SourceCore
variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  (f : Biholomorph d d M M) (a : AnosovDatum f)
  (P : Ghys.AnosovIntrinsicFoliationPresentation f a)

/-- A compact source core in an actual native stable product.  The stable parameter radius is strictly inside the native domain; the transverse core is compact in its open source transversal. -/
structure NativeStableSourceCore where
  center : M
  dimension : ℕ
  family : NativePlaqueFamily (realModel d) (V := Fin dimension → ℝ)
    a.splitting.stable.toDistribution center
  box : letI := P.realCharts; P.foliations.boxIndex
  stableCoordinate : FoliationCoordinateDisk (2*d-2)
  transversal : Opens (FoliationCoordinateDisk 2)
  anchor_mem : letI := P.realCharts; ∀ t : transversal,
    ((P.foliations.box box).chart (stableCoordinate,t.val)).val ∈ family.centerDomain
  in_box : letI := P.realCharts; ∀ (v : Metric.ball (0 : Fin dimension → ℝ) family.radius) (t : transversal),
    (family.plaque ⟨((P.foliations.box box).chart (stableCoordinate,t.val)).val,
      anchor_mem t⟩).param v.val ∈ (P.foliations.box box).image
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt : radius < family.radius
  transverseCore : Set transversal
  compact_transverseCore : IsCompact transverseCore

namespace NativeStableSourceCore
variable {f a P} (C : NativeStableSourceCore f a P)

def parameterDomain : Opens (Fin C.dimension → ℝ) :=
  ⟨Metric.ball 0 C.family.radius,Metric.isOpen_ball⟩

def anchor (t : C.transversal) : C.family.centerDomain :=
  letI := P.realCharts
  ⟨((P.foliations.box C.box).chart (C.stableCoordinate,t.val)).val,C.anchor_mem t⟩

def evaluation (p : C.parameterDomain × C.transversal) : M :=
  (C.family.plaque (C.anchor p.2)).param p.1.val

def parameterCore : Set (C.parameterDomain × C.transversal) :=
  {v | ‖v.val‖ ≤ C.radius} ×ˢ C.transverseCore

def image : Set M := C.evaluation '' C.parameterCore

omit [CompactSpace M] in
theorem continuous_anchor : Continuous C.anchor := by
  let := P.realCharts
  exact (continuous_subtype_val.comp ((P.foliations.box C.box).chart.continuous.comp
    (continuous_const.prodMk continuous_subtype_val))).subtype_mk _

theorem open_evaluation : IsOpenEmbedding C.evaluation := by
  let := P.realCharts
  exact anosov_native_stable_family_product_open f a P C.family C.box C.stableCoordinate
    C.transversal C.anchor_mem (fun p ↦ C.in_box p.1 p.2)

omit [CompactSpace M] in
theorem compact_parameterCore : IsCompact C.parameterCore := by
  have hi : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius ⊆
      Metric.ball 0 C.family.radius := Metric.closedBall_subset_ball C.radius_lt
  have he : {v : C.parameterDomain | ‖v.val‖ ≤ C.radius} =
      (fun v : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius ↦
        (⟨v.val,hi v.property⟩ : C.parameterDomain)) '' univ := by
    ext v
    simp only [mem_ofPred_eq,mem_image,mem_univ,true_and]
    constructor
    · intro hv
      exact ⟨⟨v.val,by simpa using hv⟩,rfl⟩
    · rintro ⟨w,hw⟩
      have hval : w.val = v.val := congrArg Subtype.val hw
      simpa only [Metric.mem_closedBall,dist_zero_right,hval] using w.property
  change IsCompact ({v : C.parameterDomain | ‖v.val‖ ≤ C.radius} ×ˢ C.transverseCore)
  rw [he]
  exact ((isCompact_univ : IsCompact (univ : Set (Metric.closedBall
    (0 : Fin C.dimension → ℝ) C.radius))).image
    (continuous_subtype_val.subtype_mk _)).prod C.compact_transverseCore

theorem compact_image : IsCompact C.image :=
  C.compact_parameterCore.image C.open_evaluation.continuous

/-- The closed stable parameter ball is strictly inside the native domain. -/
def closedEvaluation (p : C.transversal × Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius) : M :=
  (C.family.plaque (C.anchor p.1)).param p.2.val

omit [CompactSpace M] in
theorem continuous_closedEvaluation : Continuous C.closedEvaluation :=
  C.family.jointly_continuous.comp
    ((C.continuous_anchor.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk
        (fun p ↦ Metric.closedBall_subset_ball C.radius_lt p.2.property)))

/-- An iterate of a whole native core plaque lying in one receiving box has constant receiving unstable coordinate.  The common stable class is justified by the original contraction and orbit-shift invariance before connectedness is used. -/
theorem iterate_receiving_coordinate_constant :
    letI := P.realCharts
    ∀ (n : ℕ) (b : P.foliations.boxIndex) (t : C.transversal)
      (hbox : ∀ v : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius,
        ((f : M → M)^[n]) (C.closedEvaluation (t,v)) ∈ (P.foliations.box b).image)
      (v w : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius),
      ((P.foliations.box b).chart.symm ⟨((f : M → M)^[n])
        (C.closedEvaluation (t,v)),hbox v⟩).2 =
      ((P.foliations.box b).chart.symm ⟨((f : M → M)^[n])
        (C.closedEvaluation (t,w)),hbox w⟩).2 := by
  let := P.realCharts
  intro n b t hbox v w
  let Y := Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius
  let q := Quotient.mk P.foliations.stablePartition (((f : M → M)^[n]) (C.anchor t).val)
  let := P.foliations.stableTopology q
  let := P.foliations.stableCharts q
  let := P.stableSmooth q
  let := (P.stableNative q).countable
  let : PreconnectedSpace Y := isPreconnected_iff_preconnectedSpace.mp
    (convex_closedBall (0 : Fin C.dimension → ℝ) C.radius).isPreconnected
  have hrel (v : Y) : P.foliations.stablePartition
      (((f : M → M)^[n]) (C.anchor t).val)
      (((f : M → M)^[n]) (C.closedEvaluation (t,v))) := by
    have h0 := anosov_native_plaque_in_presentation_stable_class f a P C.family
      (C.anchor t) v.val (Metric.closedBall_subset_ball C.radius_lt v.property)
    suffices hall : ∀ m : ℕ, P.foliations.stablePartition
        (((f : M → M)^[m]) (C.anchor t).val)
        (((f : M → M)^[m]) (C.closedEvaluation (t,v))) from hall n
    intro m
    induction m with
    | zero => exact h0
    | succ m ih =>
      simpa only [Function.iterate_succ_apply'] using
        (P.stablePartition_map_iff _ _).mpr ih
  exact stable_connected_range_in_box P.foliations b q
    (fun v : Y ↦ ((f : M → M)^[n]) (C.closedEvaluation (t,v)))
    ((f.continuous.iterate n).comp (C.continuous_closedEvaluation.comp
      (continuous_const.prodMk continuous_id))) hbox
    (fun v ↦ Quotient.sound (P.foliations.stablePartition.symm (hrel v))) inferInstance v w

omit [CompactSpace M] in
/-- The receiving transverse projection of an iterated anchor transversal is locally injective.  Compose its original unstable plaque embedding with the intrinsic unstable iterate, then use local constancy of the other coordinate. -/
theorem iterate_projection_locally_injective {Z : Type*} :
    letI := P.realCharts
    ∀ (n : ℕ) (b : P.foliations.boxIndex) (proj : M → Z) (label : FoliationCoordinateDisk 2 → Z),
      Function.Injective label →
      (∀ z (hz : z ∈ (P.foliations.box b).image),
        proj z = label ((P.foliations.box b).chart.symm ⟨z,hz⟩).2) →
      ∀ t : C.transversal,
        ((f : M → M)^[n]) (C.anchor t).val ∈ (P.foliations.box b).image →
        ∃ V, IsOpen V ∧ t ∈ V ∧
          V.InjOn (fun u ↦ proj (((f : M → M)^[n]) (C.anchor u).val)) := by
  let := P.realCharts
  intro n b proj label hinj hproj t ht
  let x := (C.anchor t).val
  let : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  have hlabel : P.foliations.unstableLabel C.box C.stableCoordinate =
      Quotient.mk P.foliations.unstablePartition x :=
    (P.foliations.unstable_label C.box C.stableCoordinate t.val).symm
  let j : FoliationCoordinateDisk 2 → P.foliations.ULeaf x := fun w ↦
    ⟨((P.foliations.box C.box).chart (C.stableCoordinate,w)).val,
      (P.foliations.unstable_label C.box C.stableCoordinate w).trans hlabel⟩
  have hj : IsOpenEmbedding j := unstable_plaque_open_at_class_g10 P.foliations
    C.box C.stableCoordinate _ hlabel
  obtain ⟨E,hE⟩ := Ghys.intrinsic_unstable_iterate_biholomorph_g17 f a P n x
  let g : C.transversal → P.foliations.ULeaf (((f : M → M)^[n]) x) :=
    E ∘ j ∘ Subtype.val
  have hval (u : C.transversal) : (g u).val = ((f : M → M)^[n]) (C.anchor u).val := hE _
  obtain ⟨V,hVo,htV,hinj⟩ := unstable_receiving_projection_locally_injective
    P.foliations b _ g (E.continuous.comp (hj.continuous.comp continuous_subtype_val))
    (E.injective.comp (hj.injective.comp Subtype.val_injective)) proj label hinj hproj t
    (by rw [hval]; exact ht)
  exact ⟨V,hVo,htV,by simpa only [hval] using hinj⟩

/-- The actual compact core retains the original uniform stable shrinking. -/
theorem uniform_shrinking (m : MetricSpace M) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    (∀ x y : M, riemannianEDist (realModel d) x y < ⊤ →
      ENNReal.ofReal (m.dist x y) = riemannianEDist (realModel d) x y) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ C.parameterCore,
        m.dist (((f : M → M)^[n]) (C.evaluation p))
          (((f : M → M)^[n]) (C.anchor p.2).val) < ε := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  intro hm ε hε
  have h := anosov_native_stable_plaque_uniform_shrinking f a m hm C.family
    (C.anchor '' C.transverseCore) (C.compact_transverseCore.image C.continuous_anchor)
    C.radius_pos C.radius_lt ε hε
  filter_upwards [h] with n hn p hp
  exact hn (C.anchor p.2) ⟨p.2,hp.2,rfl⟩ p.1.val (by simpa using hp.1)

/-- The original unstable anchor slice, with its literal ambient values, lifted to the leaf of any chosen anchor in the same box. -/
def unstableAnchor (w₀ : FoliationCoordinateDisk 2) :
    letI := P.realCharts
    C.transversal → P.foliations.ULeaf
      (((P.foliations.box C.box).chart (C.stableCoordinate,w₀)).val) := by
  letI := P.realCharts
  intro t
  exact ⟨(C.anchor t).val,
    (P.foliations.unstable_label C.box C.stableCoordinate t.val).trans
      (P.foliations.unstable_label C.box C.stableCoordinate w₀).symm⟩

omit [CompactSpace M] in
theorem open_unstableAnchor (w₀ : FoliationCoordinateDisk 2) :
    letI := P.realCharts
    IsOpenEmbedding (C.unstableAnchor w₀) := by
  let := P.realCharts
  exact (unstable_plaque_open_at_class_g10 P.foliations C.box C.stableCoordinate _
    (P.foliations.unstable_label C.box C.stableCoordinate w₀).symm).comp
      C.transversal.isOpen.isOpenEmbedding_subtypeVal

/-- Stable coordinate of the actual source plaque point in its containing box. -/
def stableParameter (p : C.parameterDomain × C.transversal) :
    FoliationCoordinateDisk (2*d-2) :=
  letI := P.realCharts
  ((P.foliations.box C.box).chart.symm ⟨C.evaluation p,C.in_box p.1 p.2⟩).1

theorem continuous_stableParameter : Continuous C.stableParameter := by
  let := P.realCharts
  exact continuous_fst.comp ((P.foliations.box C.box).chart.symm.continuous.comp
    (C.open_evaluation.continuous.subtype_mk _))

/-- Stable coordinate of the original closed native plaque in its containing box. -/
def closedStableParameter (t : C.transversal)
    (v : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius) :
    FoliationCoordinateDisk (2*d-2) :=
  C.stableParameter (⟨v.val,Metric.closedBall_subset_ball C.radius_lt v.property⟩,t)

theorem continuous_closedStableParameter (t : C.transversal) :
    Continuous (C.closedStableParameter t) :=
  C.continuous_stableParameter.comp
    ((continuous_subtype_val.subtype_mk _).prodMk continuous_const)

/-- The whole native plaque has exactly its original anchor's transverse coordinate.  This uses its actual common stable leaf, rather than assuming that an arbitrary connected subset of a box lies in one plaque. -/
theorem closed_source_coordinates :
    letI := P.realCharts
    ∀ (t : C.transversal) (v : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius),
      ((P.foliations.box C.box).chart (C.closedStableParameter t v,t.val)).val =
        C.closedEvaluation (t,v) := by
  let := P.realCharts
  intro t v
  let z : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius :=
    ⟨0,Metric.mem_closedBall_self C.radius_pos.le⟩
  have hin (w : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius) :
      C.closedEvaluation (t,w) ∈ (P.foliations.box C.box).image :=
    C.in_box ⟨w.val,Metric.closedBall_subset_ball C.radius_lt w.property⟩ t
  have hz : C.closedEvaluation (t,z) =
      ((P.foliations.box C.box).chart (C.stableCoordinate,t.val)).val :=
    (C.family.plaque (C.anchor t)).centered
  have hzero : (P.foliations.box C.box).chart.symm
      ⟨C.closedEvaluation (t,z),hin z⟩ = (C.stableCoordinate,t.val) := by
    apply (P.foliations.box C.box).chart.injective
    rw [(P.foliations.box C.box).chart.apply_symm_apply]
    exact Subtype.ext hz
  have hsnd := C.iterate_receiving_coordinate_constant 0 C.box t hin v z
  simp only [Function.iterate_zero,Function.id_def,hzero] at hsnd
  have hp : (C.closedStableParameter t v,t.val) =
      (P.foliations.box C.box).chart.symm ⟨C.closedEvaluation (t,v),hin v⟩ :=
    Prod.ext rfl hsnd.symm
  rw [hp]
  exact congrArg Subtype.val ((P.foliations.box C.box).chart.apply_symm_apply _)

/-- The actual closed native plaque supplies the compact connected source strip needed by dynamical holonomy naturality.  It retains the real connector, so no identification of arbitrary stable paths with the same endpoints occurs. -/
theorem closed_source_strip :
    letI := P.realCharts
    ∀ t : C.transversal,
      ∃ K : Set (FoliationCoordinateDisk (2*d-2)),
        IsCompact K ∧ IsPreconnected K ∧ C.stableCoordinate ∈ K ∧
        (∀ v : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius,
          C.closedStableParameter t v ∈ K) ∧
        ∀ s ∈ K, ∃ v : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius,
          ((P.foliations.box C.box).chart (s,t.val)).val = C.closedEvaluation (t,v) := by
  let := P.realCharts
  intro t
  let Y := Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius
  let : PreconnectedSpace Y := isPreconnected_iff_preconnectedSpace.mp
    (convex_closedBall (0 : Fin C.dimension → ℝ) C.radius).isPreconnected
  refine ⟨range (C.closedStableParameter t),isCompact_range (C.continuous_closedStableParameter t),
    isPreconnected_range (C.continuous_closedStableParameter t),?_,fun v ↦ mem_range_self v,?_⟩
  · let z : Y := ⟨0,Metric.mem_closedBall_self C.radius_pos.le⟩
    refine ⟨z,?_⟩
    have heq := C.closed_source_coordinates t z
    rw [show C.closedEvaluation (t,z) =
      ((P.foliations.box C.box).chart (C.stableCoordinate,t.val)).val from
        (C.family.plaque (C.anchor t)).centered] at heq
    exact congrArg Prod.fst ((P.foliations.box C.box).chart.injective (Subtype.ext heq))
  · rintro s ⟨v,rfl⟩
    exact ⟨v,C.closed_source_coordinates t v⟩

/-- The literal forward iterate conjugates the original native-core plaque holonomy to the direct receiving-box holonomy as a germ.  The compact connected strip is constructed from this core, and the entire image plaque is assumed inside the receiving box, exactly as supplied by the shrinking buffers. -/
theorem iterate_holonomy_germ :
    letI := P.realCharts
    ∀ (n : ℕ) (b : P.foliations.boxIndex) (t : C.transversal)
      (v : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius),
      (∀ w : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius,
        ((f : M → M)^[n]) (C.closedEvaluation (t,w)) ∈ (P.foliations.box b).image) →
      let x := (C.anchor t).val
      let y := C.closedEvaluation (t,v)
      ∀ (Ex : P.foliations.ULeaf x ≃ₜ P.foliations.ULeaf (((f : M → M)^[n]) x))
        (Ey : P.foliations.ULeaf y ≃ₜ P.foliations.ULeaf (((f : M → M)^[n]) y)),
      (∀ z, (Ex z).val = ((f : M → M)^[n]) z.val) →
      (∀ z, (Ey z).val = ((f : M → M)^[n]) z.val) →
      ∀ (e : LocalPlaqueTransport P.foliations x y),
      e.box = C.box → e.first = C.stableCoordinate →
      e.second = C.closedStableParameter t v → e.transverse = t.val →
      ∀ (e' : LocalPlaqueTransport P.foliations (((f : M → M)^[n]) x)
        (((f : M → M)^[n]) y)), e'.box = b →
      (Ey ∘ e.map) =ᶠ[𝓝 (P.foliations.uPoint x)] (e'.map ∘ Ex) := by
  let := P.realCharts
  intro n b t v hbox x y Ex Ey hEx hEy e heb hea hey hew e' he'b
  obtain ⟨K,hK,hKconn,ha,hv,hcover⟩ := C.closed_source_strip t
  apply image_plaque_germ_of_strip_g12 P.foliations ((f : M → M)^[n])
    (f.continuous.iterate n) ?_ Ex Ey hEx hEy e e' K hK hKconn
    (hea.symm ▸ ha) (hey.symm ▸ hv v)
  · intro s hs
    obtain ⟨w,hw⟩ := hcover s hs
    rw [heb,hew,he'b,hw]
    exact hbox w
  · intro q
    induction q using Quotient.inductionOn with
    | _ z =>
      obtain ⟨E,hE⟩ := Ghys.intrinsic_stable_iterate_homeomorph_g17 f a P n z
      exact ⟨Quotient.mk P.foliations.stablePartition (((f : M → M)^[n]) z),E,hE⟩

/-- The projected iterate is unchanged along a source-core transport as a germ in the original source leaf, with its original complete affine chart. -/
theorem iterate_projection_germ {Z : Type*} :
    letI := P.realCharts
    ∀ (n : ℕ) (b : P.foliations.boxIndex) (proj : M → Z)
      (label : FoliationCoordinateDisk 2 → Z),
      (∀ z (hz : z ∈ (P.foliations.box b).image),
        proj z = label ((P.foliations.box b).chart.symm ⟨z,hz⟩).2) →
      ∀ (t : C.transversal) (v : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius),
      (∀ w : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius,
        ((f : M → M)^[n]) (C.closedEvaluation (t,w)) ∈ (P.foliations.box b).image) →
      ∀ (w₀ : FoliationCoordinateDisk 2) (y : M)
        (e : LocalPlaqueTransport P.foliations
          (((P.foliations.box C.box).chart (C.stableCoordinate,w₀)).val) y),
      e.box = C.box → e.first = C.stableCoordinate →
      e.second = C.closedStableParameter t v →
      C.unstableAnchor w₀ t ∈ e.map.source →
      (fun z ↦ proj (((f : M → M)^[n]) (e.map z).val)) =ᶠ[𝓝 (C.unstableAnchor w₀ t)]
        (fun z ↦ proj (((f : M → M)^[n]) z.val)) := by
  let := P.realCharts
  intro n b proj label hproj t v hbox w₀ y e heb hea hey hp
  obtain ⟨K,hK,hKconn,ha,hv,hcover⟩ := C.closed_source_strip t
  apply image_strip_projection_germ_g17 P.foliations ((f : M → M)^[n])
    (f.continuous.iterate n) ?_ b proj label hproj e (C.unstableAnchor w₀ t) hp
    t.val (by rw [heb,hea]; rfl) K hK hKconn (hea.symm ▸ ha) (hey.symm ▸ hv v)
  · intro s hs
    obtain ⟨w,hw⟩ := hcover s hs
    rw [heb,hw]
    exact hbox w
  · intro q
    induction q using Quotient.inductionOn with
    | _ z =>
      obtain ⟨E,hE⟩ := Ghys.intrinsic_stable_iterate_homeomorph_g17 f a P n z
      exact ⟨Quotient.mk P.foliations.stablePartition (((f : M → M)^[n]) z),E,hE⟩

/-- The source Schwarzian for an actual native root equals the pullback of the receiving scalar holonomy.  The source receiving chart is the actual iterate's affine pullback, proved maximal for the original supplied family. -/
theorem iterate_scalar_schwarzian :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    ∀ (A : Ghys.AffineUnstableLeafStructures P.foliations P.complexLeaves),
      A.ActsAffinely P.foliations P.complexLeaves f →
      ∀ (n : ℕ) (b : P.foliations.boxIndex) (proj : M → ℂ)
        (label : FoliationCoordinateDisk 2 → ℂ),
      (∀ z (hz : z ∈ (P.foliations.box b).image),
        proj z = label ((P.foliations.box b).chart.symm ⟨z,hz⟩).2) →
      ∀ (t : C.transversal) (v : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius),
      (∀ w : Metric.closedBall (0 : Fin C.dimension → ℝ) C.radius,
        ((f : M → M)^[n]) (C.closedEvaluation (t,w)) ∈ (P.foliations.box b).image) →
      ∀ (w₀ : FoliationCoordinateDisk 2) (y y' r : M),
      let x := ((P.foliations.box C.box).chart (C.stableCoordinate,w₀)).val
      ∀ (h : LocalPlaqueTransport P.foliations x y),
      h.box = C.box → h.first = C.stableCoordinate →
      h.second = C.closedStableParameter t v →
      C.unstableAnchor w₀ t ∈ h.map.source →
      ∀ E : Biholomorph 1 1 (P.foliations.ULeaf y) (P.foliations.ULeaf y'),
      (∀ z, (E z).val = ((f : M → M)^[n]) z.val) →
      ∀ (k : OpenPartialHomeomorph (P.foliations.ULeaf r) (P.foliations.ULeaf y'))
        (c : OpenPartialHomeomorph (P.foliations.ULeaf x) ℂ)
        (d₀ : OpenPartialHomeomorph (P.foliations.ULeaf r) ℂ)
        (e : OpenPartialHomeomorph (P.foliations.ULeaf y') ℂ),
      c.source = univ → d₀.source = univ →
      e ∈ (A.atPoint P.foliations P.complexLeaves y').maximalAtlas _ →
      (∀ z ∈ k.target, proj z.val = d₀ (k.symm z)) →
      E (h.map (C.unstableAnchor w₀ t)) ∈ k.target →
      E (h.map (C.unstableAnchor w₀ t)) ∈ e.source →
      let ec := E.toHomeomorph.toOpenPartialHomeomorph.trans e
      let G := fun z ↦ proj (((f : M → M)^[n]) (c.symm z).val)
      ec ∈ (A.atPoint P.foliations P.complexLeaves y).maximalAtlas _ ∧
        h.map (C.unstableAnchor w₀ t) ∈ ec.source ∧
        Ghys.schwarzian (Ghys.affineLocalMapExpression c h.map ec) (c (C.unstableAnchor w₀ t)) =
          Ghys.schwarzian ((Ghys.affineLocalMapExpression d₀ k e) ∘ G)
            (c (C.unstableAnchor w₀ t)) := by
  let := P.realCharts
  let : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  intro A hAct n b proj label hcoord t v hbox w₀ y y' r x h hhb hhf hhs hp
    E hE k c d₀ e hcs hds he hproj hpk hpe ec G
  have hActn := Ghys.intrinsic_affine_action_iterate_g17 f a P A hAct n
  have hec := Ghys.intrinsic_affine_pullback_chart_g17 f a P A ((f : M → M)^[n]) hActn
    (Quotient.mk P.foliations.unstablePartition y)
    (Quotient.mk P.foliations.unstablePartition y') E hE e he
  refine ⟨hec,⟨mem_univ _,hpe⟩,?_⟩
  have hpc : C.unstableAnchor w₀ t ∈ c.source := by rw [hcs]; trivial
  have hpj := C.iterate_projection_germ n b proj label hcoord t v hbox w₀ y h hhb hhf hhs hp
  have hG : (fun z ↦ proj (E (h.map z)).val) =ᶠ[𝓝 (C.unstableAnchor w₀ t)]
      (fun z ↦ G (c z)) := by
    filter_upwards [hpj,c.open_source.mem_nhds hpc] with z hz hzc
    simpa only [G,c.left_inv hzc,hE] using hz
  have hfactor := Ghys.affine_expression_projection_factor_germ h.map E.toHomeomorph k
    c d₀ e hds (fun z ↦ proj z.val) hproj G (C.unstableAnchor w₀ t) hpc hp hpk hG
  unfold Ghys.schwarzian
  rw [hfactor.deriv.eq_of_nhds,hfactor.deriv.deriv.eq_of_nhds,
    hfactor.deriv.deriv.deriv.eq_of_nhds]

/-- In any complete source affine coordinate, the original compact transversal has a compact scalar image and the actual native source core has a finite Schwarzian variation bound.  This applies the global scalar family's bound to the continuous image of the native parameter core, including its true stable coordinate in the containing box. -/
theorem scalar_core_variation_bound (w₀ : FoliationCoordinateDisk 2) :
    letI := P.realCharts
    ∀ (c : OpenPartialHomeomorph
      (P.foliations.ULeaf (((P.foliations.box C.box).chart (C.stableCoordinate,w₀)).val)) ℂ),
      c.source = univ → ∀ S : ℂ × FoliationCoordinateDisk (2*d-2) → ℂ,
      ContinuousOn S ((c.target ∩ c.symm ⁻¹' range (C.unstableAnchor w₀)) ×ˢ univ) →
      IsCompact ((fun t ↦ c (C.unstableAnchor w₀ t)) '' C.transverseCore) ∧
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ p ∈ C.parameterCore, ∀ q ∈ C.parameterCore,
          dist (S (c (C.unstableAnchor w₀ p.2),C.stableParameter p))
            (S (c (C.unstableAnchor w₀ q.2),C.stableParameter q)) ≤ B := by
  let := P.realCharts
  intro c hcs S hS
  have hc : Continuous c := (c.isOpenEmbedding hcs).continuous
  have hcoord : Continuous (fun t ↦ c (C.unstableAnchor w₀ t)) :=
    hc.comp (C.open_unstableAnchor w₀).continuous
  refine ⟨C.compact_transverseCore.image hcoord,?_⟩
  let J : C.parameterDomain × C.transversal → ℂ × FoliationCoordinateDisk (2*d-2) :=
    fun p ↦ (c (C.unstableAnchor w₀ p.2),C.stableParameter p)
  have hJ : Continuous J := (hcoord.comp continuous_snd).prodMk C.continuous_stableParameter
  have hin (p : C.parameterDomain × C.transversal) :
      J p ∈ (c.target ∩ c.symm ⁻¹' range (C.unstableAnchor w₀)) ×ˢ univ := by
    have hp : C.unstableAnchor w₀ p.2 ∈ c.source := by rw [hcs]; trivial
    exact ⟨⟨c.map_source hp,by
      change c.symm (c (C.unstableAnchor w₀ p.2)) ∈ range (C.unstableAnchor w₀)
      rw [c.left_inv hp]
      exact mem_range_self _⟩,mem_univ _⟩
  have hSJ : ContinuousOn (S ∘ J) C.parameterCore :=
    hS.comp hJ.continuousOn (fun p _ ↦ hin p)
  obtain ⟨b,hb⟩ := C.compact_parameterCore.exists_bound_of_continuousOn hSJ
  refine ⟨2 * max b 0, mul_nonneg (by norm_num) (le_max_right _ _),?_⟩
  intro p hp q hq
  calc
    dist (S (J p)) (S (J q)) ≤ ‖S (J p)‖ + ‖S (J q)‖ := dist_le_norm_add_norm _ _
    _ ≤ b + b := add_le_add (hb p hp) (hb q hq)
    _ ≤ 2 * max b 0 := by linarith [le_max_left b 0]

omit [CompactSpace M] in
/-- The literal compact native root restriction has the analytic density budget in any complete source coordinate.  The holomorphicity and nonzero Jacobian premises are precisely the conclusions of the receiving-projection calculus theorem; the finite roots and the density are constructed here. -/
theorem root_density_budget (w₀ : FoliationCoordinateDisk 2) :
    letI := P.realCharts
    ∀ (c : OpenPartialHomeomorph
      (P.foliations.ULeaf (((P.foliations.box C.box).chart (C.stableCoordinate,w₀)).val)) ℂ),
      c.source = univ → ∀ (n : ℕ) (K₁ : Set M), IsCompact K₁ →
      ∀ (b : P.foliations.boxIndex), K₁ ⊆ (P.foliations.box b).image →
      ∀ proj : M → ℂ,
      let χ := fun t ↦ c (C.unstableAnchor w₀ t)
      let G := fun z ↦ proj (((f : M → M)^[n]) (c.symm z).val)
      let Ω := c.target ∩ (fun z ↦ ((f : M → M)^[n]) (c.symm z).val) ⁻¹'
        (P.foliations.box b).image
      DifferentiableOn ℂ G Ω → (∀ z ∈ Ω, deriv G z ≠ 0) →
      ∀ weight : ℝ≥0∞, ∃ B : ℂ → ℝ≥0∞, Measurable B ∧
        (∫⁻ y, B y ∂MeasureTheory.volume) ≤ weight * MeasureTheory.volume (χ '' C.transverseCore) ∧
        ∀ y (roots : Finset C.transversal),
          (∀ t, t ∈ roots ↔ t ∈ C.transverseCore ∧
            ((f : M → M)^[n]) (C.anchor t).val ∈ K₁ ∧
            proj (((f : M → M)^[n]) (C.anchor t).val) = y) →
          B y = ∑ t ∈ roots, weight / ENNReal.ofReal (‖deriv G (χ t)‖ ^ 2) := by
  classical
  let := P.realCharts
  intro c hcs n K₁ hK₁ b hKb proj χ G Ω hg hnz weight
  have hχ : Continuous χ := (c.isOpenEmbedding hcs).continuous.comp
    (C.open_unstableAnchor w₀).continuous
  have hinj : Function.Injective χ := (c.isOpenEmbedding hcs).injective.comp
    (C.open_unstableAnchor w₀).injective
  have hfn : Continuous ((f : M → M)^[n]) := f.continuous.iterate n
  let R := C.transverseCore ∩ (fun t ↦ ((f : M → M)^[n]) (C.anchor t).val) ⁻¹' K₁
  have hR : IsCompact R := C.compact_transverseCore.inter_right
    (hK₁.isClosed.preimage (hfn.comp (continuous_subtype_val.comp C.continuous_anchor)))
  have hcsrc (t : C.transversal) : C.unstableAnchor w₀ t ∈ c.source := by rw [hcs]; trivial
  have hval (t : C.transversal) : (c.symm (χ t)).val = (C.anchor t).val := by
    rw [show χ t = c (C.unstableAnchor w₀ t) from rfl,c.left_inv (hcsrc t)]
    rfl
  have hΩ : IsOpen Ω :=
    (hfn.comp_continuousOn ((P.foliations.unstable_inclusion _).comp_continuousOn
      c.symm.continuousOn)).isOpen_inter_preimage c.open_target (P.foliations.box b).isOpen_image
  have hRU : χ '' R ⊆ Ω := by
    rintro _ ⟨t,ht,rfl⟩
    refine ⟨c.map_source (hcsrc t),?_⟩
    change ((f : M → M)^[n]) (c.symm (χ t)).val ∈ (P.foliations.box b).image
    rw [hval]
    exact hKb ht.2
  obtain ⟨B,hB,hbudget,_,hroot⟩ := Analysis.Complex.compact_coordinate_root_density_budget
    χ hχ hinj R C.transverseCore hR inter_subset_left Ω hΩ hRU G hg
    (fun t ht ↦ hnz _ (hRU (mem_image_of_mem χ ht))) weight
  refine ⟨B,hB,hbudget,?_⟩
  intro y roots hr
  apply hroot y roots
  intro t
  simpa only [R,mem_inter_iff,mem_preimage,G,hval,and_assoc] using hr t

/-- The source variation data required by the local-cover proof exist for every actual native core and the original supplied affine family.  Complete coordinates give a single compact planar transversal, and the arbitrary-family coordinate bridge and whole-box scalar gluing supply its true finite bound. -/
theorem complete_scalar_family
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    letI := P.realCharts
    letI : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
      fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
    ∀ (A : Ghys.AffineUnstableLeafStructures P.foliations P.complexLeaves),
      A.ActsAffinely P.foliations P.complexLeaves f →
      A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves →
      (∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        (A.structureAt q).Complete (IntrinsicFoliationLeaf P.foliations.unstablePartition q)) →
      ∀ w₀ : FoliationCoordinateDisk 2,
      let x := fun s ↦ ((P.foliations.box C.box).chart (s,w₀)).val
      let W : Set (P.foliations.ULeaf (x C.stableCoordinate)) :=
        {z | ∃ w : FoliationCoordinateDisk 2,
          ((P.foliations.box C.box).chart (C.stableCoordinate,w)).val = z.val}
      ∃ (c : OpenPartialHomeomorph (P.foliations.ULeaf (x C.stableCoordinate)) ℂ)
        (h : ∀ s, LocalPlaqueTransport P.foliations (x C.stableCoordinate) (x s))
        (S : ℂ × FoliationCoordinateDisk (2*d-2) → ℂ) (B : ℝ),
        c ∈ (A.atPoint P.foliations P.complexLeaves (x C.stableCoordinate)).maximalAtlas _ ∧
        c.source = univ ∧ c.target = univ ∧
        (∀ s, (h s).box = C.box ∧ (h s).first = C.stableCoordinate ∧ (h s).second = s ∧
          (h s).transverse = w₀ ∧ (h s).map.source = W) ∧
        ContinuousOn S ((c.target ∩ c.symm ⁻¹' W) ×ˢ univ) ∧
        (∀ p ∈ ((c.target ∩ c.symm ⁻¹' W) ×ˢ univ),
          ∀ e : OpenPartialHomeomorph (P.foliations.ULeaf (x p.2)) ℂ,
          e ∈ (A.atPoint P.foliations P.complexLeaves (x p.2)).maximalAtlas _ →
          (h p.2).map (c.symm p.1) ∈ e.source →
          S p = Ghys.schwarzian (Ghys.affineLocalMapExpression c (h p.2).map e) p.1) ∧
        IsCompact ((fun t ↦ c (C.unstableAnchor w₀ t)) '' C.transverseCore) ∧
        0 ≤ B ∧ ∀ p ∈ C.parameterCore, ∀ q ∈ C.parameterCore,
          dist (S (c (C.unstableAnchor w₀ p.2),C.stableParameter p))
            (S (c (C.unstableAnchor w₀ q.2),C.stableParameter q)) ≤ B := by
  let := P.realCharts
  let : ∀ x : M, ChartedSpace (ComplexModel 1) (P.foliations.ULeaf x) :=
    fun x ↦ P.complexLeaves.charts (Quotient.mk P.foliations.unstablePartition x)
  intro A hAct hCont hComplete w₀ x W
  obtain ⟨c,h,S,hc,hcs,hct,hmeta,hS,hrepr,_⟩ :=
    Ghys.one_box_complete_affine_schwarzian_family f a hRank P A hAct hCont hComplete
      C.box C.stableCoordinate w₀
  have hSmall : ContinuousOn S
      ((c.target ∩ c.symm ⁻¹' range (C.unstableAnchor w₀)) ×ˢ univ) := by
    apply hS.mono
    intro p hp
    refine ⟨⟨hp.1.1,?_⟩,hp.2⟩
    obtain ⟨t,ht⟩ := hp.1.2
    exact ⟨t.val,congrArg Subtype.val ht⟩
  obtain ⟨hcompact,B,hB,hbound⟩ := C.scalar_core_variation_bound w₀ c hcs S hSmall
  exact ⟨c,h,S,B,hc,hcs,hct,hmeta,hS,hrepr,hcompact,hB,hbound⟩

end NativeStableSourceCore
/-- Every ambient point lies in the interior of an actual compact native source core.  The original receiving box and its unstable anchor slice are retained; only the common stable radius and transverse neighborhood shrink. -/
theorem anosov_native_stable_source_core_at (x : M) :
    ∃ C : NativeStableSourceCore f a P, x ∈ interior C.image := by
  classical
  let := P.realCharts
  obtain ⟨r,⟨F⟩⟩ := anosov_native_stable_family_exists f a x
  obtain ⟨b,hxb⟩ := P.foliations.cover x
  let st := (P.foliations.box b).chart.symm ⟨x,hxb⟩
  have hmark : ((P.foliations.box b).chart (st.1,st.2)).val = x :=
    congrArg Subtype.val ((P.foliations.box b).chart.apply_symm_apply ⟨x,hxb⟩)
  obtain ⟨R,hR,hRF,T,ht,hcenter,hbox,ho⟩ :=
    anosov_native_stable_family_local_product f a P F b st.1 st.2 hmark
  let F' := F.restrictRadius R hR hRF.le
  let : LocallyCompactSpace (FoliationCoordinateDisk 2) :=
    Metric.isOpen_ball.locallyCompactSpace
  let : LocallyCompactSpace T := T.isOpen.locallyCompactSpace
  let t : T := ⟨st.2,ht⟩
  obtain ⟨K,hK,htK,_⟩ := exists_compact_subset isOpen_univ (mem_univ t)
  let C : NativeStableSourceCore f a P := {
    center := x, dimension := r, family := F', box := b,
    stableCoordinate := st.1, transversal := T, anchor_mem := hcenter,
    in_box := fun v t ↦ hbox (v,t), radius := R/2,
    radius_pos := half_pos hR, radius_lt := half_lt_self hR,
    transverseCore := K, compact_transverseCore := hK }
  let z : C.parameterDomain := ⟨0,Metric.mem_ball_self hR⟩
  let W : Set (C.parameterDomain × T) :=
    {v | ‖v.val‖ < R/2} ×ˢ interior K
  have hWo : IsOpen W := (isOpen_lt continuous_subtype_val.norm continuous_const).prod
    isOpen_interior
  have hWcore : W ⊆ C.parameterCore := by
    intro p hp
    change ‖p.1.val‖ < R/2 ∧ p.2 ∈ interior K at hp
    exact ⟨hp.1.le,interior_subset hp.2⟩
  have hzt : (z,t) ∈ W := ⟨by simpa [z] using half_pos hR,htK⟩
  have hvalue : C.evaluation (z,t) = x := by
    change (F.plaque _).param 0 = x
    exact (F.plaque _).centered.trans hmark
  refine ⟨C,mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset
    ((C.open_evaluation.isOpenMap W hWo).mem_nhds ⟨(z,t),hzt,hvalue⟩)
    (image_mono hWcore)

/-- Finitely many actual compact native source cores cover the compact ambient manifold. -/
theorem anosov_finite_native_stable_source_cover :
    ∃ n : ℕ, ∃ C : Fin n → NativeStableSourceCore f a P,
      (univ : Set M) ⊆ ⋃ i, (C i).image := by
  classical
  choose C hC using anosov_native_stable_source_core_at f a P
  obtain ⟨s,hs⟩ := (isCompact_univ : IsCompact (univ : Set M)).elim_finite_subcover
    (fun x ↦ interior (C x).image) (fun _ ↦ isOpen_interior)
    (fun x _ ↦ mem_iUnion.mpr ⟨x,hC x⟩)
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s,fun i ↦ C (e.symm i).val,?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hs hx)
  exact mem_iUnion.mpr ⟨e ⟨y,hy⟩,by simpa using interior_subset hxy⟩

/-- The compact root-cover theorem applies to the actual native source cores.  Local injectivity near compact anchor roots, whole-plaque shrinking, and receiving-label constancy are all supplied by the original Anosov datum and the intrinsic foliation geometry. -/
theorem native_source_cores_eventual_root_cover
    {ι Z : Type*} [Fintype ι] [TopologicalSpace Z] [T2Space Z] (C : ι → NativeStableSourceCore f a P)
    (hcover : (univ : Set M) ⊆ ⋃ i, (C i).image)
    (m : MetricSpace M) (hmTop : m.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace M)) :
    letI := P.realCharts
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
      ⟨a.metric.toRiemannianMetric⟩
    (∀ x y : M, riemannianEDist (realModel d) x y < ⊤ →
      ENNReal.ofReal (m.dist x y) = riemannianEDist (realModel d) x y) →
    ∀ (b : P.foliations.boxIndex) (K₀ K₁ : Set M)
      (proj : M → Z) (label : FoliationCoordinateDisk 2 → Z),
      Function.Injective label →
      IsCompact K₀ → IsCompact K₁ → K₀ ⊆ interior K₁ →
      K₁ ⊆ (P.foliations.box b).image →
      ContinuousOn proj (P.foliations.box b).image →
      (∀ z (hz : z ∈ (P.foliations.box b).image),
        proj z = label ((P.foliations.box b).chart.symm ⟨z,hz⟩).2) →
      ∀ᶠ n : ℕ in atTop, ∀ x : Z,
        (∀ i, {t | t ∈ (C i).transverseCore ∧
          ((f : M → M)^[n]) ((C i).anchor t).val ∈ K₁ ∧
          proj (((f : M → M)^[n]) ((C i).anchor t).val) = x}.Finite) ∧
        (∀ i t, t ∈ (C i).transverseCore →
          ((f : M → M)^[n]) ((C i).anchor t).val ∈ K₁ →
          IsCompact ({z ∈ K₀ | proj z = x} ∩
            range (fun v ↦ ((f : M → M)^[n]) ((C i).closedEvaluation (t,v))))) ∧
        (∀ z ∈ K₀, proj z = x → ∃ i t,
          (t ∈ (C i).transverseCore ∧
            ((f : M → M)^[n]) ((C i).anchor t).val ∈ K₁ ∧
            proj (((f : M → M)^[n]) ((C i).anchor t).val) = x) ∧
          z ∈ range (fun v ↦ ((f : M → M)^[n]) ((C i).closedEvaluation (t,v)))) := by
  classical
  let := P.realCharts
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  intro hm b K₀ K₁ proj label hinj hK₀ hK₁ h₀ h₁ hπ hcoord
  have hlocal (n : ℕ) (i) (t : (C i).transversal)
      (_ht : t ∈ (C i).transverseCore)
      (hk : ((f : M → M)^[n]) ((C i).anchor t).val ∈ K₁) :=
    (C i).iterate_projection_locally_injective n b proj label hinj hcoord t (h₁ hk)
  let : MetricSpace M := m.replaceTopology hmTop.symm
  obtain ⟨ε,hε,hbuf₀,hbuf₁⟩ := compact_nested_receiving_buffers K₀ K₁
    (P.foliations.box b).image hK₀ hK₁ (P.foliations.box b).isOpen_image h₀ h₁
  have hsmall := Filter.eventually_all.mpr (fun i ↦ (C i).uniform_shrinking m hm ε hε)
  filter_upwards [hsmall] with n hn
  let fn : M ≃ₜ M := f.toHomeomorph ^ n
  have hfn (z : M) : fn z = ((f : M → M)^[n]) z := by
    suffices hall : ∀ k : ℕ, (f.toHomeomorph ^ k) z = ((f : M → M)^[k]) z from hall n
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simpa only [pow_succ',Homeomorph.mul_apply,
        Function.iterate_succ_apply',Diffeomorph.coe_toHomeomorph] using congrArg f ih
  let Y := fun i ↦ Metric.closedBall (0 : Fin (C i).dimension → ℝ) (C i).radius
  let y₀ : ∀ i, Y i := fun i ↦ ⟨0,Metric.mem_closedBall_self (C i).radius_pos.le⟩
  have hzero (i) (t : (C i).transversal) :
      (C i).closedEvaluation (t,y₀ i) = ((C i).anchor t).val :=
    ((C i).family.plaque ((C i).anchor t)).centered
  have hΦcover (z : M) : ∃ i t, t ∈ (C i).transverseCore ∧
      ∃ v : Y i, (C i).closedEvaluation (t,v) = z := by
    obtain ⟨i,p,hp,hpz⟩ := mem_iUnion.mp (hcover (mem_univ z))
    exact ⟨i,p.2,hp.2,⟨p.1.val,by
      change ‖p.1.val - 0‖ ≤ (C i).radius
      simpa only [sub_zero,Set.mem_ofPred_eq] using hp.1⟩,hpz⟩
  have hshrink (i) (t : (C i).transversal) (ht : t ∈ (C i).transverseCore) (v : Y i) :
      dist (fn ((C i).closedEvaluation (t,v)))
        (fn ((C i).closedEvaluation (t,y₀ i))) < ε := by
    rw [hfn,hfn,hzero]
    let v' : (C i).parameterDomain :=
      ⟨v.val,Metric.closedBall_subset_ball (C i).radius_lt v.property⟩
    exact hn i (v',t) ⟨by
      change ‖v.val‖ ≤ (C i).radius
      exact (mem_closedBall_zero_iff.mp v.property),ht⟩
  have hlabel (i) (t : (C i).transversal) (_ht : t ∈ (C i).transverseCore)
      (hb : ∀ v : Y i, fn ((C i).closedEvaluation (t,v)) ∈ (P.foliations.box b).image)
      (v : Y i) : proj (fn ((C i).closedEvaluation (t,v))) =
        proj (fn ((C i).closedEvaluation (t,y₀ i))) := by
    simp only [hfn] at hb ⊢
    rw [hcoord _ (hb v),hcoord _ (hb (y₀ i))]
    exact congrArg label ((C i).iterate_receiving_coordinate_constant n b t hb v (y₀ i))
  have hl (i) (t : (C i).transversal) (ht : t ∈ (C i).transverseCore)
      (hk : fn ((C i).closedEvaluation (t,y₀ i)) ∈ K₁) :
      ∃ V, IsOpen V ∧ t ∈ V ∧ V.InjOn (fun u ↦ proj (fn ((C i).closedEvaluation (u,y₀ i)))) := by
    simpa only [hfn,hzero] using hlocal n i t ht (by simpa only [hfn,hzero] using hk)
  intro x
  obtain ⟨hfin,hcompact,hcov⟩ := compact_contracted_plaque_root_cover
    (fun i ↦ (C i).transverseCore) (fun i ↦ (C i).compact_transverseCore)
    (fun i ↦ (C i).closedEvaluation) (fun i ↦ (C i).continuous_closedEvaluation)
    y₀ hΦcover fn proj (P.foliations.box b).image K₀ K₁ hK₀ hK₁
    (h₀.trans (interior_subset.trans h₁)) hπ ε hbuf₀ hbuf₁ hshrink hlabel hl x
  simp only [hfn,hzero] at hfin hcompact hcov
  exact ⟨hfin,fun i t ht hk ↦ (hcompact i t ht hk).2,hcov⟩

end SourceCore

end HolomorphicAnosov
