import HolomorphicAnosov.Geometry.Holonomy.ContinuousPrefixFamilyG18
import HolomorphicAnosov.Paper.Ghys.NativeAffinePresentationAtlasesG1
import HolomorphicAnosov.Analysis.Complex.ParametricHolomorphicFlatCoordinateG1
import HolomorphicAnosov.Ghys.NativeFlowboxConnectionCoefficient
import HolomorphicAnosov.Ghys.AffineDevelopingConnectedChart
import HolomorphicAnosov.Ghys.AffineCompleteness
import HolomorphicAnosov.Geometry.FinitePlaqueHolonomy

/-! This module constructs common-source affine coordinates for stable prefix holonomy. (Ghys, Prop. 3.1(ii)) -/
noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
universe u v

section PrefixCoordinates
variable {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (Fin (s+2) → ℝ) M]
  (F : TransverseContinuousFoliations.{u,v} s 2 M)
  (C : IntrinsicComplexUnstableLeaves F)

/-- Stable prefix germs admit representatives on one connected neighborhood with continuously varying affine target coordinates. (Ghys, Prop. 3.1(ii)) -/
def AffineUnstableLeafStructures.HasContinuousPrefixCoordinates
    (A : AffineUnstableLeafStructures F C) : Prop :=
  ∀ (q : Quotient F.stablePartition)
    (a b : IntrinsicFoliationLeaf F.stablePartition q) (γ : Path a b)
    (H : LocalHolonomyContinuation F γ),
    ∃ h : ∀ r : unitInterval, PathHolonomyRepresentative F γ 0 r,
      (∀ r : unitInterval,
        Filter.Germ.ofFun (h r).map =
          (Filter.Germ.ofFun (prefixHolonomy F γ H r) :
            Filter.Germ (𝓝 (F.uPoint (γ 0).val)) (F.ULeaf (γ r).val))) ∧
    ∃ U : Set (F.ULeaf (γ 0).val),
      IsOpen U ∧ IsConnected U ∧ F.uPoint (γ 0).val ∈ U ∧
      (∀ r : unitInterval, U ⊆ (h r).map.source) ∧
    ∃ c : ∀ r : unitInterval, OpenPartialHomeomorph (F.ULeaf (γ r).val) ℂ,
      (∀ r : unitInterval,
        letI := C.charts (Quotient.mk F.unstablePartition (γ r).val)
        c r ∈ ComplexAffineStructure.maximalAtlas (F.ULeaf (γ r).val)
          (A.atPoint F C (γ r).val)) ∧
      (∀ (r : unitInterval) (w : F.ULeaf (γ 0).val), w ∈ U →
        (h r).map w ∈ (c r).source) ∧
      ∀ w ∈ U, Continuous (fun r : unitInterval ↦ c r ((h r).map w))

/-- Continuous point evaluations give continuous affine ratios. (Ghys, Prop. 3.1(ii)) -/
theorem affine_holonomy_ratio_continuous_of_prefix_coordinates_g1
    (A : AffineUnstableLeafStructures F C)
    (hA : A.HasContinuousPrefixCoordinates F C) :
    A.ContinuousAlongStableHolonomy F C := by
  intro q a b γ H
  obtain ⟨h, hgerm, U, hopen, hconn, hbase, hsource, c, hc, htarget, hcont⟩ :=
    hA q a b γ H
  refine ⟨h, hgerm, U, hopen, hconn, hbase, hsource, c, hc, htarget, ?_⟩
  intro x hx y hy z hz hxy hxz hyz
  apply ((hcont x hx).sub (hcont y hy)).div ((hcont x hx).sub (hcont z hz))
  intro r heq
  apply hxz
  apply (h r).map.injOn (hsource r hx) (hsource r hz)
  apply (c r).injOn (htarget r x hx) (htarget r z hz)
  exact sub_eq_zero.mp heq

end PrefixCoordinates
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- On a compact plaque family over one scalar disk, native affine charts exist on a smaller common disk with jointly continuous evaluations. (Ghys, Prop. 3.1(ii)) -/
theorem native_compact_flowbox_affine_coordinates_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (k : Fin G.boxCount) {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (t : T → G.transverse k) (ht : Continuous (fun p ↦ (t p).val))
    (z₀ : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hdisk : ∀ p z, z ∈ Metric.ball z₀ δ → (z, (t p).val) ∈ (G.box k).target) :
    ∃ (r : ℝ) (e : T → OpenPartialHomeomorph ℂ ℂ)
      (C : ∀ p, OpenPartialHomeomorph (L (G.label k (t p))) ℂ),
      0 < r ∧ Metric.ball z₀ r ⊆ Metric.ball z₀ δ ∧
      ContinuousOn (fun p : T × ℂ ↦ e p.1 p.2) (univ ×ˢ Metric.ball z₀ r) ∧
      (∀ p, (e p).source = Metric.ball z₀ r) ∧
      ∀ p, C p ∈ ComplexAffineStructure.maximalAtlas _ (G.affineAt f a L U (G.label k (t p))) ∧
        ∀ (z : ℂ) (_hz : z ∈ Metric.ball z₀ r),
          ∃ hzδ : z ∈ Metric.ball z₀ δ,
            (G.parametrization k (t p) ⟨z, hdisk p z hzδ⟩).val ∈ (C p).source ∧
            C p (G.parametrization k (t p) ⟨z, hdisk p z hzδ⟩).val = e p z := by
  classical
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
  have hcharts (p : T) := native_flowbox_real_chart f a L U G k (t p)
    ⟨z₀, hdisk p z₀ (Metric.mem_ball_self hδ)⟩
  choose c hc hs hct hf hi _ _ using hcharts
  let ch (p : T) : LeafChart (L (G.label k (t p))) := ⟨c p, hc p⟩
  obtain ⟨A, hA, hAB⟩ := native_flowbox_connection_coefficient L f a U G k
  have hB (p : T) := hAB (t p) (ch p) (hct p) (hi p) (hf p)
  choose B hBhol hBeq hBgraph using hB
  let A' : T → ℂ → ℂ := fun p z ↦ A (z, (t p).val)
  have hcont : ContinuousOn (Function.uncurry A') (univ ×ˢ Metric.ball z₀ δ) :=
    hA.comp (continuous_snd.prodMk (ht.comp continuous_fst)).continuousOn
      (fun p hp ↦ hdisk p.1 p.2 hp.2)
  have hsource (p : T) : Metric.ball z₀ δ ⊆ (c p).target := by
    intro z hz
    rw [hct p]
    exact hdisk p z hz
  have hhol (p : T) : DifferentiableOn ℂ (A' p) (Metric.ball z₀ δ) := by
    apply ((hBhol p).mono (hsource p)).congr
    intro z hz
    exact (hBeq p z (hsource p hz)).symm
  obtain ⟨r, e, hr, hrδ, hecont, he⟩ := parametric_holomorphic_flat_charts_g1
    Metric.isOpen_ball (convex_ball z₀ δ) (Metric.mem_ball_self hδ) A' hcont hhol
  let C (p : T) := (c p).trans (e p)
  refine ⟨r, e, C, hr, hrδ, hecont, fun p ↦ (he p).1, ?_⟩
  intro p
  refine ⟨?_, ?_⟩
  · apply native_connection_ode_chart_affine L f a U G (G.label k (t p)) (ch p)
      (B p) (hBgraph p) (e p) (he p).2.2.2.1 (he p).2.2.2.2.1
    intro z hz
    have hzδ := hrδ ((he p).1 ▸ hz)
    have h := (he p).2.2.2.2.2 z hz
    rw [show A' p z = B p z from (hBeq p z (hsource p hzδ)).symm] at h
    exact h
  · intro z hz
    have hzin : z ∈ (c p).target := hsource p (hrδ hz)
    have hpoint := hi p (⟨z, hdisk p z (hrδ hz)⟩ : nativeAffineFlowboxSlice (G.box k) (t p).val)
    refine ⟨hrδ hz, ?_, ?_⟩
    · change (G.parametrization k (t p) _).val ∈ (c p).source ∧
        c p (G.parametrization k (t p) _).val ∈ (e p).source
      rw [← hpoint, (c p).right_inv hzin]
      exact ⟨(c p).map_target hzin, (he p).1.symm ▸ hz⟩
    · change e p (c p (G.parametrization k (t p) _).val) = e p z
      rw [← hpoint, (c p).right_inv hzin]

/-- The native affine family has local scalar coordinates continuous in the ambient topology and affine on each intrinsic plaque germ. -/
theorem native_local_continuous_affine_coordinate_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U) (x : M) :
    ∃ (O : Set M) (K : M → ℂ), IsOpen O ∧ x ∈ O ∧ ContinuousOn K O ∧
      ∀ i z, (U.leaf i).inclusion z ∈ O →
        ∃ c : OpenPartialHomeomorph (L i) ℂ,
          c ∈ ComplexAffineStructure.maximalAtlas _ (G.affineAt f a L U i) ∧
          z ∈ c.source ∧ (c : L i → ℂ) =ᶠ[𝓝 z] K ∘ (U.leaf i).inclusion := by
  classical
  obtain ⟨k, hxk⟩ := G.box_cover x
  let z₀ := (G.box k x).1
  let t₀ := (G.box k x).2
  obtain ⟨R, hR, hRbox⟩ := Metric.isOpen_iff.mp (G.box k).open_target (G.box k x)
    ((G.box k).map_source hxk)
  let V := Metric.closedBall t₀ (R/2)
  have hhalf : 0 < R/2 := by positivity
  have hV : V ⊆ Metric.ball t₀ R := Metric.closedBall_subset_ball (by linarith)
  have hdisk (p : V) (z : ℂ) (hz : z ∈ Metric.ball z₀ (R/2)) :
      (z,p.val) ∈ (G.box k).target := by
    apply hRbox
    change (z,p.val) ∈ Metric.ball (z₀,t₀) R
    rw [← ball_prod_same]
    exact ⟨Metric.ball_subset_ball (by linarith) hz, hV p.property⟩
  let t : V → G.transverse k := fun p ↦
    ⟨p.val, G.transverse_contains k (z₀,p.val) (hdisk p z₀ (Metric.mem_ball_self hhalf))⟩
  let : CompactSpace V := isCompact_iff_compactSpace.mp (isCompact_closedBall t₀ (R/2))
  obtain ⟨r, e, C, hr, hrR, hecont, hes, hC⟩ := native_compact_flowbox_affine_coordinates_g1
    f a L U G k t continuous_subtype_val z₀ (R/2) hhalf hdisk
  let O := (G.box k).source ∩ (G.box k) ⁻¹'
    (Metric.ball z₀ r ×ˢ Metric.ball t₀ (R/2))
  let K : M → ℂ := fun y ↦ if h : (G.box k y).2 ∈ V then
    e ⟨(G.box k y).2,h⟩ (G.box k y).1 else 0
  have hO : IsOpen O := (G.box k).continuousOn.isOpen_inter_preimage
    (G.box k).open_source (Metric.isOpen_ball.prod Metric.isOpen_ball)
  have hKO (y : O) : (G.box k y.val).2 ∈ V := Metric.ball_subset_closedBall y.property.2.2
  have hcb : Continuous (fun y : O ↦ G.box k y.val) :=
    (G.box k).continuousOn.comp_continuous continuous_subtype_val (fun y ↦ y.property.1)
  have hK : ContinuousOn K O := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hp : Continuous (fun y : O ↦
        ((⟨(G.box k y.val).2, hKO y⟩ : V), (G.box k y.val).1)) :=
      (hcb.snd.subtype_mk _).prodMk hcb.fst
    apply (hecont.comp_continuous hp (fun y ↦ ⟨mem_univ _, y.property.2.1⟩)).congr
    intro y
    change e ⟨_, hKO y⟩ _ = K y.val
    simp only [K, dite_eq_left (hKO y)]
  refine ⟨O, K, hO, ⟨hxk, Metric.mem_ball_self hr, Metric.mem_ball_self hhalf⟩, hK, ?_⟩
  intro i z hz
  let p : V := ⟨(G.box k ((U.leaf i).inclusion z)).2,
    Metric.ball_subset_closedBall hz.2.2⟩
  let v : nativeAffineFlowboxSlice (G.box k) (t p).val :=
    ⟨(G.box k ((U.leaf i).inclusion z)).1, (G.box k).map_source hz.1⟩
  have hinc : (U.leaf (G.label k (t p))).inclusion (G.parametrization k (t p) v).val =
      (U.leaf i).inclusion z := by
    rw [← G.parametrization_inclusion]
    exact (G.box k).left_inv hz.1
  have hlabel := U.disjoint _ _ _ _ hinc
  clear_value v p
  cases hlabel
  have hpoint : (G.parametrization k (t p) v).val = z := (U.leaf _).injective hinc
  have hzbranch : z ∈ G.branch k (t p) := hpoint ▸ (G.parametrization k (t p) v).property
  have hpsecond : p.val = (G.box k ((U.leaf (G.label k (t p))).inclusion z)).2 := by
    have hh := G.parametrization_inclusion k (t p) v
    rw [hpoint] at hh
    have hc := congrArg (G.box k) hh
    rw [(G.box k).right_inv v.property] at hc
    exact congrArg Prod.snd hc
  have heval (w : L (G.label k (t p))) (hw : w ∈ G.branch k (t p))
      (hwO : (U.leaf (G.label k (t p))).inclusion w ∈ O) :
      w ∈ (C p).source ∧ C p w = K ((U.leaf (G.label k (t p))).inclusion w) := by
    let u := (G.parametrization k (t p)).symm ⟨w, hw⟩
    have hparam : (G.parametrization k (t p) u).val = w :=
      congrArg Subtype.val ((G.parametrization k (t p)).apply_symm_apply ⟨w,hw⟩)
    have hpair : (u.val,p.val) = G.box k ((U.leaf (G.label k (t p))).inclusion w) := by
      have hh := G.parametrization_inclusion k (t p) u
      rw [hparam] at hh
      have hc := congrArg (G.box k) hh
      rw [(G.box k).right_inv u.property] at hc
      exact hc
    have hu : u.val ∈ Metric.ball z₀ r := by
      have hh : u.val = (G.box k ((U.leaf (G.label k (t p))).inclusion w)).1 := congrArg Prod.fst hpair
      rw [hh]
      exact hwO.2.1
    obtain ⟨hzδ, hsrc, hv⟩ := (hC p).2 u.val hu
    have huu : (⟨u.val, hdisk p u.val hzδ⟩ : nativeAffineFlowboxSlice (G.box k) (t p).val) = u := rfl
    rw [huu, hparam] at hsrc hv
    refine ⟨hsrc, hv.trans ?_⟩
    simp only [K, ← hpair, dite_eq_left p.property]
  have hbase := heval z hzbranch hz
  refine ⟨C p, (hC p).1, hbase.1, ?_⟩
  have hopenpre : IsOpen ((U.leaf (G.label k (t p))).inclusion ⁻¹' O) :=
    hO.preimage (U.leaf (G.label k (t p))).immersion.contMDiff.continuous
  filter_upwards [(G.branch k (t p)).isOpen.mem_nhds hzbranch, hopenpre.mem_nhds hz] with w hw hwO
  exact (heval w hw hwO).2

/-- A supplied intrinsic presentation inherits the ambient continuous affine coordinates through point-preserving affine leaf identifications. -/
theorem native_local_affine_coordinate_on_presentation_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    : letI := P.realCharts
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      (∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        ∃ (i : ι) (T : Diffeomorph (complexModel 1) (complexModel 1) (L i)
            (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞),
          (∀ z, (T z).val = (U.leaf i).inclusion z) ∧
          ∀ e : OpenPartialHomeomorph
              (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ℂ,
            e ∈ ComplexAffineStructure.maximalAtlas _ (A.structureAt q) ↔
              T.toHomeomorph.toOpenPartialHomeomorph.trans e ∈
                ComplexAffineStructure.maximalAtlas _ (G.affineAt f a L U i)) →
      ∀ x : M, ∃ (O : Set M) (K : M → ℂ), IsOpen O ∧ x ∈ O ∧ ContinuousOn K O ∧
        ∀ (q : Quotient P.foliations.unstablePartition),
          letI := P.foliations.unstableTopology q
          letI := P.complexLeaves.charts q
          ∀ y : IntrinsicFoliationLeaf P.foliations.unstablePartition q, y.val ∈ O →
            ∃ c : OpenPartialHomeomorph (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ℂ,
              c ∈ ComplexAffineStructure.maximalAtlas _ (A.structureAt q) ∧ y ∈ c.source ∧
              (c : _ → ℂ) =ᶠ[𝓝 y] K ∘ Subtype.val := by
  classical
  let := P.realCharts
  intro A hA x
  obtain ⟨O,K,hO,hx,hK,hlocal⟩ := native_local_continuous_affine_coordinate_g1 f a L U G x
  refine ⟨O,K,hO,hx,hK,?_⟩
  intro q
  let := P.foliations.unstableTopology q
  let := P.complexLeaves.charts q
  intro y hy
  obtain ⟨i,T,hT,hmax⟩ := hA q
  have hzy : (U.leaf i).inclusion (T.symm y) = y.val := by rw [← hT, T.apply_symm_apply]
  obtain ⟨c,hc,hzc,hcgerm⟩ := hlocal i (T.symm y) (hzy.symm ▸ hy)
  let d := T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c
  refine ⟨d, ?_, ?_, ?_⟩
  · apply (hmax d).mpr
    have heq : T.toHomeomorph.toOpenPartialHomeomorph.trans d = c := by
      rw [show d = T.toHomeomorph.symm.toOpenPartialHomeomorph.trans c from rfl,
        ← OpenPartialHomeomorph.trans_assoc, ← Homeomorph.trans_toOpenPartialHomeomorph,
        Homeomorph.self_trans_symm]
      exact OpenPartialHomeomorph.refl_trans c
    rwa [heq]
  · change y ∈ Set.univ ∧ T.symm y ∈ c.source
    exact ⟨mem_univ _, hzc⟩
  · have h := T.symm.continuous.tendsto y hcgerm
    filter_upwards [h] with y' hy'
    change c (T.symm y') = K y'.val
    change c (T.symm y') = K ((U.leaf i).inclusion (T.symm y')) at hy'
    rw [← hT, T.apply_symm_apply] at hy'
    exact hy'

/-- A compact parameter family admits one source neighborhood subordinate to prescribed receiving neighborhoods. -/
theorem compact_family_common_source_neighborhood_g1
    {T X Y : Type*} [TopologicalSpace T] [CompactSpace T]
    [TopologicalSpace X] [TopologicalSpace Y]
    (E : T × X → Y) {W₀ : Set X} (hW₀ : IsOpen W₀)
    (hE : ContinuousOn E (univ ×ˢ W₀)) {x₀ : X} (hx₀ : x₀ ∈ W₀)
    (O : T → Set Y) (hO : ∀ t, IsOpen (O t)) (hEO : ∀ t, E (t,x₀) ∈ O t) :
    ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ t : T, ∃ (j : T) (V : Set T), IsOpen V ∧ t ∈ V ∧
        MapsTo E (V ×ˢ W) (O j) := by
  classical
  have hrect (t : T) : ∃ V W, IsOpen V ∧ IsOpen W ∧ t ∈ V ∧ x₀ ∈ W ∧
      V ×ˢ W ⊆ (univ ×ˢ W₀) ∩ E ⁻¹' O t :=
    isOpen_prod_iff.mp (hE.isOpen_inter_preimage (isOpen_univ.prod hW₀) (hO t))
      t x₀ ⟨⟨mem_univ _,hx₀⟩,hEO t⟩
  choose V W hV hW htV hxW hVW using hrect
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover V hV (by
    intro t _
    exact mem_iUnion.mpr ⟨t,htV t⟩)
  let W' := W₀ ∩ ⋂ j ∈ s, W j
  refine ⟨W', hW₀.inter (isOpen_biInter_finset fun j _ ↦ hW j), ?_,
    inter_subset_left, ?_⟩
  · exact ⟨hx₀, mem_iInter₂.mpr (fun j _ ↦ hxW j)⟩
  · intro t
    obtain ⟨j,hjs,htj⟩ := mem_iUnion₂.mp (hs (mem_univ t))
    refine ⟨j,V j,hV j,htj,?_⟩
    intro p hp
    exact (hVW j ⟨hp.1,mem_iInter₂.mp hp.2.2 j hjs⟩).2

/-- A plane coordinate supplies a connected source neighborhood containing two anchor points. -/
theorem plane_coordinate_two_anchor_neighborhood_g1
    {X : Type*} [TopologicalSpace X] (e : X ≃ₜ ℂ)
    {W : Set X} (hW : IsOpen W) {x : X} (hx : x ∈ W) :
    ∃ (U : Set X) (y : X), IsOpen U ∧ IsConnected U ∧ x ∈ U ∧ U ⊆ W ∧
      y ∈ U ∧ x ≠ y := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (e.isOpenMap W hW) (e x) ⟨x,hx,rfl⟩
  let U := e ⁻¹' Metric.ball (e x) r
  let z : ℂ := e x + (r/2 : ℝ)
  have hz : z ∈ Metric.ball (e x) r := by
    rw [Metric.mem_ball,dist_eq_norm]
    simp only [z,add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : 0 < r/2)]
    linarith
  refine ⟨U,e.symm z,Metric.isOpen_ball.preimage e.continuous,
    e.isConnected_preimage.mpr ((convex_ball (e x) r).isConnected
      ⟨e x,Metric.mem_ball_self hr⟩),Metric.mem_ball_self hr,?_,?_,?_⟩
  · intro w hw
    obtain ⟨w',hw',heq⟩ := hball hw
    exact e.injective heq ▸ hw'
  · change e (e.symm z) ∈ Metric.ball (e x) r
    simpa using hz
  · intro heq
    have he : e x = z := by simpa using congrArg e heq
    have hz0 : (r/2 : ℝ) = 0 := by
      apply Complex.ofReal_injective
      change ((r/2 : ℝ) : ℂ) = 0
      exact add_left_cancel (show e x + ((r/2 : ℝ) : ℂ) = e x + 0 by simpa [z] using he.symm)
    linarith

/-- Locally continuous representatives modulo affine postcomposition yield continuous normalized evaluations. -/
theorem continuous_normalized_affine_family_of_local_representatives_g1
    {T X : Type*} [TopologicalSpace T] [TopologicalSpace X]
    (U : Set X) (F : T → OpenPartialHomeomorph X ℂ)
    (hsource : ∀ t, U ⊆ (F t).source)
    (a b : U) (hab : a ≠ b)
    (hloc : ∀ t₀ : T, ∃ (V : Set T) (H : T × U → ℂ), IsOpen V ∧ t₀ ∈ V ∧
      ContinuousOn H (V ×ˢ univ) ∧
      ∀ t ∈ V, ∃ B : ComplexAffineTransformation,
        ∀ x : U, H (t,x) = B.apply (F t x.val)) :
    Continuous (fun p : T × U ↦ (F p.1 p.2.val - F p.1 a.val) /
      (F p.1 b.val - F p.1 a.val)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀,x₀⟩
  obtain ⟨V,H,hV,htV,hH,hlocal⟩ := hloc t₀
  have hΩ : IsOpen (V ×ˢ (univ : Set U)) := hV.prod isOpen_univ
  have hin : (t₀,x₀) ∈ V ×ˢ (univ : Set U) := ⟨htV,mem_univ _⟩
  have hval : ContinuousAt H (t₀,x₀) := hH.continuousAt (hΩ.mem_nhds hin)
  have hanchor (c : U) : ContinuousAt (fun p : T × U ↦ H (p.1,c)) (t₀,x₀) :=
    (hH.continuousAt (hΩ.mem_nhds ⟨htV,mem_univ _⟩)).comp (continuous_fst.prodMk continuous_const).continuousAt
  have hne : H (t₀,b) - H (t₀,a) ≠ 0 := by
    obtain ⟨B,hB⟩ := hlocal t₀ htV
    rw [hB b,hB a]
    dsimp [ComplexAffineTransformation.apply]
    have hd : F t₀ b.val - F t₀ a.val ≠ 0 := sub_ne_zero.mpr (fun h ↦
      hab (Subtype.ext ((F t₀).injOn (hsource t₀ a.property) (hsource t₀ b.property) h.symm)))
    rw [show B.slope * F t₀ b.val + B.translation - (B.slope * F t₀ a.val + B.translation) =
      B.slope * (F t₀ b.val - F t₀ a.val) by ring]
    exact mul_ne_zero B.slope_ne_zero hd
  apply ((hval.sub (hanchor a)).div ((hanchor b).sub (hanchor a)) hne).congr
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hV.mem_nhds htV)] with p hp
  obtain ⟨B,hB⟩ := hlocal p.1 hp
  change (H (p.1,p.2) - H (p.1,a)) / (H (p.1,b) - H (p.1,a)) = _
  rw [hB p.2,hB a,hB b]
  dsimp only [ComplexAffineTransformation.apply]
  rw [show B.slope * F p.1 p.2.val + B.translation - (B.slope * F p.1 a.val + B.translation) =
    B.slope * (F p.1 p.2.val - F p.1 a.val) by ring,
    show B.slope * F p.1 b.val + B.translation - (B.slope * F p.1 a.val + B.translation) =
    B.slope * (F p.1 b.val - F p.1 a.val) by ring,
    mul_div_mul_left _ _ B.slope_ne_zero]

/-- Continuous ambient representatives and local affine coordinates assemble into globally normalized target charts on a connected source. -/
theorem continuous_normalized_complete_coordinate_family_g1
    {T X Z : Type*} [TopologicalSpace T] [CompactSpace T]
    [TopologicalSpace X] [TopologicalSpace Z]
    (e : X ≃ₜ ℂ) (Y : T → Type*) [∀ t, TopologicalSpace (Y t)]
    [∀ t, ChartedSpace (ComplexModel 1) (Y t)]
    (A : ∀ t, ComplexAffineStructure (Y t))
    (D : ∀ t, Diffeomorph (complexModel 1) 𝓘(ℂ) (Y t) ℂ ∞)
    (hD : ∀ t c, c ∈ (A t).out.charts → ∀ x ∈ c.source,
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D t y = b.apply (c y))
    (h : ∀ t, OpenPartialHomeomorph X (Y t)) (i : ∀ t, Y t → Z)
    {W₀ : Set X} (hW₀ : IsOpen W₀) {x₀ : X} (hx₀ : x₀ ∈ W₀)
    (hsource : ∀ t, W₀ ⊆ (h t).source)
    (hE : ContinuousOn (fun p : T × X ↦ i p.1 (h p.1 p.2)) (univ ×ˢ W₀))
    (hloc : ∀ z : Z, ∃ (O : Set Z) (K : Z → ℂ), IsOpen O ∧ z ∈ O ∧
      ContinuousOn K O ∧ ∀ t y, i t y ∈ O →
        ∃ c : OpenPartialHomeomorph (Y t) ℂ,
          c ∈ (A t).maximalAtlas (Y t) ∧ y ∈ c.source ∧
          ∀ᶠ y' in 𝓝 y, c y' = K (i t y')) :
    ∃ (U : Set X) (c : ∀ t, OpenPartialHomeomorph (Y t) ℂ),
      IsOpen U ∧ IsConnected U ∧ x₀ ∈ U ∧ U ⊆ W₀ ∧
      (∀ t, c t ∈ (A t).maximalAtlas (Y t) ∧ (c t).source = univ) ∧
      Continuous (fun p : T × U ↦ c p.1 (h p.1 p.2.val)) := by
  classical
  let E : T × X → Z := fun p ↦ i p.1 (h p.1 p.2)
  choose O K hO hEO hK hKl using fun t ↦ hloc (E (t,x₀))
  obtain ⟨W,hW,hxW,hWW₀,hcover⟩ := compact_family_common_source_neighborhood_g1
    E hW₀ hE hx₀ O hO hEO
  obtain ⟨U,y,hU,hconn,hxU,hUW,hyU,hxy⟩ :=
    plane_coordinate_two_anchor_neighborhood_g1 e hW hxW
  have hUW₀ : U ⊆ W₀ := hUW.trans hWW₀
  let F (t : T) := (h t).trans (D t).toHomeomorph.toOpenPartialHomeomorph
  have hFs (t : T) : U ⊆ (F t).source := fun _ hx ↦
    ⟨hsource t (hUW₀ hx),mem_univ _⟩
  have hDmax (t : T) : (D t).toHomeomorph.toOpenPartialHomeomorph ∈
      (A t).maximalAtlas (Y t) :=
    ⟨⟨(D t).contMDiff.contMDiffOn,(D t).symm.contMDiff.contMDiffOn⟩,
      fun c hc x hx ↦ hD t c hc x hx.1⟩
  have hlocal (t₀ : T) : ∃ (V : Set T) (H : T × U → ℂ), IsOpen V ∧ t₀ ∈ V ∧
      ContinuousOn H (V ×ˢ univ) ∧ ∀ t ∈ V, ∃ B : ComplexAffineTransformation,
        ∀ x : U, H (t,x) = B.apply (F t x.val) := by
    obtain ⟨j,V,hV,htV,hEV⟩ := hcover t₀
    let H : T × U → ℂ := fun p ↦ K j (E (p.1,p.2.val))
    refine ⟨V,H,hV,htV,?_,?_⟩
    · apply (hK j).comp
        (hE.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
          (fun p _ ↦ ⟨mem_univ _,hUW₀ p.2.property⟩))
      intro p hp
      exact hEV ⟨hp.1,hUW p.2.property⟩
    · intro t ht
      obtain ⟨B,hB⟩ := affine_of_locally_affine_on_connected_g1
        (fun w ↦ K j (E (t,w))) (F t) (hFs t) hconn.2 hxU (by
          intro w
          obtain ⟨c,hc,hwc,hcgerm⟩ := hKl j t (h t w.val)
            (show E (t,w.val) ∈ O j from hEV ⟨ht,hUW w.property⟩)
          obtain ⟨B,hBgerm⟩ := maximal_affine_charts_compatible_g1 (A t)
            (D t).toHomeomorph.toOpenPartialHomeomorph c (hDmax t) hc
            (h t w.val) ⟨mem_univ _,hwc⟩
          refine ⟨B,?_⟩
          have hh := (h t).continuousAt (hsource t (hUW₀ w.property))
          filter_upwards [hh hcgerm,hh hBgerm] with v hv hv'
          exact hv.symm.trans hv')
      exact ⟨B,fun w ↦ hB w.val w.property⟩
  have hn := continuous_normalized_affine_family_of_local_representatives_g1 U F hFs
    ⟨x₀,hxU⟩ ⟨y,hyU⟩ (fun he ↦ hxy (congrArg Subtype.val he)) hlocal
  have hne (t : T) : h t x₀ ≠ h t y := fun he ↦ hxy
    ((h t).injOn (hsource t (hUW₀ hxU)) (hsource t (hUW₀ hyU)) he)
  choose c hc hcs hce using fun t ↦ affine_global_developing_normalized_chart_g1
    (A t) (D t) (hD t) (h t x₀) (h t y) (hne t)
  refine ⟨U,c,hU,hconn,hxU,hUW₀,fun t ↦ ⟨hc t,hcs t⟩,?_⟩
  apply hn.congr
  intro p
  exact (hce p.1 (h p.1 p.2.val)).symm

/-- The affine part of stable-prefix continuity follows from the common-source prefix family and complete affine leaves. -/
theorem affine_prefix_coordinates_of_ambient_continuous_family_g1
    {s : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+2) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s 2 M)
    (C : IntrinsicComplexUnstableLeaves F) (A : AffineUnstableLeafStructures F C)
    (hcomplete : ∀ q : Quotient F.unstablePartition,
      letI := F.unstableTopology q
      letI := C.charts q
      (A.structureAt q).Complete (IntrinsicFoliationLeaf F.unstablePartition q))
    (hlocal : ∀ x : M, ∃ (O : Set M) (K : M → ℂ), IsOpen O ∧ x ∈ O ∧
      ContinuousOn K O ∧ ∀ q : Quotient F.unstablePartition,
        letI := F.unstableTopology q
        letI := C.charts q
        ∀ y : IntrinsicFoliationLeaf F.unstablePartition q, y.val ∈ O →
          ∃ c : OpenPartialHomeomorph (IntrinsicFoliationLeaf F.unstablePartition q) ℂ,
            c ∈ (A.structureAt q).maximalAtlas _ ∧ y ∈ c.source ∧
            ∀ᶠ y' in 𝓝 y, c y' = K y'.val)
    (hprefix : ∀ (q : Quotient F.stablePartition)
      (a b : IntrinsicFoliationLeaf F.stablePartition q) (γ : Path a b)
      (H : LocalHolonomyContinuation F γ),
      ∃ h : ∀ r : unitInterval, PathHolonomyRepresentative F γ 0 r,
        (∀ r : unitInterval,
          Filter.Germ.ofFun (h r).map =
            (Filter.Germ.ofFun (prefixHolonomy F γ H r) :
              Filter.Germ (𝓝 (F.uPoint (γ 0).val)) (F.ULeaf (γ r).val))) ∧
      ∃ W : Set (F.ULeaf (γ 0).val), IsOpen W ∧ F.uPoint (γ 0).val ∈ W ∧
        (∀ r, W ⊆ (h r).map.source) ∧
        ContinuousOn (fun p : unitInterval × F.ULeaf (γ 0).val ↦
          ((h p.1).map p.2).val) (univ ×ˢ W)) :
    A.HasContinuousPrefixCoordinates F C := by
  classical
  intro q a b γ H
  obtain ⟨h,hgerm,W,hW,hxW,hsource,hcont⟩ := hprefix q a b γ H
  let Y (r : unitInterval) := F.ULeaf (γ r).val
  let (r : unitInterval) : TopologicalSpace (Y r) := F.uLeafTopology (γ r).val
  let (r : unitInterval) : ChartedSpace (ComplexModel 1) (Y r) :=
    C.charts (Quotient.mk F.unstablePartition (γ r).val)
  have hdev (r : unitInterval) := (hcomplete
    (Quotient.mk F.unstablePartition (γ r).val)).2
  choose D hD using hdev
  obtain ⟨U,c,hU,hconn,hxU,hUW,hc,hccont⟩ :=
    continuous_normalized_complete_coordinate_family_g1 (D 0).toHomeomorph Y
      (fun r ↦ A.atPoint F C (γ r).val) D hD (fun r ↦ (h r).map)
      (fun _ y ↦ y.val) hW hxW hsource hcont (by
        intro x
        obtain ⟨O,K,hO,hx,hK,hKl⟩ := hlocal x
        exact ⟨O,K,hO,hx,hK,fun r ↦ hKl (Quotient.mk F.unstablePartition (γ r).val)⟩)
  refine ⟨h,hgerm,U,hU,hconn,hxU,fun r ↦ hUW.trans (hsource r),c,
    fun r ↦ (hc r).1,?_,?_⟩
  · intro r w hw
    rw [(hc r).2]
    exact mem_univ _
  · intro w hw
    exact hccont.comp (continuous_id.prodMk (continuous_const (y := (⟨w,hw⟩ : U))))

/-- The invariant jet-induced affine structures transported to the supplied presentation admit common-source continuous affine coordinates for every stable prefix path. (Ghys, Prop. 3.1(ii)) -/
theorem native_affine_holonomy_coordinates_g1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : AnosovIntrinsicFoliationPresentation f a)
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    : letI := P.realCharts
    ∀ (A : AffineUnstableLeafStructures P.foliations P.complexLeaves),
      (∀ q : Quotient P.foliations.unstablePartition,
        letI := P.foliations.unstableTopology q
        letI := P.complexLeaves.charts q
        ∃ (i : ι) (T : Diffeomorph (complexModel 1) (complexModel 1) (L i)
            (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ∞),
          (∀ z, (T z).val = (U.leaf i).inclusion z) ∧
          ∀ e : OpenPartialHomeomorph
              (IntrinsicFoliationLeaf P.foliations.unstablePartition q) ℂ,
            e ∈ ComplexAffineStructure.maximalAtlas _ (A.structureAt q) ↔
              T.toHomeomorph.toOpenPartialHomeomorph.trans e ∈
                ComplexAffineStructure.maximalAtlas _ (G.affineAt f a L U i)) →
      A.HasContinuousPrefixCoordinates P.foliations P.complexLeaves := by
  classical
  let := P.realCharts
  intro A hA
  have hcomp (q : Quotient P.foliations.unstablePartition) :
      letI := P.foliations.unstableTopology q
      letI := P.complexLeaves.charts q
      (A.structureAt q).Complete (IntrinsicFoliationLeaf P.foliations.unstablePartition q) := by
    let := P.foliations.unstableTopology q
    let := P.complexLeaves.charts q
    obtain ⟨i,T,hT,hmax⟩ := hA q
    obtain ⟨D,hD⟩ := (affine_completeness f a L U G i).1.2
    let E := T.symm.trans D
    have hDmax : D.toHomeomorph.toOpenPartialHomeomorph ∈
        (G.affineAt f a L U i).maximalAtlas (L i) :=
      ⟨⟨D.contMDiff.contMDiffOn,D.symm.contMDiff.contMDiffOn⟩,
        fun c hc x hx ↦ hD c hc x hx.1⟩
    have hEmax : E.toHomeomorph.toOpenPartialHomeomorph ∈ (A.structureAt q).maximalAtlas _ := by
      apply (hmax _).mpr
      have heq : T.toHomeomorph.toOpenPartialHomeomorph.trans
          E.toHomeomorph.toOpenPartialHomeomorph = D.toHomeomorph.toOpenPartialHomeomorph := by
        change T.toHomeomorph.toOpenPartialHomeomorph.trans
          (T.toHomeomorph.symm.trans D.toHomeomorph).toOpenPartialHomeomorph = _
        rw [Homeomorph.trans_toOpenPartialHomeomorph,← OpenPartialHomeomorph.trans_assoc,
          ← Homeomorph.trans_toOpenPartialHomeomorph,Homeomorph.self_trans_symm]
        exact OpenPartialHomeomorph.refl_trans _
      rwa [heq]
    exact ⟨E.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace,E,
      fun c hc x hx ↦ hEmax.2 c hc x ⟨hx,mem_univ _⟩⟩
  apply affine_prefix_coordinates_of_ambient_continuous_family_g1 P.foliations P.complexLeaves A
    hcomp (native_local_affine_coordinate_on_presentation_g1 f a P L U G A hA)
  intro q x y γ H
  obtain ⟨h,W,hW,hxW,hsource,hcont⟩ := path_continuous_prefix_family_g1 P.foliations γ
  refine ⟨h,?_,W,hW,hxW,hsource,hcont⟩
  intro r
  exact (local_continuation_representative_germ P.foliations γ H 0 r bot_le (h r)).symm

end HolomorphicAnosov.Ghys


