import HolomorphicAnosov.Dynamics.Anosov.StablePathIterateLength
import HolomorphicAnosov.Geometry.NativeIdentificationPartitionAsymptotic
import HolomorphicAnosov.Geometry.NativeIdentificationStablePlaqueLiftG18
import HolomorphicAnosov.Geometry.Holonomy.ConnectedRangeInBox
import HolomorphicAnosov.Geometry.NativePlaqueFamilyCoordinateJet

noncomputable section
open Set Filter Manifold TopologicalSpace _root_.Topology
open scoped ContDiff _root_.Topology
namespace HolomorphicAnosov
universe u v
attribute [local instance] complex_isManifold_real

/-- A stable plaque family anchored on an open receiving transversal is an ambient open product when
its plaques stay in the receiving box and in their stable partition classes. (Hirsch–Pugh–Shub,
§7, pp. 115–116) -/
theorem native_identification_stable_family_product_open_g18
    {d s t r : ℕ} {M : Type u}
    [MetricSpace M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,v} f Ps Pu s t) {center : M}
    (F : NativePlaqueFamily (realModel d) (V := Fin r → ℝ) Ps center)
    (R : ℝ) (hR : 0 < R) (hRF : R ≤ F.radius) :
    letI := A.realAmbientCharts
    (∀ p : F.centerDomain, ∀ v ∈ Metric.ball (0 : Fin r → ℝ) F.radius,
      A.F.stablePartition p.val ((F.plaque p).param v)) →
    ∀ (b : A.F.boxIndex) (s₀ : FoliationCoordinateDisk s)
      (T : Opens (FoliationCoordinateDisk t))
      (hcenter : ∀ t : T, ((A.F.box b).chart (s₀,t.val)).val ∈ F.centerDomain),
      let U : Opens (Fin r → ℝ) := ⟨Metric.ball 0 R,Metric.isOpen_ball⟩
      let J : U × T → M := fun p ↦
        (F.plaque ⟨((A.F.box b).chart (s₀,p.2.val)).val,hcenter p.2⟩).param p.1.val
      ∀ hbox : ∀ p, J p ∈ (A.F.box b).image,
        IsOpenEmbedding J ∧ ∀ p, ((A.F.box b).chart.symm ⟨J p,hbox p⟩).2 = p.2.val := by
  let := A.realAmbientCharts
  intro hstable b s₀ T hcenter
  dsimp only
  let U : Opens (Fin r → ℝ) := ⟨Metric.ball 0 R,Metric.isOpen_ball⟩
  let anchor : T → F.centerDomain := fun t ↦
    ⟨((A.F.box b).chart (s₀,t.val)).val,hcenter t⟩
  let J : U × T → M := fun p ↦ (F.plaque (anchor p.2)).param p.1.val
  intro hbox
  have hanchor : Continuous anchor :=
    (continuous_subtype_val.comp ((A.F.box b).chart.continuous.comp
      (continuous_const.prodMk continuous_subtype_val))).subtype_mk _
  have hJ : Continuous J := F.jointly_continuous.comp
    ((hanchor.comp continuous_snd).prodMk
      ((continuous_subtype_val.comp continuous_fst).subtype_mk
        (fun p ↦ Metric.ball_subset_ball hRF p.1.property)))
  have hleaf (t : T) (v : U) :
      Quotient.mk A.F.stablePartition (J (v,t)) = A.F.stableLabel b t.val := by
    have h := hstable (anchor t) v.val (Metric.ball_subset_ball hRF v.property)
    exact (Quotient.sound (A.F.stablePartition.symm h)).trans
      (A.F.stable_label b s₀ t.val)
  have hlift (t : T) :
      letI := A.F.stableTopology (A.F.stableLabel b t.val)
      ∃ g : U → IntrinsicFoliationLeaf A.F.stablePartition (A.F.stableLabel b t.val),
        IsOpenEmbedding g ∧ ∀ v, (g v).val = J (v,t) := by
    have heq : A.F.stableLabel b t.val =
        Quotient.mk A.F.stablePartition (anchor t).val :=
      (A.F.stable_label b s₀ t.val).symm
    rw [heq]
    let := A.F.stableTopology (Quotient.mk A.F.stablePartition (anchor t).val)
    obtain ⟨g,hg,ho⟩ := native_identification_embedded_stable_plaque_open_lift_g18 A
      (F.plaque (anchor t)) (anchor t).val
      (fun v hv ↦ hstable (anchor t) v (by rwa [F.domain_eq] at hv))
    have hsub : (U : Set (Fin r → ℝ)) ⊆ (F.plaque (anchor t)).domain := by
      rw [F.domain_eq]
      exact Metric.ball_subset_ball hRF
    let e : U → (F.plaque (anchor t)).domain := Set.inclusion hsub
    have he : IsOpenEmbedding e := IsOpenEmbedding.inclusion hsub
      (U.isOpen.preimage continuous_subtype_val)
    exact ⟨g ∘ e,ho.comp he,fun v ↦ hg (e v)⟩
  have hcoord (p : U × T) :
      ((A.F.box b).chart.symm ⟨J p,hbox p⟩).2 = p.2.val := by
    let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp
      (convex_ball (0 : Fin r → ℝ) R).isPreconnected
    let q := A.F.stableLabel b p.2.val
    let := A.F.stableTopology q
    have hcount : SecondCountableTopology
        (IntrinsicFoliationLeaf A.F.stablePartition q) := by
      have heq : q = Quotient.mk A.F.stablePartition (anchor p.2).val :=
        (A.F.stable_label b s₀ p.2.val).symm
      change @SecondCountableTopology
        (IntrinsicFoliationLeaf A.F.stablePartition q) (A.F.stableTopology q)
      rw [heq]
      let := A.stableTopology (anchor p.2).val
      let := (A.nativeS (anchor p.2).val).secondCountable
      exact (A.stableClassHomeomorph (anchor p.2).val).secondCountableTopology
    let := hcount
    let z : U := ⟨0,Metric.mem_ball_self hR⟩
    have hc := stable_connected_range_in_box A.F b q
      (fun v : U ↦ J (v,p.2)) (hJ.comp (continuous_id.prodMk continuous_const))
      (fun v ↦ hbox (v,p.2)) (hleaf p.2) inferInstance p.1 z
    have hzero : J (z,p.2) = ((A.F.box b).chart (s₀,p.2.val)).val :=
      (F.plaque (anchor p.2)).centered
    have he : (⟨J (z,p.2),hbox (z,p.2)⟩ : (A.F.box b).image) =
        (A.F.box b).chart (s₀,p.2.val) := Subtype.ext hzero
    exact hc.trans (congrArg Prod.snd ((congrArg (A.F.box b).chart.symm he).trans
      ((A.F.box b).chart.symm_apply_apply _)))
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  exact ⟨stable_plaque_product_open_embedding A.F b T J hJ hbox hcoord hlift,hcoord⟩


/-- Near a marked receiving-box point, a stable plaque family restricts to an ambient open product
contained in that box. -/
theorem native_identification_stable_family_local_product_g18
    {d s t r : ℕ} {M : Type u}
    [MetricSpace M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u,v} f Ps Pu s t) {center : M}
    (F : NativePlaqueFamily (realModel d) (V := Fin r → ℝ) Ps center) :
    letI := A.realAmbientCharts
    (∀ p : F.centerDomain, ∀ v ∈ Metric.ball (0 : Fin r → ℝ) F.radius,
      A.F.stablePartition p.val ((F.plaque p).param v)) →
    ∀ (b : A.F.boxIndex) (s₀ : FoliationCoordinateDisk s)
      (t₀ : FoliationCoordinateDisk t),
      ((A.F.box b).chart (s₀,t₀)).val = center →
      ∃ R : ℝ, 0 < R ∧ R < F.radius ∧
      ∃ T : Opens (FoliationCoordinateDisk t), t₀ ∈ T ∧
      ∃ hcenter : ∀ t : T, ((A.F.box b).chart (s₀,t.val)).val ∈ F.centerDomain,
      let U : Opens (Fin r → ℝ) := ⟨Metric.ball 0 R,Metric.isOpen_ball⟩
      let J : U × T → M := fun p ↦
        (F.plaque ⟨((A.F.box b).chart (s₀,p.2.val)).val,hcenter p.2⟩).param p.1.val
      ∃ hbox : ∀ p, J p ∈ (A.F.box b).image,
        IsOpenEmbedding J ∧ ∀ p, ((A.F.box b).chart.symm ⟨J p,hbox p⟩).2 = p.2.val := by
  let := A.realAmbientCharts
  intro hstable b s₀ t₀ hmark
  let p₀ : F.centerDomain := ⟨center,F.center_mem⟩
  have hcm : center ∈ (A.F.box b).image :=
    hmark ▸ ((A.F.box b).chart (s₀,t₀)).property
  have hn : (fun z : F.centerDomain × (Fin r → ℝ) ↦ (F.plaque z.1).param z.2) ⁻¹'
      (A.F.box b).image ∈ 𝓝 (p₀,0) :=
    F.continuousAt_centered_param ((A.F.box b).isOpen_image.mem_nhds
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
  let β : FoliationCoordinateDisk t → M := fun t ↦ ((A.F.box b).chart (s₀,t)).val
  have hβ : Continuous β := continuous_subtype_val.comp
    ((A.F.box b).chart.continuous.comp (continuous_const.prodMk continuous_id))
  let T : Opens (FoliationCoordinateDisk t) :=
    ⟨β ⁻¹' (Subtype.val '' N),
      (F.centerDomain_open.isOpenMap_subtype_val N hN).preimage hβ⟩
  have ht₀ : t₀ ∈ T := ⟨p₀,hpN,hmark.symm⟩
  have hcenter (t : T) : β t.val ∈ F.centerDomain := by
    obtain ⟨q,_,hq⟩ := t.property
    exact hq ▸ q.property
  let U : Opens (Fin r → ℝ) := ⟨Metric.ball 0 R,Metric.isOpen_ball⟩
  have hbox (p : U × T) :
      (F.plaque ⟨β p.2.val,hcenter p.2⟩).param p.1.val ∈ (A.F.box b).image := by
    obtain ⟨q,hq,hqval⟩ := p.2.property
    have he : (⟨β p.2.val,hcenter p.2⟩ : F.centerDomain) = q := Subtype.ext hqval.symm
    rw [he]
    have hv : p.1.val ∈ W := hηW (Metric.ball_subset_ball hRη.le p.1.property)
    exact @hNW (q,p.1.val) ⟨hq,hv⟩
  refine ⟨R,hR,hRF,T,ht₀,hcenter,hbox,?_⟩
  exact native_identification_stable_family_product_open_g18 A F R hR hRF.le
    hstable b s₀ T hcenter hbox


/-- Anosov stable contraction places every point of a stable plaque in its anchor's identified
stable partition class. (Hirsch–Pugh–Shub, §7) -/
theorem native_identification_anosov_stable_plaque_class_g18
    {d s t : ℕ} {M : Type u} {V : Type*} [m0 : MetricSpace M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (A : NativeTransverseAsymptoticIdentification.{u,u} f.toHomeomorph
      a.splitting.stable.toDistribution a.splitting.unstable.toDistribution s t)
    {center : M} (F : NativePlaqueFamily (realModel d) (V := V)
      a.splitting.stable.toDistribution center)
    (p : F.centerDomain) (v : V) (hv : v ∈ Metric.ball (0 : V) F.radius) :
    letI := A.realAmbientCharts
    A.F.stablePartition p.val ((F.plaque p).param v) := by
  let := A.realAmbientCharts
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨m,hmTop,hm⟩ := anosov_exists_full_length_metric f a
  let : MetricSpace M := m0
  obtain ⟨r,hvr,hr⟩ := exists_between (show ‖v‖ < F.radius by simpa using hv)
  have hr0 : 0 < r := (norm_nonneg v).trans_lt hvr
  have hdist : @ForwardAsymptotic M m f p.val ((F.plaque p).param v) := by
    apply tendsto_order.mpr
    constructor
    · intro b hb
      exact Filter.Eventually.of_forall (fun n ↦ hb.trans_le
        (@dist_nonneg M m.toPseudoMetricSpace _ _))
    · intro ε hε
      filter_upwards [anosov_native_stable_plaque_uniform_shrinking f a m hm F
        {p} isCompact_singleton hr0 hr ε hε] with n hn
      exact hn p (Set.mem_singleton p) v (by simpa using hvr.le)
  have hu : m0.toUniformSpace = m.toUniformSpace :=
    unique_uniformity_of_compact rfl hmTop
  apply (native_identification_stable_partition_iff_asymptotic A _ _).mpr
  change @ForwardAsymptotic M m0 (f : M → M) p.val ((F.plaque p).param v)
  have h₁ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ m0.toPseudoMetricSpace
    (fun n ↦ (((f : M → M)^[n]) ((F.plaque p).param v), ((f : M → M)^[n]) p.val)) atTop
  have h₂ := @tendsto_uniformity_iff_dist_tendsto_zero M ℕ m.toPseudoMetricSpace
    (fun n ↦ (((f : M → M)^[n]) ((F.plaque p).param v), ((f : M → M)^[n]) p.val)) atTop
  unfold ForwardAsymptotic at hdist ⊢
  rw [← h₁]
  rw [← h₂] at hdist
  change Tendsto _ _ m0.toUniformSpace.uniformity
  have heu : m0.toUniformSpace.uniformity = m.toUniformSpace.uniformity :=
    congrArg (fun u : UniformSpace M ↦ u.uniformity) hu
  rw [heu]
  exact hdist

/-- An Anosov stable plaque family admits an ambient open local product near a marked receiving-box
point. -/
theorem native_identification_anosov_stable_family_local_product_g18
    {d s t r : ℕ} {M : Type u}
    [MetricSpace M] [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (A : NativeTransverseAsymptoticIdentification.{u,u} f.toHomeomorph
      a.splitting.stable.toDistribution a.splitting.unstable.toDistribution s t) {center : M}
    (F : NativePlaqueFamily (realModel d) (V := Fin r → ℝ)
      a.splitting.stable.toDistribution center) :
    letI := A.realAmbientCharts
    ∀ (b : A.F.boxIndex) (s₀ : FoliationCoordinateDisk s)
      (t₀ : FoliationCoordinateDisk t),
      ((A.F.box b).chart (s₀,t₀)).val = center →
      ∃ R : ℝ, 0 < R ∧ R < F.radius ∧
      ∃ T : Opens (FoliationCoordinateDisk t), t₀ ∈ T ∧
      ∃ hcenter : ∀ t : T, ((A.F.box b).chart (s₀,t.val)).val ∈ F.centerDomain,
      let U : Opens (Fin r → ℝ) := ⟨Metric.ball 0 R,Metric.isOpen_ball⟩
      let J : U × T → M := fun p ↦
        (F.plaque ⟨((A.F.box b).chart (s₀,p.2.val)).val,hcenter p.2⟩).param p.1.val
      ∃ hbox : ∀ p, J p ∈ (A.F.box b).image,
        IsOpenEmbedding J ∧ ∀ p, ((A.F.box b).chart.symm ⟨J p,hbox p⟩).2 = p.2.val := by
  let := A.realAmbientCharts
  exact native_identification_stable_family_local_product_g18 A F
    (fun p v hv ↦ native_identification_anosov_stable_plaque_class_g18 f a A F p v hv)

end HolomorphicAnosov
