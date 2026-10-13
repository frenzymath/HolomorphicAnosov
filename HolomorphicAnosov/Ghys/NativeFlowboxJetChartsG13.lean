import HolomorphicAnosov.Ghys.NativeLeafwiseParametrizationJetBundle
import HolomorphicAnosov.Geometry.OpenDiffeomorphMaximalChartField
import HolomorphicAnosov.Ghys.NativeLeafwiseJetFlowboxContinuity
import HolomorphicAnosov.Ghys.CurveJetTruncationBase

/-! Native flowbox coefficient charts on leafwise jet quotients. Source: Ghys §3 pp.591–592. -/

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter TopologicalSpace
open scoped _root_.Topology Manifold ContDiff
universe u
variable {ι : Type u} (L : ι → Type u)
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
variable [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
variable {d : ℕ} {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real Classical.propDecidable
variable [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
variable {D : RealTangentDistribution (realModel d) M}
variable (U : HPS.LeafPartition D ι L (fun _ ↦ 2))

omit [IsManifold (complexModel d) ∞ M] in
/-- The receiving branch of a genuine native flowbox gives an intrinsic compatible chart at any original leaf point in its source. Source: Ghys (1995), §3 pp.591–592. -/
theorem native_flowbox_receiving_chart
    {s : ℕ} (T : Opens (Fin s → ℝ))
    (c : OpenPartialHomeomorph M (ℂ × (Fin s → ℝ)))
    (label : T → ι) (branch : ∀ t, Opens (L (label t)))
    (parametrization : ∀ t : T, Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
      (⟨{z | (z, t.val) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
      (branch t) ∞)
    (htarget : ∀ p ∈ c.target, p.2 ∈ T)
    (hparam : ∀ t z, c.symm (z.val, t.val) =
      (U.leaf (label t)).inclusion (parametrization t z).val)
    (ell : ι) (x : L ell) (hx : (U.leaf ell).inclusion x ∈ c.source) :
    ∃ q : LeafChart (L ell), x ∈ q.1.source ∧
      q.1.target = {z | (z, (c ((U.leaf ell).inclusion x)).2) ∈ c.target} ∧
      (∀ v ∈ q.1.source, (U.leaf ell).inclusion v ∈ c.source ∧
        c ((U.leaf ell).inclusion v) = (q.1 v, (c ((U.leaf ell).inclusion x)).2)) ∧
      (∀ gamma : CurveParamGerm (L ell),
        curveGermBase (L ell) gamma.1 ∈ q.1.source →
        gamma.1.map (nativeLeafFlowboxScalar L U c ell) =
          gamma.1.map (q.1 : L ell → ℂ)) := by
  obtain ⟨t, z, he, hlabel⟩ : ∃ t : T,
      ∃ z : (⟨{z | (z, t.val) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ),
      (U.leaf (label t)).inclusion (parametrization t z).val =
        (U.leaf ell).inclusion x ∧ label t = ell := by
    let p := c ((U.leaf ell).inclusion x)
    have hp : p ∈ c.target := c.map_source hx
    let t : T := ⟨p.2, htarget p hp⟩
    let z : (⟨{z | (z, t.val) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ) :=
      ⟨p.1, hp⟩
    have he : (U.leaf (label t)).inclusion (parametrization t z).val =
        (U.leaf ell).inclusion x := by
      rw [← hparam t z]
      exact c.left_inv hx
    exact ⟨t, z, he, U.disjoint _ _ _ _ he⟩
  subst ell
  have hx' := (U.leaf (label t)).injective he
  subst x
  obtain ⟨q, hq, hs, ht, hi, hf⟩ :=
    open_diffeomorph_maximal_chart_field _ _ z (parametrization t)
  have hcoord (v : branch t) :
      (U.leaf (label t)).inclusion v.val ∈ c.source ∧
      c ((U.leaf (label t)).inclusion v.val) = (q v.val, t.val) := by
    let w := (parametrization t).symm v
    have hv : (parametrization t w).val = v.val :=
      congrArg Subtype.val ((parametrization t).apply_symm_apply v)
    rw [hf v, ← hv, ← hparam t w]
    exact ⟨c.map_target w.property, c.right_inv w.property⟩
  have hmap (gamma : CurveParamGerm (L (label t)))
      (hb : curveGermBase (L (label t)) gamma.1 ∈ q.source) :
      gamma.1.map (nativeLeafFlowboxScalar L U c (label t)) =
        gamma.1.map (q : L (label t) → ℂ) := by
    obtain ⟨g, hg0, _, _, hge⟩ := gamma.2
    have hbase : curveGermBase (L (label t)) gamma.1 = g 0 := by
      rw [← hge]
      rfl
    have hnear : ∀ᶠ v in 𝓝 (0 : ℂ), g v ∈ branch t :=
      (g.continuousAt hg0).eventually ((branch t).isOpen.mem_nhds
        (by simpa only [hs, hbase, SetLike.mem_coe] using hb))
    rw [← hge]
    apply Filter.Germ.coe_eq.mpr
    exact hnear.mono (fun v hv ↦ congrArg Prod.fst (hcoord ⟨g v, hv⟩).2)
  refine ⟨⟨q, hq⟩, ?_, ?_, ?_, hmap⟩
  · rw [hs]
    exact (parametrization t z).property
  · rw [(hcoord (parametrization t z)).2]
    exact ht
  · intro v hv
    rw [(hcoord (parametrization t z)).2]
    exact hcoord ⟨v, by simpa only [hs, SetLike.mem_coe] using hv⟩


variable [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)]

omit [IsManifold (complexModel d) ∞ M] in
/-- Native flowbox first coefficients parametrize the actual first-contact quotient. Source: Ghys (1995), §3 p.591. -/
theorem native_flowbox_jet1_bijOn
    {s : ℕ} (T : Opens (Fin s → ℝ))
    (c : OpenPartialHomeomorph M (ℂ × (Fin s → ℝ)))
    (label : T → ι) (branch : ∀ t, Opens (L (label t)))
    (parametrization : ∀ t : T, Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
      (⟨{z | (z, t.val) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
      (branch t) ∞)
    (htarget : ∀ p ∈ c.target, p.2 ∈ T)
    (hparam : ∀ t z, c.symm (z.val, t.val) =
      (U.leaf (label t)).inclusion (parametrization t z).val) :
    BijOn (nativeLeafwiseJet1Coeff L U c)
      {j | nativeLeafwiseJet1Base L U j ∈ c.source}
      {w | w.1 ∈ c.target ∧ w.2 ≠ 0} := by
  have hchart := native_flowbox_receiving_chart L U T c label branch parametrization
    htarget hparam
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨ell, j⟩ hj
    obtain ⟨q, hq, _, _, hm⟩ := hchart ell (curveJet1Base (L ell) j) hj
    refine ⟨c.map_source hj, ?_⟩
    have hne := ((leaf_jet_complex_manifold (L ell)).2.2.2.1 q).1.mapsTo hq
    change germFirst (j.out.1.map (nativeLeafFlowboxScalar L U c ell)) ≠ 0
    rw [hm j.out hq]
    exact hne.2
  · rintro ⟨ell, j⟩ hj ⟨ell', j'⟩ hj' he
    have hb : (U.leaf ell).inclusion (curveJet1Base (L ell) j) =
        (U.leaf ell').inclusion (curveJet1Base (L ell') j') :=
      c.injOn hj hj' (congrArg Prod.fst he)
    have hl : ell = ell' := U.disjoint _ _ _ _ hb
    subst ell'
    have hb' := (U.leaf ell).injective hb
    obtain ⟨q, hq, _, _, hm⟩ := hchart ell (curveJet1Base (L ell) j) hj
    have hq' : curveJet1Base (L ell) j' ∈ q.1.source := hb' ▸ hq
    have he' := congrArg Prod.snd he
    change germFirst (j.out.1.map (nativeLeafFlowboxScalar L U c ell)) =
      germFirst (j'.out.1.map (nativeLeafFlowboxScalar L U c ell)) at he'
    rw [hm j.out hq, hm j'.out hq'] at he'
    have hjj : j = j' := ((leaf_jet_complex_manifold (L ell)).2.2.2.1 q).1.injOn
      hq hq' (Prod.ext (congrArg q.1 hb') he')
    cases hjj
    rfl
  · intro w hw
    let t : T := ⟨w.1.2, htarget w.1 hw.1⟩
    let z : (⟨{z | (z, t.val) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ) :=
      ⟨w.1.1, hw.1⟩
    let x := (parametrization t z).val
    have hx : (U.leaf (label t)).inclusion x ∈ c.source := by
      rw [← hparam t z]
      exact c.map_target hw.1
    have hcx : c ((U.leaf (label t)).inclusion x) = w.1 := by
      rw [← hparam t z]
      exact c.right_inv hw.1
    obtain ⟨q, hq, ht, hc, hm⟩ := hchart (label t) x hx
    have htarget' : (q.1 x, w.2) ∈ curveJet1Target (L (label t)) q :=
      ⟨q.1.map_source hq, hw.2⟩
    obtain ⟨j, hj, hcoeff⟩ :=
      ((leaf_jet_complex_manifold (L (label t))).2.2.2.1 q).1.surjOn htarget'
    have hbase : curveJet1Base (L (label t)) j = x :=
      q.1.injOn hj hq (congrArg Prod.fst hcoeff)
    refine ⟨⟨label t, j⟩, ?_, ?_⟩
    · change (U.leaf (label t)).inclusion (curveJet1Base (L (label t)) j) ∈ c.source
      rwa [hbase]
    · apply Prod.ext
      · change c ((U.leaf (label t)).inclusion (curveJet1Base (L (label t)) j)) = w.1
        rwa [hbase]
      · change germFirst (j.out.1.map (nativeLeafFlowboxScalar L U c (label t))) = w.2
        rw [hm j.out hj]
        exact congrArg Prod.snd hcoeff

omit [IsManifold (complexModel d) ∞ M] in
/-- Native flowbox second coefficients parametrize the actual second-contact quotient. Source: Ghys (1995), §3 p.591. -/
theorem native_flowbox_jet2_bijOn
    {s : ℕ} (T : Opens (Fin s → ℝ))
    (c : OpenPartialHomeomorph M (ℂ × (Fin s → ℝ)))
    (label : T → ι) (branch : ∀ t, Opens (L (label t)))
    (parametrization : ∀ t : T, Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
      (⟨{z | (z, t.val) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
      (branch t) ∞)
    (htarget : ∀ p ∈ c.target, p.2 ∈ T)
    (hparam : ∀ t z, c.symm (z.val, t.val) =
      (U.leaf (label t)).inclusion (parametrization t z).val) :
    BijOn (nativeLeafwiseJet2Coeff L U c)
      {j | nativeLeafwiseJet2Base L U j ∈ c.source}
      {w | w.1.1 ∈ c.target ∧ w.1.2 ≠ 0} := by
  have hchart := native_flowbox_receiving_chart L U T c label branch parametrization
    htarget hparam
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨ell, j⟩ hj
    obtain ⟨q, hq, _, _, hm⟩ := hchart ell (curveJet2Base (L ell) j) hj
    refine ⟨c.map_source hj, ?_⟩
    have hne := ((leaf_jet_complex_manifold (L ell)).2.2.2.1 q).2.1.mapsTo hq
    change germFirst (j.out.1.map (nativeLeafFlowboxScalar L U c ell)) ≠ 0
    rw [hm j.out hq]
    exact hne.2
  · rintro ⟨ell, j⟩ hj ⟨ell', j'⟩ hj' he
    have hb : (U.leaf ell).inclusion (curveJet2Base (L ell) j) =
        (U.leaf ell').inclusion (curveJet2Base (L ell') j') :=
      c.injOn hj hj' (congrArg (fun w ↦ w.1.1) he)
    have hl : ell = ell' := U.disjoint _ _ _ _ hb
    subst ell'
    have hb' := (U.leaf ell).injective hb
    obtain ⟨q, hq, _, _, hm⟩ := hchart ell (curveJet2Base (L ell) j) hj
    have hq' : curveJet2Base (L ell) j' ∈ q.1.source := hb' ▸ hq
    have he' := congrArg (fun w ↦ w.1.2) he
    have he'' := congrArg Prod.snd he
    change germFirst (j.out.1.map (nativeLeafFlowboxScalar L U c ell)) =
      germFirst (j'.out.1.map (nativeLeafFlowboxScalar L U c ell)) at he'
    rw [hm j.out hq, hm j'.out hq'] at he'
    change germSecond (j.out.1.map (nativeLeafFlowboxScalar L U c ell)) =
      germSecond (j'.out.1.map (nativeLeafFlowboxScalar L U c ell)) at he''
    rw [hm j.out hq, hm j'.out hq'] at he''
    have hjj : j = j' := ((leaf_jet_complex_manifold (L ell)).2.2.2.1 q).2.1.injOn
      hq hq' (Prod.ext (Prod.ext (congrArg q.1 hb') he') he'')
    cases hjj
    rfl
  · intro w hw
    let t : T := ⟨w.1.1.2, htarget w.1.1 hw.1⟩
    let z : (⟨{z | (z, t.val) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ) :=
      ⟨w.1.1.1, hw.1⟩
    let x := (parametrization t z).val
    have hx : (U.leaf (label t)).inclusion x ∈ c.source := by
      rw [← hparam t z]
      exact c.map_target hw.1
    have hcx : c ((U.leaf (label t)).inclusion x) = w.1.1 := by
      rw [← hparam t z]
      exact c.right_inv hw.1
    obtain ⟨q, hq, ht, hc, hm⟩ := hchart (label t) x hx
    have htarget' : ((q.1 x, w.1.2), w.2) ∈ curveJet2Target (L (label t)) q :=
      ⟨q.1.map_source hq, hw.2⟩
    obtain ⟨j, hj, hcoeff⟩ :=
      ((leaf_jet_complex_manifold (L (label t))).2.2.2.1 q).2.1.surjOn htarget'
    have hbase : curveJet2Base (L (label t)) j = x :=
      q.1.injOn hj hq (congrArg (fun w ↦ w.1.1) hcoeff)
    refine ⟨⟨label t, j⟩, ?_, ?_⟩
    · change (U.leaf (label t)).inclusion (curveJet2Base (L (label t)) j) ∈ c.source
      rwa [hbase]
    · apply Prod.ext
      · apply Prod.ext
        · change c ((U.leaf (label t)).inclusion (curveJet2Base (L (label t)) j)) = w.1.1
          rwa [hbase]
        · change germFirst (j.out.1.map (nativeLeafFlowboxScalar L U c (label t))) = w.1.2
          rw [hm j.out hj]
          exact congrArg (fun w ↦ w.1.2) hcoeff
      · change germSecond (j.out.1.map (nativeLeafFlowboxScalar L U c (label t))) = w.2
        rw [hm j.out hj]
        exact congrArg Prod.snd hcoeff



variable {n s : ℕ} (T : Fin n → Opens (Fin s → ℝ))
variable (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin s → ℝ)))
variable (label : ∀ i, T i → ι) (branch : ∀ i t, Opens (L (label i t)))
variable (parametrization : ∀ i (t : T i), Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  (⟨{z | (z, t.val) ∈ (c i).target},
    (c i).open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
  (branch i t) ∞)
variable (htarget : ∀ i p, p ∈ (c i).target → p.2 ∈ T i)
variable (hparam : ∀ i t z, (c i).symm (z.val, t.val) =
  (U.leaf (label i t)).inclusion (parametrization i t z).val)

include htarget hparam in
omit [IsManifold (complexModel d) ∞ M]
  [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)] in
/-- Taylor coefficients in two native flowboxes obey the same intrinsic complex chain rule. Source: Ghys §3 p.591. -/
theorem native_flowbox_germ_transition
    (k l : Fin n) (ell : ι) (gamma : CurveParamGerm (L ell))
    (hk : (U.leaf ell).inclusion (curveGermBase (L ell) gamma.1) ∈ (c k).source)
    (hl : (U.leaf ell).inclusion (curveGermBase (L ell) gamma.1) ∈ (c l).source) :
    let p := (c k) ((U.leaf ell).inclusion (curveGermBase (L ell) gamma.1))
    let H := fun z ↦ ((c l) ((c k).symm (z, p.2))).1
    germFirst (gamma.1.map (nativeLeafFlowboxScalar L U (c l) ell)) =
      deriv H p.1 * germFirst (gamma.1.map (nativeLeafFlowboxScalar L U (c k) ell)) ∧
    germSecond (gamma.1.map (nativeLeafFlowboxScalar L U (c l) ell)) =
      deriv H p.1 * germSecond (gamma.1.map (nativeLeafFlowboxScalar L U (c k) ell)) +
        iteratedDeriv 2 H p.1 / 2 *
          germFirst (gamma.1.map (nativeLeafFlowboxScalar L U (c k) ell)) ^ 2 := by
  let x := curveGermBase (L ell) gamma.1
  obtain ⟨q, hq, _, hqc, hqm⟩ := native_flowbox_receiving_chart L U (T k) (c k)
    (label k) (branch k) (parametrization k) (htarget k) (hparam k) ell x hk
  obtain ⟨r, hr, _, hrc, hrm⟩ := native_flowbox_receiving_chart L U (T l) (c l)
    (label l) (branch l) (parametrization l) (htarget l) (hparam l) ell x hl
  let p := (c k) ((U.leaf ell).inclusion x)
  let H := fun z ↦ ((c l) ((c k).symm (z, p.2))).1
  have hp : p.1 = q.1 x := congrArg Prod.fst (hqc x hq).2
  have hnear : H =ᶠ[𝓝 (q.1 x)] (r.1 ∘ q.1.symm) := by
    have hpre : ∀ᶠ z in 𝓝 (q.1 x), q.1.symm z ∈ r.1.source := by
      have hc := q.1.continuousAt_symm (q.1.map_source hq)
      have hr' : q.1.symm (q.1 x) ∈ r.1.source := by rwa [q.1.left_inv hq]
      exact hc.eventually (r.1.open_source.mem_nhds hr')
    filter_upwards [q.1.open_target.mem_nhds (q.1.map_source hq), hpre] with z hz hzr
    have hqz := hqc (q.1.symm z) (q.1.map_target hz)
    have he : (c k) ((U.leaf ell).inclusion (q.1.symm z)) = (z, p.2) := by
      simpa only [q.1.right_inv hz] using hqz.2
    have hinv : (c k).symm (z, p.2) = (U.leaf ell).inclusion (q.1.symm z) := by
      rw [← he, (c k).left_inv hqz.1]
    change ((c l) ((c k).symm (z, p.2))).1 = r.1 (q.1.symm z)
    rw [hinv]
    exact congrArg Prod.fst (hrc (q.1.symm z) hzr).2
  change germFirst (gamma.1.map (nativeLeafFlowboxScalar L U (c l) ell)) =
      deriv H p.1 * germFirst (gamma.1.map (nativeLeafFlowboxScalar L U (c k) ell)) ∧
    germSecond (gamma.1.map (nativeLeafFlowboxScalar L U (c l) ell)) =
      deriv H p.1 * germSecond (gamma.1.map (nativeLeafFlowboxScalar L U (c k) ell)) +
        iteratedDeriv 2 H p.1 / 2 *
          germFirst (gamma.1.map (nativeLeafFlowboxScalar L U (c k) ell)) ^ 2
  rw [hqm gamma hq, hrm gamma hr, hp, hnear.deriv_eq, hnear.iteratedDeriv_eq 2]
  obtain ⟨g, hg0, hg, _, hge⟩ := gamma.2
  have hb : x = g 0 := by change curveGermBase (L ell) gamma.1 = g 0; rw [← hge]; rfl
  have hformula := curve_chart_two_jet_transport q.1 r.1 q.2 r.2 g
    (hg.contMDiffAt (g.open_source.mem_nhds hg0)) (hb ▸ hq) (hb ▸ hr)
  rw [← hge, hb]
  exact hformula



include htarget hparam in
omit [IsManifold (complexModel d) ∞ M] in
/-- Full native jet charts have precisely their prescribed coefficient-generated transverse topologies. Source: Ghys §3 pp.591–592. -/
theorem native_flowbox_jet_charts
    [Nonempty (NativeLeafwiseJet1 L)] [Nonempty (NativeLeafwiseJet2 L)]
    (hcover : ∀ x : M, ∃ k, x ∈ (c k).source)
    (hA : ∀ k l, ContinuousOn (fun p : ℂ × (Fin s → ℝ) ↦
      deriv (fun z ↦ ((c l) ((c k).symm (z, p.2))).1) p.1)
        ((c k).symm.trans (c l)).source)
    (hB : ∀ k l, ContinuousOn (fun p : ℂ × (Fin s → ℝ) ↦
      iteratedDeriv 2 (fun z ↦ ((c l) ((c k).symm (z, p.2))).1) p.1)
        ((c k).symm.trans (c l)).source) :
    letI := nativeLeafwiseJet1Topology L U c
    letI := nativeLeafwiseJet2Topology L U c
    ∃ (E1 : Fin n → OpenPartialHomeomorph (NativeLeafwiseJet1 L)
          ((ℂ × (Fin s → ℝ)) × ℂ))
      (E2 : Fin n → OpenPartialHomeomorph (NativeLeafwiseJet2 L)
          (((ℂ × (Fin s → ℝ)) × ℂ) × ℂ)),
    ∀ k, (E1 k).source = (nativeLeafwiseJet1Base L U) ⁻¹' (c k).source ∧
      (E1 k).target = {w | w.1 ∈ (c k).target ∧ w.2 ≠ 0} ∧
      (E1 k : NativeLeafwiseJet1 L → _) = nativeLeafwiseJet1Coeff L U (c k) ∧
      (E2 k).source = (nativeLeafwiseJet2Base L U) ⁻¹' (c k).source ∧
      (E2 k).target = {w | w.1.1 ∈ (c k).target ∧ w.1.2 ≠ 0} ∧
      (E2 k : NativeLeafwiseJet2 L → _) = nativeLeafwiseJet2Coeff L U (c k) := by
  let := nativeLeafwiseJet1Topology L U c
  let := nativeLeafwiseJet2Topology L U c
  let e1 (k : Fin n) : PartialEquiv (NativeLeafwiseJet1 L) ((ℂ × (Fin s → ℝ)) × ℂ) :=
    (native_flowbox_jet1_bijOn L U (T k) (c k) (label k) (branch k)
      (parametrization k) (htarget k) (hparam k)).toPartialEquiv _ _ _
  let e2 (k : Fin n) : PartialEquiv (NativeLeafwiseJet2 L) (((ℂ × (Fin s → ℝ)) × ℂ) × ℂ) :=
    (native_flowbox_jet2_bijOn L U (T k) (c k) (label k) (branch k)
      (parametrization k) (htarget k) (hparam k)).toPartialEquiv _ _ _
  have hb1 (k : Fin n) (w : (ℂ × (Fin s → ℝ)) × ℂ) (hw : w ∈ (e1 k).target) :
      nativeLeafwiseJet1Base L U ((e1 k).symm w) = (c k).symm w.1 := by
    have heq := congrArg Prod.fst ((e1 k).right_inv hw)
    change (c k) (nativeLeafwiseJet1Base L U ((e1 k).symm w)) = w.1 at heq
    rw [← heq, (c k).left_inv ((e1 k).map_target hw)]
  have hb2 (k : Fin n) (w : ((ℂ × (Fin s → ℝ)) × ℂ) × ℂ)
      (hw : w ∈ (e2 k).target) :
      nativeLeafwiseJet2Base L U ((e2 k).symm w) = (c k).symm w.1.1 := by
    have heq := congrArg (fun w ↦ w.1.1) ((e2 k).right_inv hw)
    change (c k) (nativeLeafwiseJet2Base L U ((e2 k).symm w)) = w.1.1 at heq
    rw [← heq, (c k).left_inv ((e2 k).map_target hw)]
  let O (k l : Fin n) := ((c k).symm.trans (c l)).source
  have hs1 (k l : Fin n) : ((e1 k).symm.trans (e1 l)).source =
      {w | w.1 ∈ O k l ∧ w.2 ≠ 0} := by
    ext w
    change (w ∈ (e1 k).target ∧ nativeLeafwiseJet1Base L U ((e1 k).symm w) ∈ (c l).source) ↔
      (w.1 ∈ (c k).target ∧ (c k).symm w.1 ∈ (c l).source) ∧ w.2 ≠ 0
    constructor
    · rintro ⟨hw, hl⟩
      exact ⟨⟨hw.1, by rwa [hb1 k w hw] at hl⟩, hw.2⟩
    · rintro ⟨⟨hk, hl⟩, ha⟩
      have hw : w ∈ (e1 k).target := ⟨hk, ha⟩
      exact ⟨hw, by rwa [hb1 k w hw]⟩
  have hs2 (k l : Fin n) : ((e2 k).symm.trans (e2 l)).source =
      {w | w.1.1 ∈ O k l ∧ w.1.2 ≠ 0} := by
    ext w
    change (w ∈ (e2 k).target ∧ nativeLeafwiseJet2Base L U ((e2 k).symm w) ∈ (c l).source) ↔
      (w.1.1 ∈ (c k).target ∧ (c k).symm w.1.1 ∈ (c l).source) ∧ w.1.2 ≠ 0
    constructor
    · rintro ⟨hw, hl⟩
      exact ⟨⟨hw.1, by rwa [hb2 k w hw] at hl⟩, hw.2⟩
    · rintro ⟨⟨hk, hl⟩, ha⟩
      have hw : w ∈ (e2 k).target := ⟨hk, ha⟩
      exact ⟨hw, by rwa [hb2 k w hw]⟩
  have hopen1 (k l : Fin n) : IsOpen ((e1 k).symm.trans (e1 l)).source := by
    rw [hs1]
    exact (((c k).symm.trans (c l)).open_source.preimage continuous_fst).inter
      (isOpen_ne.preimage continuous_snd)
  have hopen2 (k l : Fin n) : IsOpen ((e2 k).symm.trans (e2 l)).source := by
    rw [hs2]
    exact (((c k).symm.trans (c l)).open_source.preimage continuous_fst.fst).inter
      (isOpen_ne.preimage continuous_fst.snd)
  let A (k l : Fin n) (p : ℂ × (Fin s → ℝ)) :=
    deriv (fun z ↦ ((c l) ((c k).symm (z, p.2))).1) p.1
  let B (k l : Fin n) (p : ℂ × (Fin s → ℝ)) :=
    iteratedDeriv 2 (fun z ↦ ((c l) ((c k).symm (z, p.2))).1) p.1
  have ht1 (k l : Fin n) : ContinuousOn ((e1 k).symm.trans (e1 l))
      ((e1 k).symm.trans (e1 l)).source := by
    have hmap : MapsTo (fun w ↦ w.1) ((e1 k).symm.trans (e1 l)).source (O k l) :=
      fun w hw ↦ (hs1 k l ▸ hw).1
    have hcont := (((c k).symm.trans (c l)).continuousOn.comp continuousOn_fst hmap).prodMk
      (((hA k l).comp continuousOn_fst hmap).mul continuousOn_snd)
    apply hcont.congr
    intro w hw
    have hb := hb1 k w hw.1
    have heq := (e1 k).right_inv hw.1
    have ht := native_flowbox_germ_transition L U T c label branch parametrization
      htarget hparam k l ((e1 k).symm w).1 ((e1 k).symm w).2.out
      ((e1 k).map_target hw.1) hw.2
    have hbase := congrArg Prod.fst heq
    have hfirst := congrArg Prod.snd heq
    change (c k) (nativeLeafwiseJet1Base L U ((e1 k).symm w)) = w.1 at hbase
    change germFirst (((e1 k).symm w).2.out.1.map
      (nativeLeafFlowboxScalar L U (c k) ((e1 k).symm w).1)) = w.2 at hfirst
    dsimp only [nativeLeafwiseJet1Base, curveJet1Base] at hbase
    apply Prod.ext
    · exact congrArg (c l) hb
    · change germFirst (((e1 k).symm w).2.out.1.map
        (nativeLeafFlowboxScalar L U (c l) ((e1 k).symm w).1)) = A k l w.1 * w.2
      simpa only [hbase, hfirst, A] using ht.1
  have ht2 (k l : Fin n) : ContinuousOn ((e2 k).symm.trans (e2 l))
      ((e2 k).symm.trans (e2 l)).source := by
    have hmap : MapsTo (fun w ↦ w.1.1) ((e2 k).symm.trans (e2 l)).source (O k l) :=
      fun w hw ↦ (hs2 k l ▸ hw).1
    have hcont := ((((c k).symm.trans (c l)).continuousOn.comp continuousOn_fst.fst hmap).prodMk
      (((hA k l).comp continuousOn_fst.fst hmap).mul continuousOn_fst.snd)).prodMk
      ((((hA k l).comp continuousOn_fst.fst hmap).mul continuousOn_snd).add
        ((((hB k l).comp continuousOn_fst.fst hmap).div_const 2).mul
          (continuousOn_fst.snd.pow 2)))
    apply hcont.congr
    intro w hw
    have hb := hb2 k w hw.1
    have heq := (e2 k).right_inv hw.1
    have ht := native_flowbox_germ_transition L U T c label branch parametrization
      htarget hparam k l ((e2 k).symm w).1 ((e2 k).symm w).2.out
      ((e2 k).map_target hw.1) hw.2
    have hbase := congrArg (fun w ↦ w.1.1) heq
    have hfirst := congrArg (fun w ↦ w.1.2) heq
    have hsecond := congrArg Prod.snd heq
    change (c k) (nativeLeafwiseJet2Base L U ((e2 k).symm w)) = w.1.1 at hbase
    change germFirst (((e2 k).symm w).2.out.1.map
      (nativeLeafFlowboxScalar L U (c k) ((e2 k).symm w).1)) = w.1.2 at hfirst
    change germSecond (((e2 k).symm w).2.out.1.map
      (nativeLeafFlowboxScalar L U (c k) ((e2 k).symm w).1)) = w.2 at hsecond
    dsimp only [nativeLeafwiseJet2Base, curveJet2Base] at hbase
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (c l) hb
      · change germFirst (((e2 k).symm w).2.out.1.map
          (nativeLeafFlowboxScalar L U (c l) ((e2 k).symm w).1)) = A k l w.1.1 * w.1.2
        simpa only [hbase, hfirst, A] using ht.1
    · change germSecond (((e2 k).symm w).2.out.1.map
        (nativeLeafFlowboxScalar L U (c l) ((e2 k).symm w).1)) =
          A k l w.1.1 * w.2 + B k l w.1.1 / 2 * w.1.2 ^ 2
      simpa only [hbase, hfirst, hsecond, A, B] using ht.2
  obtain ⟨a1, ha1, _⟩ := generated_coefficient_atlas e1
    (fun j ↦ hcover (nativeLeafwiseJet1Base L U j)) hopen1 ht1
  obtain ⟨a2, ha2, _⟩ := generated_coefficient_atlas e2
    (fun j ↦ hcover (nativeLeafwiseJet2Base L U j)) hopen2 ht2
  let E1 := fun k ↦ (ha1 k).choose
  let E2 := fun k ↦ (ha2 k).choose
  refine ⟨E1, E2, ?_⟩
  intro k
  have he1 : (E1 k).toPartialEquiv = e1 k := (ha1 k).choose_spec.2
  have he2 : (E2 k).toPartialEquiv = e2 k := (ha2 k).choose_spec.2
  exact ⟨congrArg PartialEquiv.source he1, congrArg PartialEquiv.target he1,
    congrArg (fun e ↦ e.toFun) he1, congrArg PartialEquiv.source he2,
    congrArg PartialEquiv.target he2, congrArg (fun e ↦ e.toFun) he2⟩



include htarget hparam in
omit [IsManifold (complexModel d) ∞ M] in
/-- Truncation drops the last native coefficient on every genuine flowbox. Source: Ghys §3 p.591. -/
theorem native_flowbox_truncation_coeff (k : Fin n) (j : NativeLeafwiseJet2 L)
    (hj : nativeLeafwiseJet2Base L U j ∈ (c k).source) :
    nativeLeafwiseJet1Base L U (nativeLeafwiseJetTruncation L j) =
      nativeLeafwiseJet2Base L U j ∧
    nativeLeafwiseJet1Coeff L U (c k) (nativeLeafwiseJetTruncation L j) =
      (nativeLeafwiseJet2Coeff L U (c k) j).1 := by
  have hb := curve_jet_truncation_base (L j.1) j.2
  have hb' : nativeLeafwiseJet1Base L U (nativeLeafwiseJetTruncation L j) =
      nativeLeafwiseJet2Base L U j := congrArg (U.leaf j.1).inclusion hb
  refine ⟨hb', Prod.ext (congrArg (c k) hb') ?_⟩
  obtain ⟨q, hq, _, _, hm⟩ := native_flowbox_receiving_chart L U (T k) (c k)
    (label k) (branch k) (parametrization k) (htarget k) (hparam k) j.1
    (curveJet2Base (L j.1) j.2) hj
  have hq' : curveJet1Base (L j.1) (curveJetTruncation (L j.1) j.2) ∈ q.1.source :=
    hb.symm ▸ hq
  change germFirst ((curveJetTruncation (L j.1) j.2).out.1.map
    (nativeLeafFlowboxScalar L U (c k) j.1)) =
    germFirst (j.2.out.1.map (nativeLeafFlowboxScalar L U (c k) j.1))
  rw [hm _ hq', hm _ hq]
  exact congrArg Prod.snd (((leaf_jet_complex_manifold (L j.1)).2.2.2.1 q).2.2 j.2 hq).2

include htarget hparam in
omit [IsManifold (complexModel d) ∞ M] in
/-- Pure source scaling multiplies native first and second coefficients by the first and second powers of the scalar. Source: Ghys §3 p.591. -/
theorem native_flowbox_scale_coeff (k : Fin n) (omega : ℂˣ) :
    (∀ j : NativeLeafwiseJet1 L, nativeLeafwiseJet1Base L U j ∈ (c k).source →
      nativeLeafwiseJet1Base L U (nativeLeafwiseJet1Scale L omega j) =
        nativeLeafwiseJet1Base L U j ∧
      nativeLeafwiseJet1Coeff L U (c k) (nativeLeafwiseJet1Scale L omega j) =
        ((nativeLeafwiseJet1Coeff L U (c k) j).1,
          (omega : ℂ) * (nativeLeafwiseJet1Coeff L U (c k) j).2)) ∧
    (∀ j : NativeLeafwiseJet2 L, nativeLeafwiseJet2Base L U j ∈ (c k).source →
      nativeLeafwiseJet2Base L U (nativeLeafwiseJet2Reparametrize L (.scale omega) j) =
        nativeLeafwiseJet2Base L U j ∧
      nativeLeafwiseJet2Coeff L U (c k) (nativeLeafwiseJet2Reparametrize L (.scale omega) j) =
        (((nativeLeafwiseJet2Coeff L U (c k) j).1.1,
          (omega : ℂ) * (nativeLeafwiseJet2Coeff L U (c k) j).1.2),
          (omega : ℂ) ^ 2 * (nativeLeafwiseJet2Coeff L U (c k) j).2)) := by
  constructor
  · intro j hj
    have hscale := (curve_jet_reparametrization (L j.1)).2.2.2.1 omega j.2
    have hb : nativeLeafwiseJet1Base L U (nativeLeafwiseJet1Scale L omega j) =
        nativeLeafwiseJet1Base L U j := congrArg (U.leaf j.1).inclusion hscale.1
    refine ⟨hb, Prod.ext (congrArg (c k) hb) ?_⟩
    obtain ⟨q, hq, _, _, hm⟩ := native_flowbox_receiving_chart L U (T k) (c k)
      (label k) (branch k) (parametrization k) (htarget k) (hparam k) j.1
      (curveJet1Base (L j.1) j.2) hj
    have hq' := hscale.1.symm ▸ hq
    change germFirst ((curveJet1Scale (L j.1) omega j.2).out.1.map
      (nativeLeafFlowboxScalar L U (c k) j.1)) =
      (omega : ℂ) * germFirst (j.2.out.1.map (nativeLeafFlowboxScalar L U (c k) j.1))
    rw [hm _ hq', hm _ hq]
    exact congrArg Prod.snd (hscale.2 q hq)
  · intro j hj
    have hscale := (curve_jet_reparametrization (L j.1)).2.2.1 (.scale omega) j.2
    have hb : nativeLeafwiseJet2Base L U (nativeLeafwiseJet2Reparametrize L (.scale omega) j) =
        nativeLeafwiseJet2Base L U j := congrArg (U.leaf j.1).inclusion hscale.1
    obtain ⟨q, hq, _, _, hm⟩ := native_flowbox_receiving_chart L U (T k) (c k)
      (label k) (branch k) (parametrization k) (htarget k) (hparam k) j.1
      (curveJet2Base (L j.1) j.2) hj
    have hq' := hscale.1.symm ▸ hq
    refine ⟨hb, Prod.ext (Prod.ext (congrArg (c k) hb) ?_) ?_⟩
    · change germFirst ((curveJet2Reparametrize (L j.1) (.scale omega) j.2).out.1.map
        (nativeLeafFlowboxScalar L U (c k) j.1)) =
        (omega : ℂ) * germFirst (j.2.out.1.map (nativeLeafFlowboxScalar L U (c k) j.1))
      rw [hm _ hq', hm _ hq]
      exact congrArg (fun w ↦ w.1.2) (hscale.2.2 q hq)
    · change germSecond ((curveJet2Reparametrize (L j.1) (.scale omega) j.2).out.1.map
        (nativeLeafFlowboxScalar L U (c k) j.1)) =
        (omega : ℂ)^2 * germSecond (j.2.out.1.map (nativeLeafFlowboxScalar L U (c k) j.1))
      rw [hm _ hq', hm _ hq]
      simpa only [curveJet2Coeff, curveGermSecond, CurveJetReparametrization.scale,
        mul_zero, zero_mul, sub_zero] using
        congrArg Prod.snd (hscale.2.2 q hq)




end HolomorphicAnosov.Ghys
