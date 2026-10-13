import HolomorphicAnosov.Ghys.NativeFlowboxJetChartsG13
import HolomorphicAnosov.Ghys.JetPartitionFiniteSectionG10
import HolomorphicAnosov.Ghys.JetPartitionWeightedContinuityG10
import HolomorphicAnosov.Ghys.NativeJetScalingTruncation

/-! Gluing homogeneous local sections of the original native two-jet bundle. -/

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

variable [∀ i, T2Space (L i)] [∀ i, SecondCountableTopology (L i)]

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

open scoped BigOperators
include htarget hparam in
omit [IsManifold (complexModel d) ∞ M] in
/-- Finite subordinate weights glue homogeneous native local sections into a continuous homogeneous section, with the weighted coefficient formula in every flowbox. (Ghys, §3) -/
theorem native_flowbox_glued_section
    (hcover : ∀ x : M, ∃ k, x ∈ (c k).source)
    (rho : Fin n → M → ℝ)
    (hrho : ∀ k, Continuous (rho k) ∧ tsupport (rho k) ⊆ (c k).source)
    (hrhoSum : ∀ x, ∑ k, rho k x = 1) :
    letI := nativeLeafwiseJet1Topology L U c
    letI := nativeLeafwiseJet2Topology L U c
    ∀ (E1 : Fin n → OpenPartialHomeomorph (NativeLeafwiseJet1 L)
          ((ℂ × (Fin s → ℝ)) × ℂ))
      (E2 : Fin n → OpenPartialHomeomorph (NativeLeafwiseJet2 L)
          (((ℂ × (Fin s → ℝ)) × ℂ) × ℂ)),
    (∀ k, (E1 k).source = (nativeLeafwiseJet1Base L U) ⁻¹' (c k).source ∧
      (E1 k).target = {w | w.1 ∈ (c k).target ∧ w.2 ≠ 0} ∧
      (E1 k : NativeLeafwiseJet1 L → _) = nativeLeafwiseJet1Coeff L U (c k) ∧
      (E2 k).source = (nativeLeafwiseJet2Base L U) ⁻¹' (c k).source ∧
      (E2 k).target = {w | w.1.1 ∈ (c k).target ∧ w.1.2 ≠ 0} ∧
      (E2 k : NativeLeafwiseJet2 L → _) = nativeLeafwiseJet2Coeff L U (c k)) →
    ∀ localSection : ∀ k, {j : NativeLeafwiseJet1 L |
        nativeLeafwiseJet1Base L U j ∈ (c k).source} → NativeLeafwiseJet2 L,
    (∀ k, Continuous (localSection k)) →
    (∀ k j, nativeLeafwiseJetTruncation L (localSection k j) = j.val) →
    (∀ k (omega : ℂˣ) j j', j'.val = nativeLeafwiseJet1Scale L omega j.val →
        localSection k j' = nativeLeafwiseJet2Reparametrize L (.scale omega)
          (localSection k j)) →
    ∃ sectionMap : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L,
      Continuous sectionMap ∧ (∀ j, nativeLeafwiseJetTruncation L (sectionMap j) = j) ∧
      (∀ (omega : ℂˣ) j, sectionMap (nativeLeafwiseJet1Scale L omega j) =
        nativeLeafwiseJet2Reparametrize L (.scale omega) (sectionMap j)) ∧
      (∀ k j, nativeLeafwiseJet1Base L U j ∈ (c k).source →
        (nativeLeafwiseJet2Coeff L U (c k) (sectionMap j)).2 = ∑ l : Fin n,
          if hl : nativeLeafwiseJet1Base L U j ∈ (c l).source then
            (rho l (nativeLeafwiseJet1Base L U j) : ℂ) *
              (nativeLeafwiseJet2Coeff L U (c k) (localSection l ⟨j, hl⟩)).2 else 0) := by
  let := nativeLeafwiseJet1Topology L U c
  let := nativeLeafwiseJet2Topology L U c
  intro E1 E2 hE localSection hlocalContinuous hlocalTruncation hlocalScaling
  let p1 := nativeLeafwiseJet1Base L U
  let p2 := nativeLeafwiseJetTruncation L
  let C1 := fun k ↦ nativeLeafwiseJet1Coeff L U (c k)
  let C2 := fun k ↦ nativeLeafwiseJet2Coeff L U (c k)
  have hbase (q : NativeLeafwiseJet2 L) :
      p1 (p2 q) = nativeLeafwiseJet2Base L U q :=
    congrArg (U.leaf q.1).inclusion (curve_jet_truncation_base (L q.1) q.2)
  have hfibreSource (k : Fin n) (j : NativeLeafwiseJet1 L) (hj : p1 j ∈ (c k).source)
      (q : {q : NativeLeafwiseJet2 L // p2 q = j}) :
      nativeLeafwiseJet2Base L U q.val ∈ (c k).source := by
    rw [← hbase q.val, q.property]
    exact hj
  have hprojection (k : Fin n) (j : NativeLeafwiseJet1 L) (hj : p1 j ∈ (c k).source)
      (q : {q : NativeLeafwiseJet2 L // p2 q = j}) : (C2 k q.val).1 = C1 k j := by
    have ht := native_flowbox_truncation_coeff L U T c label branch parametrization
      htarget hparam k q.val (hfibreSource k j hj q)
    exact ht.2.symm.trans (congrArg (C1 k) q.property)
  have hfibre (k : Fin n) (j : NativeLeafwiseJet1 L) (hj : p1 j ∈ (c k).source) :
      Function.Bijective (fun q : {q : NativeLeafwiseJet2 L // p2 q = j} ↦ (C2 k q.val).2) := by
    constructor
    · intro q r hqr
      apply Subtype.ext
      apply (E2 k).injOn
      · rw [(hE k).2.2.2.1]; exact hfibreSource k j hj q
      · rw [(hE k).2.2.2.1]; exact hfibreSource k j hj r
      · rw [(hE k).2.2.2.2.2]
        exact Prod.ext ((hprojection k j hj q).trans (hprojection k j hj r).symm) hqr
    · intro b
      have htarget' : ((C1 k j), b) ∈ (E2 k).target := by
        rw [(hE k).2.2.2.2.1]
        have ht := (E1 k).map_source (show j ∈ (E1 k).source by rw [(hE k).1]; exact hj)
        rw [(hE k).2.1, (hE k).2.2.1] at ht
        exact ht
      let q := (E2 k).symm (C1 k j, b)
      have hqs : nativeLeafwiseJet2Base L U q ∈ (c k).source := by
        have h := (E2 k).map_target htarget'
        rwa [(hE k).2.2.2.1] at h
      have hqc : C2 k q = (C1 k j, b) := by
        dsimp only [C2]
        rw [← (hE k).2.2.2.2.2]
        exact (E2 k).right_inv htarget'
      have hq : p2 q = j := by
        have ht := native_flowbox_truncation_coeff L U T c label branch parametrization
          htarget hparam k q hqs
        apply (E1 k).injOn
        · rw [(hE k).1]
          change p1 (p2 q) ∈ (c k).source
          rw [hbase]
          exact hqs
        · rw [(hE k).1]; exact hj
        · rw [(hE k).2.2.1, ht.2]
          exact congrArg Prod.fst hqc
      exact ⟨⟨q, hq⟩, congrArg Prod.snd hqc⟩
  let e (k : Fin n) (j : NativeLeafwiseJet1 L) (hj : p1 j ∈ (c k).source) :
      {q : NativeLeafwiseJet2 L // p2 q = j} ≃ ℂ := Equiv.ofBijective _ (hfibre k j hj)
  have haffine (k l : Fin n) (j : NativeLeafwiseJet1 L)
      (hk : p1 j ∈ (c k).source) (hl : p1 j ∈ (c l).source) :
      ∃ A B : ℂ, ∀ q, e l j hl q = A * e k j hk q + B := by
    let p := (C1 k j).1
    let H := fun z ↦ ((c l) ((c k).symm (z, p.2))).1
    refine ⟨deriv H p.1, iteratedDeriv 2 H p.1 / 2 * (C1 k j).2 ^ 2, ?_⟩
    intro q
    have ht := (native_flowbox_germ_transition L U T c label branch parametrization
      htarget hparam k l q.val.1 q.val.2.out
      (hfibreSource k j hk q) (hfibreSource l j hl q)).2
    have hp := hprojection k j hk q
    have hpbase := congrArg Prod.fst hp
    have hpfirst := congrArg Prod.snd hp
    dsimp only [C2, nativeLeafwiseJet2Coeff, nativeLeafwiseJet2Base, curveJet2Base] at hpbase hpfirst
    change (C2 l q.val).2 = deriv H p.1 * (C2 k q.val).2 +
      iteratedDeriv 2 H p.1 / 2 * (C1 k j).2 ^ 2
    simpa only [hpbase, hpfirst, C2, nativeLeafwiseJet2Coeff] using ht
  have hrhoZero (k : Fin n) (j : NativeLeafwiseJet1 L) (hj : p1 j ∉ (c k).source) :
      rho k (p1 j) = 0 := by
    by_contra h
    exact hj ((hrho k).2 (subset_closure h))
  obtain ⟨sectionFibre, hweighted, _⟩ := exists_unique_guarded_finite_affine_section p2
    (fun k ↦ p1 ⁻¹' (c k).source) (fun j ↦ hcover (p1 j))
    (fun k j ↦ rho k (p1 j)) (fun j ↦ hrhoSum (p1 j)) hrhoZero e
    (fun k j hj ↦ ⟨localSection k ⟨j, hj⟩, hlocalTruncation k ⟨j, hj⟩⟩) haffine
  let sectionMap := fun j ↦ (sectionFibre j).val
  have hsectionTruncation (j) : p2 (sectionMap j) = j := (sectionFibre j).property
  have hsectionWeighted (k j) (hj : p1 j ∈ (c k).source) :
      (C2 k (sectionMap j)).2 = ∑ l : Fin n, if hl : p1 j ∈ (c l).source then
        (rho l (p1 j) : ℂ) * (C2 k (localSection l ⟨j, hl⟩)).2 else 0 :=
    hweighted k j hj
  refine ⟨sectionMap, ?_, hsectionTruncation, ?_, hsectionWeighted⟩
  · have hp1 : Continuous p1 :=
      ((nativeLeafwiseJet_flowbox_continuity L U c).2.2 hcover).1
    rw [continuous_iff_continuousAt]
    intro j
    obtain ⟨k, hj⟩ := hcover (p1 j)
    let X := {j : NativeLeafwiseJet1 L | p1 j ∈ (c k).source}
    let V (l : Fin n) : Set X := {j | p1 j.val ∈ (c l).source}
    let weight (l : Fin n) (j : X) := rho l (p1 j.val)
    let values (l : Fin n) (j : V l) :=
      (C2 k (localSection l ⟨j.val.val, j.property⟩)).2
    have hpX : Continuous (fun j : X ↦ p1 j.val) := hp1.comp continuous_subtype_val
    have hV (l : Fin n) : IsOpen (V l) := (c l).open_source.preimage hpX
    have hw (l : Fin n) : Continuous (weight l) := (hrho l).1.comp hpX
    have hsupport (l : Fin n) : tsupport (weight l) ⊆ V l := by
      have hc : tsupport (weight l) ⊆ (fun j : X ↦ p1 j.val) ⁻¹' tsupport (rho l) := by
        apply closure_minimal
        · intro j hj
          exact subset_closure hj
        · exact (isClosed_tsupport (rho l)).preimage hpX
      intro j hj
      exact (hrho l).2 (hc hj)
    have hvalues (l : Fin n) : Continuous (values l) := by
      have hval : Continuous (fun j : V l ↦
          (⟨j.val.val, j.property⟩ : {j : NativeLeafwiseJet1 L | p1 j ∈ (c l).source})) :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have hlocal := (hlocalContinuous l).comp hval
      have hmem (j : V l) : localSection l ⟨j.val.val, j.property⟩ ∈ (E2 k).source := by
        rw [(hE k).2.2.2.1]
        change nativeLeafwiseJet2Base L U (localSection l ⟨j.val.val, j.property⟩) ∈ (c k).source
        rw [← hbase, show p2 (localSection l ⟨j.val.val, j.property⟩) = j.val.val from
          hlocalTruncation l ⟨j.val.val, j.property⟩]
        exact j.val.property
      have hc := ((E2 k).continuousOn.comp_continuous hlocal hmem).snd
      simpa only [(hE k).2.2.2.2.2, values, C2, Function.comp_apply] using hc
    have hsum := continuous_guarded_weighted_sum V hV weight hw hsupport values hvalues
    let weighted (j : X) := ∑ l : Fin n, if hl : p1 j.val ∈ (c l).source then
      (rho l (p1 j.val) : ℂ) * (C2 k (localSection l ⟨j.val, hl⟩)).2 else 0
    have hsum' : Continuous weighted := hsum
    have hfirst : Continuous (fun j : X ↦ C1 k j.val) := by
      have hc := (E1 k).continuousOn.comp_continuous continuous_subtype_val
        (show ∀ j : X, j.val ∈ (E1 k).source from fun j ↦ by
          rw [(hE k).1]; exact j.property)
      simpa only [(hE k).2.2.1, C1, Function.comp_def] using hc
    have htarget' (j : X) : (C1 k j.val, weighted j) ∈ (E2 k).target := by
      rw [(hE k).2.2.2.2.1]
      have ht := (E1 k).map_source (show j.val ∈ (E1 k).source by
        rw [(hE k).1]; exact j.property)
      rwa [(hE k).2.1, (hE k).2.2.1] at ht
    have hcont := (E2 k).symm.continuousOn.comp_continuous
      (hfirst.prodMk hsum') htarget'
    have heq (j : X) : (E2 k).symm (C1 k j.val, weighted j) = sectionMap j.val := by
      have hcoeff : C2 k (sectionMap j.val) = (C1 k j.val, weighted j) :=
        Prod.ext (hprojection k j.val j.property (sectionFibre j.val))
          (hsectionWeighted k j.val j.property)
      rw [← hcoeff]
      change (E2 k).symm (nativeLeafwiseJet2Coeff L U (c k) (sectionMap j.val)) = _
      rw [← (hE k).2.2.2.2.2]
      exact (E2 k).left_inv (by
        rw [(hE k).2.2.2.1]
        exact hfibreSource k j.val j.property (sectionFibre j.val))
    have hon : ContinuousOn sectionMap (p1 ⁻¹' (c k).source) :=
      continuousOn_iff_continuous_domRestrict.mpr (hcont.congr heq)
    exact hon.continuousAt (((c k).open_source.preimage hp1).mem_nhds hj)
  · intro omega j
    obtain ⟨k, hk⟩ := hcover (p1 j)
    let j' := nativeLeafwiseJet1Scale L omega j
    have hb1 : p1 j' = p1 j :=
      ((native_flowbox_scale_coeff L U T c label branch parametrization
        htarget hparam k omega).1 j hk).1
    have hk' : p1 j' ∈ (c k).source := hb1.symm ▸ hk
    let q' : {q : NativeLeafwiseJet2 L // p2 q = j'} :=
      ⟨nativeLeafwiseJet2Reparametrize L (.scale omega) (sectionMap j), by
        change nativeLeafwiseJetTruncation L
          (nativeLeafwiseJet2Reparametrize L (.scale omega) (sectionMap j)) = j'
        rw [nativeJetScalingTruncation]
        exact congrArg (nativeLeafwiseJet1Scale L omega) (hsectionTruncation j)⟩
    have heq : sectionFibre j' = q' := by
      apply (hfibre k j' hk').1
      change (C2 k (sectionMap j')).2 =
        (C2 k (nativeLeafwiseJet2Reparametrize L (.scale omega) (sectionMap j))).2
      have hs2 := (native_flowbox_scale_coeff L U T c label branch parametrization
        htarget hparam k omega).2 (sectionMap j)
          (hfibreSource k j hk (sectionFibre j))
      have hsecond : (C2 k (nativeLeafwiseJet2Reparametrize L (.scale omega)
          (sectionMap j))).2 = (omega : ℂ)^2 * (C2 k (sectionMap j)).2 :=
        congrArg Prod.snd hs2.2
      rw [hsecond, hsectionWeighted k j' hk', hsectionWeighted k j hk, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : p1 j ∈ (c l).source
      · have hl' : p1 j' ∈ (c l).source := hb1.symm ▸ hl
        simp only [dite_eq_left hl, hb1]
        have he := hlocalScaling l omega ⟨j, hl⟩ ⟨j', hl'⟩ rfl
        rw [he]
        have hlocsource : nativeLeafwiseJet2Base L U (localSection l ⟨j, hl⟩) ∈
            (c k).source := by
          rw [← hbase]
          change p1 (nativeLeafwiseJetTruncation L (localSection l ⟨j, hl⟩)) ∈ (c k).source
          rw [hlocalTruncation]
          exact hk
        have hsl := (native_flowbox_scale_coeff L U T c label branch parametrization
          htarget hparam k omega).2 (localSection l ⟨j, hl⟩) hlocsource
        have hsl' : (C2 k (nativeLeafwiseJet2Reparametrize L (.scale omega)
            (localSection l ⟨j, hl⟩))).2 =
            (omega : ℂ)^2 * (C2 k (localSection l ⟨j, hl⟩)).2 :=
          congrArg Prod.snd hsl.2
        rw [hsl']
        ring
      · have hl' : p1 j' ∉ (c l).source := by simpa only [hb1] using hl
        simp only [dite_eq_right hl, dite_eq_right hl', mul_zero]
    exact congrArg Subtype.val heq




end HolomorphicAnosov.Ghys
