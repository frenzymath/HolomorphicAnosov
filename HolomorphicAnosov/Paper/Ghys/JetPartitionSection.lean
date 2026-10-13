import HolomorphicAnosov.Ghys.NativeFlowboxJetZeroSectionsG13
import HolomorphicAnosov.Ghys.NativeFlowboxJetGluingG13
import HolomorphicAnosov.Paper.Ghys.ActualInvariantSectionFlowboxCoverG5
import Mathlib.Topology.PartitionOfUnity

/-! This module constructs a continuous homogeneous section by partition of unity. (Ghys, §3) -/

noncomputable section
namespace HolomorphicAnosov.Ghys.JetPartitionSection
open Set Filter TopologicalSpace
open scoped _root_.Topology Manifold ContDiff BigOperators
universe u
set_option autoImplicit false
variable {d : ℕ} {M : Type u}
variable [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
variable [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real Classical.propDecidable

/-- A finite partition of unity glues local affine-germ sections into a continuous homogeneous section of the original unstable two-jet bundle. (Ghys, §3) -/
theorem jet_partition_section [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    let scalarSlice := fun (c : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) (t : Fin (2 * d - 2) → ℝ) ↦
      (⟨{z | (z, t) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
    ∃ (ι : Type u) (L : ι → Type u) (top : ∀ i, TopologicalSpace (L i)),
    letI := top
    ∃ (realChart : ∀ i, ChartedSpace (Fin 2 → ℝ) (L i)),
    letI := realChart
    ∃ (realSmooth : ∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)),
    letI := realSmooth
    ∃ (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
      (complexChart : ∀ i, ChartedSpace ℂ (L i)),
    letI := complexChart
    ∃ (complexSmooth : ∀ i, IsManifold 𝓘(ℂ) ∞ (L i)),
    letI := complexSmooth
    letI : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
    letI : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
    (∀ i, ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion ∧
      ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion z)) ∧
    (∃ m : MetricSpace M,
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace M) ∧
      ∀ i (x : L i) y,
        (∃ z, (U.leaf i).inclusion z = y) ↔
          @ForwardAsymptotic M m (f.symm : M → M) ((U.leaf i).inclusion x) y) ∧
    Nonempty (HPS.LeafDynamicalInvariance U f.toReal) ∧
    ∃ (n : ℕ) (T : Fin n → Opens (Fin (2 * d - 2) → ℝ))
      (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
      (label : ∀ i, T i → ι) (branch : ∀ i t, Opens (L (label i t)))
      (parametrization : ∀ i t,
        Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (scalarSlice (c i) t.val) (branch i t) ∞),
    (∀ x : M, ∃ i, x ∈ (c i).source) ∧
    (∀ i p, p ∈ (c i).target → p.2 ∈ T i) ∧
    (∀ i t (z : scalarSlice (c i) t.val), (c i).symm (z.val, t.val) =
      (U.leaf (label i t)).inclusion ((parametrization i t z).val)) ∧
    let J1 := NativeLeafwiseJet1 L
    let J2 := NativeLeafwiseJet2 L
    let p1 := nativeLeafwiseJet1Base L U
    let p2 := nativeLeafwiseJetTruncation L
    let C1 := fun i ↦ nativeLeafwiseJet1Coeff L U (c i)
    let C2 := fun i ↦ nativeLeafwiseJet2Coeff L U (c i)
    letI := nativeLeafwiseJet1Topology L U c
    letI := nativeLeafwiseJet2Topology L U c
    ∃ (e1 : Fin n → OpenPartialHomeomorph J1 ((ℂ × (Fin (2 * d - 2) → ℝ)) × ℂ))
      (e2 : Fin n → OpenPartialHomeomorph J2
        (((ℂ × (Fin (2 * d - 2) → ℝ)) × ℂ) × ℂ)),
    (∀ i, (e1 i).source = p1 ⁻¹' (c i).source ∧
      (e1 i).target = {w | w.1 ∈ (c i).target ∧ w.2 ≠ 0} ∧
      EqOn (e1 i) (C1 i) (e1 i).source ∧
      (e2 i).source = (nativeLeafwiseJet2Base L U) ⁻¹' (c i).source ∧
      (e2 i).target = {w | w.1.1 ∈ (c i).target ∧ w.1.2 ≠ 0} ∧
      EqOn (e2 i) (C2 i) (e2 i).source) ∧
    ∃ (localSection : ∀ i, {j : J1 | p1 j ∈ (c i).source} → J2)
      (rho : Fin n → M → ℝ) (s : J1 → J2),
    (∀ i, Continuous (localSection i)) ∧
    (∀ i j, p2 (localSection i j) = j.val ∧ (C2 i (localSection i j)).2 = 0) ∧
    (∀ i j, ∃ gamma : CurveParamGerm (L j.val.1),
      localSection i j = ⟨j.val.1, curveJet2Class (L j.val.1) gamma⟩ ∧
      gamma.1.map (U.leaf j.val.1).inclusion =
        (((fun v : ℂ ↦ (c i).symm
          ((C1 i j.val).1.1 + (C1 i j.val).2 * v, (C1 i j.val).1.2)) :
          ℂ → M) : Filter.Germ (𝓝 (0 : ℂ)) M)) ∧
    (∀ i ell,
      letI := nativeLeafJet1Charts L ell
      letI := nativeLeafJet2Charts L ell
      ∃ sigma : CurveJet1 (L ell) → CurveJet2 (L ell),
        ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, (ℂ × ℂ) × ℂ) ∞ sigma
          {j | p1 (nativeLeafwiseJet1Inclusion L ell j) ∈ (c i).source} ∧
        ∀ j (hj : p1 (nativeLeafwiseJet1Inclusion L ell j) ∈ (c i).source),
          localSection i ⟨nativeLeafwiseJet1Inclusion L ell j, hj⟩ =
            nativeLeafwiseJet2Inclusion L ell (sigma j)) ∧
    (∀ i (omega : ℂˣ) j j', j'.val = nativeLeafwiseJet1Scale L omega j.val →
      localSection i j' = nativeLeafwiseJet2Reparametrize L (.scale omega)
        (localSection i j)) ∧
    (∀ i, Continuous (rho i) ∧ tsupport (rho i) ⊆ (c i).source ∧
      ∀ x, 0 ≤ rho i x ∧ rho i x ≤ 1) ∧
    (∀ x, ∑ i : Fin n, rho i x = 1) ∧
    Continuous s ∧ (∀ j, p2 (s j) = j) ∧
    (∀ (omega : ℂˣ) j, s (nativeLeafwiseJet1Scale L omega j) =
      nativeLeafwiseJet2Reparametrize L (.scale omega) (s j)) ∧
    (∀ i j, p1 j ∈ (c i).source →
      (C2 i (s j)).2 = ∑ k : Fin n,
        if hk : p1 j ∈ (c k).source then
          (rho k (p1 j) : ℂ) * (C2 i (localSection k ⟨j, hk⟩)).2 else 0) ∧
    (∀ i j, p1 j ∈ (c i).source → ∀ q : J2, p2 q = j →
      (C2 i (s j)).2 = (C2 i q).2 + ∑ k : Fin n,
        if hk : p1 j ∈ (c k).source then
          (rho k (p1 j) : ℂ) *
            ((C2 i (localSection k ⟨j, hk⟩)).2 - (C2 i q).2) else 0) := by
  obtain ⟨ιs, ι, Ls, L, topS, top, realS, realChart, smoothS, realSmooth,
    S, U, complexChart, complexSmooth, hhol, hmetric, hSinv, hUinv, hboxes,
    hfinite, hproduct⟩ :=
    ActualInvariantSectionFlowboxCoverG5.actual_invariant_section_flowbox_cover f a hRank
  let := topS
  let := top
  let := realS
  let := realChart
  let := smoothS
  let := realSmooth
  let := complexChart
  let := complexSmooth
  refine ⟨ι, L, top, realChart, realSmooth, U, complexChart, complexSmooth,
    hhol, ?_, hUinv, ?_⟩
  · obtain ⟨m, hm, hs, hu⟩ := hmetric
    exact ⟨m, hm, hu⟩
  by_cases hM : Nonempty M
  · let := hM
    obtain ⟨n, T, c, label, branch, parametrization, hcover, htransverse, hparam,
      hopen, hcontinuous, hfirst, hsecond, hoverlap⟩ := hfinite
    obtain ⟨rho, hrhoSupport, hrhoSum, hrhoBounds, hrhoCompact⟩ :=
      exists_continuous_sum_one_of_isOpen_isCompact
        (fun i ↦ (c i).open_source) isCompact_univ (by
          intro x _
          obtain ⟨i, hi⟩ := hcover x
          exact mem_iUnion.mpr ⟨i, hi⟩)
    have hrho : ∀ i, Continuous (rho i) ∧ tsupport (rho i) ⊆ (c i).source ∧
        ∀ x, 0 ≤ rho i x ∧ rho i x ≤ 1 := by
      intro i
      exact ⟨(rho i).continuous, hrhoSupport i, hrhoBounds i⟩
    have hrhoSumReal : ∀ x, ∑ i : Fin n, rho i x = 1 := by
      intro x
      simpa only [Finset.sum_apply, Pi.one_apply] using
        hrhoSum (mem_univ x)
    have hrhoZero : ∀ i x, x ∉ (c i).source → rho i x = 0 := by
      intro i x hx
      by_contra h
      exact hx (hrhoSupport i (subset_closure h))
    have hrhoSumComplex : ∀ x, ∑ i : Fin n, (rho i x : ℂ) = 1 := by
      intro x
      exact_mod_cast hrhoSumReal x
    have hanchor : ∀ (x : M) (b : ∀ i, x ∈ (c i).source → ℂ) (q : ℂ),
        (∑ i : Fin n, if hi : x ∈ (c i).source then (rho i x : ℂ) * b i hi else 0) =
          q + ∑ i : Fin n, if hi : x ∈ (c i).source then
            (rho i x : ℂ) * (b i hi - q) else 0 := by
      intro x b q
      have hweight : ∑ i : Fin n,
          (if x ∈ (c i).source then (rho i x : ℂ) else 0) = 1 := by
        calc
          _ = ∑ i : Fin n, (rho i x : ℂ) := by
            apply Finset.sum_congr rfl
            intro i _
            split_ifs with hi
            · rfl
            · simp [hrhoZero i x hi]
          _ = 1 := hrhoSumComplex x
      have hterm : ∀ i : Fin n,
          (if hi : x ∈ (c i).source then (rho i x : ℂ) * (b i hi - q) else 0) =
            (if hi : x ∈ (c i).source then (rho i x : ℂ) * b i hi else 0) -
              (if x ∈ (c i).source then (rho i x : ℂ) else 0) * q := by
        intro i
        split_ifs <;> simp [mul_sub]
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hweight, one_mul]
      exact (add_sub_cancel q _).symm
    refine ⟨n, T, c, label, branch, parametrization, hcover, htransverse, hparam, ?_⟩
    let J1 := NativeLeafwiseJet1 L
    let J2 := NativeLeafwiseJet2 L
    let p1 := nativeLeafwiseJet1Base L U
    let p2 := nativeLeafwiseJetTruncation L
    let C1 := fun i ↦ nativeLeafwiseJet1Coeff L U (c i)
    let C2 := fun i ↦ nativeLeafwiseJet2Coeff L U (c i)
    let := nativeLeafwiseJet1Topology L U c
    let := nativeLeafwiseJet2Topology L U c
    let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
    let : ∀ i, SecondCountableTopology (L i) := fun i ↦ (U.leaf i).countable
    let scalarSlice := fun (q : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) (t : Fin (2 * d - 2) → ℝ) ↦
      (⟨{z | (z, t) ∈ q.target},
        q.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
    let x : M := Classical.choice hM
    obtain ⟨k, hk⟩ := hcover x
    obtain ⟨j1, _, _⟩ := (native_flowbox_jet1_bijOn L U (T k) (c k) (label k)
      (branch k) (parametrization k) (htransverse k) (hparam k)).surjOn
      (show ((c k) x, (1 : ℂ)) ∈ {w | w.1 ∈ (c k).target ∧ w.2 ≠ 0} from
        ⟨(c k).map_source hk, one_ne_zero⟩)
    obtain ⟨j2, _, _⟩ := (native_flowbox_jet2_bijOn L U (T k) (c k) (label k)
      (branch k) (parametrization k) (htransverse k) (hparam k)).surjOn
      (show (((c k) x, (1 : ℂ)), (0 : ℂ)) ∈
        {w | w.1.1 ∈ (c k).target ∧ w.1.2 ≠ 0} from
        ⟨(c k).map_source hk, one_ne_zero⟩)
    let : Nonempty (NativeLeafwiseJet1 L) := ⟨j1⟩
    let : Nonempty (NativeLeafwiseJet2 L) := ⟨j2⟩
    have hA : ∀ k l, ContinuousOn (fun p : ℂ × (Fin (2 * d - 2) → ℝ) ↦
        deriv (fun z ↦ ((c l) ((c k).symm (z, p.2))).1) p.1)
          ((c k).symm.trans (c l)).source := by
      intro k l
      apply (hfirst k l).congr
      intro p hp
      have hS : IsOpen {z : ℂ | (z, p.2) ∈ ((c k).symm.trans (c l)).source} :=
        ((c k).symm.trans (c l)).open_source.preimage (continuous_id.prodMk continuous_const)
      exact (derivWithin_of_isOpen hS hp).symm
    have hB : ∀ k l, ContinuousOn (fun p : ℂ × (Fin (2 * d - 2) → ℝ) ↦
        iteratedDeriv 2 (fun z ↦ ((c l) ((c k).symm (z, p.2))).1) p.1)
          ((c k).symm.trans (c l)).source := by
      intro k l
      apply (hsecond k l).congr
      intro p hp
      let S := {z : ℂ | (z, p.2) ∈ ((c k).symm.trans (c l)).source}
      let H := fun z ↦ ((c l) ((c k).symm (z, p.2))).1
      have hS : IsOpen S := ((c k).symm.trans (c l)).open_source.preimage
        (continuous_id.prodMk continuous_const)
      have hd : derivWithin H S =ᶠ[𝓝 p.1] deriv H := by
        filter_upwards [hS.mem_nhds hp] with z hz
        exact derivWithin_of_isOpen hS hz
      change iteratedDeriv 2 H p.1 = derivWithin (derivWithin H S) S p.1
      rw [derivWithin_of_isOpen hS hp, hd.deriv_eq]
      simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    obtain ⟨e1, e2, he⟩ := native_flowbox_jet_charts L U T c label branch parametrization
      htransverse hparam hcover hA hB
    obtain ⟨localSection, hlocalContinuous, hlocalCoeff, hlocalGerm, hlocalHolomorphic,
      hlocalScaling⟩ := native_flowbox_zero_sections_full L U T c label branch parametrization
        htransverse hparam e1 e2 he
    obtain ⟨s, hsContinuous, hsTruncation, hsScaling, hsWeighted⟩ :=
      native_flowbox_glued_section L U T c label branch parametrization htransverse hparam
        hcover (fun k ↦ rho k) (fun k ↦ ⟨(hrho k).1, (hrho k).2.1⟩)
        hrhoSumReal e1 e2 he localSection hlocalContinuous
        (fun k j ↦ (hlocalCoeff k j).1) hlocalScaling
    have hcharts : ∀ k, (e1 k).source = p1 ⁻¹' (c k).source ∧
        (e1 k).target = {w | w.1 ∈ (c k).target ∧ w.2 ≠ 0} ∧
        EqOn (e1 k) (C1 k) (e1 k).source ∧
        (e2 k).source = (nativeLeafwiseJet2Base L U) ⁻¹' (c k).source ∧
        (e2 k).target = {w | w.1.1 ∈ (c k).target ∧ w.1.2 ≠ 0} ∧
        EqOn (e2 k) (C2 k) (e2 k).source := by
      intro k
      exact ⟨(he k).1, (he k).2.1, (fun _ _ ↦ congrFun (he k).2.2.1 _),
        (he k).2.2.2.1, (he k).2.2.2.2.1, (fun _ _ ↦ congrFun (he k).2.2.2.2.2 _)⟩
    have hlocalTruncation : ∀ k j, p2 (localSection k j) = j.val ∧
        (C2 k (localSection k j)).2 = 0 := fun k j ↦
      ⟨(hlocalCoeff k j).1, congrArg Prod.snd (hlocalCoeff k j).2⟩
    refine ⟨e1, e2, hcharts, localSection, (fun i ↦ rho i), s,
      hlocalContinuous, hlocalTruncation, hlocalGerm, hlocalHolomorphic,
      hlocalScaling, hrho, hrhoSumReal, hsContinuous, hsTruncation, hsScaling,
      hsWeighted, ?_⟩
    intro i j hj q hq
    rw [hsWeighted i j hj]
    exact hanchor (p1 j) (fun k hk ↦ (C2 i (localSection k ⟨j, hk⟩)).2) (C2 i q).2
  · let : IsEmpty M := not_nonempty_iff.mp hM
    let : IsEmpty (NativeLeafwiseJet1 L) :=
      ⟨fun j ↦ isEmptyElim (nativeLeafwiseJet1Base L U j)⟩
    let : IsEmpty (NativeLeafwiseJet2 L) :=
      ⟨fun j ↦ isEmptyElim (nativeLeafwiseJet2Base L U j)⟩
    refine ⟨0, Fin.elim0, Fin.elim0, (fun i ↦ Fin.elim0 i),
      (fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i), ?_, ?_, ?_, ?_⟩
    · exact fun x ↦ isEmptyElim x
    · exact fun i ↦ Fin.elim0 i
    · exact fun i ↦ Fin.elim0 i
    · let := nativeLeafwiseJet1Topology L U
        (Fin.elim0 : Fin 0 → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
      let := nativeLeafwiseJet2Topology L U
        (Fin.elim0 : Fin 0 → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
      refine ⟨Fin.elim0, Fin.elim0, (fun i ↦ Fin.elim0 i),
        (fun i ↦ Fin.elim0 i), Fin.elim0, (fun j ↦ isEmptyElim j), ?_⟩
      simp only [Fin.forall_fin_zero, true_and]
      exact ⟨(fun x ↦ isEmptyElim x), continuous_of_discreteTopology,
        (fun j ↦ isEmptyElim j), (fun _ j ↦ isEmptyElim j),
        trivial⟩

end HolomorphicAnosov.Ghys.JetPartitionSection
