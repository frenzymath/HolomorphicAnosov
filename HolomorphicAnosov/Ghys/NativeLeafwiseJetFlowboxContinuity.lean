import HolomorphicAnosov.Ghys.NativeLeafwiseParametrizationJetBundle

/-! Continuity in the guarded native jet topology (Ghys, §3) -/

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology
open scoped Manifold ContDiff
universe u
set_option autoImplicit false
variable {ι : Type u} (L : ι → Type u)
variable [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace ℂ (L i)]
variable [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
variable {d : ℕ} {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real
variable [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
variable [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
variable {D : RealTangentDistribution (realModel d) M}

omit [IsManifold (complexModel d) ∞ M] in
/-- Each guarded coefficient map is continuous on its open native jet domain. (Ghys, §3) -/
theorem nativeLeafwiseJet_flowbox_continuity
    (U : HPS.LeafPartition D ι L (fun _ ↦ 2)) {n s : ℕ}
    (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin s → ℝ))) :
    letI := nativeLeafwiseJet1Topology L U c
    letI := nativeLeafwiseJet2Topology L U c
    (∀ k, IsOpen {j | nativeLeafwiseJet1Base L U j ∈ (c k).source} ∧
      ContinuousOn (nativeLeafwiseJet1Coeff L U (c k))
        {j | nativeLeafwiseJet1Base L U j ∈ (c k).source}) ∧
    (∀ k, IsOpen {j | nativeLeafwiseJet2Base L U j ∈ (c k).source} ∧
      ContinuousOn (nativeLeafwiseJet2Coeff L U (c k))
        {j | nativeLeafwiseJet2Base L U j ∈ (c k).source}) ∧
    ((∀ x : M, ∃ k, x ∈ (c k).source) →
      Continuous (nativeLeafwiseJet1Base L U) ∧
      Continuous (nativeLeafwiseJet2Base L U)) := by
  let := nativeLeafwiseJet1Topology L U c
  let := nativeLeafwiseJet2Topology L U c
  have h1 : ∀ k, IsOpen {j | nativeLeafwiseJet1Base L U j ∈ (c k).source} ∧
      ContinuousOn (nativeLeafwiseJet1Coeff L U (c k))
        {j | nativeLeafwiseJet1Base L U j ∈ (c k).source} := by
    intro k
    have hopen : IsOpen {j | nativeLeafwiseJet1Base L U j ∈ (c k).source} :=
      TopologicalSpace.isOpen_generateFrom_of_mem
        ⟨k, Set.univ, isOpen_univ, by ext j; simp⟩
    refine ⟨hopen, (continuousOn_open_iff hopen).mpr ?_⟩
    intro O hO
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨k, O, hO, rfl⟩
  have h2 : ∀ k, IsOpen {j | nativeLeafwiseJet2Base L U j ∈ (c k).source} ∧
      ContinuousOn (nativeLeafwiseJet2Coeff L U (c k))
        {j | nativeLeafwiseJet2Base L U j ∈ (c k).source} := by
    intro k
    have hopen : IsOpen {j | nativeLeafwiseJet2Base L U j ∈ (c k).source} :=
      TopologicalSpace.isOpen_generateFrom_of_mem
        ⟨k, Set.univ, isOpen_univ, by ext j; simp⟩
    refine ⟨hopen, (continuousOn_open_iff hopen).mpr ?_⟩
    intro O hO
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨k, O, hO, rfl⟩
  refine ⟨h1, h2, ?_⟩
  intro hcover
  constructor
  · rw [continuous_iff_continuousAt]
    intro j
    obtain ⟨k, hj⟩ := hcover (nativeLeafwiseJet1Base L U j)
    have hc := ((h1 k).2.continuousAt ((h1 k).1.mem_nhds hj)).fst
    have hs := ((c k).continuousAt_symm ((c k).map_source hj)).comp (x := j) hc
    apply hs.congr
    filter_upwards [(h1 k).1.mem_nhds hj] with j' hj'
    exact (c k).left_inv hj'
  · rw [continuous_iff_continuousAt]
    intro j
    obtain ⟨k, hj⟩ := hcover (nativeLeafwiseJet2Base L U j)
    have hc := ((h2 k).2.continuousAt ((h2 k).1.mem_nhds hj)).fst.fst
    have hs := ((c k).continuousAt_symm ((c k).map_source hj)).comp (x := j) hc
    apply hs.congr
    filter_upwards [(h2 k).1.mem_nhds hj] with j' hj'
    exact (c k).left_inv hj'

omit [IsManifold (complexModel d) ∞ M] in
/-- The guarded coefficient criterion for continuity into the original native second-jet topology. (Ghys, §3) -/
theorem nativeLeafwiseJetSection_continuous_of_coeff
    (U : HPS.LeafPartition D ι L (fun _ ↦ 2)) {n s : ℕ}
    (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin s → ℝ)))
    (σ : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
    (hbase : ∀ j, nativeLeafwiseJet2Base L U (σ j) = nativeLeafwiseJet1Base L U j) :
    letI := nativeLeafwiseJet1Topology L U c
    letI := nativeLeafwiseJet2Topology L U c
    (∀ k, ContinuousOn (fun j ↦ nativeLeafwiseJet2Coeff L U (c k) (σ j))
      {j | nativeLeafwiseJet1Base L U j ∈ (c k).source}) → Continuous σ := by
  let := nativeLeafwiseJet1Topology L U c
  let := nativeLeafwiseJet2Topology L U c
  intro hcoeff
  apply continuous_generateFrom_iff.mpr
  rintro S ⟨k, O, hO, rfl⟩
  have hguard := (nativeLeafwiseJet_flowbox_continuity L U c).1 k |>.1
  have ho := (continuousOn_open_iff hguard).mp (hcoeff k) O hO
  convert ho using 1
  ext j
  simp only [mem_preimage, mem_ofPred_eq, mem_inter_iff, hbase]

omit [IsManifold (complexModel d) ∞ M] in
/-- A continuous quadratic flowbox coefficient gives a continuous homogeneous section on the native total jet carrier. (Ghys, §3) -/
theorem nativeLeafwiseJetSection_continuous_of_quadratic_coeff
    (U : HPS.LeafPartition D ι L (fun _ ↦ 2)) {n s : ℕ}
    (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin s → ℝ)))
    (hcover : ∀ x : M, ∃ k, x ∈ (c k).source)
    (σ : NativeLeafwiseJet1 L → NativeLeafwiseJet2 L)
    (hbase : ∀ j, nativeLeafwiseJet2Base L U (σ j) = nativeLeafwiseJet1Base L U j)
    (A : Fin n → M → ℂ)
    (hA : ∀ k, ContinuousOn (A k) (c k).source)
    (hcoeff : ∀ k j, nativeLeafwiseJet1Base L U j ∈ (c k).source →
      nativeLeafwiseJet2Coeff L U (c k) (σ j) =
        (nativeLeafwiseJet1Coeff L U (c k) j,
          A k (nativeLeafwiseJet1Base L U j) * (nativeLeafwiseJet1Coeff L U (c k) j).2 ^ 2)) :
    letI := nativeLeafwiseJet1Topology L U c
    letI := nativeLeafwiseJet2Topology L U c
    Continuous σ := by
  let := nativeLeafwiseJet1Topology L U c
  let := nativeLeafwiseJet2Topology L U c
  apply nativeLeafwiseJetSection_continuous_of_coeff L U c σ hbase
  intro k
  have htop := nativeLeafwiseJet_flowbox_continuity L U c
  have hB := (htop.2.2 hcover).1
  have hC := (htop.1 k).2
  have hAk := (hA k).comp hB.continuousOn (fun j hj ↦ hj)
  apply (hC.prodMk (hAk.mul (hC.snd.pow 2))).congr
  intro j hj
  exact hcoeff k j hj

end HolomorphicAnosov.Ghys
