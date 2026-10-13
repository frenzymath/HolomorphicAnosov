import HolomorphicAnosov.Geometry.TransverseMobiusFrameGerm

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov.Ghys
/-- A continuous frame family gives locally fixed representatives of its projective
coordinate germs. (Thurston, §3.5, pp. 34–35) -/
theorem transverse_mobius_frame_continuation_g4
    {M L ι K : Type*} [TopologicalSpace M] [TopologicalSpace L] [TopologicalSpace K]
    (A : FlatProjectiveAtlas M L ι) (Z : FiberBundleCore ι M MobiusGroup)
    (hbase : Z.baseSet = fun i ↦ (A.chart i).source)
    (hindex : Z.indexAt = A.indexAt)
    (hchange : Z.coordChange = fun i j x g ↦ g * (A.transition i j x)⁻¹)
    (α : K → M) (hα : Continuous α) (s : C(K, Z.TotalSpace))
    (hs : ∀ t, (s t).proj = α t) :
    ∀ t, ∃ T : Set K, IsOpen T ∧ t ∈ T ∧ ∃ i, ∃ g : ComplexMobiusTransformation,
      ∃ U : Set M, IsOpen U ∧ α t ∈ U ∧ U ⊆ (A.chart i).source ∧
        ∀ u ∈ T, α u ∈ U ∧
          (fun w ↦ (mobiusGroupToComplexMobius (s u).2).apply
            (complexProjectiveLineFinite ((A.chart (A.indexAt (s u).proj) w).2)))
          =ᶠ[𝓝 (α u)]
          (fun w ↦ g.apply (complexProjectiveLineFinite ((A.chart i w).2))) := by
  intro t
  let i := A.indexAt (α t)
  have hi : α t ∈ (A.chart i).source := A.mem_source _
  have hst : s t ∈ (Z.localTriv i).source := by
    rw [(Z.localTriv i).mem_source, ← Z.baseSet_at, hbase]
    simpa only [hs t] using hi
  let a : MobiusGroup := (Z.localTriv i (s t)).2
  have hlabelAt : ContinuousAt (fun z : Z.TotalSpace ↦ (Z.localTriv i z).2) (s t) :=
    ((Z.localTriv i).toOpenPartialHomeomorph.continuousAt hst).snd
  have hlabel : ∀ᶠ u in 𝓝 t, (Z.localTriv i (s u)).2 = a :=
    s.continuous.continuousAt (hlabelAt.eventually
      ((isOpen_discrete {a}).mem_nhds rfl))
  have hin : ∀ᶠ u in 𝓝 t, α u ∈ (A.chart i).source :=
    hα.continuousAt ((A.chart i).open_source.mem_nhds hi)
  obtain ⟨T, hTsub, hT, htT⟩ := mem_nhds_iff.mp (hlabel.and hin)
  refine ⟨T, hT, htT, i, mobiusGroupToComplexMobius a, (A.chart i).source,
    (A.chart i).open_source, hi, subset_rfl, ?_⟩
  intro u hu
  have h := hTsub hu
  refine ⟨h.2, ?_⟩
  simpa only [hs u, h.1] using transverse_mobius_frame_germ A Z hindex hchange
    (s u) i (by rw [hs u]; exact h.2)

end HolomorphicAnosov.Ghys
