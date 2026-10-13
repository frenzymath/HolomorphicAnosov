import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgrade
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackCharts
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackIsManifold
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas.coverPullbackSheetSmooth

/-! Intrinsic partition leaves inherit complex atlases with holomorphic immersed inclusions from
their native leaves. (Lee, Prop. 1.15, p.9; HPS, p.116; Ghys, pp.588–590) -/

noncomputable section
namespace HolomorphicAnosov
open Set Filter
open scoped ContDiff Manifold _root_.Topology
universe u

variable {d s : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M]
  [IsManifold (realModel d) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
  (B : NativeTransverseAsymptoticIdentification.{u, u} f Ps Pu s 2)

/-- The intrinsic unstable partition admits complex curve atlases for which its inclusions into the
ambient complex manifold are holomorphic immersions. (Lee, Prop. 1.15, p.9; HPS, p.116; Ghys,
pp.588–590; Zhang, Prop. 2.9; Ghys, Thm B) -/
theorem native_partition_complex_structure :
    letI := B.realAmbientCharts
    ∃ C : IntrinsicComplexUnstableLeaves B.F,
      ∀ q : Quotient B.F.unstablePartition,
        letI := B.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf B.F.unstablePartition q → M) ∧
        ∀ z : IntrinsicFoliationLeaf B.F.unstablePartition q,
          Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
            (Subtype.val : IntrinsicFoliationLeaf B.F.unstablePartition q → M) z := by
  classical
  let := B.realAmbientCharts
  have hcharts : ∀ q : Quotient B.F.unstablePartition,
      letI := B.F.unstableTopology q
      ∃ c : ChartedSpace (ComplexModel 1) (IntrinsicFoliationLeaf B.F.unstablePartition q),
        letI := c
        IsManifold (complexModel 1) ∞ (IntrinsicFoliationLeaf B.F.unstablePartition q) ∧
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf B.F.unstablePartition q → M) ∧
        ∀ z : IntrinsicFoliationLeaf B.F.unstablePartition q,
          Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
            (Subtype.val : IntrinsicFoliationLeaf B.F.unstablePartition q → M) z := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      let := B.F.unstableTopology (Quotient.mk B.F.unstablePartition x)
      let := B.unstableTopology x
      let := B.unstableCharts x
      let := (B.complexU1 x).charts
      let := (B.complexU1 x).complex_manifold
      let H := B.unstableClassHomeomorph x
      let c := coverPullbackCharts (d := 1) H H.isLocalHomeomorph
      refine ⟨c, coverPullbackIsManifold (d := 1) H H.isLocalHomeomorph, ?_⟩
      let := c
      let := coverPullbackIsManifold (d := 1) H H.isLocalHomeomorph
      have hh := coverPullbackSheetSmooth (d := 1) H H.isLocalHomeomorph
        H.toOpenPartialHomeomorph (fun _ _ ↦ rfl)
      let e : Biholomorph 1 1 (B.F.ULeaf x) (UnstableAsymptoticLeaf f x) :=
        { toEquiv := H.toEquiv
          contMDiff_toFun := contMDiffOn_univ.mp hh.1
          contMDiff_invFun := contMDiffOn_univ.mp hh.2 }
      have he (z : B.F.ULeaf x) : (e z).val = z.val := B.unstable_points x z
      have heq : (Subtype.val : UnstableAsymptoticLeaf f x → M) ∘ e =
          (Subtype.val : B.F.ULeaf x → M) := funext he
      constructor
      · rw [← heq]
        exact (B.complexU1 x).inclusion_holomorphic.comp e.contMDiff
      · intro z
        rw [← heq]
        let h := (B.complexU1 x).inclusion_immersion (e z)
        have hc := h.isImmersionAtOfComplement_complement
        have hdom : e.toHomeomorph.transOpenPartialHomeomorph hc.domChart ∈
            IsManifold.maximalAtlas (complexModel 1) ∞ (B.F.ULeaf x) := by
          apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
          · exact (contMDiffOn_of_mem_maximalAtlas hc.domChart_mem_maximalAtlas).comp
              e.contMDiff.contMDiffOn (fun _ hz ↦ hz)
          · exact e.symm.contMDiff.comp_contMDiffOn
              (contMDiffOn_symm_of_mem_maximalAtlas hc.domChart_mem_maximalAtlas)
        refine ⟨h.complement, inferInstance, inferInstance, ?_⟩
        apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
          (hc.continuousAt.comp e.contMDiff.continuous.continuousAt) hc.equiv
          (e.toHomeomorph.transOpenPartialHomeomorph hc.domChart) hc.codChart
          (by simpa using hc.mem_domChart_source) hc.mem_codChart_source hdom
          hc.codChart_mem_maximalAtlas
        intro y hy
        simpa [OpenPartialHomeomorph.extend, Function.comp_def] using hc.writtenInCharts hy
  choose c hc using hcharts
  refine ⟨{ real_dimension := rfl, charts := c, complex_manifold := fun q ↦ (hc q).1 }, ?_⟩
  exact fun q ↦ (hc q).2

end HolomorphicAnosov

