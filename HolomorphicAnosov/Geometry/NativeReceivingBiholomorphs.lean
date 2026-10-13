import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgrade
import Mathlib.Geometry.Manifold.Immersion

/-! Point-preserving identifications of native receiving leaves are biholomorphic when the
partition-leaf inclusions are holomorphic immersions. (Ghys, pp. 588–590; HPS, p. 116) -/

noncomputable section
namespace HolomorphicAnosov
open Set
open scoped ContDiff Manifold Topology _root_.Topology
universe u

variable {d s t : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
  (B : NativeTransverseAsymptoticIdentification.{u, u} f Ps Pu s t)

/-- The point-preserving native receiving homeomorphisms are biholomorphic if the partition-leaf
inclusions are holomorphic immersions. (Ghys, pp. 588–590 and Thm. B; HPS, p. 116; Zhang, Prop.
2.9) -/
theorem native_receiving_biholomorphs
    (C : letI := B.realAmbientCharts; IntrinsicComplexUnstableLeaves B.F)
    (hC : letI := B.realAmbientCharts
      ∀ q : Quotient B.F.unstablePartition,
        letI := B.F.unstableTopology q
        letI := C.charts q
        ContMDiff (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf B.F.unstablePartition q → M) ∧
        ∀ z : IntrinsicFoliationLeaf B.F.unstablePartition q,
          Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
            (Subtype.val : IntrinsicFoliationLeaf B.F.unstablePartition q → M) z) :
    ∃ E : ∀ x : M, letI := B.realAmbientCharts
      letI := C.charts (Quotient.mk B.F.unstablePartition x)
      letI := B.unstableTopology x
      letI := B.unstableCharts x
      letI := (B.complexU1 x).charts
      Biholomorph 1 1 (B.F.ULeaf x) (UnstableAsymptoticLeaf f x),
      letI := B.realAmbientCharts
      ∀ x : M, letI := B.unstableTopology x
        letI := B.unstableCharts x
        letI := (B.complexU1 x).charts
        letI := C.charts (Quotient.mk B.F.unstablePartition x)
        (E x).toHomeomorph = B.unstableClassHomeomorph x := by
  classical
  let := B.realAmbientCharts
  have hE : ∀ x : M,
      letI := C.charts (Quotient.mk B.F.unstablePartition x)
      letI := B.unstableTopology x
      letI := B.unstableCharts x
      letI := (B.complexU1 x).charts
      ∃ e : Biholomorph 1 1 (B.F.ULeaf x) (UnstableAsymptoticLeaf f x),
        e.toHomeomorph = B.unstableClassHomeomorph x := by
    intro x
    let := C.charts (Quotient.mk B.F.unstablePartition x)
    let := B.unstableTopology x
    let := B.unstableCharts x
    let := (B.complexU1 x).charts
    let H := B.unstableClassHomeomorph x
    have hforward : (Subtype.val : UnstableAsymptoticLeaf f x → M) ∘ H =
        (Subtype.val : B.F.ULeaf x → M) := funext (B.unstable_points x)
    have hinverse : (Subtype.val : B.F.ULeaf x → M) ∘ H.symm =
        (Subtype.val : UnstableAsymptoticLeaf f x → M) := by
      funext z
      have hz := B.unstable_points x (H.symm z)
      change (H (H.symm z)).val = (H.symm z).val at hz
      simpa only [Function.comp_apply, H.apply_symm_apply] using hz.symm
    have hs : ContMDiff (complexModel 1) (complexModel 1) ∞ H := by
      intro z
      apply (ContMDiffAt.iff_comp_isImmersionAt
        ((B.complexU1 x).inclusion_immersion (H z))).mpr
      refine ⟨H.continuous.continuousAt, ?_⟩
      rw [hforward]
      exact (hC (Quotient.mk B.F.unstablePartition x)).1 z
    have hi : ContMDiff (complexModel 1) (complexModel 1) ∞ H.symm := by
      intro z
      apply (ContMDiffAt.iff_comp_isImmersionAt
        ((hC (Quotient.mk B.F.unstablePartition x)).2 (H.symm z))).mpr
      refine ⟨H.symm.continuous.continuousAt, ?_⟩
      rw [hinverse]
      exact (B.complexU1 x).inclusion_holomorphic z
    exact ⟨{ toEquiv := H.toEquiv, contMDiff_toFun := hs, contMDiff_invFun := hi }, rfl⟩
  choose E hE using hE
  exact ⟨E, hE⟩

end HolomorphicAnosov

