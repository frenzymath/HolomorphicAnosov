import HolomorphicAnosov.Paper.Ghys.NativeUnstablePointHomeomorph
import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import Mathlib.Geometry.Manifold.Immersion

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set
open scoped ContDiff Manifold
universe u v w

/-- The point-preserving comparison of two native unstable carriers is biholomorphic for their supplied complex atlases. (Ghys, §§2, 5; HPS, §7) -/
theorem native_unstable_point_biholomorph_g10
    {d s s' : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (realModel d) ∞ M]
    [SecondCountableTopology M]
    {f : M ≃ₜ M} {Ps Pu : RealTangentDistribution (realModel d) M}
    (A : NativeTransverseAsymptoticIdentification.{u, v} f Ps Pu s 2)
    (B : NativeTransverseAsymptoticIdentification.{u, w} f Ps Pu s' 2)
    (CA : letI := A.realAmbientCharts; IntrinsicComplexUnstableLeaves A.F)
    (CB : letI := B.realAmbientCharts; IntrinsicComplexUnstableLeaves B.F)
    (x : M)
    (hA : letI := A.realAmbientCharts
      letI := CA.charts (Quotient.mk A.F.unstablePartition x)
      ContMDiff (complexModel 1) (complexModel d) ∞ (Subtype.val : A.F.ULeaf x → M) ∧
      ∀ z : A.F.ULeaf x, Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
        (Subtype.val : A.F.ULeaf x → M) z)
    (hB : letI := B.realAmbientCharts
      letI := CB.charts (Quotient.mk B.F.unstablePartition x)
      ContMDiff (complexModel 1) (complexModel d) ∞ (Subtype.val : B.F.ULeaf x → M))
    (hBInv : letI := B.realAmbientCharts
      letI := CB.charts (Quotient.mk B.F.unstablePartition x)
      letI := B.F.unstableCharts (Quotient.mk B.F.unstablePartition x)
      letI := (B.nativeU x).topology
      letI := (B.nativeU x).charts
      letI := (B.complexU1 x).charts
      ContMDiff (complexModel 1) (complexModel 1) ∞ (B.unstableIdentification x).symm) :
    letI := A.realAmbientCharts
    letI := B.realAmbientCharts
    letI := CA.charts (Quotient.mk A.F.unstablePartition x)
    letI := CB.charts (Quotient.mk B.F.unstablePartition x)
    ∃ e : Biholomorph 1 1 (A.F.ULeaf x) (B.F.ULeaf x),
      ∀ z, (e z).val = z.val := by
  let := A.realAmbientCharts
  let := B.realAmbientCharts
  let := CA.charts (Quotient.mk A.F.unstablePartition x)
  let := CB.charts (Quotient.mk B.F.unstablePartition x)
  let := B.F.unstableCharts (Quotient.mk B.F.unstablePartition x)
  obtain ⟨H, hH⟩ := native_unstable_point_homeomorph A B x
  let := (B.nativeU x).topology
  let := (B.nativeU x).charts
  let := (B.complexU1 x).charts
  let T := H.trans (B.unstableClassHomeomorph x)
  have hTval : ∀ z : A.F.ULeaf x, (T z).val = z.val := by
    intro z
    exact (B.unstable_points x (H z)).trans (hH z)
  have hT : ContMDiff (complexModel 1) (complexModel 1) ∞ T := by
    intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt
      ((B.complexU1 x).inclusion_immersion (T z))).mpr
    refine ⟨T.continuous.continuousAt, ?_⟩
    have heq : (Subtype.val : UnstableAsymptoticLeaf f x → M) ∘ T =
        (Subtype.val : A.F.ULeaf x → M) := funext hTval
    rw [heq]
    exact hA.1 z
  have hforward : ContMDiff (complexModel 1) (complexModel 1) ∞ H := by
    have heq : ((B.unstableIdentification x).symm : _ → _) ∘ T = H := by
      funext z
      exact (B.unstableIdentification x).symm_apply_apply (H z)
    rw [← heq]
    exact hBInv.comp hT
  have hinverse : ContMDiff (complexModel 1) (complexModel 1) ∞ H.symm := by
    intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt (hA.2 (H.symm z))).mpr
    refine ⟨H.symm.continuous.continuousAt, ?_⟩
    have heq : (Subtype.val : A.F.ULeaf x → M) ∘ H.symm =
        (Subtype.val : B.F.ULeaf x → M) := by
      funext z
      exact (hH (H.symm z)).symm.trans (congrArg Subtype.val (H.apply_symm_apply z))
    rw [heq]
    exact hB z
  exact ⟨{ toEquiv := H.toEquiv, contMDiff_toFun := hforward,
           contMDiff_invFun := hinverse }, hH⟩

end HolomorphicAnosov.Ghys
