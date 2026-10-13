import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import HolomorphicAnosov.Ghys.AffineProjectiveStructure

/-! This file identifies the stable and unstable Anosov leaves, their inclusions, and their
intrinsic real and complex structures with partition classes of the manifold. It also defines
affine action on the intrinsic unstable leaves. (HPS, §7, pp.115–116; Ghys, §2, pp.588–589; §3,
p.590) -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

variable {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]

/-- A presentation of the stable and unstable Anosov foliations by intrinsic partition classes, with
compatible real and complex leaf structures and transverse product boxes. It identifies the leaf
inclusions and tangent images with those of the Anosov foliations. (HPS, §7, pp.115–116; Ghys,
§2, pp.588–589) -/
structure AnosovIntrinsicFoliationPresentation
    (f : Biholomorph d d M M) (a : AnosovDatum f) where
  realCharts : ChartedSpace (Fin ((2*d-2)+2) → ℝ) M
  foliations : letI := realCharts
    TransverseContinuousFoliations.{u, u} (2*d-2) 2 M
  complexLeaves : letI := realCharts
    IntrinsicComplexUnstableLeaves foliations
  metric : MetricSpace M
  metric_topology : metric.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace M)
  stable_asymptotic : ∀ x y : M,
    foliations.stablePartition x y ↔ @ForwardAsymptotic M metric f x y
  unstable_asymptotic : ∀ x y : M,
    foliations.unstablePartition x y ↔ @ForwardAsymptotic M metric f.symm x y
  stableSmooth : ∀ q : Quotient foliations.stablePartition,
    letI := foliations.stableTopology q
    letI := foliations.stableCharts q
    IsManifold 𝓘(ℝ, Fin (2*d-2) → ℝ) ∞
      (IntrinsicFoliationLeaf foliations.stablePartition q)
  unstableSmooth : ∀ q : Quotient foliations.unstablePartition,
    letI := foliations.unstableTopology q
    letI := foliations.unstableCharts q
    IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞
      (IntrinsicFoliationLeaf foliations.unstablePartition q)
  stableNative : ∀ q : Quotient foliations.stablePartition,
    letI := foliations.stableTopology q
    letI := foliations.stableCharts q
    letI := stableSmooth q
    HPS.NativeLeaf (r := 2*d-2) a.splitting.stable.toDistribution
      (IntrinsicFoliationLeaf foliations.stablePartition q)
  unstableNative : ∀ q : Quotient foliations.unstablePartition,
    letI := foliations.unstableTopology q
    letI := foliations.unstableCharts q
    letI := unstableSmooth q
    HPS.NativeLeaf (r := 2) a.splitting.unstable.toDistribution
      (IntrinsicFoliationLeaf foliations.unstablePartition q)
  stable_inclusion_eq : ∀ q,
    letI := foliations.stableTopology q
    letI := foliations.stableCharts q
    letI := stableSmooth q
    (stableNative q).inclusion = Subtype.val
  unstable_inclusion_eq : ∀ q,
    letI := foliations.unstableTopology q
    letI := foliations.unstableCharts q
    letI := unstableSmooth q
    (unstableNative q).inclusion = Subtype.val
  unstable_real_complex_compatible : ∀ q : Quotient foliations.unstablePartition,
    letI := foliations.unstableTopology q
    letI := foliations.unstableCharts q
    letI := complexLeaves.charts q
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) (realModel 1) ∞
        (id : IntrinsicFoliationLeaf foliations.unstablePartition q →
          IntrinsicFoliationLeaf foliations.unstablePartition q) ∧
      ContMDiff (realModel 1) 𝓘(ℝ, Fin 2 → ℝ) ∞
        (id : IntrinsicFoliationLeaf foliations.unstablePartition q →
          IntrinsicFoliationLeaf foliations.unstablePartition q)
  unstable_holomorphic : ∀ q : Quotient foliations.unstablePartition,
    letI := foliations.unstableTopology q
    letI := complexLeaves.charts q
    ContMDiff (complexModel 1) (complexModel d) ∞
      (Subtype.val : IntrinsicFoliationLeaf foliations.unstablePartition q → M)

section AffineAction
variable {s : ℕ} [ChartedSpace (Fin (s+2) → ℝ) M]
variable (F : TransverseContinuousFoliations.{u,u} s 2 M)
  (C : IntrinsicComplexUnstableLeaves F)

/-- The map acts affinely on unstable leaves when its expression in any source and target maximal
affine charts is an invertible affine germ at each source point. (Ghys, Prop. 3.1(i), p.590) -/
def AffineUnstableLeafStructures.ActsAffinely
    (A : AffineUnstableLeafStructures F C) (f : M → M) : Prop :=
  ∀ (x : M) (c : OpenPartialHomeomorph (F.ULeaf x) ℂ)
    (e : OpenPartialHomeomorph (F.ULeaf (f x)) ℂ),
    (letI := C.charts (Quotient.mk F.unstablePartition x);
      c ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint F C x)) →
    (letI := C.charts (Quotient.mk F.unstablePartition (f x));
      e ∈ ComplexAffineStructure.maximalAtlas _ (A.atPoint F C (f x))) →
    F.uPoint x ∈ c.source → F.uPoint (f x) ∈ e.source →
    ∃ b : ComplexAffineTransformation,
      ∀ᶠ y in 𝓝 (F.uPoint x), y ∈ c.source ∧
        ∃ z : F.ULeaf (f x), z.val = f y.val ∧ z ∈ e.source ∧
          e z = b.apply (c y)
end AffineAction
end HolomorphicAnosov.Ghys
