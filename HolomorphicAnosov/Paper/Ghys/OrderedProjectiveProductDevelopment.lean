import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ComplexProjectiveLine
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-! Ordered projective product atlases compatible with complete affine intrinsic Anosov leaves, and
their developments on holomorphic covers. (Ghys, Prop. 3.1 p.590, §4 p.597, and §5 pp.597–599) -/

noncomputable section

open Filter _root_.Topology
open scoped ContDiff

namespace HolomorphicAnosov.Ghys

universe u v w

attribute [local instance] complex_isManifold_real

/-- An intrinsic asymptotic leaf with compatible real and complex manifold structures and a complete
affine structure. (Ghys, §2 pp.588–589 and Prop. 3.1 p.590) -/
structure NativeCompleteAffineAsymptoticLeaf
    {S : Type u} [MetricSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (g : S ≃ₜ S) (P : RealTangentDistribution (realModel 2) S) (x : S) where
  native : NativeAsymptoticLeafDatum (realModel 2) g P x
  rank_two : native.rank = 2
  complexCharts : letI := native.topology
    ChartedSpace (ComplexModel 1) (StableAsymptoticLeaf g x)
  complexManifold : letI := native.topology; letI := complexCharts
    IsManifold (complexModel 1) ∞ (StableAsymptoticLeaf g x)
  realCompatibility : letI := native.topology; letI := native.charts
    letI := complexCharts
    ContMDiff (modelWithCornersSelf ℝ (Fin native.rank → ℝ)) (realModel 1) ∞
        (id : StableAsymptoticLeaf g x → StableAsymptoticLeaf g x) ∧
      ContMDiff (realModel 1) (modelWithCornersSelf ℝ (Fin native.rank → ℝ)) ∞
        (id : StableAsymptoticLeaf g x → StableAsymptoticLeaf g x)
  inclusion_holomorphic : letI := native.topology; letI := complexCharts
    ContMDiff (complexModel 1) (complexModel 2) ∞
      (Subtype.val : StableAsymptoticLeaf g x → S)
  affineStructure : letI := native.topology; letI := complexCharts
    ComplexAffineStructure (StableAsymptoticLeaf g x)
  complete : letI := native.topology; letI := complexCharts
    ComplexAffineStructure.Complete (StableAsymptoticLeaf g x) affineStructure

/-- An ordered holomorphic projective product atlas compatible with the Anosov splitting and the
complete affine structures on its intrinsic leaves. Its locally constant transitions act in
stable-first order. (Ghys, §3 p.590, §4 p.597, and §5 p.598) -/
structure OrderedProjectiveProductAtlas
    {S : Type u} [t : TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f) where
  metric : MetricSpace S
  metric_topology : t = metric.toUniformSpace.toTopologicalSpace
  stableLeaf : letI : MetricSpace S := metric.replaceTopology metric_topology
    ∀ x : S, NativeCompleteAffineAsymptoticLeaf f.toHomeomorph
      a.splitting.stable.toDistribution x
  unstableLeaf : letI : MetricSpace S := metric.replaceTopology metric_topology
    ∀ x : S, NativeCompleteAffineAsymptoticLeaf f.toHomeomorph.symm
      a.splitting.unstable.toDistribution x
  index : Type v
  chart : index → OpenPartialHomeomorph S (ComplexProjectiveLine × ComplexProjectiveLine)
  cover : ∀ x : S, ∃ i : index, x ∈ (chart i).source
  holomorphic : ∀ i : index,
    ContMDiffOn (complexModel 2) ((complexModel 1).prod (complexModel 1)) ∞
        (chart i) (chart i).source ∧
      ContMDiffOn ((complexModel 1).prod (complexModel 1)) (complexModel 2) ∞
        (chart i).symm (chart i).target
  transition : index → index → S →
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ ×
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ
  transition_locallyConstant : ∀ i j : index,
    IsLocallyConstant (fun x : ↥((chart i).source ∩ (chart j).source) ↦ transition i j x)
  transition_self : ∀ (i : index) (x : S), x ∈ (chart i).source → transition i i x = 1
  transition_comp : ∀ (i j k : index) (x : S),
    x ∈ (chart i).source ∩ (chart j).source ∩ (chart k).source →
      transition i k x = transition j k x * transition i j x
  transition_agrees : ∀ (i j : index) (x : S),
    x ∈ (chart i).source ∩ (chart j).source →
      chart j x = ((transition i j x).1 • (chart i x).1,
        (transition i j x).2 • (chart i x).2)
  stable_kernel : ∀ (i : index) (x : S), x ∈ (chart i).source →
    LinearMap.ker (mfderiv (realModel 2) (realModel 1)
      (fun y ↦ (chart i y).2) x).toLinearMap = a.splitting.stable.toDistribution x
  unstable_kernel : ∀ (i : index) (x : S), x ∈ (chart i).source →
    LinearMap.ker (mfderiv (realModel 2) (realModel 1)
      (fun y ↦ (chart i y).1) x).toLinearMap = a.splitting.unstable.toDistribution x
  stable_affine : letI : MetricSpace S := metric.replaceTopology metric_topology
    ∀ (x : S) (i : index),
      let L := stableLeaf x
      letI := L.native.topology
      letI := L.complexCharts
      ∀ y : StableAsymptoticLeaf f.toHomeomorph x, y.val ∈ (chart i).source →
        ∃ c ∈ ComplexAffineStructure.maximalAtlas _ L.affineStructure,
          y ∈ c.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
            ∀ᶠ z in 𝓝 y, z ∈ c.source ∧ z.val ∈ (chart i).source ∧
              (chart i z.val).1 = g • complexProjectiveLineFinite (c z) ∧
              (chart i z.val).2 = (chart i y.val).2
  unstable_affine : letI : MetricSpace S := metric.replaceTopology metric_topology
    ∀ (x : S) (i : index),
      let L := unstableLeaf x
      letI := L.native.topology
      letI := L.complexCharts
      ∀ y : UnstableAsymptoticLeaf f.toHomeomorph x, y.val ∈ (chart i).source →
        ∃ c ∈ ComplexAffineStructure.maximalAtlas _ L.affineStructure,
          y ∈ c.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
            ∀ᶠ z in 𝓝 y, z ∈ c.source ∧ z.val ∈ (chart i).source ∧
              (chart i z.val).2 = g • complexProjectiveLineFinite (c z) ∧
              (chart i z.val).1 = (chart i y.val).1

/-- A development of the ordered projective product atlas on a universal holomorphic cover, with
holonomy equivariant under the left deck action. (Ghys, §5 pp.597–599) -/
structure OrderedProjectiveProductDevelopment
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    {f : Biholomorph 2 2 S S} {a : AnosovDatum f}
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [ChartedSpace (ComplexModel 2) U]
    [IsManifold (complexModel 2) ∞ U] (p : U → S) where
  covering : IsCoveringMap p
  surjective : Function.Surjective p
  simplyConnected : SimplyConnectedSpace U
  cover_holomorphic : IsLocalDiffeomorph (complexModel 2) (complexModel 2) ∞ p
  developingMap : U → ComplexProjectiveLine × ComplexProjectiveLine
  localBiholomorph : IsLocalDiffeomorph (complexModel 2)
    ((complexModel 1).prod (complexModel 1)) ∞ developingMap
  holonomy : deck p →*
    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ ×
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ)
  equivariant : ∀ (γ : deck p) (x : U),
    developingMap (γ • x) = ((holonomy γ).1 • (developingMap x).1,
      (holonomy γ).2 • (developingMap x).2)
  locally_chart : ∀ x : U, ∃ (i : A.index) (N : Set U)
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ ×
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ),
    IsOpen N ∧ x ∈ N ∧ Set.MapsTo p N (A.chart i).source ∧
      ∀ y ∈ N, developingMap y = (g.1 • (A.chart i (p y)).1, g.2 • (A.chart i (p y)).2)

end HolomorphicAnosov.Ghys
