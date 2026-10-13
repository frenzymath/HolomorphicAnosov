import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingInjectiveBaseStage
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingLeafTools
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingSetTools
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingGraphIntersection
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingOnePointInduction
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingGraphTransport
import HolomorphicAnosov.Paper.Ghys.SurfaceDevelopingNativeStageInduction
import HolomorphicAnosov.Paper.Ghys.SurfaceGraphPatching
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Topology.GraphComplementConnected
import HolomorphicAnosov.Topology.SurfaceInjectivityKernel
import HolomorphicAnosov.Paper.Ghys.SurfaceProjectiveProduct
import HolomorphicAnosov.Paper.Ghys.CompleteLiftedProjectiveLeaves
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Connected.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLine
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic
import HolomorphicAnosov.Geometry.NativeProjectiveLineTopology

/-!
Injectivity of the developing map and continuous graph-complement descriptions of its
image on connected positive finite prefixes of unstable saturations.
(Ghys, Lemma 5.2, pp. 599–600)
-/

noncomputable section
open Set _root_.Topology
open scoped ContDiff

universe u v w
namespace HolomorphicAnosov.Ghys

attribute [local instance] complex_isManifold_real



/-- The developing map is injective on each connected nonempty finite prefix of open unstable
saturations. Its image is a continuous graph complement over the projective line with at
most one base point removed. (Ghys, pp. 599–600) -/
theorem surface_developing_injective_finite_prefix
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [T2Space U]
    [ChartedSpace (ComplexModel 2) U] [IsManifold (complexModel 2) ∞ U]
    (p : U → S) (D : OrderedProjectiveProductDevelopment A p)
    (hleaves : CompleteLiftedProjectiveLeaves D) (x : ℕ → U)
    (hopen : ∀ i, IsOpen (unstableSaturation D (x i)))
    (hprefix : ∀ n, 1 ≤ n → IsConnected
      (⋃ i ∈ Finset.range n, unstableSaturation D (x i))) :
    ∀ n, 1 ≤ n → Set.InjOn D.developingMap
      (⋃ i ∈ Finset.range n, unstableSaturation D (x i)) ∧
      ∃ (F : Set ComplexProjectiveLine)
        (u : C({p : ComplexProjectiveLine // p ∉ F}, ComplexProjectiveLine)),
        (F = ∅ ∨ ∃ pole : ComplexProjectiveLine, F = {pole}) ∧
        D.developingMap '' (⋃ i ∈ Finset.range n, unstableSaturation D (x i)) =
          {z | ∃ hp : z.1 ∉ F, z.2 ≠ u ⟨z.1, hp⟩} :=
  native_stage_induction_with_homeomorph f a A p D hleaves
    NativeProjectiveTopology.nativeProjectiveLineHomeomorphOnePoint x hopen hprefix

/-- For an open connected cover by unstable saturations with connected positive prefixes,
the developing map is injective on every positive prefix. Each prefix image is a continuous
graph complement over the projective line with at most one base point removed.
(Ghys, Lemma 5.2, pp. 599–600) -/
theorem surface_developing_injective_stage_induction
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsCompactComplexManifold 2 S]
    (f : Biholomorph 2 2 S S) (a : AnosovDatum f)
    (A : OrderedProjectiveProductAtlas.{u, v} f a)
    {U : Type w} [TopologicalSpace U] [T2Space U]
    [ChartedSpace (ComplexModel 2) U] [IsManifold (complexModel 2) ∞ U]
    (p : U → S) (D : OrderedProjectiveProductDevelopment A p)
    (hleaves : CompleteLiftedProjectiveLeaves D)
    (x : ℕ → U)
    (hopen : ∀ i : ℕ, IsOpen (unstableSaturation D (x i)))
    (hconn : ∀ i : ℕ, IsConnected (unstableSaturation D (x i)))
    (hcover : (⋃ i : ℕ, unstableSaturation D (x i)) = Set.univ) :
    let Ω : ℕ → Set U := fun n ↦ ⋃ i ∈ Finset.range n, unstableSaturation D (x i)
    (∀ n : ℕ, 1 ≤ n → IsConnected (Ω n)) →
    ∀ n : ℕ, 1 ≤ n →
      Set.InjOn D.developingMap (Ω n) ∧
      ∃ (F : Set ComplexProjectiveLine)
        (u : C({p : ComplexProjectiveLine // p ∉ F}, ComplexProjectiveLine)),
        (F = ∅ ∨ ∃ pole : ComplexProjectiveLine, F = {pole}) ∧
        D.developingMap '' Ω n =
          {z : ComplexProjectiveLine × ComplexProjectiveLine |
            ∃ hp : z.1 ∉ F, z.2 ≠ u ⟨z.1, hp⟩} := by
  have _ := hconn
  have _ := hcover
  dsimp only
  intro hprefix
  exact surface_developing_injective_finite_prefix f a A p D hleaves x hopen hprefix


end HolomorphicAnosov.Ghys
