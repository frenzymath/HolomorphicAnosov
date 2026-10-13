import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativePlaqueRetraction

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- Native equivalence closure gives finite holonomy transport of the smooth projection germ. -/
theorem native_projection_germ_transport {d p q : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (Fs : RegularHolomorphicFoliation.{u, v} d p q M)
    (Fu : RegularHolomorphicFoliation.{u, w} d q p M) (o : M)
    (a b : M) (hab : Fu.partition a b)
    (ha : ∃ φ : M → Fs.Leaf o,
      ContMDiffAt (complexModel d) (complexModel p) ∞ φ a ∧
      ∀ᶠ y in 𝓝 a, Fu.partition y (φ y).val) :
    ∃ φ : M → Fs.Leaf o,
      ContMDiffAt (complexModel d) (complexModel p) ∞ φ b ∧
      ∀ᶠ y in 𝓝 b, Fu.partition y (φ y).val := by
  let P : M → Prop := fun z ↦ ∃ φ : M → Fs.Leaf o,
    ContMDiffAt (complexModel d) (complexModel p) ∞ φ z ∧
    ∀ᶠ y in 𝓝 z, Fu.partition y (φ y).val
  have hstep : ∀ (i : Fu.boxIndex) (a b : M),
      a ∈ (Fu.box i).source → b ∈ (Fu.box i).source →
      ((Fu.box i) a).2 = ((Fu.box i) b).2 → P a → P b := by
    intro i a b hai hbi heq ⟨φ, hφ, hφrel⟩
    obtain ⟨α, hα, hαb, hαrel⟩ := native_plaque_retraction Fu i a b hai hbi heq
    refine ⟨φ ∘ α, hφ.comp_of_eq hα hαb, ?_⟩
    have hpre : ∀ᶠ y in 𝓝 b, Fu.partition (α y) (φ (α y)).val := by
      have ht : Filter.Tendsto α (𝓝 b) (𝓝 a) := by
        simpa only [ContinuousAt, hαb] using hα.continuousAt
      exact ht.eventually (p := fun y ↦ Fu.partition y (φ y).val) hφrel
    filter_upwards [hαrel, hpre] with y hy hpy
    exact Fu.partition.trans hy hpy
  have hp : P a ↔ P b := by
    have hgen := (Fu.partition_generated a b).mp hab
    clear hab ha
    induction hgen with
    | rel a b h =>
        obtain ⟨i, t, s, s', ha, hb⟩ := h
        have hst : (s.val, t.val) ∈ (Fu.box i).target := by
          rw [Fu.box_target]
          exact ⟨s.property, t.property⟩
        have hs't : (s'.val, t.val) ∈ (Fu.box i).target := by
          rw [Fu.box_target]
          exact ⟨s'.property, t.property⟩
        have hai : a ∈ (Fu.box i).source := ha ▸ (Fu.box i).map_target hst
        have hbi : b ∈ (Fu.box i).source := hb ▸ (Fu.box i).map_target hs't
        have heq : ((Fu.box i) a).2 = ((Fu.box i) b).2 := by
          rw [← ha, ← hb, (Fu.box i).right_inv hst, (Fu.box i).right_inv hs't]
        exact ⟨hstep i a b hai hbi heq, hstep i b a hbi hai heq.symm⟩
    | refl a => exact Iff.rfl
    | symm a b h ih => exact ih.symm
    | trans a b c h1 h2 ih1 ih2 => exact ih1.trans ih2
  exact hp.mp ha

