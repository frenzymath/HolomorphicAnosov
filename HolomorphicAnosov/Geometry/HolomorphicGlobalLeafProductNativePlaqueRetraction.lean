import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeSameBoxPartition

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- A finite plaque step transports a smooth local germ along the original partition by freezing the first coordinate in the same holomorphic box. -/
theorem native_plaque_retraction {d r c : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (F : RegularHolomorphicFoliation.{u, v} d r c M) (i : F.boxIndex)
    (a b : M) (ha : a ∈ (F.box i).source) (hb : b ∈ (F.box i).source)
    (hab : ((F.box i) a).2 = ((F.box i) b).2) :
    ∃ α : M → M, ContMDiffAt (complexModel d) (complexModel d) ∞ α b ∧
      α b = a ∧ ∀ᶠ y in 𝓝 b, F.partition y (α y) := by
  let τ : M → ComplexModel r × ComplexModel c :=
    fun y ↦ (((F.box i) a).1, ((F.box i) y).2)
  let α : M → M := (F.box i).symm ∘ τ
  have hτb : τ b = (F.box i) a := by
    exact Prod.ext rfl hab.symm
  have hαb : α b = a := by
    change (F.box i).symm (τ b) = a
    rw [hτb]
    exact (F.box i).left_inv ha
  have hτ : ContMDiffAt (complexModel d)
      ((complexModel r).prod (complexModel c)) ∞ τ b := by
    have hbox := (F.box_holomorphic i).contMDiffAt
      ((F.box i).open_source.mem_nhds hb)
    exact contMDiffAt_const.prodMk (contMDiffAt_snd.comp b hbox)
  have ht : τ b ∈ (F.box i).target := hτb ▸ (F.box i).map_source ha
  have hα : ContMDiffAt (complexModel d) (complexModel d) ∞ α b :=
    ((F.box_inverse_holomorphic i).contMDiffAt
      ((F.box i).open_target.mem_nhds ht)).comp b hτ
  refine ⟨α, hα, hαb, ?_⟩
  have hτmem := hτ.continuousAt.preimage_mem_nhds
    ((F.box i).open_target.mem_nhds ht)
  filter_upwards [(F.box i).open_source.mem_nhds hb, hτmem] with y hy hτy
  apply native_same_box_partition F i y (α y) hy ((F.box i).map_target hτy)
  have hright := (F.box i).right_inv hτy
  exact (congrArg Prod.snd hright).symm

