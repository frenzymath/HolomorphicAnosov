import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProductNativeTransverseFibreOpen

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- The actual transverse differential annihilates the native leaf inclusion.    Its composite is locally constant in the intrinsic topology, so this is a true derivative identity before any kernel or rank argument. -/
theorem native_transverse_annihilates_leaf {d r c : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (F : RegularHolomorphicFoliation.{u, v} d r c M)
    (q : Quotient F.partition) (i : F.boxIndex) :
    letI := F.leafTopology q
    letI := F.leafCharts q
    ∀ z : IntrinsicFoliationLeaf F.partition q, z.val ∈ (F.box i).source →
      (mfderiv (complexModel d) (complexModel c)
        (fun y : M ↦ ((F.box i) y).2) z.val).comp
        (mfderiv (complexModel r) (complexModel d)
          (fun y : IntrinsicFoliationLeaf F.partition q ↦ y.val) z) = 0 := by
  let _ := F.leafTopology q
  let _ := F.leafCharts q
  let _ := F.leafManifold q
  intro z hz
  let Q : M → ComplexModel c := fun y ↦ ((F.box i) y).2
  have hevent : (fun y : IntrinsicFoliationLeaf F.partition q ↦ Q y.val)
      =ᶠ[𝓝 z] (fun _ ↦ Q z.val) := by
    have hopen := native_transverse_fibre_open F q i (Q z.val)
    filter_upwards [hopen.mem_nhds ⟨hz, rfl⟩] with y hy
    exact hy.2
  have hzero := hevent.mfderiv_eq (I := complexModel r) (I' := complexModel c)
  simp only [mfderiv_const, ContinuousLinearMap.comp_zero] at hzero
  have hbox := (F.box_holomorphic i).contMDiffAt ((F.box i).open_source.mem_nhds hz)
  have hQ : MDifferentiableAt (complexModel d) (complexModel c) Q z.val :=
    (contMDiffAt_snd.comp z.val hbox).mdifferentiableAt (by simp)
  have hinc := (F.inclusion_holomorphic q).mdifferentiableAt (by simp) (x := z)
  change mfderiv (complexModel r) (complexModel c)
    (Q ∘ (fun y : IntrinsicFoliationLeaf F.partition q ↦ y.val)) z = 0 at hzero
  rw [mfderiv_comp z hQ hinc] at hzero
  exact hzero

