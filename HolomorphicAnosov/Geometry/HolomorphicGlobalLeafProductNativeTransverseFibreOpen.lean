import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

namespace HolomorphicAnosov

open Set TopologicalSpace _root_.Topology
open scoped ContDiff Manifold

universe u v w

set_option autoImplicit false

/-- A fixed transverse-coordinate fibre inside a box is intrinsically open in each native leaf.    The assertion is false for ambient subspace topology and is proved using precisely the stored plaque-generated topology and overlap law. -/
theorem native_transverse_fibre_open {d r c : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (F : RegularHolomorphicFoliation.{u, v} d r c M)
    (q : Quotient F.partition) (j : F.boxIndex) (b₀ : ComplexModel c) :
    letI := F.leafTopology q
    IsOpen {y : IntrinsicFoliationLeaf F.partition q |
      y.val ∈ (F.box j).source ∧ ((F.box j) y.val).2 = b₀} := by
  let _ := F.leafTopology q
  apply (F.topology_generated q _).mpr
  intro i b hlabel
  apply isOpen_iff_forall_mem_open.mpr
  intro a ha
  change (F.box i).symm (a.val, b.val) ∈ (F.box j).source ∧
    ((F.box j) ((F.box i).symm (a.val, b.val))).2 = b₀ at ha
  have hab : (a.val, b.val) ∈ (F.box i).target := by
    rw [F.box_target]
    exact ⟨a.property, b.property⟩
  obtain ⟨W, hW, haW, hsub, htrans⟩ := F.transverse_overlap i j _ hab ha.1
  let f : complexFoliationDisk r → ComplexModel r × ComplexModel c :=
    fun a ↦ (a.val, b.val)
  refine ⟨f ⁻¹' W, ?_, hW.preimage (continuous_subtype_val.prodMk continuous_const), haW⟩
  intro a' ha'
  change (F.box i).symm (a'.val, b.val) ∈ (F.box j).source ∧
    ((F.box j) ((F.box i).symm (a'.val, b.val))).2 = b₀
  refine ⟨(hsub ha').2, ?_⟩
  exact (htrans _ ha' _ haW rfl).trans ha.2

