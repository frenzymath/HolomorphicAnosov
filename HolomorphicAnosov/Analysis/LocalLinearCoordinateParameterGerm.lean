import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Continuous
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.OpenPartialHomeomorph.Defs

noncomputable section
open Set Filter Topology _root_.Topology
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- Pull a normalized local linear-coordinate identity to a continuous transverse parameter,
then express both varying coordinate fibres in a fixed complex normed space.

Source ingredients: Zhang, Codimension-one holomorphic Anosov diffeomorphisms, Lemma 2.8,
pp.9–10, its normalized coordinate neighborhood and linear coefficient; Nisoli, Chapter 1,
equation (1.11), pp.22–23, chronological coordinate composition. The parameter and fibre
identifications here are an agent-written expansion. Continuity pulls the open coordinate
neighborhood back to the parameter center. On that neighborhood coordinate inversion places
the actual source point inside the local map's source. Its prescribed parameter correspondence
then replaces its image by the receiving parametrization. Finally conjugate the coefficient by
the two fixed-fibre identifications. No off-source value or target continuity is used.
-/
theorem local_linear_coordinate_parameter_germ
    {Y L L' E E' V : Type*} [TopologicalSpace Y] [TopologicalSpace L]
    [TopologicalSpace L'] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : Y) (jx : Y → L) (jy : Y → L') (hjx : ContinuousAt jx w)
    (e : OpenPartialHomeomorph L L') (φx : L ≃ₜ E) (φy : L' ≃ₜ E')
    (hx : φx (jx w) = 0) (D : E ≃L[ℂ] E')
    (N : Set E) (hN : IsOpen N) (hzero : 0 ∈ N)
    (hlinear : ∀ v ∈ N, φx.symm v ∈ e.source ∧ φy (e (φx.symm v)) = D v)
    (hparam : ∀ v, jx v ∈ e.source → e (jx v) = jy v)
    (Jx : E ≃L[ℂ] V) (Jy : E' ≃L[ℂ] V) :
    ∀ᶠ v in 𝓝 w, jx v ∈ e.source ∧
      Jy (φy (jy v)) = ((Jx.symm.trans D).trans Jy) (Jx (φx (jx v))) := by
  have hn : ∀ᶠ v in 𝓝 w, φx (jx v) ∈ N :=
    (φx.continuous.continuousAt.comp hjx).eventually_mem
      (hN.mem_nhds (by simpa only [Function.comp_apply, hx] using hzero))
  filter_upwards [hn] with v hv
  obtain ⟨hsrc, heq⟩ := hlinear (φx (jx v)) hv
  simp only [φx.symm_apply_apply] at hsrc heq
  refine ⟨hsrc, ?_⟩
  rw [hparam v hsrc] at heq
  simpa only [ContinuousLinearEquiv.trans_apply, Jx.symm_apply_apply] using congrArg Jy heq


end HolomorphicAnosov
