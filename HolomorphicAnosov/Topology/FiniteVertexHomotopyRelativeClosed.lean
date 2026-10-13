import HolomorphicAnosov.Topology.CWComplex.GlueTwoClosed
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Separation.Basic

noncomputable section
universe u v
namespace HolomorphicAnosov.Topology

/-- A map on a space covered by finitely many vertices and a closed subset can
be homotoped to send all vertices to a chosen point while keeping the closed
subset fixed, provided its vertices already map to that point.
Source: Hatcher, Algebraic Topology, proof of Theorem 2A.1 p.167, the homotopy
on the zero-skeleton together with the distinguished edge. Choose constant
tracks on vertices in the closed subset and connecting paths on the remaining
vertices. The vertex set is finite and discrete, so these tracks form a jointly
continuous map. Paste this map with the stationary homotopy on the closed
subset; they agree on the intersection. Empty vertex sets are included. -/
theorem finiteVertex_homotopy_relative_closed
    {Z : Type u} {X : Type v} [TopologicalSpace Z] [T1Space Z]
    [TopologicalSpace X] [PathConnectedSpace X]
    (V E : Set Z) (hV : V.Finite) (hE : IsClosed E)
    (hcover : ∀ z : Z, z ∈ V ∨ z ∈ E)
    (f : C(Z, X)) (x : X) (hfixed : ∀ z ∈ V ∩ E, f z = x) :
    ∃ H : C(unitInterval × Z, X),
      (∀ z, H (0, z) = f z) ∧
      (∀ t z, z ∈ E → H (t, z) = f z) ∧
      (∀ z, z ∈ V → H (1, z) = x) := by
  classical
  let : Finite V := hV.to_subtype
  let p (z : V) : Path (f z.val) x :=
    if hz : z.val ∈ E then (Path.refl (f z.val)).cast rfl
      (hfixed z.val ⟨z.property, hz⟩).symm
    else PathConnectedSpace.somePath (f z.val) x
  let tracks : C(unitInterval × V, X) :=
    ⟨fun z ↦ p z.2 z.1,
      continuous_prod_of_discrete_right.mpr (fun z ↦ (p z).continuous)⟩
  let S : Set (unitInterval × Z) := {z | z.2 ∈ V}
  let T : Set (unitInterval × Z) := {z | z.2 ∈ E}
  let a : C(S, X) := ⟨fun z ↦ tracks (z.val.1, ⟨z.val.2, z.property⟩), by
    exact tracks.continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _))⟩
  let b : C(T, X) := ⟨fun z ↦ f z.val.2,
    f.continuous.comp (continuous_snd.comp continuous_subtype_val)⟩
  obtain ⟨H, hS, hT⟩ := HolomorphicAnosov.cw_glue_two_closed S T
    (hV.isClosed.preimage continuous_snd) (hE.preimage continuous_snd)
    (fun z ↦ hcover z.2) a b (by
      intro z hzV hzE
      simp [a, b, tracks, p, show z.2 ∈ E from hzE])
  refine ⟨H, ?_, ?_, ?_⟩
  · intro z
    rcases hcover z with hz | hz
    · rw [hS (0, z) hz]
      exact (p ⟨z, hz⟩).source
    · exact hT (0, z) hz
  · intro t z hz
    exact hT (t, z) hz
  · intro z hz
    rw [hS (1, z) hz]
    exact (p ⟨z, hz⟩).target

end HolomorphicAnosov.Topology
