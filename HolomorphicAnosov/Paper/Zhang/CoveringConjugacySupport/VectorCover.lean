import Mathlib.Topology.Covering.Quotient
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open scoped Topology
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- Zhang p.11 and Hatcher Proposition 1.40(b), pp.72–73, on the actual vector quotient. -/
theorem covering_conjugacy_vector_cover_g15
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ] :
    IsCoveringMap (QuotientAddGroup.mk : V → V ⧸ Γ.toAddSubgroup) ∧
      Function.Surjective (QuotientAddGroup.mk : V → V ⧸ Γ.toAddSubgroup) ∧
      SimplyConnectedSpace V ∧
      (∀ D : V ≃ₜ V, (∀ v, (QuotientAddGroup.mk (D v) : V ⧸ Γ.toAddSubgroup) =
        QuotientAddGroup.mk v) ↔ ∃! γ : Γ, ∀ v, D v = v + (γ : V)) := by
  have hq := Γ.toAddSubgroup.isAddQuotientCoveringMap_of_comm
    (show IsDiscrete (Γ.toAddSubgroup : Set V) from
      isDiscrete_iff_discreteTopology.mpr inferInstance)
  refine ⟨hq.isCoveringMap, hq.surjective, inferInstance, ?_⟩
  intro D
  constructor
  · intro hD
    have hzero : D 0 ∈ Γ := by
      have hz := (QuotientAddGroup.eq_iff_sub_mem.mp (hD 0))
      simpa using hz
    let γ : Γ := ⟨D 0, hzero⟩
    have he : (D : V → V) = fun v ↦ v + (γ : V) := by
      have hc : (QuotientAddGroup.mk : V → V ⧸ Γ.toAddSubgroup) ∘ D =
          QuotientAddGroup.mk ∘ (fun v ↦ v + (γ : V)) := by
        funext v
        exact (hD v).trans
          (QuotientAddGroup.eq_iff_sub_mem.mpr (by simp)).symm
      exact hq.isCoveringMap.eq_of_comp_eq D.continuous
        (continuous_id.add continuous_const) hc 0 (by simp [γ])
    refine ⟨γ, fun v ↦ congrFun he v, ?_⟩
    intro η hη
    apply Subtype.ext
    simpa [γ] using (hη 0).symm
  · rintro ⟨γ, hγ, _⟩ v
    rw [hγ v]
    exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simp)


end HolomorphicAnosov
