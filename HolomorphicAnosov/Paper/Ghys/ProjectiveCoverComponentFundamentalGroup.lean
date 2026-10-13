import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Connected.LocallyConnected

/-! Inclusion of an open connected component induces an equivalence of based fundamental groups.
(Hatcher, Prop. 1.31 and the component reduction preceding Prop. 1.38) -/

open Set
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Ghys

/-- The canonical inclusion of the open connected component through `x₀` induces an equivalence of
based fundamental groups. -/
theorem projective_cover_component_fundamental_group_equiv_gap
    {M : Type u} [TopologicalSpace M] [LocallyConnectedSpace M] (x₀ : M) :
    let C := connectedComponent x₀
    let i : C → M := Subtype.val
    ∃ e : FundamentalGroup C ⟨x₀, mem_connectedComponent⟩ ≃*
        FundamentalGroup M x₀,
      e.toMonoidHom = FundamentalGroup.mapOfEq
        ⟨i, continuous_subtype_val⟩ rfl := by
  let C := connectedComponent x₀
  let c : C := ⟨x₀, mem_connectedComponent⟩
  let i : C(C, M) := ⟨Subtype.val, continuous_subtype_val⟩
  let f : FundamentalGroup C c →* FundamentalGroup M x₀ := FundamentalGroup.mapOfEq i rfl
  have path_range : ∀ {y : M}, (p : Path x₀ y) →
      Set.range p ⊆ connectedComponent x₀ := by
    intro y p
    have hx : x₀ ∈ Set.range p := ⟨0, p.source⟩
    exact (isPreconnected_range p.continuous).subset_connectedComponent hx
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      induction a using Path.Homotopic.Quotient.ind with | mk p =>
      induction b using Path.Homotopic.Quotient.ind with | mk q =>
      have hm : (p.map i.continuous).Homotopic (q.map i.continuous) := by
        apply Path.Homotopic.Quotient.exact
        simpa only [f, FundamentalGroup.mapOfEq_apply,
          Path.Homotopic.Quotient.cast_rfl_rfl, ← Path.Homotopic.Quotient.mk_map] using hab
      rcases hm with ⟨F⟩
      apply Path.Homotopic.Quotient.eq.mpr
      refine ⟨{
        toFun := fun z => ⟨F z, path_range (F.eval z.1) ⟨z.2, rfl⟩⟩
        continuous_toFun := (map_continuous F).subtype_mk _
        map_zero_left := ?_
        map_one_left := ?_
        prop' := ?_
      }⟩
      · intro t
        apply Subtype.ext
        exact F.apply_zero t
      · intro t
        apply Subtype.ext
        exact F.apply_one t
      · intro t z hz
        apply Subtype.ext
        exact F.eq_fst t hz
    · intro a
      induction a using Path.Homotopic.Quotient.ind with | mk p =>
      let q : Path c c := {
        toFun := fun t => ⟨p t, path_range p ⟨t, rfl⟩⟩
        continuous_toFun := p.continuous.subtype_mk _
        source' := Subtype.ext p.source
        target' := Subtype.ext p.target
      }
      refine ⟨Path.Homotopic.Quotient.mk q, ?_⟩
      simp only [f, FundamentalGroup.mapOfEq_apply,
        Path.Homotopic.Quotient.cast_rfl_rfl, ← Path.Homotopic.Quotient.mk_map]
      congr 1
  exact ⟨MulEquiv.ofBijective f hf, rfl⟩


end HolomorphicAnosov.Ghys
