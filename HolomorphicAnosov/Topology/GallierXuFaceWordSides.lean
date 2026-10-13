import HolomorphicAnosov.Topology.GallierXuFaceTriangleWitness
noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu
lemma triangle_side_for_pair2 {N : ℕ}
    {K : AbstractSimplicialComplex (Fin N)} (s : Triangle K) (o : Fin 3 ≃ ↥s.val)
    {u v : Fin N} (hu : u ∈ s.val) (hv : v ∈ s.val) (huv : u ≠ v) :
    ∃ i : Fin 3, (o i).val = u ∧ (o (finRotate 3 i)).val = v ∨
      (o i).val = v ∧ (o (finRotate 3 i)).val = u := by
  obtain ⟨i, hi⟩ := o.surjective ⟨u, hu⟩
  obtain ⟨j, hj⟩ := o.surjective ⟨v, hv⟩
  have hi' : (o i).val = u := congrArg Subtype.val hi
  have hj' : (o j).val = v := congrArg Subtype.val hj
  have hij : i ≠ j := by
    intro h
    exact huv (hi'.symm.trans ((congrArg (fun k ↦ (o k).val) h).trans hj'))
  have hrot : ∀ a b : Fin 3, a ≠ b → b = finRotate 3 a ∨ a = finRotate 3 b := by
    decide
  rcases hrot i j hij with h | h
  · exact ⟨i, Or.inl ⟨hi', h ▸ hj'⟩⟩
  · exact ⟨j, Or.inr ⟨hj', h ▸ hi'⟩⟩

end HolomorphicAnosov.Topology.GallierXu
