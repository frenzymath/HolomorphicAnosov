import HolomorphicAnosov.Topology.CWComplex.DiskAdjunction

/-! Universal property of finite disk adjunctions.
Source: Hatcher, Algebraic Topology, Appendix p.519, quotient attachment. -/
open TopCat
open scoped TopCat
universe u v
namespace HolomorphicAnosov.FiniteCellAdjunction

/-- Compatible continuous maps on the old space and attached disks descend
uniquely to the actual adjunction quotient. The coproduct map is continuous,
respects each boundary generator and hence its equivalence closure. Quotient
lifting gives the descent and its continuity; representative induction gives
uniqueness. This is the universal property underlying the attaching pushout,
with the original quotient topology and arbitrary continuous attachments. -/
theorem adjunction_desc_existsUnique {n : ℕ} {X : TopCat.{u}} {k : ℕ}
    {a : Fin k → C(∂𝔻 n, X)} {Y : TopCat.{v}}
    (f : C(X, Y)) (g : Fin k → C(𝔻 n, Y))
    (h : ∀ (i : Fin k) (z : ∂𝔻 n), g i (diskBoundaryInclusion n z) = f (a i z)) :
    ∃! F : C(adjunction n X k a, Y),
      (∀ x, F (oldInclusion x) = f x) ∧
      (∀ i z, F (newCharacteristic i z) = g i z) := by
  let raw : X ⊕ (Fin k × 𝔻 n) → Y := Sum.elim f (fun p ↦ g p.1 p.2)
  have hraw : Continuous raw := f.continuous.sumElim (by
    apply continuous_prod_of_discrete_left.mpr
    intro i
    exact (g i).continuous)
  have hrespect : ∀ p q : X ⊕ (Fin k × 𝔻 n),
      (Relation.EqvGen.setoid (fun p q ↦ ∃ (i : Fin k) (z : ∂𝔻 n),
        p = Sum.inr (i, diskBoundaryInclusion n z) ∧ q = Sum.inl (a i z))) p q →
      raw p = raw q := by
    intro p q hpq
    induction hpq with
    | rel p q hpq =>
      obtain ⟨i, z, rfl, rfl⟩ := hpq
      exact h i z
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  let F : C(adjunction n X k a, Y) := ⟨Quotient.lift raw hrespect, hraw.quotient_lift hrespect⟩
  refine ⟨F, ⟨fun _ ↦ rfl, fun _ _ ↦ rfl⟩, ?_⟩
  intro G hG
  ext x
  refine Quotient.inductionOn x ?_
  intro p
  cases p with
  | inl x => exact hG.1 x
  | inr p => exact hG.2 p.1 p.2

end HolomorphicAnosov.FiniteCellAdjunction
