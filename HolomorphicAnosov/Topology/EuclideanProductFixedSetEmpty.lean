import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition

noncomputable section
open TopologicalSpace
namespace HolomorphicAnosov

/-- If either factor has no fixed point, the ordered-coordinate product map has none.
Source: Dold (1965), §1.6, printed p.2, the product fixed-set equality.
Proof: apply the coordinate equivalence to a hypothetical product fixed-point equality.
The resulting two component equations give a fixed point of each factor, contradicting
whichever factor's fixed set is empty. No compactness or positive dimension is needed. -/
theorem euclidean_product_fixedSet_eq_empty :
    let euclideanProductDomain :
      ∀ {n m : ℕ}, Opens (EuclideanSpace ℝ (Fin n)) →
        Opens (EuclideanSpace ℝ (Fin m)) → Opens (EuclideanSpace ℝ (Fin (n + m))) :=
      fun {n} {m} U V ↦
        ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ)) ⁻¹' (U ×ˢ V),
          (U.isOpen.prod V.isOpen).preimage EuclideanSpace.finAddEquivProd.continuous⟩
    let euclideanProductMap :
      ∀ {n m : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
        {V : Opens (EuclideanSpace ℝ (Fin m))},
        C(U, EuclideanSpace ℝ (Fin n)) → C(V, EuclideanSpace ℝ (Fin m)) →
          C(euclideanProductDomain U V, EuclideanSpace ℝ (Fin (n + m))) :=
      fun {n} {m} {U} {V} f g ↦ by
        let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
        let a : C(euclideanProductDomain U V, U) :=
          ⟨fun x ↦ ⟨(e x.1).1, x.2.1⟩,
            (e.continuous.comp continuous_subtype_val).fst.subtype_mk _⟩
        let b : C(euclideanProductDomain U V, V) :=
          ⟨fun x ↦ ⟨(e x.1).2, x.2.2⟩,
            (e.continuous.comp continuous_subtype_val).snd.subtype_mk _⟩
        exact ⟨fun x ↦ e.symm (f (a x), g (b x)),
          e.symm.continuous.comp ((f.continuous.comp a.continuous).prodMk
            (g.continuous.comp b.continuous))⟩
    ∀ (n m : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
      (V : Opens (EuclideanSpace ℝ (Fin m)))
      (f : C(U, EuclideanSpace ℝ (Fin n))) (g : C(V, EuclideanSpace ℝ (Fin m))),
      euclideanFixedSet f = ∅ ∨ euclideanFixedSet g = ∅ →
      euclideanFixedSet (euclideanProductMap f g) = ∅ := by
  dsimp only
  intro n m U V f g he
  ext x
  constructor
  · intro hx
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    let u : U := ⟨(e x.1).1, x.2.1⟩
    let v : V := ⟨(e x.1).2, x.2.2⟩
    change e.symm (f u, g v) = x.1 at hx
    have hp : (f u, g v) = e x.1 := by
      simpa only [e.apply_symm_apply] using congrArg e hx
    rcases he with hf | hg
    · have hu : u ∈ euclideanFixedSet f := congrArg Prod.fst hp
      rw [hf] at hu
      exact hu.elim
    · have hv : v ∈ euclideanFixedSet g := congrArg Prod.snd hp
      rw [hg] at hv
      exact hv.elim
  · exact False.elim

end HolomorphicAnosov
