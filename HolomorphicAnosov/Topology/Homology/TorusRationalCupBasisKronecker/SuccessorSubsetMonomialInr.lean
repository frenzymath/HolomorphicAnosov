import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SuccessorSubsetIndex
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SortAdjoinLastCoordinate
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SpecifiedCupAssocUnit

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- Hatcher, Algebraic Topology, p207 supplies the binary cup associativity and unit laws; Example 3.16 p216 gives the coordinate-product context. The proof of the native sorted-list and dependent-degree-cast formula is agent-written. It directly inducts on the specified earlier-coordinate list using the binary cup laws and the existing sorting theorem. It then transports the subset-cardinality equality through the graded cup product.

DAG node: `topo.torus_public_successor_subset_monomial_inr_g17`. -/
theorem successor_subset_monomial_inr
    (n : ℕ) (X : TopCat)
    (cup : ∀ p q : ℕ, SingularCochain.cohomology ℚ X p →ₗ[ℚ]
      SingularCochain.cohomology ℚ X q →ₗ[ℚ]
        SingularCochain.cohomology ℚ X (p + q))
    (one : SingularCochain.cohomology ℚ X 0)
    (alpha : Fin (n + 1) → SingularCochain.cohomology ℚ X 1)
    (hrep : ∀ p q (b : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) p)
        (c : SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) q),
      ∃ hc : SingularCochain.cupCochain ℚ X b.val c.val ∈
          SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) (p + q),
        cup p q (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) p b)
          (SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) q c) =
          SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) (p + q)
            ⟨SingularCochain.cupCochain ℚ X b.val c.val, hc⟩)
    (hunit : ∃ hu : SingularCochain.oneCochain ℚ X ∈
        SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) 0,
      one = SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) 0
        ⟨SingularCochain.oneCochain ℚ X, hu⟩)
    (k : ℕ) (S : {S : Finset (Fin n) // S.card = k}) :
    let H := fun d ↦ (SingularCochain.cohomology ℚ X d : Type)
    let m : ∀ l : List (Fin (n + 1)), H l.length :=
      fun l ↦ List.rec (motive := fun l ↦ H l.length) one
        (fun i l v ↦ cast (congrArg H (Nat.add_comm 1 l.length))
          (cup 1 l.length (alpha i) v)) l
    let T := successorSubsetIndex n k (Sum.inr S)
    cast (congrArg H ((T.val.length_sort (· ≤ ·)).trans T.property))
      (m (T.val.sort (· ≤ ·))) =
      cup k 1 (cast (congrArg H
        ((by simp : ((S.val.sort (· ≤ ·)).map Fin.castSucc).length =
          (S.val.sort (· ≤ ·)).length).trans
          ((S.val.length_sort (· ≤ ·)).trans S.property)))
        (m ((S.val.sort (· ≤ ·)).map Fin.castSucc))) (alpha (Fin.last n)) := by
  let H := fun d ↦ (SingularCochain.cohomology ℚ X d : Type)
  let m : ∀ l : List (Fin (n + 1)), H l.length :=
    fun l ↦ List.rec (motive := fun l ↦ H l.length) one
      (fun i l v ↦ cast (congrArg H (Nat.add_comm 1 l.length))
        (cup 1 l.length (alpha i) v)) l
  let l := (S.val.sort (· ≤ ·)).map Fin.castSucc
  have hl : l.length = k := by
    dsimp [l]
    simp [S.property]
  apply eq_of_heq
  refine HEq.trans (cast_heq _ _) ?_
  have happ : HEq
      (m ((insert (Fin.last n) (S.val.map Fin.castSuccEmb)).sort (· ≤ ·)))
      (cup l.length 1 (m l) (alpha (Fin.last n))) := by
    rw [sort_adjoin_last_coordinate]
    obtain ⟨hassoc, hunitlaws⟩ := specified_cup_assoc_unit X cup one hrep hunit
    let l := (S.val.sort (· ≤ ·)).map Fin.castSucc
    let j := Fin.last n
    let m : ∀ l : List (Fin (n + 1)), SingularCochain.cohomology ℚ X l.length := fun l ↦
      List.rec (motive := fun l ↦ SingularCochain.cohomology ℚ X l.length) one
        (fun i l v ↦ cast (congrArg
          (fun d ↦ (SingularCochain.cohomology ℚ X d : Type))
          (Nat.add_comm 1 l.length)) (cup 1 l.length (alpha i) v)) l
    change HEq (m (l ++ [j])) (cup l.length 1 (m l) (alpha j))
    induction l with
    | nil =>
        change HEq (m [j]) (cup 0 1 (m []) (alpha j))
        change HEq
          (cast (congrArg (fun d ↦
            (SingularCochain.cohomology ℚ X d : Type)) (Nat.add_comm 1 0))
            (cup 1 0 (alpha j) one)) (cup 0 1 one (alpha j))
        exact HEq.trans (cast_heq _ _)
          (HEq.trans (hunitlaws 1 (alpha j)).2 (hunitlaws 1 (alpha j)).1.symm)
    | cons i l ih =>
        change HEq
          (cast (congrArg (fun d ↦
            (SingularCochain.cohomology ℚ X d : Type))
            (Nat.add_comm 1 (l ++ [j]).length))
            (cup 1 (l ++ [j]).length (alpha i) (m (l ++ [j]))))
          (cup (l.length + 1) 1
            (cast (congrArg (fun d ↦
              (SingularCochain.cohomology ℚ X d : Type))
              (Nat.add_comm 1 l.length)) (cup 1 l.length (alpha i) (m l)))
            (alpha j))
        have hlen : (l ++ [j]).length = l.length + 1 := by
          simp only [List.length_append, List.length_singleton]
        have hs :
            (⟨(l ++ [j]).length, m (l ++ [j])⟩ : Sigma
              (fun d ↦ SingularCochain.cohomology ℚ X d)) =
              ⟨l.length + 1, cup l.length 1 (m l) (alpha j)⟩ := by
          apply Sigma.mk.inj_iff.mpr
          exact ⟨hlen, ih⟩
        let F : Sigma (fun d ↦ SingularCochain.cohomology ℚ X d) →
            Sigma (fun d ↦ SingularCochain.cohomology ℚ X d) := fun p ↦
          ⟨1 + p.1, cup 1 p.1 (alpha i) p.2⟩
        have hout := congrArg F hs
        have hc := ((by
          intro H _ _ cup l x y
          -- Package the dependent first index and its argument in `Sigma H`.
          -- Congruence of this single ordinary function transports both the
          -- `Nat.add_comm` input cast and the indexed cup codomain at once.
          let F : (Sigma H) → Sigma H := fun p ↦
            ⟨p.1 + 1, cup p.1 1 p.2 y⟩
          have harg : (⟨l + 1, cast (congrArg H (Nat.add_comm 1 l)) x⟩ : Sigma H) =
              ⟨1 + l, x⟩ := by
            apply Sigma.mk.inj_iff.mpr
            exact ⟨Nat.add_comm l 1, cast_heq _ _⟩
          have hres := congrArg F harg
          exact (Sigma.mk.inj_iff.mp hres).2
        ) : ∀ {H : ℕ → Type} [∀ d, AddCommGroup (H d)] [∀ d, Module ℚ (H d)]
      (cup : ∀ p q, H p →ₗ[ℚ] H q →ₗ[ℚ] H (p + q))
      (l : ℕ) (x : H (1 + l)) (y : H 1),
      HEq ((cup (l + 1) 1)
        (cast (congrArg H (Nat.add_comm 1 l)) x) y)
        ((cup (1 + l) 1) x y)) cup l.length
          (cup 1 l.length (alpha i) (m l)) (alpha j)
        have ha := hassoc 1 l.length 1 (alpha i) (m l) (alpha j)
        exact HEq.trans (cast_heq _ _)
          (HEq.trans ((Sigma.mk.inj_iff.mp hout).2)
            (HEq.trans ha.symm hc.symm))
  refine HEq.trans happ ?_
  let F : Sigma H → Sigma H := fun p ↦
    ⟨p.1 + 1, cup p.1 1 p.2 (alpha (Fin.last n))⟩
  have hs : (⟨l.length, m l⟩ : Sigma H) =
      ⟨k, cast (congrArg H hl) (m l)⟩ :=
    Sigma.mk.inj_iff.mpr ⟨hl, (cast_heq _ _).symm⟩
  exact (Sigma.mk.inj_iff.mp (congrArg F hs)).2

end HolomorphicAnosov.TorusRationalCupBasisKronecker
