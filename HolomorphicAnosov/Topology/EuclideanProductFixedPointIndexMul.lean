import HolomorphicAnosov.Topology.EuclideanProductFixedSetCompact
import HolomorphicAnosov.Topology.EuclideanProductFixedSetEmpty
import HolomorphicAnosov.Topology.EuclideanFixedPointIndexEmpty
import HolomorphicAnosov.Topology.EuclideanProductFixedPointIndexMulCore

/-!
# Product law for the canonical Euclidean fixed-point index

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), §1.6, p. 2; Hatcher, *Algebraic Topology*, p. 269.
The local product coordinates are the ordered `Fin (n + m)` coordinates used by the
parent index theorem.  The source identifies the product support orientation with the
cross product of the factor orientations and checks the grid-simplex sign.
-/

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- The canonical Euclidean index is multiplicative for the ordered-coordinate
product map.  Dold §1.6 proves the nonempty-support case by the relative
homology cross product; if either support is empty, the product support is empty
and the empty-support index theorem gives both sides zero.  The ordered
Fin (n + m) coordinates and the supplied compactness witness are exactly those
in the source construction. -/
theorem euclidean_product_fixed_point_index_mul :
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
      (f : C(U, EuclideanSpace ℝ (Fin n))) (g : C(V, EuclideanSpace ℝ (Fin m)))
      (hF : IsCompact (euclideanFixedSet f)) (hG : IsCompact (euclideanFixedSet g))
      (hP : IsCompact (euclideanFixedSet (euclideanProductMap f g))),
      euclideanFixedPointIndex (euclideanProductMap f g) hP =
        euclideanFixedPointIndex f hF * euclideanFixedPointIndex g hG := by
  dsimp only
  intro n m U V f g hF hG hP
  by_cases hf : euclideanFixedSet f = ∅
  · have hp := euclidean_product_fixedSet_eq_empty n m U V f g (Or.inl hf)
    rw [fixed_index_zero_of_empty _ _ hp, fixed_index_zero_of_empty f hF hf,
      zero_mul]
  · by_cases hg : euclideanFixedSet g = ∅
    · have hp := euclidean_product_fixedSet_eq_empty n m U V f g (Or.inr hg)
      rw [fixed_index_zero_of_empty _ _ hp, fixed_index_zero_of_empty g hG hg,
        mul_zero]
    · exact euclidean_product_fixed_point_index_mul_of_nonempty_support n m U V f g
        hF hG hP hf hg

end HolomorphicAnosov
