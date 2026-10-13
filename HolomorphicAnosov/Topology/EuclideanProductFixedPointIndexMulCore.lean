import HolomorphicAnosov.Topology.EuclideanSupportOrientationProduct

/-!
# Nonempty-support product step for the Euclidean fixed-point index

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), §1.6, printed p.2; Hatcher, *Algebraic Topology*,
p.269.  This module isolates the source's relative-homology product computation
from the empty-support reductions used by the public product law.
-/

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- Dold §1.6: the canonical Euclidean index is multiplicative on ordered
products. The native relative product has the same nonzero integral coefficient
on local and supported orientations; displacement naturality gives equality of
that coefficient times the two sides, and integer cancellation proves the law.
The nonempty hypotheses are retained verbatim in this public interface. -/
theorem euclidean_product_fixed_point_index_mul_of_nonempty_support :
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
      euclideanFixedSet f ≠ ∅ → euclideanFixedSet g ≠ ∅ →
      euclideanFixedPointIndex (euclideanProductMap f g) hP =
        euclideanFixedPointIndex f hF * euclideanFixedPointIndex g hG := by
  dsimp only
  intro n m U V f g hF hG hP _hFnonempty _hGnonempty
  exact EuclideanIndexProduct.index_mul f g hF hG hP

end HolomorphicAnosov
