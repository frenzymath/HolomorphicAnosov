import HolomorphicAnosov.Topology.EmbeddedSimplexLocalRelativeClass
import HolomorphicAnosov.Topology.ClosedEmbeddingRelativeTransport

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov

/- The embedded-simplex generator argument follows Hatcher Example 2.23 and
Theorem 2.20. The full source proof is recorded in the provider docstring below. -/

/-- Source-backed comparison provider for the embedded-simplex local class.

Hatcher's Example 2.23 (p.125) proves that the identity simplex generates
`H_d(Δ^d, ∂Δ^d; ℤ)` by induction. For the induction step, remove one facet F
from the boundary and call the union of the other facets Λ. The simplex
retracts onto Λ, so the connecting map of the triple `(Δ^d, ∂Δ^d, Λ)` is an
isomorphism. Inclusion of F identifies the target with
`H_(d-1)(F, ∂F)`: in dimension one this is a direct relative-chain
calculation, and in higher dimensions it follows from the homeomorphism of
the good-pair quotients. The connecting map sends the identity simplex to the
identity simplex of F up to sign. Starting from the coefficient-one point in
dimension zero gives a primitive generator in every dimension.

The proved positive-preimage helper supplies a unique point `t` in the
interior of the source simplex with `s t = 0`. Radial projection from `t`
gives a deformation retraction of `Δ^d \ {t}` onto `∂Δ^d`; homotopy
invariance for the corresponding relative pairs therefore carries the
identity-simplex class to the class of the embedded simplex in
`(range(s), range(s) \ {0})`. The closed embedding identifies the source
simplex with its image. Since zero is in the interior of that image, the
interiors of `range(s)` and the ambient punctured Euclidean space cover the
ambient space. Hatcher's Excision Theorem 2.20 then identifies the image pair
with `(ℝ^d, ℝ^d \ {0})`. Naturality of the singular chain construction and
of the relative quotient sends the coefficient-one identity chain literally
to `simplexLocalRelativeChain`; hence the resulting class is primitive.
Choose the inverse coordinate equivalence with value one equal to this class,
which gives the displayed `e`.

This declaration isolates the remaining formal obligation: implement the
triple connecting map, the radial homotopy comparison, and the excision map
on the native singular-subspace complexes. The cycle certificate and the
unique positive preimage are already proved above. -/
theorem embeddedSimplex_localClass_equiv_provider (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), EuclideanSpace ℝ (Fin (n + 1))))
    (hemb : Topology.IsClosedEmbedding s)
    (hzero : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈ interior (Set.range s))
    (hfaces : ∀ (i : Fin (n + 2)) (t : Convexity.StdSimplex ℝ (Fin (n + 1))),
      s (Convexity.StdSimplex.map i.succAbove t) ≠ 0) :
    ∃ e : ℤ ≃ₗ[ℤ]
        (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
          ({0} : Set _)ᶜ).homology (C := ModuleCat ℤ)
            reducedSingularIntegralCoefficients (n + 1),
      e 1 = simplexLocalRelativeClass n s hfaces := by
  obtain ⟨t, ⟨ht, hweights⟩, hunique⟩ :=
    embeddedSimplex_zero_preimage_positive n s hemb hzero hfaces
  have htfaces : ∀ (i : Fin (n + 2)) (u : Convexity.StdSimplex ℝ (Fin (n + 1))),
      t ≠ Convexity.StdSimplex.map i.succAbove u := by
    intro i u htu
    exact hfaces i u (htu ▸ ht)
  obtain ⟨e0, he0⟩ := standardSimplexIdentityClass_equiv_provider n
  obtain ⟨e1, he1⟩ := standardSimplex_punctured_transport_provider n t htfaces
  obtain ⟨e2, he2⟩ :=
    embeddedSimplex_closedEmbedding_transport_of_interior n s hemb hzero t ht htfaces
  refine ⟨(e0.trans e1).trans e2, ?_⟩
  change e2 (e1 (e0 1)) = _
  rw [he0, he1]
  exact he2

/-- The source-backed equivalence provider gives a bijective span map.
Source: Hatcher Example 2.23 p.125 and Theorem 2.20 pp.119–124. -/
theorem embeddedSimplex_localClass_free_generator (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), EuclideanSpace ℝ (Fin (n + 1))))
    (hemb : Topology.IsClosedEmbedding s)
    (hzero : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈ interior (Set.range s))
    (hfaces : ∀ (i : Fin (n + 2)) (t : Convexity.StdSimplex ℝ (Fin (n + 1))),
      s (Convexity.StdSimplex.map i.succAbove t) ≠ 0) :
    Function.Bijective (LinearMap.toSpanSingleton ℤ _ (simplexLocalRelativeClass n s hfaces)) := by
  obtain ⟨e, he⟩ := embeddedSimplex_localClass_equiv_provider n s hemb hzero hfaces
  have hmap : LinearMap.toSpanSingleton ℤ _ (simplexLocalRelativeClass n s hfaces) = e.toLinearMap := by
    apply LinearMap.ext
    intro z
    rw [LinearMap.toSpanSingleton_apply, ← he]
    simpa using (e.map_smul z (1 : ℤ)).symm
  rw [hmap]
  exact e.bijective

end HolomorphicAnosov

