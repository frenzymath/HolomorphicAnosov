import HolomorphicAnosov.Analysis.Complex.ConwayFinitePolygonCauchyRepresentation
import HolomorphicAnosov.Analysis.Normed.RudinAnnihilatorClosure
import HolomorphicAnosov.Analysis.RudinFiniteMeasureCauchyTransform
import HolomorphicAnosov.MeasureTheory.RudinCompactComplexRieszDensity
import HolomorphicAnosov.Analysis.Complex.RudinCompactPolynomialApproximation
import HolomorphicAnosov.Topology.OpenPlaneCompactExhaustion
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Polynomial approximation with connected spherical complement

Source: Walter Rudin, *Real and Complex Analysis*, third edition (1987),
Theorems 13.6–13.7, printed pp. 270–271, and Theorem 13.9, printed p. 272.
The DAG node is `analysis.conway_connected_complement_polynomial_approximation`.
The source is `literature/Rudin-Real-and-Complex-Analysis-3rd-1987.pdf`;
these printed pages are PDF pages 283–285.
-/

open Filter

namespace HolomorphicAnosov.Analysis.Complex

/-- Every holomorphic function on an open subset of the complex plane with connected
complement in the Riemann sphere is a locally uniform limit of complex polynomials.
No connectedness or nonemptiness of the open set is required. `OnePoint ℂ` is the
native one-point compactification of the complex plane, with its usual sphere topology;
the complement below includes the point at infinity. `DifferentiableOn ℂ` expresses
holomorphicity on the open set, and no behavior of `f` outside that set is prescribed.

Source: Rudin, *Real and Complex Analysis*, third edition, Theorems 13.6–13.7,
pp. 270–271, and Theorem 13.9, p. 272. Compact exhaustion: Conway, *Functions of
One Complex Variable*, VII Proposition 1.2, pp. 142–143. The finite-polygon Cauchy
representation is the named DAG prerequisite following Conway VIII Proposition 1.1,
pp. 195–196, with the written Ahlfors rectangle/interior normalization.

Natural-language proof (the complete current DAG proof; its named prerequisites remain
separate proof obligations and this Stage2 theorem is deliberately admitted):

PA1: If U is empty use the zero polynomial sequence. Otherwise A=sphere\U contains infinity and is
connected by hypothesis. Apply topo.conway_open_plane_compact_exhaustion to this arbitrary open U;
choose its compact cofinal increasing exhaustion K_n. Every component of sphere\K_n contains a
component of A. Since A is nonempty connected, its only component is A itself, so every complement
component contains infinity. Distinct components are disjoint; consequently sphere\K_n has just
one component and E={infinity} meets it.

PA2.1: Fix a nonempty compact K⊂U with sphere\K connected, as supplied by PA1 for each nonempty
K_n. Holomorphy of f on U gives continuity of f|K. Let A=C(K,C) with its supremum norm, and let M
be the complex submodule underlying the genuine polynomialFunctions K subalgebra. The named exact
carrier theorem identifies its members with restrictions of complex polynomials, so no
prescribed-pole rational carrier is assumed. By the named Rudin5.19 bounded-functional closure
criterion, f|K lies in closure M if every bounded complex-linear Φ:A→C which vanishes on M also
satisfies Φ(f|K)=0. Fix such a Φ. If Φ=0 this is immediate; otherwise the following steps apply
unchanged.

PA2.2: Apply the existence-only source Riesz density input to this compact Hausdorff subtype K and
Φ. Obtain a finite positive regular Borel measure λ on K and a Borel g:K→C, |g|≤1 pointwise, with
Φ(u)=∫u(ζ)g(ζ)dλ for every u∈A. Its zero-functional/empty-space clauses avoid normalization by
zero. Define h(z)=∫g(ζ)/(ζ−z)dλ for z∈C\K. Apply the named density specialization of Rudin10.7
with measurable space X=K, φ the continuous inclusion into C and Ω=C\K, which is open because K is
compact and closed. Its whole-image separation premise is exactly Ω∩K=∅. Thus these integrals are
genuine and h is complex analytic on Ω. This theorem concerns the plane only; analyticity at
infinity is not inferred from it. For each z outside K the kernel ζ↦(ζ−z)^−1 is continuous on K,
and the same Riesz identity also reads h(z)=Φ(ζ↦(ζ−z)^−1).

PA2.3: Use compact boundedness to choose R>0 with |ζ|≤R for ζ∈K. For |z|>2R, the WRITTEN
source13.6 equation(6)p271 is (ζ−z)^−1=−Σ_(j≥0)z^(-j−1)ζ^j. The complex geometric-sum theorem
identifies its pointwise limit; the summable real geometric majorant |z|^−1(1/2)^j and named
uniform-series theorem give uniform convergence on K. The finite-subset partial-sum net gives
natural partial sums because every finite subset of N is contained in range(N) eventually. Each
finite sum is a polynomial restriction in M, hence Φ annihilates it. The named compact
continuous-map uniform convergence equivalence identifies this with convergence in A, so
continuity of the bounded Φ and PA2.2 give h(z)=0. This implements the source equation(6) and its
annihilated polynomial moments; it does not invoke rational-function operations.

PA2.4: Extend h to the sphere complement D=sphere\K by h(infinity)=0. PA2.3 says h is identically0
on the source reciprocal-chart neighborhood D(infinity;2R)={infinity}∪{|z|>2R}, so the infinity
chart function is the zero analytic function. Let Z consist of points of D on a relative
neighborhood of which h is identically0. It is open and contains infinity. To prove closedness,
let a be a finite point of closure_D Z and choose a plane disk B around a contained in C\K. It
meets Z at some b∈B. On B, h and0 are analytic and agree on a full plane neighborhood of b, after
intersecting the neighborhood witnessing b∈Z with B. The existing analytic identity principle on
the preconnected disk B gives h=0 throughout B, so a∈Z. A closure point at infinity already
belongs to Z by the exterior-zero neighborhood. Thus Z is both open and closed in connected D, is
nonempty, and equals D. This is exactly the local zero-germ/open-closed propagation underlying
source10.18 and used by source13.6; it supplies h=0 on C\K without assuming a plane/sphere
component equivalence for an arbitrary set.

PA2.5: Use the named arbitrary-open finite polygon provider with the original U,K and f. Write
α=(2πi)^−1. It gives finitely many oriented coordinate straight edges σ_e on ordered real
intervals I_e=[a_e,b_e], whose signed tangent τ_e is a fixed complex number of modulus1
(horizontal/vertical coordinate edge with its orientation sign), such that f(ζ)=αΣ_e∫_(a_e..b_e)
f(σ_e(t))τ_e/(σ_e(t)−ζ)dt for ζ∈K. These are the provider’s own coordinate edge integrals, so no
interval reparametrization is inserted. Degenerate zero-length pieces contribute0 and may be
omitted. If the family is empty the identity says f|K=0 and therefore Φ(f|K)=0 immediately.
Otherwise its union Γ is compact, lies in U\K and is disjoint from nonempty compact K; choose η>0
with |σ_e(t)−ζ|≥η for every edge parameter and ζ∈K. Continuity of f on U and compact boundedness
give M≥0 with |f|≤M on Γ.

PA2.6: For each nondegenerate edge use the positive finite measure ν_e=volume.restrict(Ioc a_e
b_e). An ordered interval integral is by definition the integral against this same Ioc
restriction; endpoints are not assigned new values and no derivative-at-endpoint premise is used.
Define H_e(ζ,t)=g(ζ) f(σ_e(t))τ_e/(σ_e(t)−ζ) on K×I_e and extend it by0 for t outside I_e. The
unweighted kernel is continuous on K×I_e because σ_e is affine, f is continuous on its trace and
the denominator is separated from0. Its zero extension is Borel measurable, and so is g∘fst; their
product is Borel measurable. The named measurable-to-strong-measurable and strong-to-AE-strong
leaves apply with complex codomain. The pointwise density bound and separation give |H_e|≤M/η on
K×I_e and0 elsewhere. The product λ.prod ν_e is finite, hence s-finite. Apply the exact
Integrable.of_bound leaf to establish genuine full PRODUCT Bochner integrability before using the
named positive-measure integral_integral_swap. For fixed ζ or t on the retained interval the same
measurability and bound prove genuine section integrability; this is not inferred from a finite
value of a totalized integral.

PA2.7: All finite-sum/scalar interchanges in the next display have genuine integrability.
Explicitly, q_e(ζ)=∫_(a_e..b_e)f(σ_e(t))τ_e/(σ_e(t)−ζ)dt is bounded on K by (b_e−a_e)M/η. It is
continuous: the pointwise difference of the separated kernels is bounded by M|ζ−ζ0|/η², and the
integral subtraction identity plus the named norm bound gives
|q_e(ζ)−q_e(ζ0)|≤(b_e−a_e)M|ζ−ζ0|/η². Thus g q_e is Borel measurable and bounded; the
finite-measure bound leaf makes it integrable for λ. The tuple (g q_e)_e in a finite product of
copies of C is likewise measurable, bounded and integrable. Applying the existing real
continuous-linear integral-commutation theorem to its coordinate projections and the finite sum
map gives the finite-sum integral identity; the same theorem handles multiplication by α. This
avoids using a real-valued integral_add leaf for complex functions. For fixed ζ, multiplication by
g(ζ) commutes with each genuine ν_e-integral by the named RCLike scalar integral rule. These
justify integrating the polygon representation against the Riesz density.

PA2.8: Now follow source13.6’s ACTUAL printed Fubini displayp271, retaining its minus sign. The
Riesz representation and the polygon identity give Φ(f|K)=αΣ_e∫_K∫_(a_e..b_e)H_e(ζ,t)dt dλ(ζ).
PA2.6 permits positive Bochner Fubini for every edge, so this equals αΣ_e∫_(a_e..b_e) f(σ_e(t))τ_e
[∫_K g(ζ)/(σ_e(t)−ζ)dλ(ζ)]dt. The bracket is −h(σ_e(t)), since h(w)=∫g(ζ)/(ζ−w)dλ; scalar
extraction is legitimate by the actual section integrability. Every σ_e(t) lies outside K, where
PA2.4 gives h=0. Consequently Φ(f|K)=−αΣ_e∫_(a_e..b_e)f(σ_e(t))τ_e h(σ_e(t))dt=0. This uses only
the actual positive measure λ with its bounded density, not an unconditional positive-measure API
applied to a complex measure μ.

PA3: Every bounded complex-linear functional annihilating M thus annihilates f|K. The named5.19
criterion puts f|K in norm closure M. For each δ>0 choose u∈M with ||f|K−u||<δ; by the supremum
norm this gives |f(ζ)−u(ζ)|<δ for every ζ∈K. The exact polynomialFunctions carrier theorem
supplies a complex polynomial p whose restriction is u. This is the polynomial conclusion of the
source13.6–13.7 written route, obtained directly from the polynomial subspace without a general
Runge or finite-pole-to-polynomial conversion. For K empty take p=0. For every positive n apply
this compact conclusion to K_n with δ=1/n, producing p_n. Set p_0=0 if indexing begins at0.

PA4: Fix compact K⊂U and δ>0. Cofinality supplies m with K⊂K_m; K_n⊂interior K_(n+1) implies K⊂K_n
for n≥m. Choose N≥m with 1/N<δ. For n≥N the constructed polynomial satisfies sup_K|f−p_n|≤1/n<δ.
Thus p_n converges uniformly on every compact subset of U, the convergence in H(U) used in source
Cor1.15. Empty exhaustion members impose vacuous approximation requirements; U=C is covered by the
disk case of the named exhaustion theorem.
-/
theorem conway_connected_complement_polynomial_approximation
    (U : Set ℂ) (hU : IsOpen U)
    (hcompl : IsConnected ((fun z : ℂ ↦ (z : OnePoint ℂ)) '' U)ᶜ)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) :
    ∃ p : ℕ → Polynomial ℂ, ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun n z ↦ (p n).eval z) f atTop K := by
  classical
  obtain ⟨K, hK, -, hnest, hcofinal, hcomponents⟩ :=
    HolomorphicAnosov.conway_open_plane_compact_exhaustion U hU
  have hinfty : (OnePoint.infty : OnePoint ℂ) ∈ (OnePoint.some '' U)ᶜ := by simp
  have hconnected (n : ℕ+) : IsConnected (OnePoint.some '' K n)ᶜ := by
    have hi : (OnePoint.infty : OnePoint ℂ) ∈ (OnePoint.some '' K n)ᶜ := by simp
    have heq : connectedComponentIn (OnePoint.some '' K n)ᶜ OnePoint.infty =
        (OnePoint.some '' K n)ᶜ := by
      apply Set.Subset.antisymm (connectedComponentIn_subset _ _)
      intro x hx
      obtain ⟨y, hy, hsub⟩ := hcomponents n x hx
      have hmem : (OnePoint.infty : OnePoint ℂ) ∈ connectedComponentIn (OnePoint.some '' K n)ᶜ x := by
        apply hsub
        rw [hcompl.2.connectedComponentIn hy]
        exact hinfty
      rw [← connectedComponentIn_eq hmem]
      exact mem_connectedComponentIn hx
    rw [← heq]
    exact isConnected_connectedComponentIn_iff.mpr hi
  let L : ℕ → Set ℂ := fun n ↦ K n.succPNat
  have hmono : Monotone L := by
    apply monotone_nat_of_le_succ
    intro n
    exact (hnest n.succPNat).trans interior_subset
  have hp : ∀ n : ℕ, ∃ p : Polynomial ℂ, ∀ z ∈ L n,
      ‖f z - p.eval z‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    exact rudin_compact_connected_complement_polynomial_approximation U hU
      (L n) (hK _).1 (hK _).2 (hconnected _) f hf _ (by positivity)
  choose p hp using hp
  refine ⟨p, fun C hC hCU ↦ ?_⟩
  obtain ⟨m, hm⟩ := hcofinal C hC hCU
  have hCm : C ⊆ L m.natPred := by simpa [L] using hm
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hεevent : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  filter_upwards [eventually_ge_atTop m.natPred, hεevent] with n hn hεn
  intro z hz
  simpa only [dist_eq_norm] using (hp n z (hmono hn (hCm hz))).trans hεn

end HolomorphicAnosov.Analysis.Complex
