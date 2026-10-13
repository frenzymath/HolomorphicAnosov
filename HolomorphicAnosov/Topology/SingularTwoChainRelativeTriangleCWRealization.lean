import HolomorphicAnosov.Algebra.FiniteSignedOccurrenceMatching
import HolomorphicAnosov.Topology.Homology.SingularTwoChainBoundaryOccurrences
import HolomorphicAnosov.Topology.PairedCellQuotientDescent
import HolomorphicAnosov.Topology.Homology.SingularChainSignedExpansion
import HolomorphicAnosov.Topology.RelativeTriangleRealization.CWStructure
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section
namespace HolomorphicAnosov
open CategoryTheory _root_.Topology
open scoped Simplicial
universe u
open RelativeTriangleRealization

/-- A singular two-chain with one loop as boundary has a finite relative
triangle CW realization, with the original signed, ordered face parameters.

Source: Hatcher, *Algebraic Topology*, ordered simplices pp.103–104, signed
finite-chain gluing pp.108–109, Theorem 2A.1 proof p.167, and Appendix pp.519–522.

Proof (R1): Expand each nonzero integer coefficient of `c` into its absolute
value many copies, labeled by its sign. The native chain coproduct/Finsupp model
has finite support and the actual alternating face formula. For each distinct
parametrized singular edge, the boundary equation gives equally many positive
and negative occurrences, except for `f`, with one extra positive occurrence.
Match opposite occurrences with identical singular maps, leaving precisely
that positive occurrence of `f`. The expansion cannot be empty, including when
`f` is constant: a constant singular edge is still a nonzero basis generator.

Proof (R2a): Form the quotient of the disjoint ordered triangles by those face
matches with unchanged face parameters. Vertex classes are finite. Each edge
interior point is equivalent only to its matched point of the same parameter,
or just itself on the unpaired edge; equivalence chains cannot enter a vertex
from an edge interior. Triangle interiors have singleton classes. Pairing two
different faces of one triangle and identifying several vertices are allowed.
No additional equivalence is imposed from coincident target images.

Proof (R2b): Start with the finite discrete vertex classes, attach one ordered
interval for each paired edge class and the distinguished singleton class,
then attach every triangle along its three characteristic edges. The three
boundary formulas agree at vertices and paste continuously on the closed
faces. Boundary attaching maps need not be injective.

Proof (R2c): The barycentric interval and planar triangle are closed bounded
convex bodies with nonempty interiors, via the coordinates `t₁` and `(t₁,t₂)`.
The convex-body disk homeomorphisms preserve their boundaries and interiors,
also for the native CW disk norm. Finite disk adjunction in dimension at most
two gives the compact Hausdorff finite CW structure, with exactly these vertex,
edge and triangle cells. Zero-cells are points, without using a nonempty sphere
in dimension zero.

Proof (R2d): The inductive disk-attachment space and the original triangle
quotient have exactly the same classes. Their open-set tests coincide: triangle
preimages test the quotient topology, edge tests follow by restriction to faces,
and vertex tests are automatic in the discrete zero-skeleton. The canonical
bijection is consequently a homeomorphism. Transport the CW structure while
retaining the exact ordered characteristic maps and the displayed cell indices.

Proof (R3): The maps `σᵢ` agree on matched faces, so quotient descent gives a
continuous `S` with `S ∘ χᵢ = σᵢ` and the distinguished edge mapping to `f`.
All vertex cells together with this edge form a subcomplex, since its endpoints
are vertex classes. The signs label the chain and do not reverse parameters.
Repeated simplex maps, self-pairings of distinct faces, disconnected quotients,
and distinct endpoint classes with the same target image are included. No
separation or local-connectivity assumption on `X` is used. -/
theorem singularTwoChainRelativeTriangleCWRealization (X : TopCat.{u})
    (f : C(Simplex 1, X))
    (_hf : f (Convexity.StdSimplex.single 0) = f (Convexity.StdSimplex.single 1))
    (c : IntegralSingularChain X 2)
    (hc : (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))).d 2 1) c =
      generator X 1 f) :
    ∃ (m : ℕ) (σ : Fin m → C(Simplex 2, X)) (ε : Fin m → ℤ)
      (distinguished : Occurrence m) (pair : Occurrence m → Occurrence m),
      (∀ i, ε i = -1 ∨ ε i = 1) ∧
      c = ∑ i, ε i • generator X 2 (σ i) ∧
      Function.Involutive pair ∧
      pair distinguished = distinguished ∧
      (∀ o, o ≠ distinguished → pair o ≠ o) ∧
      (∀ o, o ≠ distinguished →
        ε (pair o).1 * (-1 : ℤ) ^ (pair o).2.val = -(ε o.1 * (-1 : ℤ) ^ o.2.val)) ∧
      (∀ o, (σ o.1).comp (face o.2) = (σ (pair o).1).comp (face (pair o).2)) ∧
      ε distinguished.1 * (-1 : ℤ) ^ distinguished.2.val = 1 ∧
      (σ distinguished.1).comp (face distinguished.2) = f ∧
      HasCWStructure pair distinguished ∧
      ∃ S : C(Space pair, X),
        (∀ i, S.comp (triangle pair i) = σ i) ∧
        S.comp (edge pair distinguished) = f := by
  obtain ⟨m, τ, ε, hε, hcτ⟩ := integralSingularChainSignedExpansion X 2 c
  let σ : Fin m → C(Simplex 2, X) :=
    fun i ↦ TopCat.toSSetObjEquiv X (Opposite.op ⦋2⦌) (τ i)
  have hc' : c = ∑ i, ε i • generator X 2 (σ i) := by
    simpa only [generator, σ, Equiv.symm_apply_apply] using hcτ
  let label : Occurrence m → C(Simplex 1, X) :=
    fun o ↦ (σ o.1).comp (face o.2)
  let sign : Occurrence m → ℤ := fun o ↦ ε o.1 * (-1 : ℤ) ^ o.2.val
  have hsigns : ∀ o, sign o = -1 ∨ sign o = 1 := by
    rintro ⟨i, j⟩
    rcases hε i with hi | hi <;> fin_cases j <;> norm_num [sign, hi]
  have hboundary : (∑ o, sign o • Finsupp.single (label o) (1 : ℤ)) =
      Finsupp.single f (1 : ℤ) := by
    apply singularTwoChainBoundaryOccurrences X f m τ ε
    rw [← hcτ]
    exact hc
  obtain ⟨distinguished, pair, hpos, hf', hinv, hfix, hnfix, hlabel, hsign⟩ :=
    finiteSignedOccurrenceMatching label sign f hsigns hboundary
  have hpair : ∀ o, (σ o.1).comp (face o.2) =
      (σ (pair o).1).comp (face (pair o).2) := fun o ↦ (hlabel o).symm
  have hcw := pairedTriangles_hasCWStructure pair hinv distinguished
  obtain ⟨S, hSpoint⟩ := pairedCellQuotientDescent face pair σ hpair
  have hS : ∀ i, S.comp (triangle pair i) = σ i := by
    intro i
    ext t
    exact hSpoint i t
  refine ⟨m, σ, ε, distinguished, pair, hε, hc', hinv, hfix, hnfix,
    hsign, hpair, hpos, hf', hcw, S, hS, ?_⟩
  ext t
  change S (Quotient.mk _ (distinguished.1, face distinguished.2 t)) = f t
  rw [hSpoint]
  exact congrArg (fun k : C(Simplex 1, X) ↦ k t) hf'



end HolomorphicAnosov
