import HolomorphicAnosov.Topology.DegreeOneHurewiczAbelianized
import HolomorphicAnosov.Topology.DegreeOneHurewiczFunction
import HolomorphicAnosov.Topology.DegreeOneHurewiczHom
import HolomorphicAnosov.Topology.IntegralSingularChains
import HolomorphicAnosov.Topology.IntegralSingularH1
import HolomorphicAnosov.Topology.IntegralSingularH1Map
import HolomorphicAnosov.Topology.LoopSingularClass
import HolomorphicAnosov.Topology.PathSingularChain
import HolomorphicAnosov.Topology.PathSingularSimplex
import HolomorphicAnosov.Topology.DegreeOneHurewiczEquivOfKernel
import HolomorphicAnosov.Topology.DegreeOneHurewiczFunctionNaturality
import HolomorphicAnosov.Topology.DegreeOneHurewiczSurjective
import HolomorphicAnosov.Topology.DegreeOneHurewiczKernel

/-!
# Degree-one singular Hurewicz map

Source: A. Hatcher, *Algebraic Topology*, Theorem 2A.1 and proof,
printed pp. 166–167, representative and naturality description p. 168;
Proposition 0.16 p. 15 and finite-chain construction pp. 108–109.
Current node: `topo.degree_one_singular_hurewicz_abelianization`.

The chain complex and homology below are the actual singular simplicial-set
complex in `ModuleCat ℤ`. The coefficient `ULift ℤ` is the type copy needed
to put integer coefficients in the universe of the arbitrary space. It
has the ordinary integer module structure. The loop simplex uses the
actual interval/simplex equivalence, and its chain is the integer-one
generator in the native coproduct. No separation or local hypothesis is used.
-/

noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial

universe u

namespace HolomorphicAnosov.Topology

/-- Degree-one integral singular Hurewicz theorem, including its literal
loop formula and naturality for every actual based continuous map.

Source: Hatcher, Theorem 2A.1 and proof, pp. 166–167, with the
representative/naturality description on p. 168. The prerequisite
certificates above give an explicitly defined homomorphism. To prove
surjectivity, expand a finite integral cycle into signed path occurrences,
replacing each negative path by its reversal: a path plus its reversal
is homologous to a constant path and hence zero. At an endpoint of a
nonloop occurrence the zero-boundary equation provides an outgoing path
occurrence. Concatenate the two; this reduces the finite occurrence
count and preserves boundary and class. Finite induction gives a sum
of loops. Path connectedness provides paths from the basepoint to their
basepoints. Conjugation along these paths does not change their homology
classes, and concatenation gives one based loop representing the cycle.
For the empty chain use the constant loop.

Every commutator maps to zero since the codomain is abelian. Conversely,
if a loop class vanishes, the native module homology quotient supplies
a finite singular two-chain bounding it. Realize its triangles as a
finite relative triangle CW complex with paired parametrized edges and
one distinguished edge representing the given loop. Keep that edge
fixed and move all other vertices to the basepoint using connecting
paths. Homotopy extension for the vertex-and-distinguished-edge
subcomplex extends this homotopy. The new triangle edges are based
loops, and paired occurrences still cancel. In the abelianization the
given loop is consequently the signed sum of their triangle boundaries.
Each triangle boundary is nullhomotopic by straight contraction inside
the triangle to its base vertex, so this sum is zero. The kernel of the
abelianization projection is exactly the commutator subgroup, proving
the reverse containment. The explicit quotient lift is therefore
bijective and gives the additive equivalence displayed below; its
function remains that lift, rather than an arbitrarily chosen map.

For naturality, represent any fundamental-group element by a loop.
The based map sends it to the composed loop with the actual endpoint
casts. The singular chain map sends its integer-one simplex generator
to the composed-loop generator, and cycle projection commutes with the
native induced homology map. Thus both sides agree on representatives,
and quotient induction gives the displayed identity. The equivalence
value on every loop is the actual cycle projection by the definition
of the quotient lift and the abelianization lift. No CW, separation,
local path connectivity, or semilocal connectivity assumption is
imposed on either space; the auxiliary finite triangle complex is
not a replacement for either space. A chosen basepoint rules out
an empty source, and the one-point case follows from constant triangles. -/
theorem degree_one_singular_hurewicz_abelianization
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Function.Surjective (degreeOneHurewicz x) ∧
    (degreeOneHurewicz x).ker = commutator (FundamentalGroup X x) ∧
    (∀ α : Path x x,
      degreeOneHurewiczFunction x (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk α)) = loopSingularClass α) ∧
    (∃ e : Additive (Abelianization (FundamentalGroup X x)) ≃+ IntegralSingularH1 X,
      (∀ a, e a = degreeOneHurewiczAbelianized x a) ∧
      (∀ α : Path x x,
        e (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk α)))) = loopSingularClass α)) ∧
    (∀ {Y : Type u} [TopologicalSpace Y] [PathConnectedSpace Y]
      (y : Y) (g : C(X, Y)) (hg : g x = y) (a : FundamentalGroup X x),
        degreeOneHurewiczFunction y (FundamentalGroup.mapOfEq g hg a) =
          integralSingularH1Map g (degreeOneHurewiczFunction x a)) := by
  have hs := degreeOneHurewicz_surjective x
  have hk := degreeOneHurewicz_kernel x
  refine ⟨hs, hk, ?_, degreeOneHurewicz_equiv_of_kernel x hs hk, ?_⟩
  · intro α
    rfl
  · intro Y _ _ y g hg a
    exact degreeOneHurewiczFunction_naturality x y g hg a

end HolomorphicAnosov.Topology

