import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeHomotopicBondMap
import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeHomotopicBondInverse
import HolomorphicAnosov.Topology.Homotopy.MappingTelescopePairing
import HolomorphicAnosov.Topology.Homotopy.IdentityMappingTelescopeRay
import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeTailHomotopyEquiv
import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeSequence
import Mathlib.Topology.Homotopy.Equiv

/-!
# Ordinary mapping-telescope homotopy comparisons

Source: Hatcher, *Algebraic Topology*, Proposition A.11 proof, p.528, facts (1)–(3)
and the identity telescope; Proposition 0.18 and its definition of a relative
homotopy equivalence, p.16, with the interval endpoint retraction in Example 0.15,
p.15. DAG node: `g9.mapping_telescope_homotopy_comparisons`.
-/

universe u v

namespace HolomorphicAnosov.MappingTelescope.Sequence

open Set ContinuousMap

/-- The three telescope comparisons, including relative level data and the
identity-telescope homeomorphism, for arbitrary topological spaces.

Source: Hatcher, Proposition A.11 proof p.528, Proposition 0.18 p.16 and
Example 0.15 p.15. The carrier is the existing ordinary quotient-cylinder
`Sequence.telescope`; there is no compactly generated topology, CW assumption,
injectivity assumption, or preconstructed comparison equivalence.

The first component requires BOTH maps to carry each original canonical level
to the same level. BOTH inverse homotopies are relative to the union of all level
images. Native `HomotopicRel` means an actual jointly continuous homotopy fixed
on that subset. Together these are exactly Hatcher's relative equivalence.
`HomotopyEquiv` in the other components includes actual continuous maps and
jointly continuous inverse homotopies. The paired sequence uses X_(2n) and the
literal composite f_(2n+1) ∘ f_(2n), with only an arithmetic index transport.
The final space P is arbitrary and independent of the varying sequence X.

Empty spaces and noninjective or constant bonds are permitted. If the first
space alone is nonempty and later spaces are empty, no such first bonding map
exists; that is the supplied-map requirement, not a new nonemptiness assumption.
If all spaces are empty, all telescope conclusions are the corresponding empty
space equivalences. Identity telescopes use the ordinary product with the real
closed ray, including its endpoint 0.

Full current natural-language proof, relative to the named quotient-descent,
interval-product-descent, homotopy composition and closed-pasting prerequisites:

1. Use Tel(f)=(coprod_n X_n×I)/((n,x,1)~(n+1,f_n(x),0)) with the genuine quotient topology and
canonical continuous cylinders. Continuous formulas on each disjoint cylinder that agree on
generator seams descend to continuous maps by continuous quotient lift; constancy on generated
equivalence follows by reflexivity, symmetry and transitivity. For a homotopy, verify seam
agreement at every parameter, then use locally compact-product descent with Y=I. This proves
joint continuity on I×Tel(f); it does not assume that product with an arbitrary topological
space preserves quotient maps.

2. The attachment comparison used in Hatcher 0.18 works for any C=coprod X_n×I and A=coprod
X_n×{0,1}. For (t,s)∈I² put λ=1/max(1−s/2,2|t−1/2|), and r(t,s)=(1/2+λ(t−1/2),2+λ(s−2)). Its
denominator is ≥1/2, it is continuous, and its value lies on the bottom edge s=0 or one vertical
side t=0,1; the coordinates stay in I. On the bottom and sides λ=1, hence r is the identity.
Interpolating (1−v)(t,s)+v r(t,s) gives a strong deformation retraction of I² onto
I×{0}∪{0,1}×I, fixed on that union. Take product with each X_n and disjoint union; reflecting
the s coordinate gives the corresponding top retraction. This writes out the interval pair
required by Hatcher A.11 and imposes no CW hypothesis on X_n.

3. More generally suppose endpoint attaching maps α₀,α₁:A→B are joined by continuous F:I×A→B. Form
W=(B⊔(C×I))/((a,s)~F(s,a)), carrying its quotient topology. The bottom and top end quotients
Z₀=B⊔_{α₀}C and Z₁=B⊔_{α₁}C have canonical inclusions i₀,i₁ into W. The preceding retractions on
C×I, with the identity on B, descend to strong deformation retractions R₀:W→Z₀ and R₁:W→Z₁. On
A×I the raw homotopies are fixed, so every identified representative F(s,a) has the same value
at every homotopy time; therefore quotient descent and interval-product descent prove
continuity. Set φ=R₁i₀ and ψ=R₀i₁. Then ψφ=R₀i₁R₁i₀≃R₀i₀=id_{Z₀} using the top deformation, and
φψ≃id_{Z₁} using the bottom deformation; whiskering by R_i and i_i gives the actual inverse
homotopies, fixed on B. The inclusions and retractions are inverse on each end quotient, so no
unsupported identification of its topology with an arbitrary quotient subspace is needed.

4. For f_n≃g_n via H_n, take B=coprod_n X_n, C=coprod_n X_n×I and attach each bottom to its own
level and top to the next via f_n or g_n. Define F on bottoms constantly and on tops by H_n; the
two endpoint pieces are a disjoint topological sum and different n lie in distinct summands. The
preceding comparison gives Tel(f)≃Tel(g), by maps and inverse homotopies fixing every level in
B. The countable family requires no common uniform-continuity bound: raw continuity is
continuity on each disjoint summand, followed by quotient and interval-product descent.

5. For tail deletion, retain cylinders n≥1 and let i be their inclusion. Send the first cylinder
(0,x,t) to level₁(f₀x) and act identically on the tail; this defines r, with ri=id. The homotopy
from id to ir sends the first cylinder to (0,x,t+v(1−t)) and fixes the tail. At t=1 the first-
cylinder value is always level₁(f₀x), so it agrees with the tail representative. Both maps and
this homotopy descend continuously by the preceding quotient arguments. Reindexing n≥1 by n−1
gives the specified tail telescope.

6. For pairing start with the disjoint union B of the odd mapping cylinders M(f_{2m+1}), together
with X₀. Attach the even cylinders X_{2m}×I: their bottoms attach to the preceding target levels
(X₀ for m=0), and their tops attach to the bottom X_{2m+1} of the next odd mapping cylinder via
f_{2m}. Slide each top attachment through that odd cylinder, by (x,s)↦[f_{2m}(x),s], from its
bottom to the target X_{2m+2}. Hold every bottom attachment fixed. Apply the preceding
homotopic-attachment comparison once to the entire disjoint family. The resulting quotient is
the composed telescope with cylinders f_{2m+1}f_{2m}, with each redundant odd mapping cylinder
attached only along its target. Collapse each redundant cylinder to its target using
(y,t)↦(y,t+v(1−t)), fixed on targets and on the composed telescope. This simultaneous quotient
homotopy gives a strong deformation retraction onto Tel(f₁f₀,f₃f₂,…). Compose the two actual
equivalences. Seam values are fixed level points throughout, so retraction and comparison
homotopies glue on all shared targets.

7. The constructions allow empty spaces, noninjective maps, constant maps and arbitrary topological
source spaces. If every X_n is the same X and each f_n=id_X, send [n,x,t] to (x,n+t)∈X×[0,∞). On
each closed strip [n,n+1] the inverse is (x,s)↦[n,x,s−n]; at integer seams the two expressions
agree. The strips are locally finite and closed, so their continuous restrictions paste to a
continuous inverse. Thus this is a homeomorphism; the original map is continuous by quotient
descent. Under this homeomorphism the homotopy (v,x,s)↦(x,(1−v)s) retracts to X×{0}, giving
Tel(id)≃X with genuine inverse homotopies.

The explicit comparison maps and level equations are proved. The relative inverse
homotopies and pairing equivalence are the two named remaining proof obligations.
-/
theorem mapping_telescope_homotopy_comparisons
    (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ n, C(X n, X (n + 1))) (P : Type v) [TopologicalSpace P] :
    let paired : ∀ n, C(X (2 * n), X (2 * (n + 1))) := fun n ↦
      Eq.mp (congrArg (fun m ↦ C(X (2 * n), X m)) (Nat.mul_succ 2 n).symm)
        ((f (2 * n + 1)).comp (f (2 * n)))
    (∀ g : ∀ n, C(X n, X (n + 1)),
      (∀ n, (f n).Homotopic (g n)) →
        ∃ e : telescope f ≃ₕ telescope g,
          (∀ n (x : X n), e (level f n x) = level g n x) ∧
          (∀ n (x : X n), e.symm (level g n x) = level f n x) ∧
          (e.invFun.comp e.toFun).HomotopicRel (ContinuousMap.id (telescope f))
            (⋃ n, Set.range (level f n)) ∧
          (e.toFun.comp e.invFun).HomotopicRel (ContinuousMap.id (telescope g))
            (⋃ n, Set.range (level g n))) ∧
    Nonempty (telescope f ≃ₕ telescope (X := fun n ↦ X (n + 1)) (fun n ↦ f (n + 1))) ∧
    Nonempty (telescope f ≃ₕ telescope (X := fun n ↦ X (2 * n)) paired) ∧
    Nonempty (telescope (X := fun _ : ℕ ↦ P) (fun _ ↦ ContinuousMap.id P) ≃ₜ
      P × Set.Ici (0 : ℝ)) ∧
    Nonempty (telescope (X := fun _ : ℕ ↦ P) (fun _ ↦ ContinuousMap.id P) ≃ₕ P) := by
  classical
  obtain ⟨hhome, hid⟩ := identity_mapping_telescope_ray P
  refine ⟨?_, mapping_telescope_tail_homotopy_equiv X f,
    mapping_telescope_pairing X f, hhome, hid⟩
  intro g hg
  let H : ∀ n, (f n).Homotopy (g n) := fun n ↦ (hg n).some
  obtain ⟨hleft, hright⟩ := homotopicBondMap_inverse H
  let e : telescope f ≃ₕ telescope g :=
    ⟨homotopicBondMap H, homotopicBondMap (fun n ↦ (H n).symm),
      hleft.homotopic, hright.homotopic⟩
  exact ⟨e, homotopicBondMap_level H,
    homotopicBondMap_level (fun n ↦ (H n).symm), hleft, hright⟩

end HolomorphicAnosov.MappingTelescope.Sequence
