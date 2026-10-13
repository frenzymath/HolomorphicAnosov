import HolomorphicAnosov.AlgebraicTopology.SingularCochainPairPullbackDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeDualComplex
import HolomorphicAnosov.AlgebraicTopology.CochainDualHomotopyEquivalence
import HolomorphicAnosov.Topology.SingularHomologyExcision

/-!
# Excision for relative singular cohomology

DAG: `topo.singular_relative_cohomology_excision_g20`.
Source: Hatcher, *Algebraic Topology*, pp.201–202, using the supported
subdivision deformation of Proposition 2.21, pp.119–124.
-/

open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false

/-- Inclusion of the intersection pair induces an isomorphism on relative singular
cohomology over every commutative coefficient ring. The subspaces need not be open,
closed or nonempty. Source: Hatcher pp.201–202, Proposition 2.21 pp.119–124.

Complete natural-language proof:

1. For the interiors cover A,B, let K=C*(A)+C*(B) in C*(X), interpreted as chain complexes on
supported ambient simplices. The existing subdivision geometry and the Lebesgue-number theorem give
eventual A-or-B smallness of each singular simplex after iterating subdivision S: pull back the open
interiors cover to its compact metric domain; barycentric diameters shrink geometrically, while
dimension0 simplices are already small. Construct Hatcher’s operators explicitly. Temporarily
augment the affine simplex complex by [∅] in degree−1, with ∂[v]=[∅]. For a point b define
c_b[v0,…,vn]=[b,v0,…,vn]; alternating-face expansion gives ∂c_b+c_b∂=id. Set S[∅]=[∅], T[∅]=0 and,
recursively on each affine vertex simplex λ with barycenter b_λ, Sλ=c_(b_λ)(S∂λ), Tλ=c_(b_λ)(λ−T∂λ).
Using the cone identity and the preceding lower-degree identity gives ∂Sλ=S∂λ and ∂Tλ=λ−T∂λ−Sλ. Thus
∂T+T∂=id−S. In dimension0 S[v]=[v] and T[v]=[v,v], whose boundary is zero; T is zero in degree−1, so
these identities restrict to the unaugmented ordinary chain complex. For a continuous singular σ
define Sσ=σ#(S id_Δ) and Tσ=σ#(T id_Δ). Barycenters and cones commute with affine face inclusions,
so the recursive identities commute with all singular faces. Their finitely many summands remain in
σ(Δ), hence preserve chains supported in A or B. All formulas extend R-linearly with their integer
signs. Choose a depth d(σ) by dimension induction, at least each face depth and large enough for all
terms of S^dσ to be small; assign depth0 to already small simplices. Define D_m=Σ_(j<m)TS^j,
Dσ=D_(d(σ))σ and ρ=id−∂D−D∂. Then ρ is a chain map. Its value on σ is S^dσ plus a sum over faces τ
of Σ_(d(τ)≤j<d(σ))TS^jτ, with the boundary signs; all summands are small by the face-depth choice
and support preservation. Thus ρ:C*(X)→K. On K, D=0 and ρ inclusion=id; on all ambient chains
inclusion ρ is homotopic to id by D. These are R-linear maps obtained with integer signs, not an
assertion that an arbitrary homology equivalence dualizes.

2. Every A simplex is small, so D vanishes on C*(A) and ρ fixes it. Quotient the chain deformation
by C*(A): inclusion K/C*(A)→C*(X)/C*(A) and ρ induce mutually inverse chain-homotopy equivalences
with the same quotient homotopy. The chain quotient K/C*(A) is canonically C*(B)/C*(A∩B), since its
free basis consists of exactly the B simplices not supported in A. Apply Hom_R(−,R). The induced
cochain maps still compose to identity up to the explicitly dual homotopies D*δ+δD*, and cochains on
these quotient chain modules are exactly the relative cochains. A homotopy difference on a relative
cocycle is a relative coboundary, so the canonical inclusion pullback induces the claimed excision
isomorphism. Choices of depths affect the chosen inverse but not naturality of the forward map,
which is literal restriction under the pair inclusion.

If X is empty, every singular chain module is zero and the conclusion is immediate.
The same formulas cover A empty or B empty; the interior-cover premise then forces
the other subspace to equal X. All operators use finite sums with integer signs,
so the proof works over the zero ring and every other commutative ring.
-/
theorem relative_cohomology_excision (R : Type u) [CommRing R] (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (n : ℕ) :
    IsIso (relativeCohomologyPullback R (X := TopCat.of B) (Y := X)
      (A := {x : B | (x : X) ∈ A}) (B := A) (subspaceInclusion X B)
      (by intro x hx; exact hx) n) := by
  let M := ModuleCat.of R R
  let P := singularExcisionSource X A B
  let Q := singularSubspacePair X A
  obtain ⟨eX, heX⟩ := singular_relative_dual_complex_iso R X A
  obtain ⟨eB, heB⟩ := singular_relative_dual_complex_iso R (TopCat.of B) {x : B | (x : X) ∈ A}
  obtain ⟨e, he⟩ := excision_source_equiv_of_small X A B M
    (NativeBarycentricOperators.smallRelativeHomotopyEquiv X A B hcover M) rfl
  let f := subspaceInclusion X B
  let hf : Set.MapsTo f {x : B | (x : X) ∈ A} A := fun _ hx => hx
  let m := (dualFunctor R).map e.hom.op
  have hnat : P.chainComplexπ M ≫ e.hom =
      SSet.chainComplexMap (TopCat.toSSet.map f) M ≫ Q.chainComplexπ M := by
    rw [he]
    exact (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} R)).app M).naturality
      (singularExcisionInclusion X A B)).symm
  have hsquare : m ≫ eB.hom = eX.hom ≫ relativePullback R f hf := by
    apply (cancel_mono (kernel.ι (pullback R
      (subspaceInclusion (TopCat.of B) {x : B | (x : X) ∈ A})))).mp
    rw [Category.assoc, heB]
    change m ≫ (dualFunctor R).map (P.chainComplexπ M).op = _
    dsimp only [relativePullback, kernel.map]
    rw [Category.assoc, kernel.lift_ι, ← Category.assoc, heX]
    change (dualFunctor R).map e.hom.op ≫
      (dualFunctor R).map (P.chainComplexπ M).op =
      (dualFunctor R).map (Q.chainComplexπ M).op ≫
      (dualFunctor R).map (SSet.chainComplexMap (TopCat.toSSet.map f) M).op
    rw [← Functor.map_comp, ← op_comp, hnat, op_comp, Functor.map_comp]
  have hm : IsIso (quotientMap R m n) := dual_homotopy_equivalence_isIso R e n
  have hq : quotientMap R m n ≫ quotientMap R eB.hom n =
      quotientMap R eX.hom n ≫ quotientMap R (relativePullback R f hf) n := by
    dsimp only [singularExcisionSource, M] at *
    have h := congrArg (fun t => quotientMap R t n) hsquare
    simpa only [quotientMap, HomologicalComplex.homologyMap_comp,
      Category.assoc, Iso.hom_inv_id_assoc] using h
  have hiX : IsIso (quotientMap R eX.hom n) := by unfold quotientMap; infer_instance
  have hiB : IsIso (quotientMap R eB.hom n) := by unfold quotientMap; infer_instance
  have hi : IsIso (quotientMap R eX.hom n ≫ quotientMap R (relativePullback R f hf) n) := by
    rw [← hq]
    infer_instance
  exact IsIso.of_isIso_comp_left (quotientMap R eX.hom n)
    (quotientMap R (relativePullback R f hf) n)

end HolomorphicAnosov.SingularCochain

