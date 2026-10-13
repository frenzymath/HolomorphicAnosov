import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCohomologyExcision
import HolomorphicAnosov.AlgebraicTopology.SingularCochainPairShortExact
import HolomorphicAnosov.AlgebraicTopology.CochainQuotientExactness
import HolomorphicAnosov.AlgebraicTopology.CochainQuotientConnectingExactness
import HolomorphicAnosov.AlgebraicTopology.CochainQuotientConnectingNaturality
import HolomorphicAnosov.AlgebraicTopology.CochainQuotientConnectingRepresentative
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCocycleOfExtension
import HolomorphicAnosov.AlgebraicTopology.SingularPairPrismSquare
import HolomorphicAnosov.AlgebraicTopology.KernelHomotopyComponentLift
import HolomorphicAnosov.Topology.SimplicialPrismCommutingSquare
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeSumCochainInjective
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeSumCochainSurjective
import HolomorphicAnosov.AlgebraicTopology.CochainFiniteProductQuotient
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
/-!
# Relative singular cohomology of arbitrary pairs

DAG: `topo.singular_relative_cohomology_pair_theorems_g2`.
Source: Hatcher, *Algebraic Topology*, pp.199–202; the supported prism and
subdivision constructions are on pp.112–113 and 119–124. This module uses the
ordinary singular cochains and actual relative kernel complex defined in
`SingularCochainCohomologyDefinition`. No abstract cohomology functor or
acyclicity assumptions are introduced. Every definition below has genuine data.
-/
open CategoryTheory CategoryTheory.Limits Opposite
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
variable (R : Type u) [CommRing R]
/-- Inclusion of relative cochains into absolute cochains. Hatcher pp.199–200. -/
def relativeInclusion (X : TopCat.{u}) (A : Set X) : relativeComplex R X A ⟶ complex R X :=
  kernel.ι (pullback R (subspaceInclusion X A))
/-- The corresponding map on cohomology. Hatcher pp.199–200. -/
def relativeForget (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    relativeCohomology R X A n ⟶ cohomology R X n :=
  quotientMap R (relativeInclusion R X A) n
/-- A homotopy through continuous maps of pairs, without pointwise fixed basepoints.
Source: Hatcher p.201. -/
def HomotopicPairMaps {X Y : TopCat.{u}} (A : Set X) (B : Set Y) (f g : X ⟶ Y) : Prop :=
  ∃ H : ContinuousMap.Homotopy f.hom g.hom,
    ∀ t x, x ∈ A → H (t, x) ∈ B

/-- Disjoint union of the given spaces, with the coproduct topology (Hatcher p.202). -/
abbrev sumSpace {ι : Type u} (X : ι → TopCat.{u}) : TopCat.{u} := TopCat.of (Σ j, X j)

/-- The disjoint union of the subspaces, as a subset of the disjoint union. Hatcher p.202. -/
def sumSubspace {ι : Type u} (X : ι → TopCat.{u}) (A : ∀ j, Set (X j)) : Set (sumSpace X) :=
  {x | x.2 ∈ A x.1}

/-- Inclusion of a summand (Hatcher p.202). -/
def summandInclusion {ι : Type u} (X : ι → TopCat.{u}) (j : ι) : X j ⟶ sumSpace X :=
  TopCat.ofHom ⟨(fun x : X j => (⟨j, x⟩ : Σ j, X j)), by
    change Continuous (@Sigma.mk ι (fun k => (X k : Type u)) j)
    exact continuous_sigmaMk⟩

/-- The canonical cohomology restriction to every summand, for the actual relative groups.
Source: Hatcher p.202. -/
def sumRestriction {ι : Type u} (X : ι → TopCat.{u}) (A : ∀ j, Set (X j)) (n : ℕ) :
    relativeCohomology R (sumSpace X) (sumSubspace X A) n →ₗ[R]
      (∀ j, relativeCohomology R (X j) (A j) n) :=
  LinearMap.pi fun j =>
    (relativeCohomologyPullback R (A := A j) (B := sumSubspace X A) (summandInclusion X j)
      (fun _x hx => hx) n).hom

/-- Disjoint union of a family of continuous maps. Hatcher p.202. -/
def sumMap {ι κ : Type u} {X : ι → TopCat.{u}} {Y : κ → TopCat.{u}}
    (indexMap : ι → κ) (f : ∀ j, X j ⟶ Y (indexMap j)) : sumSpace X ⟶ sumSpace Y :=
  TopCat.ofHom ⟨fun x => ⟨indexMap x.1, f x.1 x.2⟩,
    continuous_sigma (fun j =>
      (@continuous_sigmaMk κ (fun k => (Y k : Type u)) _ (indexMap j)).comp
        (f j).hom.continuous)⟩

/-- Componentwise pullback between the products of the relative cohomology modules.
Source: Hatcher p.202. -/
def productPairPullback {ι κ : Type u} {X : ι → TopCat.{u}} {Y : κ → TopCat.{u}}
    (indexMap : ι → κ) (A : ∀ j, Set (X j)) (B : ∀ j, Set (Y j))
    (f : ∀ j, X j ⟶ Y (indexMap j))
    (hf : ∀ j, Set.MapsTo (f j) (A j) (B (indexMap j))) (n : ℕ) :
    (∀ j, relativeCohomology R (Y j) (B j) n) →ₗ[R]
      (∀ j, relativeCohomology R (X j) (A j) n) :=
  LinearMap.pi fun j =>
    (relativeCohomologyPullback R (A := A j) (B := B (indexMap j)) (f j) (hf j) n).hom.comp
      (LinearMap.proj (indexMap j))

set_option backward.isDefEq.respectTransparency false

private theorem quotientMap_comp {Q Q' Q'' : CochainComplex (ModuleCat.{u} R) ℕ}
    (f : Q ⟶ Q') (g : Q' ⟶ Q'') (n : ℕ) :
    quotientMap R (f ≫ g) n = quotientMap R f n ≫ quotientMap R g n := by
  dsimp [quotientMap]
  rw [HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

theorem relativePullback_comp {X Y Z : TopCat.{u}}
    {A : Set X} {B : Set Y} {C : Set Z} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    relativePullback R (f ≫ g) (hg.comp hf) =
      relativePullback R g hg ≫ relativePullback R f hf := by
  apply (cancel_mono (kernel.ι (pullback R (subspaceInclusion X A)))).mp
  dsimp only [relativePullback, kernel.map]
  simp only [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
  change kernel.ι (pullback R (subspaceInclusion Z C)) ≫
      (cochainFunctor R).map (f ≫ g).op =
    kernel.ι (pullback R (subspaceInclusion Z C)) ≫
      (cochainFunctor R).map g.op ≫ (cochainFunctor R).map f.op
  simp only [op_comp, Functor.map_comp]

private theorem relativeCohomologyPullback_comp {X Y Z : TopCat.{u}}
    {A : Set X} {B : Set Y} {C : Set Z} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) (n : ℕ) :
    relativeCohomologyPullback R (f ≫ g) (hg.comp hf) n =
      relativeCohomologyPullback R g hg n ≫ relativeCohomologyPullback R f hf n := by
  rw [relativeCohomologyPullback, relativePullback_comp, quotientMap_comp]
  rfl

private theorem relativeForget_zero_mono {X : TopCat.{u}} {A : Set X} :
    Mono (relativeForget R X A 0) := by
  unfold relativeForget quotientMap
  have : Mono (relativeInclusion R X A) := by
    dsimp [relativeInclusion]
    infer_instance
  have hnot : ∀ i : ℕ, ¬ (ComplexShape.up ℕ).Rel i 0 := by
    intro i hi
    simp at hi
  have hm : Mono (HomologicalComplex.homologyMap (relativeInclusion R X A) 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
      (relativeInclusion R X A) 0 hnot
  infer_instance

private theorem relativeForget_zero_injective {X : TopCat.{u}} {A : Set X} :
    Function.Injective (relativeForget R X A 0).hom :=
  (ModuleCat.mono_iff_injective _).mp (relativeForget_zero_mono R)

private theorem sumRestriction_natural {ι κ : Type u}
    {X : ι → TopCat.{u}} {Y : κ → TopCat.{u}} (indexMap : ι → κ)
    (A : ∀ j, Set (X j)) (B : ∀ j, Set (Y j))
    (f : ∀ j, X j ⟶ Y (indexMap j))
    (hf : ∀ j, Set.MapsTo (f j) (A j) (B (indexMap j))) (n : ℕ) :
    (sumRestriction R X A n).comp
        (relativeCohomologyPullback R (A := sumSubspace X A) (B := sumSubspace Y B)
          (sumMap indexMap f) (fun x hx ↦ hf x.1 hx) n).hom =
      (productPairPullback R indexMap A B f hf n).comp (sumRestriction R Y B n) := by
  ext c j
  change (relativeCohomologyPullback R (A := A j) (B := sumSubspace X A)
      (summandInclusion X j) (fun _x hx ↦ hx) n)
      ((relativeCohomologyPullback R (A := sumSubspace X A) (B := sumSubspace Y B)
        (sumMap indexMap f) (fun x hx ↦ hf x.1 hx) n) c) =
    (relativeCohomologyPullback R (f j) (hf j) n)
      ((relativeCohomologyPullback R (A := B (indexMap j)) (B := sumSubspace Y B)
        (summandInclusion Y (indexMap j)) (fun _x hx ↦ hx) n) c)
  have hmaps : summandInclusion X j ≫ sumMap indexMap f =
      f j ≫ summandInclusion Y (indexMap j) := rfl
  have h := congrArg (fun m ↦ m c)
    (relativeCohomologyPullback_comp R (summandInclusion X j) (sumMap indexMap f)
      (fun _x hx ↦ hx) (fun x hx ↦ hf x.1 hx) n)
  simp only [hmaps] at h
  have h' := congrArg (fun m ↦ m c)
    (relativeCohomologyPullback_comp R (A := A j) (B := B (indexMap j))
      (C := sumSubspace Y B) (f j) (summandInclusion Y (indexMap j))
      (hf j) (fun _x hx ↦ hx) n)
  exact h.symm.trans h'

/-- Full relative singular cohomology pair theorem, including the canonical long
exact sequence, its extension formula and naturality, pair homotopy invariance,
excision, and finite disjoint-union splitting.

Source and complete natural-language proof: Hatcher pp.199–202, with the prism
pp.112–113 and supported subdivision pp.119–124, as in the matching DAG node.

The connecting homomorphisms are quantified simultaneously for all pairs, and
the representative formula specifies them on every cocycle and every extension.
Existence of an extension for each cocycle is explicit, so that formula is not
vacuous. Excision asserts `IsIso` for a morphism of the actual R-module objects;
the finite-sum restriction is an actual R-linear map asserted bijective, which
is precisely an R-linear isomorphism. These formulations retain the stated maps.
The relative groups and pullbacks remain the actual singular cochain quotients.
A,B and all spaces may be empty. No coefficient-field or connectedness premise
is imposed on these arbitrary commutative-ring cohomology statements.

1. By the subspace-supported simplex identification, a cochain on A is precisely an R-valued function on the subset of ambient singular simplices lying in A, extended R-linearly from the free chain basis. Extend it by zero on all other X simplices. This gives a surjective restriction map in each degree with kernel exactly C^n(X,A;R); face restrictions preserve A, so relative cochains form a subcomplex and the short sequence 0→C*(X,A)→C*(X)→C*(A)→0 consists of cochain maps. Zero extension is only a degreewise section and is not claimed to commute with δ.

2. For a cocycle α on A choose an extension ᾱ on X. Its coboundary restricts to δα=0, so δᾱ is relative and is a cocycle by δ²=0. Changing the extension adds a relative cochain, changing δᾱ by a relative coboundary. Changing α by δb and extending b changes the lifted connecting representative by the relative coboundary of ᾱ_new−ᾱ−δb̄. Thus ∂[α]=[δᾱ] is well-defined and R-linear. Exactness at H^n(X) follows as follows: a cocycle z restricting to a coboundary δb can be replaced by z−δb̄, a relative cocycle. Exactness at H^n(A) holds because ∂[α]=0 means δᾱ=δr for a relative r, so ᾱ−r is an absolute cocycle restricting to α. Exactness at H^(n+1)(X,A) holds because a relative cocycle r vanishing as an absolute class has r=δb, and restriction of b is an A-cocycle whose connecting class is [r]. Each reverse containment follows from δ²=0 or restriction vanishing. In degree0 the incoming coboundary group is zero, giving the initial injection; all negative groups may be extended by zero.

3. A continuous pair map f:(X,A)→(Z,C) commutes with face maps and δ. Given a C-cocycle extension on Z, its pullback on X is a permissible extension of the pulled-back A-cocycle; hence f*∂=∂f*. This argument does not assume the particular zero-extension section is natural. For a homotopy F of pairs define P_nσ=Σ_(i=0)^n(−1)^i F∘(σ×id)|[v0,…,vi,wi,…,wn]. Alternating face expansion cancels consecutive interior prism faces; the top and bottom give g#−f#, the remaining side faces give −P∂. Hence ∂P+P∂=g#−f#. All P images of A simplices lie in C. Dualizing gives g♯−f♯=P*δ+δP*, preserving relative cochains, and for a cocycle the difference is a relative coboundary. Thus pair homotopy invariance holds over every R, including degree0.

4. For the interiors cover A,B, let K=C*(A)+C*(B) in C*(X), interpreted as chain complexes on supported ambient simplices. The existing subdivision geometry and the Lebesgue-number theorem give eventual A-or-B smallness of each singular simplex after iterating subdivision S: pull back the open interiors cover to its compact metric domain; barycentric diameters shrink geometrically, while dimension0 simplices are already small. Construct Hatcher’s operators explicitly. Temporarily augment the affine simplex complex by [∅] in degree−1, with ∂[v]=[∅]. For a point b define c_b[v0,…,vn]=[b,v0,…,vn]; alternating-face expansion gives ∂c_b+c_b∂=id. Set S[∅]=[∅], T[∅]=0 and, recursively on each affine vertex simplex λ with barycenter b_λ, Sλ=c_(b_λ)(S∂λ), Tλ=c_(b_λ)(λ−T∂λ). Using the cone identity and the preceding lower-degree identity gives ∂Sλ=S∂λ and ∂Tλ=λ−T∂λ−Sλ. Thus ∂T+T∂=id−S. In dimension0 S[v]=[v] and T[v]=[v,v], whose boundary is zero; T is zero in degree−1, so these identities restrict to the unaugmented ordinary chain complex. For a continuous singular σ define Sσ=σ#(S id_Δ) and Tσ=σ#(T id_Δ). Barycenters and cones commute with affine face inclusions, so the recursive identities commute with all singular faces. Their finitely many summands remain in σ(Δ), hence preserve chains supported in A or B. All formulas extend R-linearly with their integer signs. Choose a depth d(σ) by dimension induction, at least each face depth and large enough for all terms of S^dσ to be small; assign depth0 to already small simplices. Define D_m=Σ_(j<m)TS^j, Dσ=D_(d(σ))σ and ρ=id−∂D−D∂. Then ρ is a chain map. Its value on σ is S^dσ plus a sum over faces τ of Σ_(d(τ)≤j<d(σ))TS^jτ, with the boundary signs; all summands are small by the face-depth choice and support preservation. Thus ρ:C*(X)→K. On K, D=0 and ρ inclusion=id; on all ambient chains inclusion ρ is homotopic to id by D. These are R-linear maps obtained with integer signs, not an assertion that an arbitrary homology equivalence dualizes.

5. Every A simplex is small, so D vanishes on C*(A) and ρ fixes it. Quotient the chain deformation by C*(A): inclusion K/C*(A)→C*(X)/C*(A) and ρ induce mutually inverse chain-homotopy equivalences with the same quotient homotopy. The chain quotient K/C*(A) is canonically C*(B)/C*(A∩B), since its free basis consists of exactly the B simplices not supported in A. Apply Hom_R(−,R). The induced cochain maps still compose to identity up to the explicitly dual homotopies D*δ+δD*, and cochains on these quotient chain modules are exactly the relative cochains. A homotopy difference on a relative cocycle is a relative coboundary, so the canonical inclusion pullback induces the claimed excision isomorphism. Choices of depths affect the chosen inverse but not naturality of the forward map, which is literal restriction under the pair inclusion.

6. A continuous singular simplex in a finite disjoint union has connected domain and hence lies in one summand. Chains therefore split as a direct sum, relative chains as the corresponding quotient sum, and cochains as the product of the individual cochain complexes, with componentwise δ. A product cochain is a cocycle exactly when each coordinate is; in the finite product it is a coboundary exactly when every coordinate is, by choosing finitely many primitives. Restriction therefore yields the stated finite-product cohomology isomorphism and its naturality. The empty family gives zero groups, and empty A gives ordinary absolute cohomology. No infinite-product exactness or tensor-flatness assertion is required.
-/
theorem relative_cohomology_pair_theorems :
    (∃ connecting : ∀ (X : TopCat.{u}) (A : Set X) (n : ℕ),
        cohomology R (TopCat.of A) n →ₗ[R] relativeCohomology R X A (n + 1),
      (∀ (X : TopCat.{u}) (A : Set X),
        Function.Injective (relativeForget R X A 0) ∧
        ∀ n : ℕ,
          LinearMap.range (relativeForget R X A n).hom =
            LinearMap.ker (cohomologyPullback R (subspaceInclusion X A) n).hom ∧
          LinearMap.range (cohomologyPullback R (subspaceInclusion X A) n).hom =
            LinearMap.ker (connecting X A n) ∧
          LinearMap.range (connecting X A n) =
            LinearMap.ker (relativeForget R X A (n + 1)).hom) ∧
      (∀ (X : TopCat.{u}) (A : Set X) (n : ℕ)
          (α : cycles R (complex R (TopCat.of A)) n),
        (∃ extension : cochains R X n,
          ((pullback R (subspaceInclusion X A)).f n) extension = α.val) ∧
        ∀ extension : cochains R X n,
          ((pullback R (subspaceInclusion X A)).f n) extension = α.val →
          ∃ β : cycles R (relativeComplex R X A) (n + 1),
            ((relativeInclusion R X A).f (n + 1)) β.val =
              (coboundary R X n) extension ∧
            connecting X A n (cocycleClass R (complex R (TopCat.of A)) n α) =
              cocycleClass R (relativeComplex R X A) (n + 1) β) ∧
      (∀ {X Y : TopCat.{u}} (A : Set X) (B : Set Y) (f : X ⟶ Y)
          (hf : Set.MapsTo f A B) (n : ℕ),
        (relativeCohomologyPullback R (A := A) (B := B) f hf (n + 1)).hom.comp (connecting Y B n) =
          (connecting X A n).comp
            (cohomologyPullback R (pairSubspaceMap (A := A) (B := B) f hf) n).hom)) ∧
    (∀ {X Y : TopCat.{u}} (A : Set X) (B : Set Y) (f g : X ⟶ Y)
        (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B),
      HomotopicPairMaps A B f g → ∀ n : ℕ,
        relativeCohomologyPullback R (A := A) (B := B) f hf n = relativeCohomologyPullback R (A := A) (B := B) g hg n) ∧
    (∀ (X : TopCat.{u}) (A B : Set X), interior A ∪ interior B = Set.univ →
      ∀ n : ℕ, IsIso (relativeCohomologyPullback R (X := TopCat.of B) (Y := X)
          (A := {x : B | (x : X) ∈ A}) (B := A) (subspaceInclusion X B)
          (by intro x hx; exact hx) n)) ∧
    (∀ (ι : Type u) [Fintype ι] (X : ι → TopCat.{u}) (A : ∀ j, Set (X j)) (n : ℕ),
      Function.Bijective (sumRestriction R X A n)) ∧
    (∀ (ι κ : Type u) [Fintype ι] [Fintype κ]
        {X : ι → TopCat.{u}} {Y : κ → TopCat.{u}} (indexMap : ι → κ)
        (A : ∀ j, Set (X j)) (B : ∀ j, Set (Y j))
        (f : ∀ j, X j ⟶ Y (indexMap j))
        (hf : ∀ j, Set.MapsTo (f j) (A j) (B (indexMap j))) (n : ℕ),
      (sumRestriction R X A n).comp
          (relativeCohomologyPullback R (A := sumSubspace X A) (B := sumSubspace Y B)
            (sumMap indexMap f) (fun x hx => hf x.1 hx) n).hom =
        (productPairPullback R indexMap A B f hf n).comp (sumRestriction R Y B n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun X A n => (quotientConnecting R (singular_cochain_pair_shortExact R X A) n).hom,
      ?_, ?_, ?_⟩
    · intro X A
      refine ⟨relativeForget_zero_injective R, ?_⟩
      intro n
      exact ⟨cochain_quotient_exact_of_shortExact R _
        (singular_cochain_pair_shortExact R X A) n,
        cochain_quotient_connecting_exact R _ (singular_cochain_pair_shortExact R X A) n⟩
    · intro X A n α
      refine ⟨singular_cochain_restriction_surjective R X A n α.val, ?_⟩
      intro b hb
      obtain ⟨β, hβ⟩ := singular_relative_cocycle_of_extension R X A n α b hb
      exact ⟨β, hβ, cochain_quotient_connecting_representative R
        (singular_cochain_pair_shortExact R X A) n α b hb β hβ⟩
    · intro X Y A B f hf n
      let φ : ShortComplex.kernelSequence (pullback R (subspaceInclusion Y B)) ⟶
          ShortComplex.kernelSequence (pullback R (subspaceInclusion X A)) :=
        { τ₁ := relativePullback R f hf
          τ₂ := pullback R f
          τ₃ := pullback R (pairSubspaceMap f hf)
          comm₁₂ := by
            dsimp [relativePullback, ShortComplex.kernelSequence]
            simp
          comm₂₃ := (pairRestrictionSquare R f hf).symm }
      exact congrArg ModuleCat.Hom.hom
        (cochain_quotient_connecting_naturality R φ
          (singular_cochain_pair_shortExact R Y B)
          (singular_cochain_pair_shortExact R X A) n)
  · intro X Y A B f g hf hg hpair n
    rcases hpair with ⟨H, hH⟩
    let HT : TopCat.Homotopy f g := H
    obtain ⟨hr⟩ := (show Nonempty (_root_.Homotopy (relativePullback R f hf)
        (relativePullback R g hg)) from by
      obtain ⟨HA, hsq⟩ := singular_pair_prism_square hf hg HT hH
      let F := (linearYoneda R (ModuleCat.{u} R)).obj (ModuleCat.of R R)
      let h := F.mapHomotopy (HT.toSSet.chainComplexMap (ModuleCat.of R R)).op
      let hA := F.mapHomotopy (HA.chainComplexMap (ModuleCat.of R R)).op
      apply kernel_homotopy_component_lift
        (pullback R (subspaceInclusion Y B)) (pullback R (subspaceInclusion X A))
        (pullback R f) (pullback R g) (pullback R (pairSubspaceMap f hf))
        (pullback R (pairSubspaceMap g hg)) (pairRestrictionSquare R f hf)
        (pairRestrictionSquare R g hg) h hA
      intro i j
      have hc := simplicial_prism_commuting_square HT.toSSet HA
        (TopCat.toSSet.map (subspaceInclusion X A))
        (TopCat.toSSet.map (subspaceInclusion Y B)) hsq (ModuleCat.of R R) j i
      have hd := congrArg (fun k => F.map k.op) hc
      simp only [Functor.map_comp, op_comp] at hd
      exact hd.symm)
    dsimp only [relativeCohomologyPullback, quotientMap]
    rw [hr.homologyMap_eq n]
  · exact relative_cohomology_excision R
  · intro ι _ X A n
    exact cochain_finite_product_quotient_bijective R
      (relativeComplex R (sumSpace X) (sumSubspace X A))
      (fun j => relativeComplex R (X j) (A j))
      (fun j => relativePullback R (A := A j) (B := sumSubspace X A)
        (summandInclusion X j) (fun _ hx => hx))
      (fun k => ⟨relative_sum_cochain_restriction_injective R X A k,
        relative_sum_cochain_restriction_surjective R X A k⟩) n
  · intro ι κ _ _ X Y indexMap A B f hf n
    exact sumRestriction_natural R indexMap A B f hf n

end HolomorphicAnosov.SingularCochain

