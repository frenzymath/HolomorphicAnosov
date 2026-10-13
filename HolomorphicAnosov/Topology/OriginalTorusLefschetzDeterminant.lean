import HolomorphicAnosov.Topology.RationalLoopHomologyG3
import HolomorphicAnosov.Algebra.KroneckerTrace
import HolomorphicAnosov.Topology.SingularChainsULiftDegreeComparison
import HolomorphicAnosov.Topology.SingularChainsULiftBoundary
import HolomorphicAnosov.Topology.SingularChainsULiftNaturality
import HolomorphicAnosov.Topology.ChainComplexIsoHomology
import HolomorphicAnosov.Topology.FunctorialTraceConjugacy
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker
import HolomorphicAnosov.Topology.TorusStandardWinding
import HolomorphicAnosov.Topology.TorusLiftWinding
import HolomorphicAnosov.Topology.TorusSelfmapWindingMatrix
import HolomorphicAnosov.Topology.TorusLefschetzTraceOfMinors
import HolomorphicAnosov.Topology.TorusPositiveDegreePullbackMinor
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.LinearAlgebra.Trace

/-!
# Lefschetz determinant for a space homeomorphic to a torus

Source: Manning, *There are No New Anosov Diffeomorphisms on Tori* (1974), p.424;
Hatcher, *Algebraic Topology*, pp.29–34, 166–167, 179, 195–198, 210, 213, 216.
The node is `topo.original_torus_lefschetz_determinant_g7`.

Ordinary singular homology and its induced maps are the actual Mathlib functor. The
integer action is specified by the actual fundamental-group map and positive real
lift endpoints, for every basepoint-connecting path. No smooth atlas is imposed on
the original space or transported along its homeomorphism. All constructions in
the statement are local expressions built from Mathlib, with no exported definition.
-/

open CategoryTheory
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace HolomorphicAnosov

/-- The ordinary rational Lefschetz number of every positive iterate of a continuous
torus self-map is the determinant of identity minus its degree-one integer action.

Source and scope: Manning (1974), proof of Theorem A, printed p.424, records the
Lefschetz eigenvalue product and explicitly says the torus case is included. The
general continuous-map computation here is the torus exterior-ring calculation in
Hatcher, Proposition 3.10 p.210, Example 3.13 p.213 and Theorem 3.15/Example 3.16
p.216, together with the ordinary trace definition p.179 and field-coefficient
Kronecker evaluation pp.195–198. Hatcher Theorem 2A.1 pp.166–167 gives the natural
degree-one loop/homology identification. His Theorem 1.7 pp.29–31 and Proposition
1.12/Example 1.13 p.34 fix the positive winding coordinates. The principal-minor
calculation in the last paragraph below is an explicitly supplied algebraic
expansion of Mathlib's determinant permutation formula, rather than a claim that
Manning prints that calculation. The named proof dependencies of the current node
retain the lower source obligations; this theorem does not prove a fixed-point
index theorem or a classification theorem.

Complete natural-language proof:

1. Write T for the product of n copies of the real quotient circle and v=q u q⁻¹.
For a based loop p in T, lift each coordinate to a real path starting at zero.
The endpoint is an integer, since the projected endpoint is zero. Hatcher's
circle proof identifies this endpoint with positive winding: the straight path
t ↦ t z projects to the loop of winding z, and straight-line interpolation of
real lifts supplies its endpoint-fixed normal-form homotopy. Lifting an
endpoint-fixed homotopy preserves the integer endpoint, because a continuous
integer-valued boundary path is constant. Coordinatewise application gives a
bijection w from the actual fundamental group to the integer vectors. Lifting
concatenation adds endpoints, and reversal negates them. Mathlib multiplies
loop classes in reverse chronological order, which gives the same addition
because integer vectors commute. Thus w is the stated group equivalence and
its lift characterization holds for every loop representative and integer vector.

2. Choose any path δ from v(0) to zero. Compose the native induced fundamental-
group map of v with the native basepoint change along δ and transport by w.
This is an additive endomorphism of the free integer module. Let its j-th column
be the image of the j-th unit vector; finite integer linear expansion of every
vector gives precisely Matrix.mulVec A. These columns determine A uniquely.
For another connecting path the basepoint changes differ by conjugation by a
loop. The winding group is abelian, so conjugation is trivial and the same A
works for every δ. This is why no fixed-basepoint hypothesis on v is needed.


3. The homeomorphism q and its inverse induce inverse ordinary singular homology
maps, so each H_k(X;Q) is linearly isomorphic to H_k(T;Q). The named rational
torus cup-basis/Kronecker theorem, obtained from Hatcher's product calculation
and field evaluation, gives one cohomology basis vector α_S for each k-element
subset S of the n coordinate indices; the corresponding evaluation-dual
homology basis has the same indices. Thus each degree is finite dimensional and
degrees greater than n vanish. These are conclusions, rather than assumed
finite-dimensionality needed to give meaning to the trace. Using ULift Q as the
coefficient module only places ordinary Q coefficients in the universe of X;
its canonical down/up linear equivalence identifies the ordinary chain complexes.

4. Construct the rational loop-to-H₁ map from actual singular one-chains.
The concatenation triangle proves additivity, the homotopy square proves
invariance, and cancellation of a path with its reverse proves basepoint-change
invariance. Thus it is natural for the unbased map v. Its positive coordinate
loop classes equal the specified rational coordinate cycles, by their literal
simplex formulas. Expanding the winding lattice on these generators proves
that v_* has matrix A_Q in that rational basis. Homology functoriality identifies
the map of v^m with the m-th power, so its matrix is (A_Q)^m. Naturality of evaluation
gives v*α_i=Σ_j A_ij α_j; equivalently the column matrix on the coordinate
cohomology basis is A_Q transposed. By cup naturality, v*α_S is the product of
these degree-one images in the increasing order of S. Expand the product.
Repeated indices vanish, and anticommutation gives precisely the permutation
sign in each minor determinant. The coefficient of α_T is the S,T minor of A_Q;
in particular the diagonal coefficient is det(A_Q restricted to S×S).
The evaluation-dual homology map is the transpose of this cohomology matrix,
so it has the same trace. Applying this calculation to v^m replaces A_Q by
B=(A_Q)^m. Consequently its degree-k trace is the sum of det(B restricted to
S×S) over all k-element S. In degree zero the basis vector is the empty cup monomial, namely the unit.
Pullback preserves its constant-one cochain representative, hence its cohomology
class. Its diagonal coefficient and the empty principal minor are both 1.

5. Functoriality conjugates the homology map of u^m to that of v^m through q.
Trace is invariant under this conjugation, so the alternating finite sum of
the traces on X is the same sum on T. This uses only the homeomorphism and its
continuous inverse, and takes no derivative of q or of the original map.

6. Expand det(I−B) by the exact determinant permutation formula, and expand each
product by selecting the −B factor on a subset S of the coordinates. Every
nonzero identity factor outside S forces the permutation to fix that coordinate.
Such permutations restrict bijectively to permutations of S, with identical
sign because the other coordinates are fixed. The contribution is therefore
(−1)^|S| det(B restricted to S×S), using the same row-permutation convention
as Mathlib's determinant. Sum over S, group by cardinality, and insert the
degree traces from step 4 and conjugacy from step 5. This is exactly the displayed
determinant equality for every m≥1. No eigenvalue decomposition, matrix unit,
hyperbolicity, invertibility, or smooth structure is used. For n=0 the torus
and X are singletons, the winding group and matrix are empty, H₀ has dimension
one and all higher groups vanish; both sides equal one. Constant maps and
orientation-reversing maps are included by the same formulas.
-/
theorem original_torus_lefschetz_determinant
    (n : ℕ) {X : Type u} [TopologicalSpace X]
    (q : X ≃ₜ UnitAddTorus (Fin n)) (u : C(X, X)) :
    let T := UnitAddTorus (Fin n)
    let v : C(T, T) := (q : C(X, T)).comp (u.comp (q.symm : C(T, X)))
    let H : ℕ → TopCat.{u} ⥤ ModuleCat.{u} ℚ := fun k ↦
      (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) k).obj
        (ModuleCat.of ℚ (ULift.{u} ℚ))
    (∀ k, FiniteDimensional ℚ ((H k).obj (TopCat.of X) : Type u)) ∧
    (∀ k, n < k → Subsingleton ((H k).obj (TopCat.of X) : Type u)) ∧
    ∃ w : FundamentalGroup T 0 ≃* Multiplicative (Fin n → ℤ),
      (∀ (p : Path (0 : T) 0) (z : Fin n → ℤ),
        w (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
            Multiplicative.ofAdd z ↔
          ∃ l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)),
            ∀ t i, (l t i : UnitAddCircle) = p t i) ∧
      ∃! A : Matrix (Fin n) (Fin n) ℤ,
        (∀ (δ : Path (v 0) (0 : T)) (γ : FundamentalGroup T 0),
          (w ((FundamentalGroup.fundamentalGroupMulEquivOfPath δ)
            (FundamentalGroup.map v 0 γ))).toAdd = Matrix.mulVec A (w γ).toAdd) ∧
        ∀ m : ℕ, 1 ≤ m →
          (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k *
            LinearMap.trace ℚ ((H k).obj (TopCat.of X) : Type u)
              ((H k).map (TopCat.ofHom
                (⟨(u : X → X)^[m], u.continuous.iterate m⟩ : C(X, X)))).hom) =
            Matrix.det (1 - (A.map (Int.castRingHom ℚ)) ^ m) := by
  classical
  let T := UnitAddTorus (Fin n)
  let v : C(T, T) := (q : C(X, T)).comp (u.comp (q.symm : C(T, X)))
  let H : ℕ → TopCat.{u} ⥤ ModuleCat.{u} ℚ := fun k ↦
    (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℚ) k).obj
      (ModuleCat.of ℚ (ULift.{u} ℚ))
  -- Keep the torus in the universe of X before applying the homology functor.
  let Tlift := ULift.{u} T
  let qlift : X ≃ₜ Tlift := q.trans Homeomorph.ulift.symm
  let vlift : C(Tlift, Tlift) :=
    (qlift : C(X, Tlift)).comp (u.comp (qlift.symm : C(Tlift, X)))
  have hsemi : Function.Semiconj qlift u vlift := by
    intro x
    change qlift (u x) = qlift (u (qlift.symm (qlift x)))
    rw [qlift.symm_apply_apply]
  have htrace (m : ℕ) :
      (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k *
        LinearMap.trace ℚ ((H k).obj (TopCat.of Tlift) : Type u)
          ((H k).map (TopCat.ofHom
            (⟨(vlift : Tlift → Tlift)^[m], vlift.continuous.iterate m⟩ :
              C(Tlift, Tlift)))).hom) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k *
        LinearMap.trace ℚ ((H k).obj (TopCat.of X) : Type u)
          ((H k).map (TopCat.ofHom
            (⟨(u : X → X)^[m], u.continuous.iterate m⟩ : C(X, X)))).hom := by
    apply functor_alternating_trace_eq_of_conjugacy H
      (TopCat.isoOfHomeo qlift)
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change qlift ((u : X → X)^[m] x) =
      (vlift : Tlift → Tlift)^[m] (qlift x)
    exact hsemi.iterate_right m x
  let : PathConnectedSpace X := q.symm.pathConnectedSpace
  let : PathConnectedSpace Tlift := qlift.pathConnectedSpace
  obtain ⟨w, hnorm, _, _⟩ := torus_pi1_standard_winding n
  have hw := normalized_winding_lift_characterization n w hnorm
  obtain ⟨A, hA, hA_unique⟩ := torus_selfmap_winding_matrix n v w
  have htransport (f : C(T, T)) :
      ∀ k, ∃ h : ((TopCat.toSSet.obj (TopCat.of Tlift)).chainComplex
          (ModuleCat.of ℚ (ULift.{u} ℚ))).homology k ≃ₗ[ℚ]
          ((TopCat.toSSet.obj (TopCat.of T)).chainComplex
            (ModuleCat.of ℚ ℚ)).homology k,
        ∀ x, h
            (HomologicalComplex.homologyMap
              (SSet.chainComplexMap
                (TopCat.toSSet.map (TopCat.ofHom
                  (⟨fun y ↦ ULift.up (f y.down),
                    (Homeomorph.ulift : Tlift ≃ₜ T).symm.continuous.comp
                      (f.continuous.comp (Homeomorph.ulift : Tlift ≃ₜ T).continuous)⟩ :
                    C(Tlift, Tlift))))
                (ModuleCat.of ℚ (ULift.{u} ℚ))) k x) =
          HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
              (ModuleCat.of ℚ ℚ)) k (h x) := by
    intro k
    let K (Y : TopCat.{0}) := (TopCat.toSSet.obj (TopCat.of (ULift.{u} Y))).chainComplex
      (ModuleCat.of ℚ (ULift.{u} ℚ))
    let L (Y : TopCat.{0}) := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)
    choose e he using (fun (Y : TopCat) (j : ℕ) ↦
      singular_chains_ulift_degree_comparison.{u} Y j)
    have hd (Y : TopCat) : ∀ j x,
        (e Y j) ((K Y).d (j + 1) j x) =
          (L Y).d (j + 1) j ((e Y (j + 1)) x) :=
      singular_chains_ulift_boundary.{u} Y
        (fun j ↦ (e Y j).toLinearMap) (he Y)
    obtain ⟨_, _, h⟩ := chain_complex_ulift_comparison
      (fun Y : TopCat.{0} ↦ K Y) (fun Y : TopCat.{0} ↦ L Y) e hd
    obtain ⟨h, hh⟩ := h k
    refine ⟨h (TopCat.of T), ?_⟩
    let upv : C(Tlift, Tlift) :=
      ⟨fun y ↦ ULift.up (f y.down),
        (Homeomorph.ulift : Tlift ≃ₜ T).symm.continuous.comp
          (f.continuous.comp (Homeomorph.ulift : Tlift ≃ₜ T).continuous)⟩
    apply hh (TopCat.of T) (TopCat.of T)
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom upv))
        (ModuleCat.of ℚ (ULift.{u} ℚ)))
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
        (ModuleCat.of ℚ ℚ))
    intro j c
    exact singular_chains_ulift_naturality.{u} (TopCat.of T) (TopCat.of T) f j
      (e (TopCat.of T) j).toLinearMap (e (TopCat.of T) j).toLinearMap
      (he (TopCat.of T) j) (he (TopCat.of T) j) c
  obtain ⟨cup, one, a, z, hz, hnormNative, hrepNative, hunitNative, hbig⟩ :=
    TorusRationalCupBasisKronecker.torus_rational_cup_basis_kronecker n
  dsimp at hbig
  rcases hbig with ⟨hBasisNative, hzeroCup, hcommNative, hsqNative,
    hENative, hrepENative, hfiniteNative, hzeroNative, hcoordNative,
    hnatCupNative, hnatPairNative⟩
  have hfiniteLift (k : ℕ) :
      FiniteDimensional ℚ ((H k).obj (TopCat.of Tlift) : Type u) := by
    obtain ⟨h, _⟩ := htransport v k
    let Cnative :=
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj (TopCat.of T)
    let : FiniteDimensional ℚ ((Cnative.sc k).moduleCatLeftHomologyData.H) := hfiniteNative k
    let e := (Cnative.sc k).moduleCatHomologyIso.toLinearEquiv
    exact FiniteDimensional.of_injective
      (e.toLinearMap.comp h.toLinearMap)
      (e.injective.comp h.injective)
  have hzeroLift (k : ℕ) (hk : n < k) :
      Subsingleton ((H k).obj (TopCat.of Tlift) : Type u) := by
    obtain ⟨h, _⟩ := htransport v k
    let Cnative :=
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).obj (TopCat.of T)
    let : Subsingleton ((Cnative.sc k).moduleCatLeftHomologyData.H) := hzeroNative k hk
    let e := (Cnative.sc k).moduleCatHomologyIso.toLinearEquiv
    exact ⟨fun x y ↦ h.injective (e.injective (Subsingleton.elim _ _))⟩
  let H0 : ℕ → TopCat.{0} ⥤ ModuleCat.{0} ℚ := fun k ↦
    (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) k).obj
      (ModuleCat.of ℚ ℚ)
  have htraceNative (m k : ℕ) :
      LinearMap.trace ℚ ((H k).obj (TopCat.of Tlift) : Type u)
        ((H k).map (TopCat.ofHom
          (⟨(vlift : Tlift → Tlift)^[m], vlift.continuous.iterate m⟩ :
            C(Tlift, Tlift)))).hom =
      LinearMap.trace ℚ ((H0 k).obj (TopCat.of T))
        ((H0 k).map (TopCat.ofHom
          (⟨(v : T → T)^[m], v.continuous.iterate m⟩ : C(T, T)))).hom := by
    let fm : C(T, T) := ⟨(v : T → T)^[m], v.continuous.iterate m⟩
    obtain ⟨h, hh⟩ := htransport fm k
    have hsemiDown : Function.Semiconj (ULift.down : Tlift → T) vlift v := by
      intro x
      rfl
    have hliftIter :
        (⟨(vlift : Tlift → Tlift)^[m], vlift.continuous.iterate m⟩ :
          C(Tlift, Tlift)) =
        (⟨fun x ↦ ULift.up (fm x.down),
          (Homeomorph.ulift : Tlift ≃ₜ T).symm.continuous.comp
            (fm.continuous.comp (Homeomorph.ulift : Tlift ≃ₜ T).continuous)⟩ :
          C(Tlift, Tlift)) := by
      apply ContinuousMap.ext
      intro x
      apply ULift.ext
      exact hsemiDown.iterate_right m x
    rw [hliftIter]
    let F := ((H k).map (TopCat.ofHom
      (⟨fun x ↦ ULift.up (fm x.down),
        (Homeomorph.ulift : Tlift ≃ₜ T).symm.continuous.comp
          (fm.continuous.comp (Homeomorph.ulift : Tlift ≃ₜ T).continuous)⟩ :
        C(Tlift, Tlift)))).hom
    let G := ((H0 k).map (TopCat.ofHom fm)).hom
    let e : ((H k).obj (TopCat.of Tlift) : Type u) ≃ₗ[ℚ]
        ((H0 k).obj (TopCat.of T)) := h
    have heq : e.conj F = G := by
      ext x
      change e (F (e.symm x)) = G x
      have hx := hh (e.symm x)
      change e (F (e.symm x)) = G (e (e.symm x)) at hx
      simpa only [e.apply_symm_apply] using hx
    change LinearMap.trace ℚ _ F = LinearMap.trace ℚ _ G
    rw [← heq, LinearMap.trace_conj']
  suffices hhomology :
      (∀ k, FiniteDimensional ℚ ((H k).obj (TopCat.of Tlift) : Type u)) ∧
      (∀ k, n < k → Subsingleton ((H k).obj (TopCat.of Tlift) : Type u)) ∧
      (∀ m : ℕ, 1 ≤ m →
        (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k *
          LinearMap.trace ℚ ((H k).obj (TopCat.of Tlift) : Type u)
            ((H k).map (TopCat.ofHom
              (⟨(vlift : Tlift → Tlift)^[m], vlift.continuous.iterate m⟩ :
                C(Tlift, Tlift)))).hom) =
          Matrix.det (1 - (A.map (Int.castRingHom ℚ)) ^ m)) by
    have hfinite (k : ℕ) : FiniteDimensional ℚ ((H k).obj (TopCat.of X) : Type u) := by
      let := hhomology.1 k
      let e := ((H k).mapIso (TopCat.isoOfHomeo
        (X := TopCat.of X) (Y := TopCat.of Tlift) qlift)).toLinearEquiv
      exact FiniteDimensional.of_injective e.toLinearMap e.injective
    have hzero (k : ℕ) (hk : n < k) :
        Subsingleton ((H k).obj (TopCat.of X) : Type u) := by
      let := hhomology.2.1 k hk
      let e := ((H k).mapIso (TopCat.isoOfHomeo
        (X := TopCat.of X) (Y := TopCat.of Tlift) qlift)).toLinearEquiv
      exact ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩
    refine ⟨hfinite, hzero, w, hw, A, ⟨hA, ?_⟩, ?_⟩
    · intro m hm
      exact (htrace m).symm.trans (hhomology.2.2 m hm)
    · intro B hB
      exact hA_unique B hB.1
  refine ⟨hfiniteLift, hzeroLift, ?_⟩
  intro m hm
  simp_rw [htraceNative]
  let fm : C(T, T) := ⟨(v : T → T)^[m], v.continuous.iterate m⟩
  let Cnative :=
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of T)
  let Hcup := fun k ↦ SingularCochain.cohomology ℚ (TopCat.of T) k
  let pull := fun k ↦
    (SingularCochain.cohomologyPullback ℚ (TopCat.ofHom fm) k).hom
  have htraceCup (k : ℕ) :
      LinearMap.trace ℚ ((H0 k).obj (TopCat.of T))
        ((H0 k).map (TopCat.ofHom fm)).hom =
      LinearMap.trace ℚ (Hcup k) (pull k) := by
    let : FiniteDimensional ℚ ((Cnative.sc k).moduleCatLeftHomologyData.H) := hfiniteNative k
    let e := (Cnative.sc k).moduleCatHomologyIso.toLinearEquiv
    let f := ((H0 k).map (TopCat.ofHom fm)).hom
    have hpair := trace_eq_of_kronecker_naturality (hENative k)
      (e.conj f) (pull k) (hnatPairNative fm k)
    exact (LinearMap.trace_conj' f e).symm.trans hpair.symm
  change (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k *
    LinearMap.trace ℚ ((H0 k).obj (TopCat.of T))
      ((H0 k).map (TopCat.ofHom fm)).hom) = _
  simp_rw [htraceCup]
  let b := fun k ↦ (hBasisNative k).choose
  let α : Fin n → Hcup 1 := fun i ↦
    (SingularCochain.cohomologyPullback ℚ
      (TorusRationalCupBasisKronecker.coordinateProjection n i) 1)
      (SingularCochain.cocycleClass ℚ
        (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a)
  obtain ⟨wc, bh0, hwc, hbh, hdual⟩ := hcoordNative
  let bh : Module.Basis (Fin n) ℚ ((Cnative.sc 1).moduleCatLeftHomologyData.H) := bh0
  let e := (Cnative.sc 1).moduleCatHomologyIso.toLinearEquiv
  let cb : Module.Basis (Fin n) ℚ (RationalSingularH1G3.H1 T) := bh.map e.symm
  have hcb (i : Fin n) : cb i =
      RationalSingularH1G3.degreeOneHurewiczFunction (0 : T)
        (w.symm (Multiplicative.ofAdd (Pi.single i (1 : ℤ)))) := by
    rw [show cb i = e.symm (bh i) from Module.Basis.map_apply _ _ _]
    have hbhi : bh i = (Cnative.sc 1).moduleCatLeftHomologyData.π (wc i) := hbh i
    rw [hbhi]
    have hwci : wc i = TorusRationalCupBasisKronecker.coordinateCycle n z i := by
      apply Subtype.ext
      exact hwc i
    rw [hwci]
    exact RationalSingularH1G3.coordinate_cycle_eq_winding n w hnorm z hz i
  let δ := PathConnectedSpace.somePath (v 0) (0 : T)
  have hmat : LinearMap.toMatrix cb cb (RationalSingularH1G3.homologyMap v) =
      A.map (Int.castRingHom ℚ) :=
    RationalSingularH1G3.homologyMap_matrix_of_winding 0 n w cb hcb v δ A (hA δ)
  have hmatm : LinearMap.toMatrix cb cb (RationalSingularH1G3.homologyMap fm) =
      (A.map (Int.castRingHom ℚ)) ^ m := by
    rw [show RationalSingularH1G3.homologyMap fm =
        RationalSingularH1G3.homologyMap v ^ m from
      RationalSingularH1G3.homologyMap_iterate v m]
    rw [← LinearMap.toMatrix_pow, hmat]
  let push := e.conj (RationalSingularH1G3.homologyMap fm)
  have hpushmat : LinearMap.toMatrix bh bh push =
      (A.map (Int.castRingHom ℚ)) ^ m := by
    rw [← hmatm]
    ext i j
    rfl
  have hpush (j : Fin n) : push (bh j) =
      ∑ i, ((A.map (Int.castRingHom ℚ)) ^ m) i j • bh i := by
    rw [← hpushmat]
    simpa only [LinearMap.toMatrix_apply] using (bh.sum_repr (push (bh j))).symm
  let E : Hcup 1 ≃ₗ[ℚ] Module.Dual ℚ ((Cnative.sc 1).moduleCatLeftHomologyData.H) := hENative 1
  have hd (i j : Fin n) : E (α i) (bh j) = if i = j then 1 else 0 := hdual i j
  have halpha (i : Fin n) : pull 1 (α i) =
      ∑ j, ((A.map (Int.castRingHom ℚ)) ^ m) i j • α j := by
    apply E.injective
    apply bh.ext
    intro j
    have hn := hnatPairNative fm 1 (α i) (bh j)
    change E (pull 1 (α i)) (bh j) = E (α i) (push (bh j)) at hn
    rw [hn, hpush]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    change (∑ x, ((A.map (Int.castRingHom ℚ)) ^ m) x j •
      E (α i) (bh x)) =
      ∑ x, ((A.map (Int.castRingHom ℚ)) ^ m) i x • E (α x) (bh j)
    simp only [hd]
    simp
  apply torus_lefschetz_trace_of_minor_diagonals n
    ((A.map (Int.castRingHom ℚ)) ^ m) (fun k ↦ (Hcup k : Type)) b pull
  intro k S
  exact torus_positive_degree_pullback_principal_minor n
    ((A.map (Int.castRingHom ℚ)) ^ m) (TopCat.of T) (TopCat.ofHom fm)
    cup one α b hrepNative hunitNative
    (fun d U ↦ (hBasisNative d).choose_spec U) halpha k S


end HolomorphicAnosov
