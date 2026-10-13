import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SpecifiedCupLeftUnit
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SpecifiedCupNaturality
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AbsoluteCupData
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AdditiveCircleNormalization
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.BasisFromKronecker
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CoordinateCupMonomialBasis
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CoordinateCycle
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CoordinateKronecker
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CoordinateProjection
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.HomologyFiniteOfCohomology
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.HomologyZeroOfCohomology
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.OddSquareZero
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularKroneckerNaturality
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularKroneckerRepresentative
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingletonIndex
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SubsetBasisZero

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option backward.isDefEq.respectTransparency false in
/-- **The rational torus exterior cup basis and its natural Kronecker pairing.**

Source: Hatcher, cochains pp.197–198; cup formula pp.206–207;
Proposition3.10 p.210; Theorem3.11 pp.210–212; Example3.13 p.213;
Theorem3.15/Example3.16 pp.216–218; Theorem2A.1 pp.166–167.

The original natural statement is: for n≥0 let Tⁿ=(ℝ/ℤ)ⁿ. Let αᵢ be the
pullback of the positively oriented rational circle generator by coordinate i.
The increasing cup monomials indexed by k-element subsets of Fin n form a
rational basis of Hᵏ(Tⁿ); the empty monomial is the unit and Hᵏ=0 for k>n.
Multiplication is exterior multiplication, αᵢαⱼ=−αⱼαᵢ and αᵢ²=0.
Kronecker evaluation is a natural linear isomorphism from Hᵏ to the full
algebraic dual of Hₖ. Homology is finite-dimensional and vanishes above n;
the coordinate positive winding classes form the basis dual to the αᵢ.
For every continuous torus self-map, pullback preserves cups and evaluation
satisfies ⟨u*a,b⟩=⟨a,u*b⟩, without any basepoint restriction.

`cup` is bilinear native quotient data supplied as an output, with its value
on every cocycle pair pinned to the genuine Alexander–Whitney cochain formula.
`one` is similarly pinned to the constant-one cochain. Each `E k` is an output
linear equivalence pinned on every original cocycle/cycle representative to
ordinary linear evaluation. Thus these are the actual operations, rather than
arbitrary algebraic structures satisfying only a multiplication table.
`monomial` recursively multiplies the increasing sorted subset; its degree is
its list length. The basis equation casts only along length_sort and card=k.
`Subsingleton` expresses a zero module, also in all empty-index edge cases.

Complete natural-language proof relative to the named source dependencies:

1. Use the actual singular dual quotient. The positive loop t↦[t] corresponds
under the pinned AddCircle homeomorphism to exp(2πit). The circle theorem gives
its cycle and the unique rational class evaluating to1 on it. Define αᵢ by the
coordinate pullbacks. The cochain front/back formula descends by the Leibniz
identity, giving bilinear cups and the constant-one unit. Cup naturality and
H²(circle)=0 give αᵢ²=0. Degree1 graded commutativity gives αᵢαⱼ=−αⱼαᵢ.

2. At n=0 the torus is a point, so H⁰ has the unit basis and positive degrees
vanish. Split Tⁿ⁺¹ into Tⁿ×circle using the actual coordinate product. The finite
coordinate CW structures and the circle's finite free cohomology permit the
source Künneth theorem. In degree k the only summands are Hᵏ(Tⁿ)⊗H⁰(circle)
and, when k≥1, Hᵏ⁻¹(Tⁿ)⊗H¹(circle). Their bases respectively give increasing
monomials omitting the final coordinate and increasing monomials containing it.
These are exactly the k-element subsets. At k=0 only the unit summand occurs;
above n+1 both vanish. Associativity and the degree1 sign law reorder every
monomial product; repetition produces a square and hence zero, otherwise the
sign is the parity of sorting the concatenated indices. This is exterior
multiplication on all degrees, not an assumed exterior presentation.

3. Apply field-chain Kronecker evaluation to the original rational singular
chains. Restrict each cocycle to cycles and descend through the two quotients.
Field subspace extension gives the linear equivalence with the full homology
dual, without finiteness assumptions. Its representative formula is ordinary
evaluation. On a continuous map the two evaluated representatives are a∘u♯
and u♯z, so their values agree. Cup pullback naturality holds on the actual
front/back simplex formula and hence on every quotient class.

4. The cohomology basis makes the full homology dual finite-dimensional. If
homology had an independent family larger than this dimension, its coordinate
functionals on the span would extend to the whole homology vector space by
LinearMap.exists_extend and remain independent, a contradiction. Thus homology
is finite-dimensional. If its dual is zero, a nonzero vector's coefficient
functional would extend to a nonzero full functional, so homology itself is zero.

5. Push the actual positive circle cycle through each coordinate inclusion.
Pairing naturality projects it to the positive circle cycle in the same
coordinate and to a constant loop otherwise. Circle normalization and constant
pullback vanishing give the matrix δᵢⱼ. Pairing proves independence. A proper
span would have a nonzero annihilating functional by subspace extension, but
every functional is a linear combination of the E(αᵢ), whose values on the
coordinate classes force every coefficient to zero. Therefore the coordinate
classes form the stated dual basis. At n=0 these bases are empty and H₁=0.
-/
theorem torus_rational_cup_basis_kronecker (n : ℕ) :
    let circleSpace : TopCat := TopCat.of UnitAddCircle
    let X : TopCat := TopCat.of (UnitAddTorus (Fin n))
    let C : TopCat ⥤ ChainComplex (ModuleCat ℚ) ℕ :=
      (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
    let cycles := fun (Y : TopCat) (k : ℕ) ↦ LinearMap.ker ((C.obj Y).sc k).g.hom
    let homology := fun (Y : TopCat) (k : ℕ) ↦ ((C.obj Y).sc k).moduleCatLeftHomologyData.H
    let cycleClass := fun (Y : TopCat) (k : ℕ) (z : cycles Y k) ↦
      ((C.obj Y).sc k).moduleCatLeftHomologyData.π z
    let positiveChain :=
      ((TopCat.toSSet.obj circleSpace).ιChainComplex (R := ModuleCat.of ℚ ℚ)
        (TopCat.toSSetObj₁Equiv.symm
          (TopCat.ofHom ⟨fun t ↦ ((t.down : ℝ) : UnitAddCircle), by fun_prop⟩))) 1
    let coordinateProjection : Fin n → (X ⟶ circleSpace) := fun i ↦
      TopCat.ofHom ⟨fun x ↦ x i, continuous_apply i⟩
    let coordinateInclusion : Fin n → (circleSpace ⟶ X) := fun i ↦
      TopCat.ofHom ⟨fun x j ↦ if j = i then x else 0,
        continuous_pi fun j ↦ by split_ifs <;> fun_prop⟩
    let pushforward := fun (u : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n))) (k : ℕ) ↦
      (((C.obj X).sc k).moduleCatHomologyIso.inv ≫
        HomologicalComplex.homologyMap (C.map (TopCat.ofHom u)) k ≫
        ((C.obj X).sc k).moduleCatHomologyIso.hom).hom
    let H := fun k ↦ SingularCochain.cohomology ℚ X k
    let Z := fun k ↦ SingularCochain.cycles ℚ (SingularCochain.complex ℚ X) k
    let cls := fun k ↦
      SingularCochain.cocycleClass ℚ (SingularCochain.complex ℚ X) k
    ∃ (cup : ∀ p q : ℕ, H p →ₗ[ℚ] H q →ₗ[ℚ] H (p + q))
      (one : H 0)
      (a : SingularCochain.cycles ℚ (SingularCochain.complex ℚ circleSpace) 1)
      (z : cycles circleSpace 1),
      z.val = positiveChain ∧
      (show (C.obj circleSpace).X 1 ⟶ ModuleCat.of ℚ ℚ from a.val) z.val = 1 ∧
      (∀ p q (b : Z p) (c : Z q),
        ∃ hc : SingularCochain.cupCochain ℚ X b.val c.val ∈ Z (p + q),
          cup p q (cls p b) (cls q c) =
            cls (p + q) ⟨SingularCochain.cupCochain ℚ X b.val c.val, hc⟩) ∧
      (∃ hu : SingularCochain.oneCochain ℚ X ∈ Z 0,
        one = cls 0 ⟨SingularCochain.oneCochain ℚ X, hu⟩) ∧
      (let circleClass :=
         ((SingularCochain.complex ℚ circleSpace).sc 1).moduleCatLeftHomologyData.π a
       let α := fun i : Fin n ↦
         (SingularCochain.cohomologyPullback ℚ (coordinateProjection i) 1).hom
           circleClass
       let monomial : ∀ l : List (Fin n), H l.length :=
         fun l ↦ List.rec (motive := fun l ↦ H l.length) one
           (fun i l v ↦ cast (congrArg (fun d ↦ (H d : Type)) (Nat.add_comm 1 l.length))
             (cup 1 l.length (α i) v)) l
       (∀ k : ℕ,
         ∃ B : Module.Basis {S : Finset (Fin n) // S.card = k} ℚ (H k),
           ∀ S, B S = cast
             (congrArg (fun d ↦ (H d : Type))
               ((S.val.length_sort (· ≤ ·)).trans S.property))
             (monomial (S.val.sort (· ≤ ·)))) ∧
       (∀ k : ℕ, n < k → Subsingleton (H k)) ∧
       (∀ i j : Fin n, cup 1 1 (α i) (α j) = -cup 1 1 (α j) (α i)) ∧
       (∀ i : Fin n, cup 1 1 (α i) (α i) = 0) ∧
       (∃ E : ∀ k : ℕ, H k ≃ₗ[ℚ] Module.Dual ℚ (homology X k),
         (∀ k (b : Z k) (c : cycles X k),
           E k (cls k b) (cycleClass X k c) =
             (show (C.obj X).X k ⟶ ModuleCat.of ℚ ℚ from b.val) c.val) ∧
         (∀ k, FiniteDimensional ℚ (homology X k)) ∧
         (∀ k, n < k → Subsingleton (homology X k)) ∧
         (∃ (w : ∀ _i : Fin n, cycles X 1)
           (B : Module.Basis (Fin n) ℚ (homology X 1)),
           (∀ i, (w i).val =
             ((C.map (coordinateInclusion i)).f 1) z.val) ∧
           (∀ i, B i = cycleClass X 1 (w i)) ∧
           (∀ i j, E 1 (α i) (B j) = if i = j then 1 else 0)) ∧
         (∀ (u : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
           (p q : ℕ) (b : H p) (c : H q),
           (SingularCochain.cohomologyPullback ℚ (TopCat.ofHom u) (p + q)).hom
             (cup p q b c) =
             cup p q ((SingularCochain.cohomologyPullback ℚ (TopCat.ofHom u) p).hom b)
               ((SingularCochain.cohomologyPullback ℚ (TopCat.ofHom u) q).hom c)) ∧
         (∀ (u : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
           (k : ℕ) (b : H k) (c : homology X k),
           E k ((SingularCochain.cohomologyPullback ℚ (TopCat.ofHom u) k).hom b) c =
             E k b (pushforward u k c)))) := by
  classical
  let X : TopCat := TopCat.of (UnitAddTorus (Fin n))
  obtain ⟨cup, one, hrep, hunit, hcomm, hnat, hright⟩ := absolute_cup_data X
  obtain ⟨a, z, hz, hnorm, hconst⟩ := additive_circle_normalization
  refine ⟨cup, one, a, z, hz, hnorm, hrep, hunit, ?_⟩
  let α := fun i : Fin n ↦
    (SingularCochain.cohomologyPullback ℚ (coordinateProjection n i) 1)
      (SingularCochain.cocycleClass ℚ
        (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 1 a)
  let monomial : ∀ l : List (Fin n), SingularCochain.cohomology ℚ X l.length :=
    fun l ↦ List.rec (motive := fun l ↦ SingularCochain.cohomology ℚ X l.length) one
      (fun i l v ↦ cast (congrArg
        (fun d ↦ (SingularCochain.cohomology ℚ X d : Type)) (Nat.add_comm 1 l.length))
          (cup 1 l.length (α i) v)) l
  -- The coordinate product induction identifies the native Künneth basis vectors.
  have hBasis : ∀ k : ℕ,
      ∃ B : Module.Basis {S : Finset (Fin n) // S.card = k} ℚ
          (SingularCochain.cohomology ℚ X k),
        ∀ S, B S = cast (congrArg
          (fun d ↦ (SingularCochain.cohomology ℚ X d : Type))
          ((S.val.length_sort (· ≤ ·)).trans S.property))
          (monomial (S.val.sort (· ≤ ·))) :=
    coordinate_cup_monomial_basis n cup one a z hz hnorm hrep hunit
  have hzero : ∀ k : ℕ, n < k → Subsingleton (SingularCochain.cohomology ℚ X k) := by
    intro k hk
    obtain ⟨B, hB⟩ := hBasis k
    exact subset_basis_zero n k B hk
  refine ⟨hBasis, hzero, (fun i j ↦ hcomm (α i) (α j)),
    (fun i ↦ odd_square_zero (cup 1 1) hcomm (α i)),
    (fun k ↦ singularKronecker X k), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k b c
    exact singularKronecker_representative X k b c
  · intro k
    obtain ⟨B, hB⟩ := hBasis k
    let := Module.Finite.of_basis B
    exact homology_finite_of_cohomology X k
  · intro k hk
    let := hzero k hk
    exact homology_zero_of_cohomology X k
  · obtain ⟨B, hB⟩ := hBasis 1
    let Bc := B.reindex (singletonIndex n).symm
    have hBc : ∀ i : Fin n, Bc i = α i := by
      intro i
      rw [Module.Basis.reindex_apply]
      change B ⟨{i}, by simp⟩ = α i
      rw [hB]
      apply eq_of_heq
      apply HEq.trans (cast_heq _ _)
      have hs : ({i} : Finset (Fin n)).sort (· ≤ ·) = [i] :=
        Finset.sort_singleton _ _
      rw [hs]
      exact heq_of_eq (hright (α i))
    let w := fun i ↦ coordinateCycle n z i
    let wc := fun i ↦ ((((SingularCochain.chainFunctor ℚ).obj X).sc 1).moduleCatLeftHomologyData.π) (w i)
    have hm : ∀ i j, singularKronecker X 1 (Bc i) (wc j) = if i = j then 1 else 0 := by
      intro i j
      rw [hBc]
      exact coordinate_kronecker n a z hnorm hconst i j
    obtain ⟨D, hD⟩ := basis_from_kronecker Bc (singularKronecker X 1) wc hm
    refine ⟨w, D, (fun i ↦ rfl), hD, ?_⟩
    intro i j
    rw [hD]
    exact coordinate_kronecker n a z hnorm hconst i j
  · intro u p q b c
    exact hnat (TopCat.ofHom u) p q b c
  · intro u k b c
    exact singularKronecker_naturality (TopCat.ofHom u) k b c

end HolomorphicAnosov.TorusRationalCupBasisKronecker
