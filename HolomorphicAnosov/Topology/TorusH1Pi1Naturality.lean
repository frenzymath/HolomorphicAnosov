import HolomorphicAnosov.Topology.TorusStandardWinding
import HolomorphicAnosov.Topology.DegreeOneHurewicz
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Integral first homology and the fundamental group of the real torus

Source: Allen Hatcher, Algebraic Topology, Theorem 2A.1 and proof, pp. 166–167,
representative description p. 168, and Proposition 1.12/Example 1.13, p. 34.
DAG node: `topo.torus_h1_pi1_naturality`.

All homology objects and maps are native ordinary singular homology with integer coefficients,
using the existing degree-one Hurewicz definitions. The additive codomain is only type-tagged
when compared to the multiplicatively written fundamental group. No abelianization isomorphism
or basis is assumed: the equivalences and integral coordinate basis are conclusions.
-/

namespace HolomorphicAnosov.Topology

/-- The actual loop-to-singular-homology map of the real torus is an isomorphism, with the
positive coordinate loops giving the integral homology basis. It is natural for every pointed
continuous self-map, whose two integer matrices in these coordinate bases therefore coincide.

Source: Hatcher, Theorem 2A.1, pp. 166–167, representative description p. 168, and
Proposition 1.12/Example 1.13 and induced homomorphisms, p. 34.

Complete natural-language proof relative to the named source prerequisites:

T1. Let T=UnitAddTorus(Fin n), the product of period-one real quotient circles with the specified product topology. It is path-connected: for x,y∈T choose real representatives aⱼ,bⱼ of their finitely many coordinates, and use t↦([ (1−t)aⱼ+t bⱼ ])ⱼ. Each coordinate is continuous by the existing quotient-projection continuity; the product continuity criterion gives a continuous path with the required endpoints. Empty Fin 0 gives the unique constant path. Apply the general topological degree-one Hurewicz theorem at 0 to obtain the loop-to-singular-H₁ homomorphism h_T, its surjectivity, and its commutator kernel.

T2. The winding equivalence w:π₁(T,0)≃Multiplicative(ℤ^(Fin n)) is a group isomorphism and sends the positive j-th standard loop αⱼ to eⱼ. Since its target is commutative, injectivity of w implies γδ=δγ in π₁(T,0). Give that same group law its resulting CommGroup structure. The existing Abelianization.equivOfComm identifies its abelianization quotient with the original group, so compose it with the Hurewicz abelianization isomorphism; the forward map is precisely h_T on loop representatives. Equivalently its kernel is trivial and its surjectivity gives the same bijective homomorphism, with MulEquiv.ofBijective preserving that forward map. Hence the loop-to-H₁ map itself, not just an unspecified abstract isomorphism, is an isomorphism.

T3. Define the coordinate homology generator bⱼ as the singular homology class of the coordinate loop αⱼ(t), with coordinate [t] at j and 0 elsewhere. Hurewicz sends [αⱼ] to bⱼ by its representative formula. The equivalence h_T∘w⁻¹ from ℤ^(Fin n) to H₁ takes eⱼ to bⱼ; every z has the finite expression z=Σⱼ zⱼeⱼ, and the equivalence sends it to Σⱼ zⱼbⱼ. Its injectivity and surjectivity establish that these are a basis, not a basis assumption in the argument. In particular the positive winding convention on αⱼ produces a positive homology generator and no transpose or sign change.

T4. For any continuous f:T→T with f(0)=0 and any loop α at 0, FundamentalGroup.mapOfEq represents f_*[α] by f∘α with endpoints cast to 0. The singular-homology functor acts by postcomposition on the corresponding singular 1-simplex, so f_*h_T([α]) is the homology class of f∘α, exactly h_T(f_*[α]). All π₁ elements have loop representatives, proving the intertwining equality. This uses no linearity or invertibility assumption on f; in particular it is not an application only to the integral toral maps appearing in the winding theorem.

T5. Write f_*[αⱼ] in winding coordinates as Σᵢ aᵢⱼeᵢ. By T3 and T4 its homology image is Σᵢ aᵢⱼbᵢ. Thus both integer matrices have the same j-th column, for every j. The finite-coordinate equality gives equality of matrices. For n=0 the winding theorem makes π₁ the trivial group ℤ^∅, T2 makes H₁ trivial, both coordinate bases are empty, and the two matrices are the unique 0×0 matrix. The constant f and orientation-reversing coordinate maps are included by the same representative argument.

The multiplication on the native fundamental group may use the reverse concatenation
convention; both coordinate winding and the singular-homology target are commutative, so the
source calculations give the displayed homomorphisms without sign reversal. The module
structure and basis coefficients are over the integers throughout. The last equality uses
`LinearMap.toMatrix_apply`: its entry is the ith coordinate of the image of the jth basis
vector, exactly the same column convention as the winding expression. For n=0 the two bases
are empty and both matrices are the unique empty matrix. The assertions include constant
self-maps, orientation-reversing maps and maps which are not invertible. -/
theorem torus_h1_pi1_naturality (n : ℕ) :
    ∃ (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
      (h : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃*
        Multiplicative (IntegralSingularH1 (UnitAddTorus (Fin n))))
      (b : Module.Basis (Fin n) ℤ (IntegralSingularH1 (UnitAddTorus (Fin n)))),
      (∀ a, (h a).toAdd = degreeOneHurewiczFunction (0 : UnitAddTorus (Fin n)) a) ∧
      (∀ z : Fin n → ℤ,
        ∃ p : Path (0 : UnitAddTorus (Fin n)) 0,
          (∀ (t : unitInterval) (j : Fin n),
            p t j = (((t : ℝ) * (z j : ℝ) : ℝ) : UnitAddCircle)) ∧
          w (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
            Multiplicative.ofAdd z) ∧
      (∀ (j : Fin n) (p : Path (0 : UnitAddTorus (Fin n)) 0),
        (∀ (t : unitInterval) (i : Fin n),
          p t i = (((t : ℝ) * (((Pi.single j (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℝ) : ℝ) :
            UnitAddCircle)) → b j = loopSingularClass p) ∧
      (∀ j : Fin n,
        b j = (h (w.symm (Multiplicative.ofAdd (Pi.single j (1 : ℤ))))).toAdd) ∧
      (∀ (f : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n))) (hf : f 0 = 0)
        (a : FundamentalGroup (UnitAddTorus (Fin n)) 0),
        (h (FundamentalGroup.mapOfEq f hf a)).toAdd =
          integralSingularH1Map f (h a).toAdd) ∧
      (∀ (f : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n))) (hf : f 0 = 0),
        LinearMap.toMatrix b b (integralSingularH1Map f) =
          fun i j ↦ (w (FundamentalGroup.mapOfEq f hf
            (w.symm (Multiplicative.ofAdd (Pi.single j (1 : ℤ)))))).toAdd i) := by
  classical
  obtain ⟨w, hwloop, hwstandard, _⟩ := torus_pi1_standard_winding n
  obtain ⟨hsurj, hker, hrep, _, hnat⟩ :=
    degree_one_singular_hurewicz_abelianization (0 : UnitAddTorus (Fin n))
  have : IsMulCommutative (FundamentalGroup (UnitAddTorus (Fin n)) 0) :=
    ⟨⟨fun a b ↦ w.injective (by simp only [map_mul, mul_comm])⟩⟩
  have hinj : Function.Injective (degreeOneHurewicz (0 : UnitAddTorus (Fin n))) :=
    (MonoidHom.ker_eq_bot_iff _).mp (hker.trans (commutator_eq_bot _))
  let h := MulEquiv.ofBijective (degreeOneHurewicz (0 : UnitAddTorus (Fin n)))
    ⟨hinj, hsurj⟩
  let e : (Fin n → ℤ) ≃+ IntegralSingularH1 (UnitAddTorus (Fin n)) :=
    AddEquiv.toMultiplicative.symm (w.symm.trans h)
  let l : (Fin n → ℤ) ≃ₗ[ℤ] IntegralSingularH1 (UnitAddTorus (Fin n)) :=
    e.toIntLinearEquiv
  let b := (Pi.basisFun ℤ (Fin n)).map l
  have hb (j : Fin n) :
      b j = (h (w.symm (Multiplicative.ofAdd (Pi.single j (1 : ℤ))))).toAdd := by
    simp only [b, Module.Basis.map_apply, Pi.basisFun_apply]
    rfl
  have hh (a : FundamentalGroup (UnitAddTorus (Fin n)) 0) :
      (h a).toAdd = degreeOneHurewiczFunction (0 : UnitAddTorus (Fin n)) a := rfl
  have hn (f : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n))) (hf : f 0 = 0)
      (a : FundamentalGroup (UnitAddTorus (Fin n)) 0) :
      (h (FundamentalGroup.mapOfEq f hf a)).toAdd = integralSingularH1Map f (h a).toAdd :=
    hnat 0 f hf a
  refine ⟨w, h, b, hh, hwloop, ?_, hb, hn, ?_⟩
  · intro j p hp
    rw [hb]
    have hw := hwstandard j p hp
    have heq : w.symm (Multiplicative.ofAdd (Pi.single j (1 : ℤ))) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) := by
      apply w.injective
      simpa only [MulEquiv.apply_symm_apply, Path.Homotopic.Quotient.mk''_eq_mk] using hw.symm
    rw [heq, hh]
    exact hrep p
  · intro f hf
    ext i j
    rw [LinearMap.toMatrix_apply, hb, ← hn f hf]
    change (Pi.basisFun ℤ (Fin n)).repr
      (l.symm ((h (FundamentalGroup.mapOfEq f hf
        (w.symm (Multiplicative.ofAdd (Pi.single j (1 : ℤ)))))).toAdd)) i = _
    rw [Pi.basisFun_repr]
    change (w (h.symm (h (FundamentalGroup.mapOfEq f hf
      (w.symm (Multiplicative.ofAdd (Pi.single j (1 : ℤ)))))))).toAdd i = _
    rw [MulEquiv.symm_apply_apply]


end HolomorphicAnosov.Topology

