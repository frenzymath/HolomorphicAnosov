import HolomorphicAnosov.Topology.PairedTriangleBoundarySumZero
import HolomorphicAnosov.Topology.SingularTriangleAbelianizationZero
import HolomorphicAnosov.Topology.PathSingularSimplex

noncomputable section
open CategoryTheory
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- A positive distinguished edge in a finite signed family of based singular
triangles has zero abelianization class when all other edges cancel in pairs.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167. Each original
singular triangle gives its based alternating boundary relation. Evaluate the
paired signed sum in the additive fundamental-group abelianization; paired
paths have equal classes and opposite coefficients, so only the distinguished
edge survives. This uses the actual triangle maps and actual based paths. -/
theorem pairedBasedTriangles_abelianization_zero {X : Type u} [TopologicalSpace X]
    {x : X} (m : ℕ)
    (σ : Fin m → (TopCat.toSSet.obj (TopCat.of X)) _⦋2⦌)
    (ε : Fin m → ℤ) (p : Fin m × Fin 3 → Path x x)
    (hface : ∀ i j, (TopCat.toSSet.obj (TopCat.of X)).δ j (σ i) =
      pathSingularSimplex (p (i, j)))
    (d : Fin m × Fin 3) (pair : Fin m × Fin 3 → Fin m × Fin 3)
    (hpair : Function.Involutive pair) (hd : pair d = d)
    (hfree : ∀ o, o ≠ d → pair o ≠ o)
    (hsign : ∀ o, o ≠ d →
      ε (pair o).1 * (-1 : ℤ) ^ (pair o).2.val = -(ε o.1 * (-1 : ℤ) ^ o.2.val))
    (hpath : ∀ o, p (pair o) = p o)
    (hdpos : ε d.1 * (-1 : ℤ) ^ d.2.val = 1) :
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (p d)))) = 0 := by
  apply pairedTriangle_boundary_sum_zero m ε
    (fun o ↦ Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (p o))))) d pair hpair hd hfree hsign
    (fun o ↦ congrArg (fun α : Path x x ↦ Additive.ofMul (Abelianization.of
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk α)))) (hpath o)) hdpos
  intro i
  exact singularTriangle_abelianization_zero (σ i) (p (i, 2)) (p (i, 0)) (p (i, 1))
    (hface i 0) (hface i 1) (hface i 2)

end HolomorphicAnosov.Topology
