import HolomorphicAnosov.Topology.ContinuousMapBasedPathSingularSimplex
import HolomorphicAnosov.Topology.PairedBasedTrianglesAbelianizationZero
import HolomorphicAnosov.Topology.PathSingularSimplexInjective
import HolomorphicAnosov.Topology.PathSingularSimplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Convexity
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- A finite signed family of continuous triangles based at all vertices,
with equally parametrized oppositely signed paired edges, makes its positive
distinguished loop trivial in the fundamental-group abelianization. Source:
Hatcher, Algebraic Topology, Theorem 2A.1 proof p.167. Regard each continuous
triangle as a native singular simplex. Its continuous edge maps have both
endpoints at the basepoint, hence are the exact simplices of based paths.
Equality of paired edge maps gives equality of their based paths by
injectivity of the path-to-simplex map. Apply the signed based-triangle
cancellation theorem and identify the distinguished path by the same
injectivity. Neither separation nor path-connectedness of the target is
needed after the vertices have been moved to the basepoint. -/
theorem pairedContinuousTriangles_abelianization_zero
    {X : Type u} [TopologicalSpace X] {x : X} (α : Path x x)
    (m : ℕ) (τ : Fin m → C(StdSimplex ℝ (Fin 3), X))
    (e : Fin m × Fin 3 → C(StdSimplex ℝ (Fin 2), X))
    (hface : ∀ i j t, τ i (t.map j.succAbove) = e (i, j) t)
    (hvertex : ∀ i j, τ i (StdSimplex.single j) = x)
    (ε : Fin m → ℤ) (d : Fin m × Fin 3)
    (pair : Fin m × Fin 3 → Fin m × Fin 3)
    (hpair : Function.Involutive pair) (hd : pair d = d)
    (hfree : ∀ o, o ≠ d → pair o ≠ o)
    (hsign : ∀ o, o ≠ d →
      ε (pair o).1 * (-1 : ℤ) ^ (pair o).2.val = -(ε o.1 * (-1 : ℤ) ^ o.2.val))
    (hedge : ∀ o, e (pair o) = e o)
    (hdpos : ε d.1 * (-1 : ℤ) ^ d.2.val = 1)
    (hdedge : e d = TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋1⦌)
      (pathSingularSimplex α)) :
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk α))) = 0 := by
  have hex (o : Fin m × Fin 3) : ∃ p : Path x x, pathSingularSimplex p =
      (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋1⦌)).symm (e o) := by
    apply continuousMap_basedPathSingularSimplex_exists x (e o)
    · have h := hface o.1 o.2 (StdSimplex.single 0)
      simpa only [StdSimplex.map_single, hvertex] using h.symm
    · have h := hface o.1 o.2 (StdSimplex.single 1)
      simpa only [StdSimplex.map_single, hvertex] using h.symm
  choose p hp using hex
  let σ : Fin m → (TopCat.toSSet.obj (TopCat.of X)) _⦋2⦌ :=
    fun i ↦ (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋2⦌)).symm (τ i)
  have hσface : ∀ i j, (TopCat.toSSet.obj (TopCat.of X)).δ j (σ i) =
      pathSingularSimplex (p (i, j)) := by
    intro i j
    rw [hp]
    apply (TopCat.toSSetObjEquiv (TopCat.of X) (Opposite.op ⦋1⦌)).injective
    apply ContinuousMap.ext
    intro t
    change τ i (t.map j.succAbove) = e (i, j) t
    exact hface i j t
  have hpaths : ∀ o, p (pair o) = p o := by
    intro o
    apply pathSingularSimplex_injective x x
    rw [hp, hp, hedge]
  have hdist : p d = α := by
    apply pathSingularSimplex_injective x x
    rw [hp, hdedge, Equiv.symm_apply_apply]
  have h := pairedBasedTriangles_abelianization_zero m σ ε p hσface d pair
    hpair hd hfree hsign hpaths hdpos
  simpa only [hdist] using h

end HolomorphicAnosov.Topology
