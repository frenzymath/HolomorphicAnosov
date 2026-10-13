import HolomorphicAnosov.Topology.SingularTrianglePathsHomotopic
import HolomorphicAnosov.Topology.LoopTriangleAbelianizationZero
import HolomorphicAnosov.Topology.PathSingularSimplex

noncomputable section
open CategoryTheory
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The ordered based edge paths of a singular triangle have zero alternating
class in the fundamental group's abelianization. Source: Hatcher, Algebraic
Topology, Theorem 2A.1 proof p.167. The actual triangle supplies the homotopy
between its two-edge route and its direct edge. Passing to the abelianization
gives the alternating boundary relation in the native face order. -/
theorem singularTriangle_abelianization_zero {X : Type u} [TopologicalSpace X]
    {x : X} (s : (TopCat.toSSet.obj (TopCat.of X)) _⦋2⦌)
    (α β γ : Path x x)
    (h0 : (TopCat.toSSet.obj (TopCat.of X)).δ 0 s = pathSingularSimplex β)
    (h1 : (TopCat.toSSet.obj (TopCat.of X)).δ 1 s = pathSingularSimplex γ)
    (h2 : (TopCat.toSSet.obj (TopCat.of X)).δ 2 s = pathSingularSimplex α) :
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk β))) -
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk γ))) +
    Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk α))) = 0 := by
  exact loopTriangle_abelianization_zero α β γ
    (singularTriangle_paths_homotopic s α β γ h0 h1 h2)

end HolomorphicAnosov.Topology
