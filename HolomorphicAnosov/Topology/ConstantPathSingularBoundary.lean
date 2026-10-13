import HolomorphicAnosov.Topology.PathSingularChain

/-!
# A constant path is an integral singular boundary

Source: Hatcher, *Algebraic Topology*, pp.108–109 and the proof of Theorem 2A.1,
p.166. The constant singular triangle has the constant edge as its boundary
in the original unnormalized chain complex.
-/

noncomputable section
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The constant path is the boundary of the constant singular triangle.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.166. The alternating
boundary of the constant triangle is the constant edge minus itself plus itself.
This is the constant edge in the original unnormalized singular chain complex. -/
theorem constantPath_singular_boundary {X : Type u} [TopologicalSpace X] (x : X) :
    ∃ c : (integralSingularChains X).X 2,
      ((integralSingularChains X).d 2 1) c = pathSingularChain (Path.refl x) := by
  let Y := TopCat.toSSet.obj (TopCat.of X)
  let R := ModuleCat.of ℤ (ULift.{u} ℤ)
  let s : Y _⦋2⦌ := (TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.const _ x)
  have hf (i : Fin 3) : Y.δ i s = pathSingularSimplex (Path.refl x) := by
    apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
    apply ContinuousMap.ext
    intro p
    rfl
  refine ⟨(Y.ιChainComplex (R := R) s) (1 : R), ?_⟩
  have hb := congrArg (fun f ↦ f.hom (1 : R)) (Y.ιChainComplex_d (R := R) s)
  change ((Y.chainComplex R).d 2 1).hom ((Y.ιChainComplex (R := R) s).hom 1) =
    _ at hb
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hb
  change ((Y.chainComplex R).d 2 1).hom ((Y.ιChainComplex (R := R) s).hom 1) = _
  rw [hb]
  simp [hf, pathSingularChain, Y, R]

end HolomorphicAnosov.Topology
