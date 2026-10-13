import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- Two triangles with a common diagonal and equal outer side edges have boundary
 equal to the difference of the other two edges.
Source: Hatcher, Algebraic Topology, Theorem 2A.1, p.166, homotopy square.
Proof: expand both alternating face sums. The two diagonal terms and the two
side-edge terms cancel; the remaining terms are the specified outer edges. -/
theorem simplicial_two_triangle_boundary
    (X : SSet.{u}) (R : ModuleCat.{u} ℤ) (s t : X _⦋2⦌)
    (hside : X.δ 0 s = X.δ 2 t) (hdiag : X.δ 1 s = X.δ 1 t) (r : R) :
    ((X.chainComplex R).d 2 1)
      ((X.ιChainComplex (R := R) s) r - (X.ιChainComplex (R := R) t) r) =
        (X.ιChainComplex (R := R) (X.δ 2 s)) r -
          (X.ιChainComplex (R := R) (X.δ 0 t)) r := by
  have hs := congrArg (fun f ↦ f.hom r) (X.ιChainComplex_d (R := R) s)
  have ht := congrArg (fun f ↦ f.hom r) (X.ιChainComplex_d (R := R) t)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at hs ht
  simp only [ModuleCat.comp_apply, ModuleCat.hom_add, ModuleCat.hom_zsmul,
    LinearMap.add_apply] at hs ht
  simp only [map_sub]
  change ((X.chainComplex R).d 2 1).hom ((X.ιChainComplex (R := R) s).hom r) -
    ((X.chainComplex R).d 2 1).hom ((X.ιChainComplex (R := R) t).hom r) = _
  rw [hs, ht]
  simp [hside, hdiag]
  abel

end HolomorphicAnosov.Topology
