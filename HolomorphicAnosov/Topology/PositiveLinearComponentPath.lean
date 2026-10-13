import HolomorphicAnosov.Topology.PositiveMatrixPath
import HolomorphicAnosov.Topology.PositiveLinearComponentPathFinZero
import HolomorphicAnosov.Topology.PositiveLinearComponentPathFinOne
import Mathlib.Analysis.Normed.Lp.Matrix

/-! # Positive determinant component of the real general linear group

Source: Hatcher, Vector Bundles and K-Theory, §1.2, pp.23–24; the elementary
matrix generator proof is implemented using Mathlib's special-linear induction.
The general matrix path is provided by PositiveMatrixPath.
-/

noncomputable section
namespace HolomorphicAnosov

/-- A positive determinant real linear equivalence has a continuous injective
operator path to the identity.

In dimensions zero and one use the existing constant and positive-scalar
paths. Otherwise choose the Euclidean coordinate matrix M of L. Its determinant
equals det L. Factor M=R*A, where R has det M in one diagonal position and
ones elsewhere, and A has determinant one. Positive diagonal interpolation
contracts R. Mathlib's special-linear induction writes A in transvections and
two-coordinate diagonal factors; each such diagonal is six transvections,
and shrinking their coefficients gives paths of determinant one. Multiply the
factor paths pointwise. Finally transport the resulting matrix path through
Matrix.toEuclideanLin and the finite-dimensional continuous-linear-map map.
Coordinate evaluation proves continuity, nonzero determinant proves a trivial
kernel, and the two endpoints transport to L and id.
Source: Hatcher VBKT §1.2 pp.23–24; Mathlib SpecialLinearGroup.lean:708–783.
-/
theorem exists_positive_linear_equiv_injective_path (n : ℕ)
    (L : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hdet : 0 < LinearMap.det L.toLinearMap) :
    ∃ D : unitInterval → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      Continuous D ∧ (∀ t, Function.Injective (D t)) ∧
      D 0 = L.toContinuousLinearEquiv.toContinuousLinearMap ∧
      D 1 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  by_cases hn0 : n = 0
  · subst n
    exact exists_positive_linear_equiv_injective_path_fin_zero L
  by_cases hn1 : n = 1
  · subst n
    exact exists_positive_linear_equiv_injective_path_fin_one L hdet
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.toEuclideanLin.symm L.toLinearMap
  have hM : 0 < M.det := by
    rw [← LinearMap.det_toLpLin 2]
    change 0 < LinearMap.det (Matrix.toEuclideanLin M)
    simpa [M] using hdet
  obtain ⟨D,hD,hinj,h0,h1⟩ := PositiveMatrixPath.positive M hM
  let C : unitInterval → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun t ↦ (Matrix.toEuclideanLin (D t)).toContinuousLinearMap
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · rw [continuous_clm_apply]
    intro x
    change Continuous (fun t ↦ WithLp.toLp 2 ((D t).mulVec x.ofLp))
    fun_prop
  · intro t
    apply LinearMap.ker_eq_bot.mp
    by_contra hker
    have hz := LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker
    have hne : (Matrix.toEuclideanLin (D t)).det ≠ 0 := by
      simpa only [Matrix.toEuclideanLin, LinearMap.det_toLpLin] using hinj t
    exact hne hz
  · apply ContinuousLinearMap.ext
    intro x
    change Matrix.toEuclideanLin (D 0) x = L x
    rw [h0]
    simp [M]
  · apply ContinuousLinearMap.ext
    intro x
    change Matrix.toEuclideanLin (D 1) x = x
    rw [h1]
    simp [Matrix.toEuclideanLin]

end HolomorphicAnosov
