import HolomorphicAnosov.Topology.WindingEndomorphismMatrix
import HolomorphicAnosov.Topology.TorusStandardWinding
import HolomorphicAnosov.Topology.Franks.PointedMapComposition
import HolomorphicAnosov.Topology.FranksIntegralToralContinuousMap

/-! The original based fundamental-group action in integer torus coordinates.
Source: Hatcher, Algebraic Topology, pp.34–35 (functoriality, inverse maps and torus
winding coordinates); Franks (1970), Proposition (2.1), pp.70–71 (the based square).
The homeomorphism is only topological; its matrix is constructed from its action
on the actual fundamental group. No hyperbolicity is asserted. -/
noncomputable section
namespace HolomorphicAnosov
open _root_.Topology

/-- Every based homeomorphism of a topological torus determines an invertible
integer matrix satisfying the exact based square for the centered coordinate map.

Proof: Center q at b and conjugate g to a pointed torus homeomorphism v. Winding
coordinates turn the induced maps of v and its inverse into lattice endomorphisms.
Their integer matrices multiply to the identity, by functoriality and uniqueness
of coordinate matrices. The normalized winding computation for the integral
toral map of this matrix identifies the two induced endomorphisms. Functoriality
transfers their equality back through the centered coordinate homeomorphism.
All constructions also apply in dimension zero. -/
theorem original_based_integral_matrix
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (b : M)
    (g : M ≃ₜ M) (hg : g b = b) :
    let h0 : C(M, UnitAddTorus (Fin n)) :=
      ⟨fun x ↦ q x - q b, q.continuous.sub continuous_const⟩
    let hh0 : h0 b = 0 := sub_self _
    ∃ A : Matrix.GeneralLinearGroup (Fin n) ℤ,
      (FundamentalGroup.mapOfEq h0 hh0).comp
        (FundamentalGroup.mapOfEq (⟨g, g.continuous⟩ : C(M, M)) hg) =
      (FundamentalGroup.mapOfEq (franksIntegralToralContinuousMap A)
        (by classical ext i; simp [franksIntegralToralContinuousMap, ContinuousMap.pi])).comp
        (FundamentalGroup.mapOfEq h0 hh0) := by
  classical
  dsimp only
  let Q := q.trans (Homeomorph.subRight (q b))
  have hQ : Q b = 0 := sub_self _
  let v := (Q.symm.trans g).trans Q
  have hv : v 0 = 0 := by
    change Q (g (Q.symm 0)) = 0
    rw [← hQ, Q.symm_apply_apply, hg]
  have hvi : v.symm 0 = 0 := by
    exact (congrArg v.symm hv).symm.trans (v.symm_apply_apply 0)
  let V : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) := ⟨v, v.continuous⟩
  let Vi : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) := ⟨v.symm, v.symm.continuous⟩
  let f := FundamentalGroup.mapOfEq V hv
  let fi := FundamentalGroup.mapOfEq Vi hvi
  have hffi : f.comp fi = MonoidHom.id _ := by
    rw [FranksPointedTransport.mapOfEq_comp]
    have hh : V.comp Vi = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact v.apply_symm_apply x
    simp only [hh]
    ext γ
    rw [FundamentalGroup.mapOfEq_apply]
    change (Path.Homotopic.Quotient.map γ (ContinuousMap.id _)).cast rfl rfl = γ
    rw [Path.Homotopic.Quotient.cast_rfl_rfl]
    induction γ using Quotient.inductionOn with
    | h p =>
      change Path.Homotopic.Quotient.mk (p.map continuous_id) =
        Path.Homotopic.Quotient.mk p
      rfl
  have hfif : fi.comp f = MonoidHom.id _ := by
    rw [FranksPointedTransport.mapOfEq_comp]
    have hh : Vi.comp V = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact v.symm_apply_apply x
    simp only [hh]
    ext γ
    rw [FundamentalGroup.mapOfEq_apply]
    change (Path.Homotopic.Quotient.map γ (ContinuousMap.id _)).cast rfl rfl = γ
    rw [Path.Homotopic.Quotient.cast_rfl_rfl]
    induction γ using Quotient.inductionOn with
    | h p =>
      change Path.Homotopic.Quotient.mk (p.map continuous_id) =
        Path.Homotopic.Quotient.mk p
      rfl
  obtain ⟨w, _, _, hwA⟩ := torus_pi1_standard_winding n
  let a := w.toMonoidHom.comp (f.comp w.symm.toMonoidHom)
  let ai := w.toMonoidHom.comp (fi.comp w.symm.toMonoidHom)
  obtain ⟨A, hA, _⟩ := winding_endomorphism_matrix n a
  obtain ⟨B, hB, _⟩ := winding_endomorphism_matrix n ai
  have hAB : A * B = 1 := by
    apply Matrix.mulVec_injective
    funext z
    rw [← Matrix.mulVec_mulVec, ← hB, ← hA, Matrix.one_mulVec]
    change (w (f (w.symm (w (fi (w.symm (Multiplicative.ofAdd z))))))).toAdd = z
    rw [w.symm_apply_apply]
    have hh := DFunLike.congr_fun hffi (w.symm (Multiplicative.ofAdd z))
    change f (fi _) = _ at hh
    rw [hh, MonoidHom.id_apply, w.apply_symm_apply]
    rfl
  have hBA : B * A = 1 := by
    apply Matrix.mulVec_injective
    funext z
    rw [← Matrix.mulVec_mulVec, ← hA, ← hB, Matrix.one_mulVec]
    change (w (fi (w.symm (w (f (w.symm (Multiplicative.ofAdd z))))))).toAdd = z
    rw [w.symm_apply_apply]
    have hh := DFunLike.congr_fun hfif (w.symm (Multiplicative.ofAdd z))
    change fi (f _) = _ at hh
    rw [hh, MonoidHom.id_apply, w.apply_symm_apply]
    rfl
  let AU : Matrix.GeneralLinearGroup (Fin n) ℤ := ⟨A, B, hAB, hBA⟩
  obtain ⟨VA, hVA, hVA0, hwVA⟩ := hwA AU
  have heqVA : VA = franksIntegralToralContinuousMap AU := by
    apply ContinuousMap.ext
    intro x
    rw [hVA x]
    ext i
    simp [franksIntegralToralContinuousMap, integralToralMap, ContinuousMap.pi]
  subst VA
  have hfA : f = FundamentalGroup.mapOfEq (franksIntegralToralContinuousMap AU) hVA0 := by
    ext γ
    apply w.injective
    apply Multiplicative.toAdd.injective
    rw [hwVA]
    simpa [a] using hA (w γ).toAdd
  refine ⟨AU, ?_⟩
  change (FundamentalGroup.mapOfEq (⟨Q, Q.continuous⟩ : C(M, _)) hQ).comp
      (FundamentalGroup.mapOfEq (⟨g, g.continuous⟩ : C(M, M)) hg) =
    (FundamentalGroup.mapOfEq (franksIntegralToralContinuousMap AU) _).comp
      (FundamentalGroup.mapOfEq (⟨Q, Q.continuous⟩ : C(M, _)) hQ)
  rw [← hfA]
  change _ = (FundamentalGroup.mapOfEq V hv).comp _
  rw [FranksPointedTransport.mapOfEq_comp, FranksPointedTransport.mapOfEq_comp]
  congr 1
  apply ContinuousMap.ext
  intro x
  change Q (g x) = Q (g (Q.symm (Q x)))
  rw [Q.symm_apply_apply]

end HolomorphicAnosov
