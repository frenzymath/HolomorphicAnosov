import HolomorphicAnosov.Topology.FranksPiOneSemiconjugacy
import HolomorphicAnosov.Topology.Franks.PointedLiftIntertwining

/-!
# Franks semiconjugacy on the specified original pullback lift

Franks (1970), Proposition (2.1), pp.70–71. This specializes the public pointed
semiconjugacy theorem to the original coordinate pullback and the centered lift
`H0(x)=x.2-u0.2`. The SAME given `F` and fixed `u0` are passed to the pointed-lift
intertwining theorem. The based fundamental-group square and hyperbolicity are
explicit inputs; this component does not construct the induced matrix.
-/

open Set _root_.Topology
namespace HolomorphicAnosov.Topology

/-- The native Franks semiconjugacy and its corrected real lift intertwine the
specified source lift fixing `u0`, with bounded and deck-invariant centered correction.

Proof: The pullback second coordinate is a homeomorphism onto real coordinate
space. It gives simple connectedness; conjugating the coordinate covering gives
the original covering projection and its surjectivity. Center the initial lift
at the SAME `u0`. Quotient subtraction verifies its projected centered torus map.
Apply Franks Proposition (2.1) at the projected fixed point. Its universal lift
clause gives a corrected lift on precisely this carrier, with basepoint zero,
bounded correction and deck invariance. Apply pointed covering uniqueness to
this same corrected lift and given F to obtain real semiconjugacy and iteration.
The projected fixed-point equation follows from F(u0)=u0 and the lift equation.

Source: Franks, Anosov Diffeomorphisms (1970), Proposition (2.1), pp.70–71;
Hatcher, Algebraic Topology, Proposition 1.34, p.62, for the lifted square.
-/
theorem native_pointed_semiconjugacy
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] [CWComplex (univ : Set M)]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (u0 : OriginalTorusPullback q)
    (g : M ≃ₜ M)
    (F : C(OriginalTorusPullback q, OriginalTorusPullback q))
    (hF : ∀ x, (F x).val.1 = g x.val.1) (hF0 : F u0 = u0)
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hA : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1) :
    let h0 : C(M, UnitAddTorus (Fin n)) :=
      ⟨fun x ↦ q x - q u0.val.1, q.continuous.sub continuous_const⟩
    let hh0 : h0 u0.val.1 = 0 := sub_self _
    let hg : g u0.val.1 = u0.val.1 := (hF u0).symm.trans
      (congrArg (fun x : OriginalTorusPullback q ↦ x.val.1) hF0)
    (FundamentalGroup.mapOfEq h0 hh0).comp
        (FundamentalGroup.mapOfEq (⟨g, g.continuous⟩ : C(M, M)) hg) =
      (FundamentalGroup.mapOfEq (franksIntegralToralContinuousMap A)
        (by classical ext i; simp [franksIntegralToralContinuousMap, ContinuousMap.pi])).comp
        (FundamentalGroup.mapOfEq h0 hh0) →
    ∃ k : C(M, UnitAddTorus (Fin n)), k u0.val.1 = 0 ∧ k.Homotopic h0 ∧
      (∀ x, k (g x) = integralToralMap A (k x)) ∧
      ∃ H : C(OriginalTorusPullback q, Fin n → ℝ), H u0 = 0 ∧
        (∀ x, coordinateProjection n (H x) = k x.val.1) ∧
        (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖(x.val.2 - u0.val.2) - H x‖ ≤ B) ∧
        (∀ (d : deck (fun x : OriginalTorusPullback q ↦ x.val.1)) x,
          ((d • x).val.2 - u0.val.2) - H (d • x) = (x.val.2 - u0.val.2) - H x) ∧
        Function.Semiconj H F (FranksMatrix.realAction A) ∧
        ∀ r : ℕ, ∀ x, H (F^[r] x) = (FranksMatrix.realAction A)^[r] (H x) := by
  classical
  dsimp only
  intro hπ
  let h0 : C(M, UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ q x - q u0.val.1, q.continuous.sub continuous_const⟩
  have hh0 : h0 u0.val.1 = 0 := sub_self _
  have hg : g u0.val.1 = u0.val.1 :=
    (hF u0).symm.trans (congrArg (fun x : OriginalTorusPullback q ↦ x.val.1) hF0)
  let Q : OriginalTorusPullback q ≃ₜ (Fin n → ℝ) := {
    toFun := fun x ↦ x.val.2
    invFun := fun v ↦ ⟨(q.symm (originalTorusProjection n v), v), q.apply_symm_apply _⟩
    left_inv := fun x ↦ by
      apply Subtype.ext
      apply Prod.ext
      · exact (congrArg q.symm x.property).symm.trans (q.symm_apply_apply _)
      · rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := continuous_snd.comp continuous_subtype_val
    continuous_invFun := ((q.symm.continuous.comp (originalTorusProjection n).continuous).prodMk
      continuous_id).subtype_mk _ }
  have : SimplyConnectedSpace (OriginalTorusPullback q) :=
    Q.toHomotopyEquiv.simplyConnectedSpace
  let P : C(OriginalTorusPullback q, M) :=
    ⟨fun x ↦ x.val.1, continuous_fst.comp continuous_subtype_val⟩
  have hproj : (P : OriginalTorusPullback q → M) =
      q.symm ∘ coordinateProjection n ∘ Q := by
    funext x
    exact ((congrArg q.symm x.property).symm.trans (q.symm_apply_apply _)).symm
  have hcov : IsCoveringMap P := by
    rw [hproj]
    exact ((coordinateProjection_cover n).isCoveringMap.comp_homeomorph Q).homeomorph_comp q.symm
  have hsurj : Function.Surjective P := by
    rw [hproj]
    exact q.symm.surjective.comp
      ((coordinateProjection_cover n).toIsQuotientMap.surjective.comp Q.surjective)
  let H0 : C(OriginalTorusPullback q, Fin n → ℝ) :=
    ⟨fun x ↦ x.val.2 - u0.val.2, Q.continuous.sub continuous_const⟩
  have hH0zero : H0 u0 = 0 := sub_self _
  have hH0lift : ∀ x, (fun i ↦ (H0 x i : UnitAddCircle)) = h0 (P x) := by
    intro x
    change (fun i ↦ ((x.val.2 i - u0.val.2 i : ℝ) : UnitAddCircle)) =
      q x.val.1 - q u0.val.1
    rw [x.property, u0.property]
    ext i
    exact AddCircle.coe_sub (p := (1 : ℝ)) (x.val.2 i) (u0.val.2 i)
  obtain ⟨k, hk0, hkhom, hkeq, _, _, hlifts⟩ :=
    franks_pi1_semiconjugacy n A hA u0.val.1 g hg h0 hh0 hπ
  obtain ⟨H, hH0, hHproj, hHbound, hHdeck⟩ :=
    hlifts (OriginalTorusPullback q) P hcov hsurj u0 rfl H0 hH0zero hH0lift
  obtain ⟨hsem, hit⟩ :=
    pointed_pullback_lift_intertwining q u0 g A k hkeq F hF hF0 H hH0 hHproj
  exact ⟨k, hk0, hkhom, hkeq, H, hH0, hHproj, hHbound, hHdeck, hsem, hit⟩

end HolomorphicAnosov.Topology
