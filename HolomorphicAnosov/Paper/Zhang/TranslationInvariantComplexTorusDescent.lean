import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.TorusModel
import Mathlib.Topology.Covering.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic.Module

/-! Fixed complex coordinates for a translation-invariant complex structure and descent of a
linearized system to a hyperbolic complex torus. (Zhang, Theorem 1.2, p. 13; Demailly, I
§3.B–3.C, pp. 22–24) -/

open scoped ContDiff

universe u v w

namespace HolomorphicAnosov

noncomputable section

namespace TranslationInvariantDescent
open scoped Manifold
variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold (complexModel d) ∞ M] in
/-- The real derivative of a holomorphic map agrees with its complex derivative under tangent
realification. (Demailly, I §3.C, p. 23) -/
theorem holomorphic_mfderiv_realification {g : M → M} {x : M}
    (hg : MDifferentiableAt (complexModel d) (complexModel d) g x)
    (v : TangentSpace (complexModel d) x) :
    mfderiv (realModel d) (realModel d) g x (complexTangentToReal d x v) =
      complexTangentToReal d (g x) (mfderiv (complexModel d) (complexModel d) g x v) := by
  have hc := hg.differentiableWithinAt_writtenInExtChartAt
  have hd : DifferentiableAt ℂ
      (writtenInExtChartAt (complexModel d) (complexModel d) x g)
      ((extChartAt (complexModel d) x) x) := by
    simpa only [complexModel, modelWithCornersSelf_coe, Set.range_id,
      differentiableWithinAt_univ] using hc
  have hr : MDifferentiableAt (realModel d) (realModel d) g x := by
    apply (mdifferentiableAt_iff g x).mpr
    exact ⟨hg.continuousAt, (hd.restrictScalars ℝ).differentiableWithinAt⟩
  rw [hr.mfderiv, hg.mfderiv]
  simp only [realModel, complexModel, modelWithCornersSelf_coe, Set.range_id,
    fderivWithin_univ]
  change (fderiv ℝ (writtenInExtChartAt (complexModel d) (complexModel d) x g)
      ((extChartAt (complexModel d) x) x)) v =
    (fderiv ℂ (writtenInExtChartAt (complexModel d) (complexModel d) x g)
      ((extChartAt (complexModel d) x) x)) v
  exact congrArg (fun L ↦ L v) (hd.fderiv_restrictScalars (𝕜 := ℝ))

omit [IsManifold (complexModel d) ∞ M] in
/-- For a transported translation `τ`, the real derivatives satisfy `DH(τ x) ∘ Dτ(x) = DH(x)`.
(Zhang, p. 13) -/
theorem transported_translation_derivative
    (H : Diffeomorph (realModel d) (modelWithCornersSelf ℝ V) M V ∞)
    (a : V) (τ : Biholomorph d d M M)
    (hτ : ∀ x, τ x = H.symm (H x + a)) (x : M) :
    (mfderiv (realModel d) (modelWithCornersSelf ℝ V) H (τ x)).comp
      (mfderiv (realModel d) (realModel d) τ x) =
    mfderiv (realModel d) (modelWithCornersSelf ℝ V) H x := by
  have he : (H ∘ τ : M → V) = fun x ↦ H x + a := by
    funext x
    simp only [Function.comp_apply, hτ, H.apply_symm_apply]
  rw [← mfderiv_comp x ((H.contMDiff (τ x)).mdifferentiableAt (by simp))
    ((τ.toReal.contMDiff x).mdifferentiableAt (by simp)), he]
  change (mfderiv (realModel d) (modelWithCornersSelf ℝ V)
    ((H : M → V) + fun _ : M ↦ a) x : TangentSpace (realModel d) x →L[ℝ] V) =
    (mfderiv (realModel d) (modelWithCornersSelf ℝ V) H x :
      TangentSpace (realModel d) x →L[ℝ] V)
  erw [mfderiv_add ((H.contMDiff x).mdifferentiableAt (by simp)) mdifferentiableAt_const,
    mfderiv_const, add_zero]

omit [IsManifold (complexModel d) ∞ M] in
/-- If all transported translations are biholomorphic, fixed real-linear coordinates make every
derivative of `H` intertwine tangent multiplication by `Complex.I`. (Zhang, p. 13) -/
theorem fixed_linear_coordinates_intertwine
    (H : Diffeomorph (realModel d) (modelWithCornersSelf ℝ V) M V ∞)
    (htranslation : ∀ a : V, ∃ τ : Biholomorph d d M M,
      ∀ x : M, τ x = H.symm (H x + a)) :
    ∃ E : V ≃L[ℝ] ComplexModel d,
      ∀ (x : M) (v : TangentSpace (complexModel d) x),
        E (mfderiv (realModel d) (modelWithCornersSelf ℝ V) H x
          (complexTangentToReal d x (Complex.I • v))) =
        Complex.I • E (mfderiv (realModel d) (modelWithCornersSelf ℝ V) H x
          (complexTangentToReal d x v)) := by
  let x0 := H.symm 0
  let T : TangentSpace (realModel d) x0 ≃L[ℝ] V :=
    (H.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv (by simp)
  let C := tangentSpaceCastModel (complexModel d) x0
  let Cr : TangentSpace (complexModel d) x0 ≃L[ℝ] ComplexModel d :=
    { toLinearEquiv := C.toLinearEquiv.restrictScalars ℝ
      continuous_toFun := C.continuous
      continuous_invFun := C.symm.continuous }
  let E := T.symm.trans ((complexTangentToReal d x0).symm.trans Cr)
  have hE (v : TangentSpace (complexModel d) x0) :
      E (mfderiv (realModel d) (modelWithCornersSelf ℝ V) H x0
        (complexTangentToReal d x0 v)) = C v := by
    change Cr ((complexTangentToReal d x0).symm (T.symm (T (complexTangentToReal d x0 v)))) = _
    rw [T.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  refine ⟨E, ?_⟩
  intro x
  obtain ⟨τ, hτ⟩ := htranslation (H x)
  have ht : τ x0 = x := by
    simp only [hτ, x0, H.apply_symm_apply, zero_add, H.symm_apply_apply]
  subst x
  intro v
  let L := (τ.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
    (x := x0) (by simp)
  obtain ⟨u, hu⟩ := L.surjective (show TangentSpace (complexModel d) (τ x0) from v)
  have hchain := transported_translation_derivative H (H (τ x0)) τ hτ x0
  have hv (w : TangentSpace (complexModel d) x0) :
      mfderiv (realModel d) (modelWithCornersSelf ℝ V) H (τ x0)
        (complexTangentToReal d (τ x0) (L w)) =
      mfderiv (realModel d) (modelWithCornersSelf ℝ V) H x0
        (complexTangentToReal d x0 w) := by
    have hh := congrArg (fun D ↦ D (complexTangentToReal d x0 w)) hchain
    change mfderiv (realModel d) (modelWithCornersSelf ℝ V) H (τ x0)
      (mfderiv (realModel d) (realModel d) τ x0 (complexTangentToReal d x0 w)) = _ at hh
    rw [holomorphic_mfderiv_realification
      ((τ.contMDiff x0).mdifferentiableAt (by simp)) w] at hh
    exact hh
  have hvi := hv (Complex.I • u)
  have hvu := hv u
  have hc : C (Complex.I • u) = Complex.I • C u := C.map_smul _ _
  have heq : E (mfderiv (realModel d) (modelWithCornersSelf ℝ V) H (τ x0)
      (complexTangentToReal d (τ x0) (Complex.I • L u))) =
      Complex.I • E (mfderiv (realModel d) (modelWithCornersSelf ℝ V) H (τ x0)
        (complexTangentToReal d (τ x0) (L u))) := by
    rw [← L.map_smul, hvi, hvu, hE, hE, hc]
  convert heq using 1 <;> (simp [hu, complexTangentToReal] <;> rfl)


/-- A real-linear map commuting with multiplication by `Complex.I` commutes with all complex
scalars. (Demailly, I §3.C, p. 23) -/
theorem complex_smul_of_I {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (L : E →L[ℝ] F)
    (hI : ∀ x, L (Complex.I • x) = Complex.I • L x) (c : ℂ) (x : E) :
    L (c • x) = c • L x := by
  have hreal (r : ℝ) (v : E) : L ((r : ℂ) • v) = (r : ℂ) • L v := by
    simpa only [← Complex.coe_algebraMap, IsScalarTower.algebraMap_smul] using L.map_smul r v
  calc
    L (c • x) = L ((c.re : ℂ) • x + (c.im : ℂ) • (Complex.I • x)) := by
      rw [← mul_smul, ← add_smul, c.re_add_im]
    _ = (c.re : ℂ) • L x + (c.im : ℂ) • (Complex.I • L x) := by
      rw [map_add, hreal, hreal, hI]
    _ = c • L x := by rw [← mul_smul, ← add_smul, c.re_add_im]

omit [IsManifold (complexModel d) ∞ M] in
/-- A real differentiable map whose tangent derivatives commute with multiplication by `Complex.I`
is complex differentiable. (Demailly, I §3.C, p. 23) -/
theorem mdifferentiable_complex_of_real
    {N : Type*} [TopologicalSpace N] [ChartedSpace (ComplexModel d) N]
    {g : M → N} (hg : MDifferentiable (realModel d) (realModel d) g)
    (hI : ∀ (x : M) (v : TangentSpace (complexModel d) x),
      (tangentSpaceCastModel (realModel d) (g x))
        (mfderiv (realModel d) (realModel d) g x
          (complexTangentToReal d x (Complex.I • v))) =
      Complex.I • (tangentSpaceCastModel (realModel d) (g x))
        (mfderiv (realModel d) (realModel d) g x (complexTangentToReal d x v))) :
    MDifferentiable (complexModel d) (complexModel d) g := by
  intro x
  have hr : DifferentiableAt ℝ
      (writtenInExtChartAt (complexModel d) (complexModel d) x g)
      ((extChartAt (complexModel d) x) x) := by
    convert (hg x).differentiableWithinAt_writtenInExtChartAt using 1
    simp only [realModel, complexModel, modelWithCornersSelf_coe, Set.range_id,
      differentiableWithinAt_univ]
    rfl
  let D := fderiv ℝ (writtenInExtChartAt (complexModel d) (complexModel d) x g)
    ((extChartAt (complexModel d) x) x)
  have hi (v : ComplexModel d) : D (Complex.I • v) = Complex.I • D v := by
    have h := hI x ((tangentSpaceCastModel (complexModel d) x).symm v)
    rw [(hg x).mfderiv] at h
    convert h using 1 <;>
      simp [D, realModel, complexModel, complexTangentToReal,
        modelWithCornersSelf_coe, ContinuousLinearMap.comp_apply] <;> rfl
  let DC : ComplexModel d →L[ℂ] ComplexModel d :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := complex_smul_of_I D hi
      cont := D.continuous }
  have hDC : DC.restrictScalars ℝ = D := by ext v; rfl
  have hc := hasFDerivAt_of_restrictScalars ℝ hr.hasFDerivAt hDC
  apply (mdifferentiableAt_iff g x).mpr
  exact ⟨(hg x).continuousAt, by
    simpa only [complexModel, modelWithCornersSelf_coe, Set.range_id] using
      hc.differentiableAt.differentiableWithinAt⟩


/-- A complex differentiable map between complex manifolds is complex smooth. (Demailly, I §3.B–3.C,
pp. 22–23) -/
theorem contMDiff_complex_of_mdifferentiable
    {N : Type*} [TopologicalSpace N] [ChartedSpace (ComplexModel d) N]
    [IsManifold (complexModel d) ∞ N] {g : M → N}
    (hg : MDifferentiable (complexModel d) (complexModel d) g) :
    ContMDiff (complexModel d) (complexModel d) ∞ g := by
  obtain ⟨hc, hd⟩ := mdifferentiable_iff.mp hg
  refine contMDiff_iff.mpr ⟨hc, ?_⟩
  intro x y
  apply (complex_contDiffOn_iff_differentiableOn ?_).mpr (hd x y)
  convert (chartAt (ComplexModel d) x).isOpen_inter_preimage_symm
      ((chartAt (ComplexModel d) y).open_source.preimage hc) using 1
  simp only [complexModel, extChartAt,
    OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl]
  rfl

omit [IsManifold (complexModel d) ∞ M] in
/-- The inverse derivative of a real diffeomorphism commutes with multiplication by `Complex.I`
whenever its forward derivative does. (Demailly, I §3.C, p. 23) -/
theorem inverse_derivative_intertwines
    {N : Type*} [TopologicalSpace N] [ChartedSpace (ComplexModel d) N]
    (K : Diffeomorph (realModel d) (realModel d) M N ∞)
    (hI : ∀ (x : M) (v : TangentSpace (complexModel d) x),
      (tangentSpaceCastModel (realModel d) (K x))
        (mfderiv (realModel d) (realModel d) K x
          (complexTangentToReal d x (Complex.I • v))) =
      Complex.I • (tangentSpaceCastModel (realModel d) (K x))
        (mfderiv (realModel d) (realModel d) K x (complexTangentToReal d x v)))
    (y : N) (v : TangentSpace (complexModel d) y) :
    (tangentSpaceCastModel (realModel d) (K.symm y))
      (mfderiv (realModel d) (realModel d) K.symm y
        (complexTangentToReal d y (Complex.I • v))) =
    Complex.I • (tangentSpaceCastModel (realModel d) (K.symm y))
      (mfderiv (realModel d) (realModel d) K.symm y (complexTangentToReal d y v)) := by
  let D := (K.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
    (x := K.symm y) (by simp)
  let Cx := tangentSpaceCastModel (realModel d) (K.symm y)
  let Cy := tangentSpaceCastModel (realModel d) (K (K.symm y))
  let L := Cx.symm.trans (D.trans Cy)
  have hi (w : ComplexModel d) : L (Complex.I • w) = Complex.I • L w := by
    convert hI (K.symm y) ((tangentSpaceCastModel (complexModel d) (K.symm y)).symm w)
      using 1 <;> simp [L, D, Cx, Cy, complexTangentToReal] <;> rfl
  let Li : ComplexModel d →L[ℝ] ComplexModel d := Cx.toContinuousLinearMap.comp
    ((mfderiv (realModel d) (realModel d) K.symm y).comp
      (tangentSpaceCastModel (realModel d) y).symm.toContinuousLinearMap)
  have hder := (K.toOpenPartialHomeomorph_mdifferentiable (by simp)).comp_symm_deriv
    (x := y) (by simp)
  have hh (w : ComplexModel d) : L (Li w) = w := by
    have h := congrArg (fun A ↦ A ((tangentSpaceCastModel (realModel d) y).symm w)) hder
    convert h using 1 <;> rfl
  have his (w : ComplexModel d) : Li (Complex.I • w) = Complex.I • Li w := by
    apply L.injective
    rw [hh, hi, hh]
  have hi' := his ((tangentSpaceCastModel (complexModel d) y) v)
  convert hi' using 1 <;>
    simp [Li, Cx, complexTangentToReal] <;> rfl


/-- A real diffeomorphism whose transported translations are biholomorphic becomes a biholomorphism
after composition with fixed real-linear coordinates. (Zhang, p. 13; Demailly, I §3.C, p. 23) -/
theorem exists_fixed_coordinate_biholomorph
    (H : Diffeomorph (realModel d) (modelWithCornersSelf ℝ V) M V ∞)
    (htranslation : ∀ a : V, ∃ τ : Biholomorph d d M M,
      ∀ x : M, τ x = H.symm (H x + a)) :
    ∃ (E : V ≃L[ℝ] ComplexModel d) (K : Biholomorph d d M (ComplexModel d)),
      ∀ x : M, K x = E (H x) := by
  obtain ⟨E, hE⟩ := fixed_linear_coordinates_intertwine H htranslation
  let K := H.trans E.toDiffeomorph
  have hK (x : M) (v : TangentSpace (complexModel d) x) :
      (tangentSpaceCastModel (realModel d) (K x))
        (mfderiv (realModel d) (realModel d) K x
          (complexTangentToReal d x (Complex.I • v))) =
      Complex.I • (tangentSpaceCastModel (realModel d) (K x))
        (mfderiv (realModel d) (realModel d) K x (complexTangentToReal d x v)) := by
    have hc := mfderiv_comp x
      ((E.toDiffeomorph.contMDiff (H x)).mdifferentiableAt (by simp))
      ((H.contMDiff x).mdifferentiableAt (by simp))
    have hDE : mfderiv (modelWithCornersSelf ℝ V) (realModel d) E (H x) =
        E.toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv]
      exact E.toContinuousLinearMap.fderiv
    change (tangentSpaceCastModel (realModel d) (E (H x)))
      (mfderiv (realModel d) (realModel d) (E ∘ H) x
        (complexTangentToReal d x (Complex.I • v))) =
      Complex.I • (tangentSpaceCastModel (realModel d) (E (H x)))
        (mfderiv (realModel d) (realModel d) (E ∘ H) x
          (complexTangentToReal d x v))
    change mfderiv (realModel d) (realModel d) (E ∘ H) x =
      (mfderiv (modelWithCornersSelf ℝ V) (realModel d) E (H x)).comp
        (mfderiv (realModel d) (modelWithCornersSelf ℝ V) H x) at hc
    rw [hc]
    erw [hDE]
    convert hE x v using 1 <;> rfl
  have hforward := mdifferentiable_complex_of_real
    (K.contMDiff.mdifferentiable (by simp)) hK
  have hbackward := mdifferentiable_complex_of_real
    (K.symm.contMDiff.mdifferentiable (by simp)) (inverse_derivative_intertwines K hK)
  let KC : Biholomorph d d M (ComplexModel d) :=
    { toEquiv := K.toEquiv
      contMDiff_toFun := contMDiff_complex_of_mdifferentiable hforward
      contMDiff_invFun := contMDiff_complex_of_mdifferentiable hbackward }
  exact ⟨E, KC, fun _ ↦ rfl⟩


omit [IsManifold (complexModel d) ∞ M] in
/-- The real-linear model of a biholomorphic map is complex linear in fixed coordinates making the
linearization biholomorphic. (Zhang, p. 13) -/
theorem conjugate_linear_complex [FiniteDimensional ℝ V]
    (H : Diffeomorph (realModel d) (modelWithCornersSelf ℝ V) M V ∞)
    (E : V ≃L[ℝ] ComplexModel d) (K : Biholomorph d d M (ComplexModel d))
    (hK : ∀ x : M, K x = E (H x)) (F : Biholomorph d d M M)
    (A : V ≃ₗ[ℝ] V) (hlinear : ∀ x, H (F x) = A (H x)) :
    ∃ B : ComplexModel d ≃L[ℂ] ComplexModel d,
      ∀ v : ComplexModel d, B v = E (A (E.symm v)) := by
  let B : ComplexModel d ≃L[ℝ] ComplexModel d :=
    E.symm.trans (A.toContinuousLinearEquiv.trans E)
  let G := K.symm.trans (F.trans K)
  have hG : (G : ComplexModel d → ComplexModel d) = B := by
    funext v
    change K (F (K.symm v)) = E (A (E.symm v))
    rw [hK, hlinear]
    congr 2
    apply E.injective
    rw [E.apply_symm_apply, ← hK, K.apply_symm_apply]
  have hdiff : DifferentiableAt ℂ (B : ComplexModel d → ComplexModel d) 0 := by
    have h := (G.contMDiff (0 : ComplexModel d)).mdifferentiableAt (by simp)
    rw [hG] at h
    exact h.differentiableAt
  have hD : (fderiv ℂ B 0).restrictScalars ℝ = B.toContinuousLinearMap := by
    rw [← hdiff.fderiv_restrictScalars (𝕜 := ℝ)]
    exact B.toContinuousLinearMap.fderiv
  have hs (c : ℂ) (v : ComplexModel d) : B (c • v) = c • B v := by
    have h := (fderiv ℂ B 0).map_smul c v
    have he (v : ComplexModel d) : (fderiv ℂ B 0) v = B v :=
      congrArg (fun L ↦ L v) hD
    simpa only [he] using h
  let BC : ComplexModel d ≃L[ℂ] ComplexModel d :=
    { toEquiv := B.toEquiv
      map_add' := B.map_add
      map_smul' := hs
      continuous_toFun := B.continuous
      continuous_invFun := B.symm.continuous }
  exact ⟨BC, fun _ ↦ rfl⟩


/-- Fixed real-linear coordinates carry a full discrete invariant lattice to a full complex lattice
preserved by the conjugated complex-linear map. (Zhang, p. 13) -/
theorem coordinate_lattice
    (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (hfull : Submodule.span ℝ (Γ : Set V) = ⊤)
    (E : V ≃L[ℝ] ComplexModel d) (A : V ≃ₗ[ℝ] V)
    (hΓ : Γ.toAddSubgroup.map A.toAddEquiv.toAddMonoidHom = Γ.toAddSubgroup)
    (B : ComplexModel d ≃L[ℂ] ComplexModel d)
    (hB : ∀ v : ComplexModel d, B v = E (A (E.symm v))) :
    ∃ (L : FullComplexLattice d) (BL : LatticeLinearEquiv L),
      (∀ v : ComplexModel d, v ∈ L.lattice ↔ E.symm v ∈ Γ) ∧
      (∀ v : ComplexModel d, BL.linear v = B v) := by
  let : IsZLattice ℝ Γ := ⟨hfull⟩
  let Λ := ZLattice.comap ℝ Γ E.symm.toLinearMap
  let L : FullComplexLattice d :=
    { lattice := Λ
      discrete := inferInstance
      full := inferInstance }
  have hm : L.lattice.toAddSubgroup.map B.toLinearEquiv.toAddEquiv.toAddMonoidHom =
      L.lattice.toAddSubgroup := by
    ext v
    change (∃ z, z ∈ Λ ∧ B z = v) ↔ v ∈ Λ
    constructor
    · rintro ⟨z, hz, rfl⟩
      change E.symm (B z) ∈ Γ
      rw [hB, E.symm_apply_apply]
      have h : A (E.symm z) ∈ Γ.toAddSubgroup.map A.toAddEquiv.toAddMonoidHom :=
        ⟨E.symm z, hz, rfl⟩
      rw [hΓ] at h
      exact h
    · intro hv
      have h : E.symm v ∈ Γ.toAddSubgroup.map A.toAddEquiv.toAddMonoidHom := by
        rw [hΓ]
        exact hv
      obtain ⟨z, hz, he⟩ := h
      refine ⟨E z, ?_, ?_⟩
      · change E.symm (E z) ∈ Γ
        rw [E.symm_apply_apply]
        exact hz
      · rw [hB, E.symm_apply_apply]
        rw [show A z = E.symm v from he, E.apply_symm_apply]
  exact ⟨L, ⟨B.toLinearEquiv, hm⟩, fun _ ↦ Iff.rfl, fun _ ↦ rfl⟩


/-- The canonical projection onto a complex torus is holomorphic in its quotient atlas. (Zhang, p.
13) -/
theorem quotient_projection_contMDiff (L : FullComplexLattice d) :
    ContMDiff (complexModel d) (complexModel d) ∞
      (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L) := by
  let := complexTorus_isManifold L
  let q := (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L)
  intro z
  let e := chartAt (ComplexModel d) (q z)
  have he : e ∈ atlas (ComplexModel d) (ComplexTorus L) := chart_mem_atlas _ _
  have hsymm : (e.symm : ComplexModel d → ComplexTorus L) = q := by
    change ∃ x : ComplexTorus L,
      ((torus_quotient_covering L).isLocalHomeomorph.localInverseAt
        ((torus_quotient_covering L).surjective.hasRightInverse.choose x)).trans
        (OpenPartialHomeomorph.refl (ComplexModel d)) = e at he
    obtain ⟨x, he⟩ := he
    rw [← he]
    simp [q]
  have hx : q z ∈ e.source := mem_chart_source _ _
  have ha : e (q z) ∈ e.target := e.map_source hx
  have hq : q (e (q z)) = q z := by
    calc
      q (e (q z)) = e.symm (e (q z)) := (congrFun hsymm (e (q z))).symm
      _ = q z := e.left_inv hx
  have hl : e (q z) - z ∈ L.lattice := QuotientAddGroup.eq_iff_sub_mem.mp hq
  let ell := e (q z) - z
  have ht : ∀ w : ComplexModel d, q (w + ell) = q w := by
    intro w
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    rw [add_sub_cancel_left]
    exact hl
  have hd := (contMDiffOn_chart_symm (I := complexModel d) (n := ∞)
      (x := q z)).contMDiffAt (e.open_target.mem_nhds ha)
  have hadd : ContMDiffAt (complexModel d) (complexModel d) ∞
      (fun w : ComplexModel d ↦ w + ell) z :=
    (contDiff_id.add contDiff_const).contMDiff.contMDiffAt
  have hd' : ContMDiffAt (complexModel d) (complexModel d) ∞ e.symm (z + ell) := by
    convert hd using 1
    simp [ell, sub_eq_add_neg, add_comm]
  have h := hd'.comp z hadd
  have heq : (e.symm ∘ fun w : ComplexModel d ↦ w + ell) = q := by
    funext w
    simp only [Function.comp_apply, hsymm, ht]
  rwa [heq] at h


omit [IsManifold (complexModel d) ∞ M] in
/-- A biholomorphism to complex Euclidean space descends through a surjective locally biholomorphic
projection to a biholomorphism onto the complex torus when their fibres agree. (Zhang, p. 13) -/
theorem quotient_biholomorphic_descent
    {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (L : FullComplexLattice d) (p : M → X) (hsurj : Function.Surjective p)
    (hhol : ∀ x : M, ∃ e : OpenPartialHomeomorph M X,
      x ∈ e.source ∧ Set.EqOn e p e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target)
    (K : Biholomorph d d M (ComplexModel d))
    (hfibre : ∀ x y : M, p x = p y ↔
      (QuotientAddGroup.mk (K x) : ComplexTorus L) = QuotientAddGroup.mk (K y)) :
    ∃ h : Biholomorph d d X (ComplexTorus L),
      ∀ x : M, h (p x) = QuotientAddGroup.mk (K x) := by
  let := complexTorus_isManifold L
  let q := (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L)
  let s := Function.surjInv hsurj
  have hs (x : X) : p (s x) = x := Function.surjInv_eq hsurj x
  let h : X → ComplexTorus L := fun x ↦ q (K (s x))
  have hh (x : M) : h (p x) = q (K x) := by
    exact (hfibre (s (p x)) x).mp (hs (p x))
  have hinj : Function.Injective h := by
    intro x y hxy
    have h := (hfibre (s x) (s y)).mpr hxy
    simpa only [hs] using h
  have hsur : Function.Surjective h := by
    intro z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact ⟨p (K.symm v), by rw [hh, K.apply_symm_apply]⟩
  let eH := Equiv.ofBijective h ⟨hinj, hsur⟩
  have hpi (v : ComplexModel d) : eH.symm (q v) = p (K.symm v) := by
    apply eH.injective
    change h (eH.symm (q v)) = h (p (K.symm v))
    rw [show h (eH.symm (q v)) = q v from eH.apply_symm_apply _, hh, K.apply_symm_apply]
  have hp : ContMDiff (complexModel d) (complexModel d) ∞ p := by
    intro x
    obtain ⟨e, hx, he, hd, _⟩ := hhol x
    exact (hd.contMDiffAt (e.open_source.mem_nhds hx)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (e.open_source.mem_nhds hx) (fun y hy ↦ (he hy).symm))
  have hforward : ContMDiff (complexModel d) (complexModel d) ∞ h := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨e, hx, he, _, hdi⟩ := hhol x
    have hpx : p x ∈ e.target := he hx ▸ e.map_source hx
    have hloc := (quotient_projection_contMDiff L).contMDiffAt.comp
      (p x) ((K.contMDiff (e.symm (p x))).comp (p x)
        (hdi.contMDiffAt (e.open_target.mem_nhds hpx)))
    apply hloc.congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hpx] with y hy
    change h y = q (K (e.symm y))
    rw [← hh]
    congr 1
    rw [← he (e.symm.map_source hy), e.right_inv hy]
  have hbackward : ContMDiff (complexModel d) (complexModel d) ∞ eH.symm := by
    intro z
    let e := chartAt (ComplexModel d) z
    have he : e ∈ atlas (ComplexModel d) (ComplexTorus L) := chart_mem_atlas _ _
    have hsymm : (e.symm : ComplexModel d → ComplexTorus L) = q := by
      change ∃ x : ComplexTorus L,
        ((torus_quotient_covering L).isLocalHomeomorph.localInverseAt
          ((torus_quotient_covering L).surjective.hasRightInverse.choose x)).trans
          (OpenPartialHomeomorph.refl (ComplexModel d)) = e at he
      obtain ⟨x, he⟩ := he
      rw [← he]
      simp [q]
    have hz : z ∈ e.source := mem_chart_source _ _
    have hloc := (hp (K.symm (e z))).comp z
      ((K.symm.contMDiff (e z)).comp z
        ((contMDiffOn_chart (I := complexModel d) (n := ∞) (x := z)).contMDiffAt
          (e.open_source.mem_nhds hz)))
    apply hloc.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hz] with y hy
    change eH.symm y = p (K.symm (e y))
    rw [← hpi, ← hsymm, e.left_inv hy]
  exact ⟨{ toEquiv := eH
           contMDiff_toFun := hforward
           contMDiff_invFun := hbackward }, hh⟩


/-- Every eigenvalue of a complex-linear conjugate of a real-linear map is an eigenvalue of its
complexification. (Zhang, p. 13) -/
theorem hasEigenvalue_baseChange_of_conjugate
    (E : V ≃L[ℝ] ComplexModel d) (A : V ≃ₗ[ℝ] V)
    (B : ComplexModel d ≃L[ℂ] ComplexModel d)
    (hB : ∀ z : ComplexModel d, B z = E (A (E.symm z)))
    (μ : ℂ) (hμ : Module.End.HasEigenvalue B.toLinearEquiv.toLinearMap μ) :
    Module.End.HasEigenvalue (A.toLinearMap.baseChange ℂ) μ := by
  open TensorProduct in
  obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
  have hzB : B z = μ • z := hz.apply_eq_smul
  let v := E.symm z
  let jv := E.symm (Complex.I • z)
  have hAz : A v = E.symm (μ • z) := by
    apply E.injective
    rw [E.apply_symm_apply, ← hB, hzB]
  have hAjz : A jv = E.symm (μ • (Complex.I • z)) := by
    apply E.injective
    rw [E.apply_symm_apply, ← hB, B.map_smul, hzB, smul_comm]
  have hA : A v = μ.re • v + μ.im • jv := by
    rw [hAz]
    have hc : μ • z = (μ.re : ℂ) • z + (μ.im : ℂ) • (Complex.I • z) := by
      rw [← mul_smul, ← add_smul, μ.re_add_im]
    rw [hc, E.symm.map_add]
    simp [v, jv, ← Complex.coe_algebraMap]
  have hAj : A jv = μ.re • jv - μ.im • v := by
    rw [hAjz]
    have hc : μ • (Complex.I • z) =
        (μ.re : ℂ) • (Complex.I • z) - (μ.im : ℂ) • z := by
      rw [← mul_smul, ← mul_smul, ← sub_smul]
      congr 1
      calc
        μ * Complex.I = ((μ.re : ℂ) + (μ.im : ℂ) * Complex.I) * Complex.I := by rw [μ.re_add_im]
        _ = (μ.re : ℂ) * Complex.I - (μ.im : ℂ) := by
          rw [add_mul, mul_assoc, Complex.I_mul_I, mul_neg_one]
          rfl
    rw [hc, E.symm.map_sub]
    simp [v, jv, ← Complex.coe_algebraMap]
  let w : ℂ ⊗[ℝ] V := (1 : ℂ) ⊗ₜ[ℝ] v - Complex.I ⊗ₜ[ℝ] jv
  have hw : w ≠ 0 := by
    intro hw
    let R : (ℂ ⊗[ℝ] V) →ₗ[ℝ] V :=
      (TensorProduct.lid ℝ V).toLinearMap.comp
        (TensorProduct.map Complex.reLm (LinearMap.id : V →ₗ[ℝ] V))
    have h := congrArg R hw
    have hv : v = 0 := by simpa [R, w] using h
    apply hz.2
    have h := congrArg E hv
    simpa [v] using h
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := w)
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, hw⟩
  change (A.toLinearMap.baseChange ℂ) ((1 : ℂ) ⊗ₜ[ℝ] v - Complex.I ⊗ₜ[ℝ] jv) =
    μ • ((1 : ℂ) ⊗ₜ[ℝ] v - Complex.I ⊗ₜ[ℝ] jv)
  simp only [map_sub, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hA, hAj, TensorProduct.tmul_add,
    TensorProduct.tmul_sub, ← TensorProduct.smul_tmul, Complex.real_smul,
    TensorProduct.smul_tmul', smul_sub]
  have ht (c : ℂ) (u : V) : c ⊗ₜ[ℝ] u = c • ((1 : ℂ) ⊗ₜ[ℝ] u) :=
    TensorProduct.tmul_eq_smul_one_tmul (R := ℝ) c u
  rw [ht (↑μ.re * 1) v, ht (↑μ.im * 1) jv,
    ht (↑μ.re * Complex.I) jv, ht (↑μ.im * Complex.I) v,
    ht (μ • 1) v, ht (μ • Complex.I) jv]
  simp only [smul_eq_mul, mul_one]
  match_scalars <;> apply Complex.ext <;> simp

end TranslationInvariantDescent

/-- A smooth linearization with biholomorphic transported translations descends through its lattice
fibres to a hyperbolic complex torus model. (Zhang, Theorem 1.2, p. 13; Demailly, I §3.C, pp.
23–24) -/
theorem translation_invariant_complex_torus_descent
    (d : ℕ) {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    {M : Type v} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] [SimplyConnectedSpace M]
    {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (_hdim : Module.finrank ℝ V = 2 * d)
    (p : M → X) (_hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (hhol : ∀ x : M, ∃ e : OpenPartialHomeomorph M X,
      x ∈ e.source ∧ Set.EqOn e p e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target)
    (f : Biholomorph d d X X) (F : Biholomorph d d M M)
    (hcover : ∀ x, p (F x) = f (p x))
    (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (hfull : Submodule.span ℝ (Γ : Set V) = ⊤)
    (A : V ≃ₗ[ℝ] V)
    (hΓ : Γ.toAddSubgroup.map A.toAddEquiv.toAddMonoidHom = Γ.toAddSubgroup)
    (hhyper : ∀ μ : ℂ, Module.End.HasEigenvalue (A.toLinearMap.baseChange ℂ) μ →
      ‖μ‖ ≠ 1)
    (H : Diffeomorph (realModel d) (modelWithCornersSelf ℝ V) M V ∞)
    (hlinear : ∀ x, H (F x) = A (H x))
    (hfibre : ∀ x y, p x = p y ↔ H y - H x ∈ Γ)
    (htranslation : ∀ a : V, ∃ τ : Biholomorph d d M M,
      ∀ x : M, τ x = H.symm (H x + a)) :
    ∃ (L : FullComplexLattice d) (B : LatticeLinearEquiv L)
      (h : Biholomorph d d X (ComplexTorus L)),
      IsManifold (complexModel d) ∞ (ComplexTorus L) ∧
      ComplexLinearHyperbolic B.linear.toLinearMap ∧
      Function.Semiconj (fun x ↦ h x) (fun x ↦ f x)
        (fun z ↦ quotientLinearEquiv B z) := by
  classical
  obtain ⟨E, K, hK⟩ := TranslationInvariantDescent.exists_fixed_coordinate_biholomorph
    H htranslation
  obtain ⟨BC, hBC⟩ := TranslationInvariantDescent.conjugate_linear_complex H E K hK F A hlinear
  obtain ⟨L, B, hL, hB⟩ := TranslationInvariantDescent.coordinate_lattice Γ hfull E A hΓ BC hBC
  have hquot (x y : M) : p x = p y ↔
      (QuotientAddGroup.mk (K x) : ComplexTorus L) = QuotientAddGroup.mk (K y) := by
    constructor
    · intro hxy
      apply Eq.symm
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      change K y - K x ∈ L.lattice
      rw [hL, E.symm.map_sub, hK, hK, E.symm_apply_apply, E.symm_apply_apply]
      exact (hfibre x y).mp hxy
    · intro hxy
      apply (hfibre x y).mpr
      have hm := QuotientAddGroup.eq_iff_sub_mem.mp hxy.symm
      change K y - K x ∈ L.lattice at hm
      rw [hL, E.symm.map_sub, hK, hK, E.symm_apply_apply, E.symm_apply_apply] at hm
      exact hm
  obtain ⟨h, hh⟩ := TranslationInvariantDescent.quotient_biholomorphic_descent
    L p hsurj hhol K hquot
  refine ⟨L, B, h, complexTorus_isManifold L, ?_, ?_⟩
  · intro μ hμ
    apply hhyper μ
    apply TranslationInvariantDescent.hasEigenvalue_baseChange_of_conjugate E A BC hBC μ
    have he : B.linear.toLinearMap = BC.toLinearEquiv.toLinearMap := by
      apply LinearMap.ext
      intro v
      exact hB v
    rwa [← he]
  · intro y
    obtain ⟨x, rfl⟩ := hsurj y
    change h (f (p x)) = quotientLinearEquiv B (h (p x))
    rw [← hcover, hh, hh]
    change (QuotientAddGroup.mk (K (F x)) : ComplexTorus L) =
      QuotientAddGroup.mk (B.linear (K x))
    rw [hB, hBC, hK, hK, hlinear, E.symm_apply_apply]


end
end HolomorphicAnosov
