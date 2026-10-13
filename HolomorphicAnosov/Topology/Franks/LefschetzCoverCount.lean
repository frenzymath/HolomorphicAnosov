import HolomorphicAnosov.Topology.Franks.PeriodicItineraryBounds
import HolomorphicAnosov.Topology.Franks.PeriodicDerivative
import HolomorphicAnosov.Topology.Franks.FiniteCoverCount
import HolomorphicAnosov.Topology.Franks.TorusENR
import HolomorphicAnosov.Topology.Franks.CoverWindingMatrix
import HolomorphicAnosov.Topology.CompactENRLefschetzLocalIndexSum
import HolomorphicAnosov.Topology.OriginalTorusLefschetzDeterminant

noncomputable section
namespace HolomorphicAnosov.FranksLefschetzCoverCount
open FixedPointIndexInterface
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- The actual integer endpoint characterization uniquely specifies winding coordinates. -/
theorem normalized_winding_unique {n : ℕ}
    (w v : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hw : ∀ (p : Path (0 : UnitAddTorus (Fin n)) 0) (z : Fin n → ℤ),
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z ↔
        ∃ l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)), ∀ t i, (l t i : UnitAddCircle) = p t i)
    (hv : ∀ (p : Path (0 : UnitAddTorus (Fin n)) 0) (z : Fin n → ℤ),
      v (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z ↔
        ∃ l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)), ∀ t i, (l t i : UnitAddCircle) = p t i) : w = v := by
  apply MulEquiv.ext
  intro γ
  induction γ using Quotient.inductionOn with
  | h p =>
    obtain ⟨z,l,hl⟩ := torus_loop_integer_endpoint_lift n p
    exact ((hw p z).mpr ⟨l,hl⟩).trans ((hv p z).mpr ⟨l,hl⟩).symm

/-- A finite fixed set with one common unit local index has cardinality equal
to the absolute Lefschetz determinant in its original normalized winding coordinates. -/
theorem fixed_count_eq_det {n : ℕ}
    (F : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
    (hfinite : {x | F x = x}.Finite) (ε : ℤˣ)
    (hindex : ∀ x, F x = x → finiteFixedPointLocalIndex (FranksTorusENR.torusENR n) F hfinite x = (ε : ℤ))
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hw : ∀ (p : Path (0 : UnitAddTorus (Fin n)) 0) (z : Fin n → ℤ),
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z ↔
        ∃ l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)), ∀ t i, (l t i : UnitAddCircle) = p t i)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ (δ : Path (F 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map F 0 γ))).toAdd = A.mulVec (w γ).toAdd) :
    (Nat.card {x // F x = x} : ℚ) = |Matrix.det (1 - A.map (Int.castRingHom ℚ))| := by
  classical
  obtain ⟨hH,hvan,w',hw',A',⟨hA',hdet⟩,_⟩ :=
    original_torus_lefschetz_determinant n (Homeomorph.refl _) F
  have hww : w' = w := normalized_winding_unique w' w hw' hw
  subst w'
  obtain ⟨B,hB,hu⟩ := torus_selfmap_winding_matrix n F w
  have hAA : A = A' := (hu A hA).trans (hu A' hA').symm
  subst A'
  have hd := hdet 1 (by omega)
  simp only [Function.iterate_one, pow_one] at hd
  have hi := compact_enr_lefschetz_local_index_sum (UnitAddTorus (Fin n))
    (FranksTorusENR.torusENR n) F n hfinite hH hvan
  have hs : (∑ x ∈ hfinite.toFinset,
      (finiteFixedPointLocalIndex (FranksTorusENR.torusENR n) F hfinite x : ℚ)) =
      (hfinite.toFinset.card : ℚ) * ((ε : ℤ) : ℚ) := by
    calc
      _ = ∑ x ∈ hfinite.toFinset, ((ε : ℤ) : ℚ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hindex x (hfinite.mem_toFinset.mp hx)]
      _ = _ := by simp
  have h := hd.symm.trans (hi.trans hs)
  have hc : (Nat.card {x // F x = x} : ℚ) = hfinite.toFinset.card := by
    exact congrArg (fun z : ℕ ↦ (z : ℚ)) (Set.ncard_eq_toFinset_card _ hfinite)
  rw [hc, h, abs_mul]
  have he : |((ε : ℤ) : ℚ)| = 1 := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> norm_num
  simp [he]

/-- The characteristic torus covering has finite nonempty deck group. -/
theorem finite_scalar_kernel (n k : ℕ) (hk : 0 < k) :
    Finite (nsmulAddMonoidHom k : UnitAddTorus (Fin n) →+ UnitAddTorus (Fin n)).ker := by
  let U := {z : UnitAddCircle // k • z = 0}
  have : Finite U := (AddCircle.finite_torsion (1 : ℝ) hk).to_subtype
  apply Finite.of_injective (fun a ↦ (fun i : Fin n ↦
    (⟨a.val i, congrFun a.property i⟩ : U)))
  intro a b h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

/-- Summing the common-index Lefschetz count over every deck translate and
canceling the finite nonzero cover degree gives the original fixed-point count. -/
theorem fixed_count_from_lifts {n k : ℕ} (hk : 0 < k)
    (f F : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
    (hfinite : {x | f x = x}.Finite) (hcomm : ∀ x, k • F x = f (k • x))
    (hindices : ∀ G : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)),
      (∀ x, k • G x = f (k • x)) → ∀ hG : {x | G x = x}.Finite,
      ∃ ε : ℤˣ, ∀ x, G x = x → finiteFixedPointLocalIndex (FranksTorusENR.torusENR n) G hG x = (ε : ℤ))
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hw : ∀ (p : Path (0 : UnitAddTorus (Fin n)) 0) (z : Fin n → ℤ),
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z ↔
        ∃ l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)), ∀ t i, (l t i : UnitAddCircle) = p t i)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ (δ : Path (f 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map f 0 γ))).toAdd = A.mulVec (w γ).toAdd) :
    (Nat.card {x // f x = x} : ℚ) = |Matrix.det (1 - A.map (Int.castRingHom ℚ))| := by
  classical
  let p : UnitAddTorus (Fin n) →+ UnitAddTorus (Fin n) := nsmulAddMonoidHom k
  let : Finite p.ker := finite_scalar_kernel n k hk
  let : Finite {x // f x = x} := hfinite.to_subtype
  let := Fintype.ofFinite p.ker
  have hfin := FranksCoverCount.deck_fixed_finite p F f
    (Topology.FranksCover.nsmul_surjective n k hk) hcomm
  have hsum := FranksCoverCount.fixed_count_sum p F f
    (Topology.FranksCover.nsmul_surjective n k hk) hcomm
  have hcount (a : p.ker) : (Nat.card {x // (a : UnitAddTorus (Fin n)) + F x = x} : ℚ) =
      |Matrix.det (1 - A.map (Int.castRingHom ℚ))| := by
    let G : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
      ⟨fun x ↦ a.val + F x, continuous_const.add F.continuous⟩
    have hc : ∀ x, k • G x = f (k • x) := by
      intro x
      change k • (a.val + F x) = _
      rw [smul_add, show k • a.val = 0 from a.property, zero_add, hcomm]
    have hG : {x | G x = x}.Finite := by
      change {x | a.val + F x = x}.Finite
      exact @Set.toFinite _ _ (hfin a)
    obtain ⟨ε,hi⟩ := hindices G hc hG
    obtain ⟨B,hB,_⟩ := torus_selfmap_winding_matrix n G w
    have hBA := FranksCoverWinding.cover_matrix_eq hk G f hc w B A hB hA
    subst B
    exact fixed_count_eq_det G hG ε hi w hw A hB
  have hs := congrArg (fun z : ℕ ↦ (z : ℚ)) hsum
  simp only [Nat.cast_sum, Nat.cast_mul] at hs
  rw [Finset.sum_congr rfl (fun a _ ↦ hcount a)] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card] at hs
  apply (mul_left_cancel₀ (show (Fintype.card p.ker : ℚ) ≠ 0 from by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card p.ker ≠ 0)))
  exact hs.symm

open scoped ContDiff in
/-- Original Anosov periodic counts equal the absolute determinant of the actual
return winding matrix. Only the original tangent bundle and its bounds are used. -/
theorem original_periodic_count_matrix {n : ℕ} {M : Type*}
    [TopologicalSpace M] [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    (q : M ≃ₜ UnitAddTorus (Fin n))
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    [Bundle.RiemannianBundle (fun y : M ↦ TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) y)]
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
    (m : ℕ) (hm : 0 < m) (hfinite : {x | (realIterate _ f m) x = x}.Finite)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hw : ∀ (p : Path (0 : UnitAddTorus (Fin n)) 0) (z : Fin n → ℤ),
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z ↔
        ∃ l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)), ∀ t i, (l t i : UnitAddCircle) = p t i)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    let g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
      ⟨fun x ↦ q ((realIterate _ f m) (q.symm x)),
        q.continuous.comp ((realIterate _ f m).continuous.comp q.symm.continuous)⟩
    (∀ (δ : Path (g 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map g 0 γ))).toAdd = A.mulVec (w γ).toAdd) →
    (Nat.card {x // (realIterate _ f m) x = x} : ℚ) = |Matrix.det (1 - A.map (Int.castRingHom ℚ))| := by
  dsimp only
  intro hA
  let g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ q ((realIterate _ f m) (q.symm x)),
      q.continuous.comp ((realIterate _ f m).continuous.comp q.symm.continuous)⟩
  let e : {x // (realIterate _ f m) x = x} ≃ {x // g x = x} := {
    toFun := fun x ↦ ⟨q x.val, by
      change q ((realIterate _ f m) (q.symm (q x.val))) = q x.val
      rw [q.symm_apply_apply, x.property]⟩
    invFun := fun x ↦ ⟨q.symm x.val, by
      have h := congrArg q.symm x.property
      simpa only [g, ContinuousMap.coe_mk, q.symm_apply_apply] using h⟩
    left_inv := by intro x; apply Subtype.ext; exact q.symm_apply_apply x.val
    right_inv := by intro x; apply Subtype.ext; exact q.apply_symm_apply x.val }
  have : Finite {x // (realIterate _ f m) x = x} := hfinite.to_subtype
  have hfinG : Finite {x // g x = x} := Finite.of_equiv _ e
  have hg : {x | g x = x}.Finite := @Set.toFinite _ _ hfinG
  obtain ⟨_,_,F,hF⟩ := Topology.FranksCover.original_cover_lift q (realIterate _ f m).toHomeomorph 2 (by omega)
  have hc : ∀ x, 2 • F x = g (2 • x) := by
    intro x
    exact (q.apply_symm_apply (2 • F x)).symm.trans (congrArg q (hF x))
  have hcount := fixed_count_from_lifts (by omega : 0 < 2) g ⟨F,F.continuous⟩ hg hc
    (fun G hG hfin ↦ FranksPeriodicDerivative.doubled_lift_index_constant q f S hb m hm G
      (by
        intro x
        have h := congrArg q.symm (hG x)
        simpa only [g, ContinuousMap.coe_mk, q.symm_apply_apply] using h)
      (FranksTorusENR.torusENR n) hfin) w hw A hA
  rw [Nat.card_congr e]
  exact hcount

open scoped ContDiff in
/-- The original periodic-point count is the determinant of identity minus the
corresponding power of one original winding matrix. -/
theorem original_periodic_count_powers {n : ℕ} {M : Type*}
    [TopologicalSpace M] [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    (q : M ≃ₜ UnitAddTorus (Fin n))
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    [Bundle.RiemannianBundle (fun y : M ↦ TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) y)]
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hw : ∀ (p : Path (0 : UnitAddTorus (Fin n)) 0) (z : Fin n → ℤ),
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z ↔
        ∃ l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)), ∀ t i, (l t i : UnitAddCircle) = p t i)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    let v : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
      ⟨fun x ↦ q (f (q.symm x)), q.continuous.comp (f.continuous.comp q.symm.continuous)⟩
    (∀ (δ : Path (v 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map v 0 γ))).toAdd = A.mulVec (w γ).toAdd) →
    ∀ m : ℕ, 0 < m → {x | (realIterate _ f m) x = x}.Finite →
      (Nat.card {x // (realIterate _ f m) x = x} : ℚ) = |Matrix.det (1 - (A.map (Int.castRingHom ℚ))^m)| := by
  dsimp only
  intro hA m hm hfinite
  let v : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ q (f (q.symm x)), q.continuous.comp (f.continuous.comp q.symm.continuous)⟩
  let g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ q ((realIterate _ f m) (q.symm x)),
      q.continuous.comp ((realIterate _ f m).continuous.comp q.symm.continuous)⟩
  have hs : Function.Semiconj q f v := by
    intro x
    change q (f x) = q (f (q.symm (q x)))
    rw [q.symm_apply_apply]
  have hg : g = FranksCoverWinding.iterateMap v m := by
    apply ContinuousMap.ext
    intro x
    have h := hs.iterate_right m (q.symm x)
    change q ((f : M → M)^[m] (q.symm x)) = (v : _ → _)^[m] x
    simpa only [q.apply_symm_apply] using h
  have hAm := FranksCoverWinding.matrix_iterates v w A hA m
  have hAg : ∀ (δ : Path (g 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map g 0 γ))).toAdd = (A^m).mulVec (w γ).toAdd := by
    exact hg.symm ▸ hAm
  have h := original_periodic_count_matrix q f S hb m hm hfinite w hw (A^m) hAg
  simpa only [Matrix.map_pow] using h

/-- Convert a rational Lefschetz cardinality to the integer determinant cardinality
    used by displacement-class fixed-point counting. -/
theorem nat_card_eq_natAbs_of_rat_count {n : ℕ} {S : Type*} [Finite S]
    (A : Matrix (Fin n) (Fin n) ℤ)
    (h : (Nat.card S : ℚ) =
      |Matrix.det (1 - (A.map (Int.castRingHom ℚ)))|) :
    Nat.card S = (Matrix.det (1 - A)).natAbs := by
  have hdet : Matrix.det (1 - (A.map (Int.castRingHom ℚ))) =
      ((Matrix.det (1 - A) : ℤ) : ℚ) := by
    have hmatrix : (Int.castRingHom ℚ).mapMatrix (1 - A) =
        1 - A.map (Int.castRingHom ℚ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.map]
      · simp [Matrix.map, hij]
    rw [← hmatrix]
    exact ((Int.castRingHom ℚ).map_det (1 - A)).symm
  have habs : (|((Matrix.det (1 - A) : ℤ) : ℚ)| : ℚ) =
      ((Matrix.det (1 - A)).natAbs : ℚ) := by
    let z : ℤ := Matrix.det (1 - A)
    change |(z : ℚ)| = (z.natAbs : ℚ)
    calc
      |(z : ℚ)| = ((|z| : ℤ) : ℚ) := (Int.cast_abs).symm
      _ = ((z.natAbs : ℤ) : ℚ) := by rw [Int.natCast_natAbs]
      _ = (z.natAbs : ℚ) := by norm_num
  rw [hdet] at h
  rw [habs] at h
  exact_mod_cast h

/-- Scalar extension of the rational determinant gives the complex determinant
norm, with the same absolute value in the reals. -/
theorem determinant_norm_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) :
    ‖Matrix.det (1 - (A.map (Int.castRingHom ℂ))^m)‖ =
      (|Matrix.det (1 - (A.map (Int.castRingHom ℚ))^m)| : ℚ) := by
  let R : Matrix (Fin n) (Fin n) ℚ →+* Matrix (Fin n) (Fin n) ℂ :=
    (Rat.castHom ℂ).mapMatrix
  have hmap : R (1 - (A.map (Int.castRingHom ℚ))^m) =
      1 - (A.map (Int.castRingHom ℂ))^m := by
    rw [map_sub, map_one, map_pow]
    congr 2
  have hdet := (Rat.castHom ℂ).map_det (1 - (A.map (Int.castRingHom ℚ))^m)
  rw [hmap] at hdet
  rw [← hdet]
  exact (Complex.norm_ratCast _).trans (Rat.cast_abs _).symm

open scoped ContDiff in
/-- Original periodic growth forces hyperbolicity of the actual original winding
matrix, using the proved geometric count equality and spectral product criterion. -/
theorem hyperbolic_of_original_periodic_growth {n : ℕ} {M : Type*}
    [TopologicalSpace M] [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    (q : M ≃ₜ UnitAddTorus (Fin n))
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    [Bundle.RiemannianBundle (fun y : M ↦ TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) y)]
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
    (hfinite : ∀ m, 0 < m → {x | (realIterate _ f m) x = x}.Finite)
    (r a b : ℝ) (k : ℕ) (hr : 0 < r) (ha : 0 < a) (hbp : 0 < b) (hk : 0 < k)
    (hgrowth : ∀ᶠ m : ℕ in Filter.atTop,
      a*r^m ≤ (Nat.card {x // (realIterate _ f (k*m)) x = x} : ℝ) ∧
      (Nat.card {x // (realIterate _ f (k*m)) x = x} : ℝ) ≤ b*r^m)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hw : ∀ (p : Path (0 : UnitAddTorus (Fin n)) 0) (z : Fin n → ℤ),
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z ↔
        ∃ l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)), ∀ t i, (l t i : UnitAddCircle) = p t i)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    let v : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
      ⟨fun x ↦ q (f (q.symm x)), q.continuous.comp (f.continuous.comp q.symm.continuous)⟩
    (∀ (δ : Path (v 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map v 0 γ))).toAdd = A.mulVec (w γ).toAdd) →
    ∀ μ : ℂ, Module.End.HasEigenvalue (A.map (Int.castRingHom ℂ)).mulVecLin μ → ‖μ‖ ≠ 1 := by
  dsimp only
  intro hA
  apply matrix_hyperbolic_of_iterated_determinant_bounds _ k r a b hr ha hbp
  filter_upwards [hgrowth, Filter.eventually_gt_atTop 0] with m hm hmpos
  have hcount := original_periodic_count_powers q f S hb w hw A hA (k*m)
    (Nat.mul_pos hk hmpos) (hfinite _ (Nat.mul_pos hk hmpos))
  have heq : ‖Matrix.det (1 - (A.map (Int.castRingHom ℂ))^(k*m))‖ =
      (Nat.card {x // (realIterate _ f (k*m)) x = x} : ℝ) := by
    rw [determinant_norm_cast]
    exact_mod_cast hcount.symm
  rwa [heq]

open scoped ContDiff in
/-- Nonvanishing Lefschetz determinant gives an original fixed point once the
actual winding matrix is hyperbolic. -/
theorem fixed_point_of_hyperbolic_winding {n : ℕ} {M : Type*}
    [TopologicalSpace M] [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    (q : M ≃ₜ UnitAddTorus (Fin n))
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    [Bundle.RiemannianBundle (fun y : M ↦ TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) y)]
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
    (hfinite : {x | f x = x}.Finite)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hw : ∀ (p : Path (0 : UnitAddTorus (Fin n)) 0) (z : Fin n → ℤ),
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z ↔
        ∃ l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)), ∀ t i, (l t i : UnitAddCircle) = p t i)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    let v : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
      ⟨fun x ↦ q (f (q.symm x)), q.continuous.comp (f.continuous.comp q.symm.continuous)⟩
    (∀ (δ : Path (v 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map v 0 γ))).toAdd = A.mulVec (w γ).toAdd) →
    (∀ μ : ℂ, Module.End.HasEigenvalue (A.map (Int.castRingHom ℂ)).mulVecLin μ → ‖μ‖ ≠ 1) →
    ∃ x, f x = x := by
  dsimp only
  intro hA hhyper
  have hc := original_periodic_count_powers q f S hb w hw A hA 1 (by omega) hfinite
  simp only [pow_one] at hc
  change (Nat.card {x : M // f x = x} : ℚ) = _ at hc
  by_contra hn
  have : IsEmpty {x : M // f x = x} := ⟨fun x ↦ hn ⟨x.val,x.property⟩⟩
  have hz : |Matrix.det (1 - A.map (Int.castRingHom ℚ))| = 0 := by
    simpa only [Nat.card_of_isEmpty, Nat.cast_zero] using hc.symm
  have hd : Matrix.det (1 - A.map (Int.castRingHom ℂ)) = 0 := by
    apply norm_eq_zero.mp
    have hh := determinant_norm_cast A 1
    simpa only [pow_one, hz, Rat.cast_zero] using hh
  apply hhyper 1 _ (by simp)
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_mulVecLin,
    Polynomial.IsRoot, Matrix.eval_charpoly]
  simpa only [map_one] using hd

open scoped ContDiff Bundle

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
  [IsContMDiffRiemannianBundle (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
    (EuclideanSpace ℝ (Fin n)) (fun x : M ↦ TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
/-- The supplied smooth inner products, repackaged as the explicit metric record. -/
def suppliedSmoothMetric : Bundle.ContMDiffRiemannianMetric
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ (EuclideanSpace ℝ (Fin n))
    (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) where
  inner := Bundle.RiemannianBundle.g.inner
  symm := Bundle.RiemannianBundle.g.symm
  pos := Bundle.RiemannianBundle.g.pos
  isVonNBounded := Bundle.RiemannianBundle.g.isVonNBounded
  contMDiff := by
    obtain ⟨g,hg,he⟩ := IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (n := ∞)
      (F := EuclideanSpace ℝ (Fin n))
      (E := fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)
    have h : g = Bundle.RiemannianBundle.g.inner := by
      funext x
      ext v w
      exact (he x v w).symm
    simpa only [h] using hg

/-- Repackage the existing native periodic-count theorem using the supplied
Riemannian bundle and its exact Anosov estimates. -/
theorem periodic_growth_of_bundle_anosov {n : ℕ} {M : Type*}
    [MetricSpace M] [ConnectedSpace M] [CompactSpace M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    [IsRiemannianManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M]
    [IsContMDiffRiemannianBundle (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n)) (fun x : M ↦ TangentSpace
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    (_q : M ≃ₜ UnitAddTorus (Fin n))
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
 :
    (∀ j : ℕ, 0 < j → {x | realIterate _ f j x = x}.Finite) ∧
    ∃ r a b : ℝ, ∃ k : ℕ, 0 < r ∧ 0 < a ∧ 0 < b ∧ 0 < k ∧
      ∀ᶠ j : ℕ in Filter.atTop,
        a*r^j ≤ (Nat.card {x // realIterate _ f (k*j) x = x} : ℝ) ∧
        (Nat.card {x // realIterate _ f (k*j) x = x} : ℝ) ≤ b*r^j := by
  obtain ⟨C,lam,hC,hlam,hlam1,hs,hu⟩ := hb
  let metric := suppliedSmoothMetric (n := n) (M := M)
  obtain ⟨hf,r,a,b,k,hr,ha,hbp,hk,hgrowth⟩ :=
    original_anosov_periodic_growth f S.stable S.unstable metric C lam
      inferInstance hC hlam hlam1 S.isCompl S.stable_map S.unstable_map
      (fun x j v hv ↦ hs j x v hv) (fun x j v hv ↦ hu j x v hv)
  have he (j : ℕ) : ((f.toHomeomorph^j : M ≃ₜ M) : M → M) = (realIterate _ f j : M → M) :=
    Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe f.toHomeomorph j
  have hf' (j : ℕ) (hj : 0 < j) : {x | realIterate _ f j x = x}.Finite := by
    have hfin := @Set.toFinite M {x | (f.toHomeomorph^j) x = x} (hf j hj)
    have he' (x : M) : (f.toHomeomorph^j) x = realIterate _ f j x := congrFun (he j) x
    simpa only [he'] using hfin
  refine ⟨hf',r,a,b,k,hr,ha,hbp,hk,?_⟩
  have he' (j : ℕ) (x : M) : (f.toHomeomorph^j) x = realIterate _ f j x := congrFun (he j) x
  simpa only [he'] using hgrowth

/-- Native Anosov bounds supply the periodic growth input for the winding
matrix criterion on the original manifold. -/
theorem hyperbolic_of_bundle_anosov {n : ℕ} {M : Type*}
    [MetricSpace M] [ConnectedSpace M] [CompactSpace M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    [IsRiemannianManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M]
    [IsContMDiffRiemannianBundle (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n)) (fun x : M ↦ TangentSpace
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    (q : M ≃ₜ UnitAddTorus (Fin n))
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hw : ∀ (p : Path (0 : UnitAddTorus (Fin n)) 0) (z : Fin n → ℤ),
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z ↔
        ∃ l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)), ∀ t i, (l t i : UnitAddCircle) = p t i)
    (A : Matrix (Fin n) (Fin n) ℤ) :
    let v : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
      ⟨fun x ↦ q (f (q.symm x)), q.continuous.comp (f.continuous.comp q.symm.continuous)⟩
    (∀ (δ : Path (v 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map v 0 γ))).toAdd = A.mulVec (w γ).toAdd) →
    ∀ μ : ℂ, Module.End.HasEigenvalue (A.map (Int.castRingHom ℂ)).mulVecLin μ → ‖μ‖ ≠ 1 := by
  dsimp only
  intro hA
  obtain ⟨hf,r,a,b,k,hr,ha,hbp,hk,hgrowth⟩ := periodic_growth_of_bundle_anosov q f S hb
  exact hyperbolic_of_original_periodic_growth q f S hb hf r a b k hr ha hbp hk hgrowth w hw A hA

end HolomorphicAnosov.FranksLefschetzCoverCount
