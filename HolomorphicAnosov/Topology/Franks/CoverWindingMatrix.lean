import HolomorphicAnosov.Topology.Franks.CharacteristicTorusCover
import HolomorphicAnosov.Topology.Franks.WindingMatrixHomotopy
import HolomorphicAnosov.Topology.TorusSelfmapWindingMatrix

noncomputable section
namespace HolomorphicAnosov.FranksCoverWinding
open CategoryTheory

/-- The constant connecting path realizes the equality-based transport. -/
theorem transport_cast_refl {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y)
    (γ : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath ((Path.refl y).cast h rfl) γ =
      (eqToIso (congrArg FundamentalGroupoid.mk h)).conj γ := by
  subst y
  simp [FundamentalGroup.fundamentalGroupMulEquivOfPath, Iso.conj_apply]
  change inv (𝟙 (FundamentalGroupoid.mk x)) ≫ γ ≫ 𝟙 _ = γ
  simp

/-- On a pointed torus map, every unbased connecting-path action is the based action. -/
theorem transport_eq_mapOfEq {n : ℕ}
    (f : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n))) (hf : f 0 = 0)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (δ : Path (f 0) (0 : UnitAddTorus (Fin n))) (γ : FundamentalGroup (UnitAddTorus (Fin n)) 0) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath δ (FundamentalGroup.map f 0 γ) =
      FundamentalGroup.mapOfEq f hf γ := by
  rw [winding_basepoint_change_independent n w δ ((Path.refl 0).cast hf rfl)]
  exact transport_cast_refl hf _

/-- Positive scalar covering semiconjugacy identifies the based fundamental-group maps.
The scalar action is the power map; cancellation takes place in the integer winding lattice. -/
theorem based_cover_action {n k : ℕ} (hk : 0 < k)
    (F f : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n))) (hF : F 0 = 0) (hf : f 0 = 0)
    (hcomm : ∀ x, k • F x = f (k • x)) :
    FundamentalGroup.mapOfEq F hF = FundamentalGroup.mapOfEq f hf := by
  let D : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ k • x, continuous_id.const_smul k⟩
  have hD : D 0 = 0 := smul_zero k
  have heq : D.comp F = f.comp D := ContinuousMap.ext hcomm
  have hmaps : (FundamentalGroup.mapOfEq D hD).comp (FundamentalGroup.mapOfEq F hF) =
      (FundamentalGroup.mapOfEq f hf).comp (FundamentalGroup.mapOfEq D hD) := by
    rw [FranksPointedTransport.mapOfEq_comp, FranksPointedTransport.mapOfEq_comp]
    congr 1
  obtain ⟨w, _, _, _⟩ := torus_pi1_standard_winding n
  ext γ
  apply w.injective
  apply Multiplicative.toAdd.injective
  have hh := congrArg (fun α ↦ (w α).toAdd) (DFunLike.congr_fun hmaps γ)
  have hDp (α : FundamentalGroup (UnitAddTorus (Fin n)) 0) :
      FundamentalGroup.mapOfEq D hD α = α ^ k := Topology.FranksCover.nsmul_fundamentalGroup n k α
  simp only [MonoidHom.comp_apply, hDp, map_pow, toAdd_pow] at hh
  funext i
  have hi := congrFun hh i
  simp only [Pi.smul_apply, nsmul_eq_mul] at hi
  exact mul_left_cancel₀ (show (k : ℤ) ≠ 0 by omega) hi

/-- Translating the output of a torus map does not change its winding matrix. -/
theorem output_translation_matrix {n : ℕ}
    (f : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n))) (a : UnitAddTorus (Fin n))
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (A B : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ (δ : Path (f 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map f 0 γ))).toAdd = A.mulVec (w γ).toAdd)
    (hB : let g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
        ⟨fun x ↦ f x - a, f.continuous.sub continuous_const⟩
      ∀ (δ : Path (g 0) (0 : UnitAddTorus (Fin n))) γ,
        (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
          (FundamentalGroup.map g 0 γ))).toAdd = B.mulVec (w γ).toAdd) : A = B := by
  let g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ f x - a, f.continuous.sub continuous_const⟩
  let p := PathConnectedSpace.somePath (0 : UnitAddTorus (Fin n)) a
  let H : f.Homotopy g := {
    toFun := fun tx ↦ f tx.2 - p tx.1
    continuous_toFun := (f.continuous.comp continuous_snd).sub (p.continuous.comp continuous_fst)
    map_zero_left := by intro x; simp
    map_one_left := by intro x; simp [g] }
  exact winding_matrix_homotopy n f g H w A B hA hB

/-- A map lifted through multiplication by a positive integer has exactly the
original unbased winding matrix. Centering both outputs makes the cover square
pointed, and a translation homotopy returns to the original maps. -/
theorem cover_matrix_eq {n k : ℕ} (hk : 0 < k)
    (F f : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
    (hcomm : ∀ x, k • F x = f (k • x))
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (A B : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ (δ : Path (F 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map F 0 γ))).toAdd = A.mulVec (w γ).toAdd)
    (hB : ∀ (δ : Path (f 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map f 0 γ))).toAdd = B.mulVec (w γ).toAdd) : A = B := by
  let F₀ : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ F x - F 0, F.continuous.sub continuous_const⟩
  let f₀ : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ f x - f 0, f.continuous.sub continuous_const⟩
  have hF₀ : F₀ 0 = 0 := sub_self _
  have hf₀ : f₀ 0 = 0 := sub_self _
  have hcomm₀ : ∀ x, k • F₀ x = f₀ (k • x) := by
    intro x
    change k • (F x - F 0) = f (k • x) - f 0
    rw [smul_sub, hcomm, hcomm, smul_zero]
  obtain ⟨A₀,hA₀,_⟩ := torus_selfmap_winding_matrix n F₀ w
  obtain ⟨B₀,hB₀,_⟩ := torus_selfmap_winding_matrix n f₀ w
  have ha : A = A₀ := output_translation_matrix F (F 0) w A A₀ hA hA₀
  have hb : B = B₀ := output_translation_matrix f (f 0) w B B₀ hB hB₀
  rw [ha,hb]
  have hm := based_cover_action hk F₀ f₀ hF₀ hf₀ hcomm₀
  apply Matrix.mulVec_injective
  funext z
  let γ := w.symm (Multiplicative.ofAdd z)
  have h1 := hA₀ ((Path.refl 0).cast hF₀ rfl) γ
  have h2 := hB₀ ((Path.refl 0).cast hf₀ rfl) γ
  rw [transport_eq_mapOfEq F₀ hF₀ w, hm] at h1
  rw [transport_eq_mapOfEq f₀ hf₀ w] at h2
  simpa [γ] using h1.symm.trans h2

/-- The continuous map carrying the literal function iterate. -/
def iterateMap {X : Type*} [TopologicalSpace X] (f : C(X,X)) (m : ℕ) : C(X,X) :=
  ⟨(f : X → X)^[m], f.continuous.iterate m⟩

theorem mapOfEq_congr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X,Y)} {x : X} {y : Y} (hf : f x = y) (hg : g x = y) (hfg : f = g) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  subst g
  rfl

/-- Based winding coordinates of a literal iterate are the matrix powers. -/
theorem based_matrix_iterates {n : ℕ}
    (f : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n))) (hf : f 0 = 0)
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ γ, (w (FundamentalGroup.mapOfEq f hf γ)).toAdd = A.mulVec (w γ).toAdd)
    (m : ℕ) : ∃ hm : iterateMap f m 0 = 0, ∀ γ,
      (w (FundamentalGroup.mapOfEq (iterateMap f m) hm γ)).toAdd = (A^m).mulVec (w γ).toAdd := by
  have hfix (j : ℕ) : iterateMap f j 0 = 0 := Function.IsFixedPt.iterate hf j
  refine ⟨hfix m, ?_⟩
  induction m with
  | zero =>
    intro γ
    rw [pow_zero, Matrix.one_mulVec]
    apply congrArg (fun α ↦ (w α).toAdd)
    rw [FundamentalGroup.mapOfEq_apply]
    change (Path.Homotopic.Quotient.map γ (ContinuousMap.id _)).cast rfl rfl = γ
    rw [Path.Homotopic.Quotient.cast_rfl_rfl]
    induction γ using Quotient.inductionOn with
    | h p => rfl
  | succ m ih =>
    intro γ
    have he : iterateMap f (m+1) = f.comp (iterateMap f m) := by
      apply ContinuousMap.ext
      intro x
      exact Function.iterate_succ_apply' (f : _ → _) m x
    have hmap := FranksPointedTransport.mapOfEq_comp (iterateMap f m) f (hfix m) hf
    have hmap' := hmap.trans (mapOfEq_congr _ (hfix (m+1)) he.symm)
    rw [← hmap', MonoidHom.comp_apply, hA, ih, pow_succ', Matrix.mulVec_mulVec]

/-- Homotopy is preserved by iterating both endpoint maps the same number of times. -/
def iterateHomotopy {X : Type*} [TopologicalSpace X] {f g : C(X,X)}
    (H : f.Homotopy g) (m : ℕ) : (iterateMap f m).Homotopy (iterateMap g m) := by
  induction m with
  | zero => exact ContinuousMap.Homotopy.refl (ContinuousMap.id _)
  | succ m ih =>
    have hf : iterateMap f (m+1) = f.comp (iterateMap f m) := by
      apply ContinuousMap.ext
      intro x
      exact Function.iterate_succ_apply' (f : _ → _) m x
    have hg : iterateMap g (m+1) = g.comp (iterateMap g m) := by
      apply ContinuousMap.ext
      intro x
      exact Function.iterate_succ_apply' (g : _ → _) m x
    rw [hf,hg]
    exact H.comp ih

/-- The unbased winding matrix of every iterate is the corresponding power,
without any fixed-point assumption on the original torus map. -/
theorem matrix_iterates {n : ℕ}
    (f : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ (δ : Path (f 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map f 0 γ))).toAdd = A.mulVec (w γ).toAdd)
    (m : ℕ) : ∀ (δ : Path (iterateMap f m 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map (iterateMap f m) 0 γ))).toAdd = (A^m).mulVec (w γ).toAdd := by
  let g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ f x - f 0, f.continuous.sub continuous_const⟩
  have hg : g 0 = 0 := sub_self _
  obtain ⟨B,hB,_⟩ := torus_selfmap_winding_matrix n g w
  have hAB : A = B := output_translation_matrix f (f 0) w A B hA hB
  subst B
  have hAb : ∀ γ, (w (FundamentalGroup.mapOfEq g hg γ)).toAdd = A.mulVec (w γ).toAdd := by
    intro γ
    have h := hB ((Path.refl 0).cast hg rfl) γ
    rwa [transport_eq_mapOfEq g hg w] at h
  obtain ⟨hgm,hAm⟩ := based_matrix_iterates g hg w A hAb m
  have hAm' : ∀ (δ : Path (iterateMap g m 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map (iterateMap g m) 0 γ))).toAdd = (A^m).mulVec (w γ).toAdd := by
    intro δ γ
    rw [transport_eq_mapOfEq _ hgm w]
    exact hAm γ
  let p := PathConnectedSpace.somePath (0 : UnitAddTorus (Fin n)) (f 0)
  let H : f.Homotopy g := {
    toFun := fun tx ↦ f tx.2 - p tx.1
    continuous_toFun := (f.continuous.comp continuous_snd).sub (p.continuous.comp continuous_fst)
    map_zero_left := by intro x; simp
    map_one_left := by intro x; simp [g] }
  obtain ⟨C,hC,_⟩ := torus_selfmap_winding_matrix n (iterateMap f m) w
  have hCA := winding_matrix_homotopy n (iterateMap f m) (iterateMap g m)
    (iterateHomotopy H m) w C (A^m) hC hAm'
  simpa only [hCA] using hC

end HolomorphicAnosov.FranksCoverWinding
