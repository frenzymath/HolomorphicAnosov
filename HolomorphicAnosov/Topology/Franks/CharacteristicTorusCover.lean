import HolomorphicAnosov.Topology.Franks.CoverPullbackAtlas
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.Topology.TorusCoordinateCover
import HolomorphicAnosov.Topology.RealVectorBundleOrientationMonodromy
import HolomorphicAnosov.Topology.TorusStandardWinding
import HolomorphicAnosov.Topology.Franks.PointedMapComposition
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Instances.AddCircle.Real

namespace HolomorphicAnosov.Topology.FranksCover

/-- The characteristic multiplication cover of the coordinate torus.
Source: Hatcher, covering classification, pp.67–70. Its composite with the real
coordinate cover is the coordinate cover after dilation by `k`. Dilation is a
homeomorphism for positive `k`; canceling the first local homeomorphism gives
local invertibility on the torus. Compactness upgrades this to a covering map. -/
theorem nsmul_cover (n k : ℕ) (hk : 0 < k) :
    IsCoveringMap (fun x : UnitAddTorus (Fin n) ↦ k • x) := by
  let P := coordinateProjection n
  have hP := (coordinateProjection_cover n).isCoveringMap.isLocalHomeomorph
  let D : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) := Homeomorph.smul (Units.mk0 (k : ℝ) (by positivity))
  have hD : (D : (Fin n → ℝ) → (Fin n → ℝ)) = fun v ↦ k • v := by
    funext v
    ext i
    simp [D, nsmul_eq_mul]
  have hcomp : IsLocalHomeomorph ((fun x : UnitAddTorus (Fin n) ↦ k • x) ∘ P) := by
    convert hP.comp D.isLocalHomeomorph using 1
    funext v
    change k • P v = P (D v)
    rw [hD, map_nsmul]
  apply isLocalHomeomorph_iff_isCoveringMap.mp
  apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
  have h := (hcomp.isLocalHomeomorphOn (s := Set.univ)).of_comp_right hP.isLocalHomeomorphOn
  simpa [P, Set.image_univ, (coordinateProjection_cover n).surjective.range_eq] using h

/-- The multiplication cover induces the power map on the actual based fundamental group.
Normalized straight integral loops generate every winding class. Multiplication by `k`
sends their pointwise quotient formula to the straight loop with winding `k z`;
normalization and injectivity of winding therefore identify the induced map. -/
theorem nsmul_fundamentalGroup (n k : ℕ) :
    let P : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
      ⟨fun x ↦ k • x, continuous_id.const_smul k⟩
    ∀ γ : FundamentalGroup (UnitAddTorus (Fin n)) 0,
      FundamentalGroup.mapOfEq P (show P 0 = 0 from smul_zero k) γ = γ ^ k := by
  dsimp only
  intro γ
  obtain ⟨w, hnorm, _⟩ := torus_pi1_standard_winding n
  obtain ⟨p, hp, hwp⟩ := hnorm (w γ).toAdd
  have hγ : FundamentalGroup.fromPath ⟦p⟧ = γ := w.injective hwp
  obtain ⟨r, hr, hwr⟩ := hnorm (k • (w γ).toAdd)
  let P : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ k • x, continuous_id.const_smul k⟩
  have hpath : (p.map P.continuous).cast (smul_zero k).symm (smul_zero k).symm = r := by
    ext t i
    change k • p t i = r t i
    rw [hp, hr]
    simp only [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [← AddCircle.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  apply w.injective
  rw [← hγ, FundamentalGroup.mapOfEq_apply]
  change w (FundamentalGroup.fromPath (.mk
    ((p.map P.continuous).cast (smul_zero k).symm (smul_zero k).symm))) = w (_ ^ k)
  rw [hpath]
  rw [map_pow]
  exact hwr.trans (congrArg (fun a ↦ a ^ k) hwp).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The usual covering lifting criterion with both endpoint casts made explicit. -/
theorem lift_of_pointed_range {A B Z : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]
    [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    (p : C(Z, B)) (hp : IsCoveringMap p) (f : C(A, B))
    (a : A) (c : Z) (b : B) (hf : f a = b) (hc : p c = b)
    (hrange : (FundamentalGroup.mapOfEq f hf).range ≤
      (FundamentalGroup.mapOfEq p hc).range) :
    ∃! F : C(A, Z), F a = c ∧ p ∘ F = f := by
  apply hp.existsUnique_continuousMap_lifts_of_range_le (hc.trans hf.symm)
  rintro _ ⟨γ, rfl⟩
  obtain ⟨δ, hδ⟩ := hrange ⟨γ, rfl⟩
  refine ⟨δ, ?_⟩
  have h := congrArg (fun z : FundamentalGroup B b ↦
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.cast z hf hf)) hδ
  simp only [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
    Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl] at h ⊢
  exact h

/-- Every based continuous torus self-map lifts through its characteristic multiplication
cover. Its induced homomorphism commutes with taking powers, so it preserves the
multiplication-cover subgroup. Apply the pointed covering lifting criterion. -/
theorem based_lift (n k : ℕ) (hk : 0 < k)
    (f : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n))) (hf : f 0 = 0) :
    ∃ F : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)),
      F 0 = 0 ∧ ∀ x, k • F x = f (k • x) := by
  let P : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ k • x, continuous_id.const_smul k⟩
  let : LocallyPathConnectedSpace (UnitAddTorus (Fin n)) :=
    (coordinateProjection_cover n).isOpenQuotientMap.isQuotientMap.locallyPathConnectedSpace
  have hP : P 0 = 0 := smul_zero k
  have hF : (f.comp P) 0 = 0 := (congrArg f hP).trans hf
  have hrange : (FundamentalGroup.mapOfEq (f.comp P) hF).range ≤
      (FundamentalGroup.mapOfEq P hP).range := by
    rintro _ ⟨γ, rfl⟩
    refine ⟨FundamentalGroup.mapOfEq f hf γ, ?_⟩
    rw [← FranksPointedTransport.mapOfEq_comp P f hP hf]
    change FundamentalGroup.mapOfEq P hP _ =
      FundamentalGroup.mapOfEq f hf (FundamentalGroup.mapOfEq P hP γ)
    rw [nsmul_fundamentalGroup, nsmul_fundamentalGroup, map_pow]
  obtain ⟨F, ⟨hF0, hcomm⟩, _⟩ := lift_of_pointed_range P (nsmul_cover n k hk)
    (f.comp P) 0 0 0 hF hP hrange
  exact ⟨F, hF0, fun x ↦ congrFun hcomm x⟩

/-- Lift a based torus homeomorphism and its inverse through the characteristic cover.
The two composites are lifts of the same projection, agree at zero, and hence are
identities by uniqueness of covering lifts on the connected torus. -/
theorem based_homeomorph_lift (n k : ℕ) (hk : 0 < k)
    (f : UnitAddTorus (Fin n) ≃ₜ UnitAddTorus (Fin n)) (hf : f 0 = 0) :
    ∃ F : UnitAddTorus (Fin n) ≃ₜ UnitAddTorus (Fin n),
      F 0 = 0 ∧ ∀ x, k • F x = f (k • x) := by
  obtain ⟨F, hF0, hF⟩ := based_lift n k hk ⟨f, f.continuous⟩ hf
  have hfi : f.symm 0 = 0 := by simpa using (congrArg f.symm hf).symm
  obtain ⟨G, hG0, hG⟩ := based_lift n k hk ⟨f.symm, f.symm.continuous⟩ hfi
  have hGF : ∀ x, G (F x) = x := by
    apply congrFun ((nsmul_cover n k hk).eq_of_comp_eq
      (G.continuous.comp F.continuous) continuous_id ?_ 0 ?_)
    · funext x
      change k • G (F x) = k • x
      rw [hG, hF]
      exact f.symm_apply_apply _
    · change G (F 0) = 0
      rw [hF0, hG0]
  have hFG : ∀ x, F (G x) = x := by
    apply congrFun ((nsmul_cover n k hk).eq_of_comp_eq
      (F.continuous.comp G.continuous) continuous_id ?_ 0 ?_)
    · funext x
      change k • F (G x) = k • x
      rw [hF, hG]
      exact f.apply_symm_apply _
    · change F (G 0) = 0
      rw [hG0, hF0]
  exact ⟨⟨⟨F, G, hGF, hFG⟩, F.continuous, G.continuous⟩, hF0, hF⟩

/-- Positive multiplication is onto: divide any real representative by the multiplier. -/
theorem nsmul_surjective (n k : ℕ) (hk : 0 < k) :
    Function.Surjective (fun x : UnitAddTorus (Fin n) ↦ k • x) := by
  intro x
  obtain ⟨v, hv⟩ := (coordinateProjection_cover n).surjective x
  refine ⟨coordinateProjection n ((k : ℝ)⁻¹ • v), ?_⟩
  change k • coordinateProjection n ((k : ℝ)⁻¹ • v) = x
  rw [← map_nsmul]
  convert hv using 2
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
  field_simp

/-- Every torus homeomorphism lifts through its characteristic multiplication cover.
Translate the image of zero to zero, lift the resulting based homeomorphism, then
translate upstairs by any preimage of the original image of zero. -/
theorem homeomorph_lift (n k : ℕ) (hk : 0 < k)
    (f : UnitAddTorus (Fin n) ≃ₜ UnitAddTorus (Fin n)) :
    ∃ F : UnitAddTorus (Fin n) ≃ₜ UnitAddTorus (Fin n),
      ∀ x, k • F x = f (k • x) := by
  let g := f.trans (Homeomorph.subRight (f 0))
  have hg : g 0 = 0 := sub_self _
  obtain ⟨G, _, hG⟩ := based_homeomorph_lift n k hk g hg
  obtain ⟨a, ha⟩ := nsmul_surjective n k hk (f 0)
  change k • a = f 0 at ha
  refine ⟨G.trans (Homeomorph.addRight a), ?_⟩
  intro x
  change k • (G x + a) = f (k • x)
  rw [smul_add, hG, ha]
  exact sub_add_cancel _ _

/-- The multiplication cover of an original topological torus carries the lifted dynamics. -/
theorem original_cover_lift {n : ℕ} {M : Type*} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (f : M ≃ₜ M) (k : ℕ) (hk : 0 < k) :
    let p : UnitAddTorus (Fin n) → M := fun x ↦ q.symm (k • x)
    IsCoveringMap p ∧ Function.Surjective p ∧
    ∃ F : UnitAddTorus (Fin n) ≃ₜ UnitAddTorus (Fin n), ∀ x, p (F x) = f (p x) := by
  dsimp only
  obtain ⟨F, hF⟩ := homeomorph_lift n k hk ((q.symm.trans f).trans q)
  refine ⟨(nsmul_cover n k hk).homeomorph_comp q.symm,
    q.symm.surjective.comp (nsmul_surjective n k hk), F, ?_⟩
  intro x
  rw [hF]
  exact q.symm_apply_apply _

open scoped ContDiff Manifold in
/-- The characteristic cover is smooth over the original real atlas, and its lifted
homeomorphism is an actual diffeomorphism. The coordinate homeomorphism `q` is used
only for the topology of the cover. Smoothness follows from the sheet formulas for
both the lift and its inverse. -/
theorem original_smooth_cover_lift {n : ℕ} {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (k : ℕ) (hk : 0 < k) :
    let p : UnitAddTorus (Fin n) → M := fun x ↦ q.symm (k • x)
    ∃ A : ChartedSpace E (UnitAddTorus (Fin n)),
      letI := A
      IsManifold 𝓘(ℝ, E) ∞ (UnitAddTorus (Fin n)) ∧
      ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (UnitAddTorus (Fin n))
        (UnitAddTorus (Fin n)) ∞, ∀ x, p (F x) = f (p x) := by
  let p : UnitAddTorus (Fin n) → M := fun x ↦ q.symm (k • x)
  obtain ⟨hp, _, F, hF⟩ := original_cover_lift q f.toHomeomorph k hk
  change ∀ x, p (F x) = f (p x) at hF
  let A := AbstractCoverPullback.charts (E := E) p hp.isLocalHomeomorph
  let : ChartedSpace E (UnitAddTorus (Fin n)) := A
  have hman := AbstractCoverPullback.isManifold (𝕜 := ℝ) (E := E) p hp.isLocalHomeomorph
  have hFs := AbstractCoverPullback.liftSmooth (𝕜 := ℝ) (E := E) p hp.isLocalHomeomorph
    f f.contMDiff F F.continuous hF
  have hFi : ∀ x, p (F.symm x) = f.symm (p x) := by
    intro x
    have h : p x = f (p (F.symm x)) := by
      simpa only [F.apply_symm_apply] using hF (F.symm x)
    rw [h, f.symm_apply_apply]
  have hFis := AbstractCoverPullback.liftSmooth (𝕜 := ℝ) (E := E) p hp.isLocalHomeomorph
    f.symm f.symm.contMDiff F.symm F.symm.continuous hFi
  let D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (UnitAddTorus (Fin n))
      (UnitAddTorus (Fin n)) ∞ :=
    { toEquiv := F.toEquiv
      contMDiff_toFun := hFs
      contMDiff_invFun := hFis }
  exact ⟨A, hman, D, hF⟩

/-- The doubled torus cover lifts through every two-sheeted cover of the original
manifold. Its induced loop classes are squares; their signs are therefore one.
The exact monodromy kernel and covering lifting criterion produce the map. -/
theorem doubled_lift_two_sheet {n : ℕ} {M Y : Type*}
    [TopologicalSpace M] [TopologicalSpace Y]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (p : Y → M) (hp : IsCoveringMap p)
    (e : (p ⁻¹' {q.symm 0}) ≃ Bool) :
    ∃ s : C(UnitAddTorus (Fin n), Y), ∀ x, p (s x) = q.symm (2 • x) := by
  let : LocallyPathConnectedSpace (UnitAddTorus (Fin n)) :=
    (coordinateProjection_cover n).isOpenQuotientMap.isQuotientMap.locallyPathConnectedSpace
  let Q : C(UnitAddTorus (Fin n), M) := ⟨q.symm, q.symm.continuous⟩
  let D : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ 2 • x, continuous_id.const_smul 2⟩
  have hD : D 0 = 0 := smul_zero 2
  have hB : (Q.comp D) 0 = q.symm 0 := congrArg Q hD
  let y₀ := e.symm false
  have hrange : (FundamentalGroup.mapOfEq (Q.comp D) hB).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ y₀.property).range := by
    rintro _ ⟨γ, rfl⟩
    apply OrientationMonodromyProof.fixed_monodromy_mem_range p hp (q.symm 0)
      y₀.val y₀.property
    apply (OrientationMonodromyProof.sign_one_iff_fixed p hp (q.symm 0) e _ y₀).mp
    rw [← FranksPointedTransport.mapOfEq_comp D Q hD rfl, MonoidHom.comp_apply,
      nsmul_fundamentalGroup, map_pow, map_pow, Int.units_sq]
  obtain ⟨s, ⟨_, hs⟩, _⟩ := lift_of_pointed_range ⟨p, hp.continuous⟩ hp
    (Q.comp D) 0 y₀.val (q.symm 0) hB y₀.property hrange
  exact ⟨s, fun x ↦ congrFun hs x⟩

/-- Every finite-rank real vector bundle acquires a continuous orientation along
the doubled torus cover, including the canonical rank-zero case. The section is
valued in the original ordered-basis orientation total space. -/
theorem doubled_orientation_section {n : ℕ} {M : Type*} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (d : ℕ) (E : M → Type*)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)] [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (Bundle.TotalSpace (Fin d → ℝ) E)]
    [FiberBundle (Fin d → ℝ) E] [VectorBundle ℝ (Fin d → ℝ) E] :
    letI := realOrientationTopology d E
    ∃ o : ∀ x : UnitAddTorus (Fin n), RealBasisOrientation d (E (q.symm (2 • x))),
      Continuous (fun x ↦ (⟨q.symm (2 • x), o x⟩ : RealOrientationTotal d E)) := by
  classical
  let := realOrientationTopology d E
  by_cases hd : d = 0
  · subst d
    let o : ∀ y : M, RealBasisOrientation 0 (E y) := fun y ↦
      Classical.choice (OrientationMonodromyProof.fibre_orientation_nonempty 0 E y)
    have hs := OrientationMonodromyProof.section_continuous_of_subsingleton 0 E
      (fun y ↦ OrientationMonodromyProof.zero_orientation_subsingleton) o
    refine ⟨fun x ↦ o (q.symm (2 • x)), ?_⟩
    exact hs.comp (q.symm.continuous.comp (continuous_id.const_smul 2))
  · let p : RealOrientationTotal d E → M := Sigma.fst
    have hp : IsCoveringMap p := OrientationMonodromyProof.projection_isCoveringMap d E
    let e := Classical.choice
      (OrientationMonodromyProof.fibre_bool_equiv d E (Nat.pos_of_ne_zero hd) (q.symm 0))
    obtain ⟨s, hs⟩ := doubled_lift_two_sheet q p hp e
    let o : ∀ x : UnitAddTorus (Fin n), RealBasisOrientation d (E (q.symm (2 • x))) :=
      fun x ↦ OrientationMonodromyProof.fibreEquiv d E (q.symm (2 • x)) ⟨s x, hs x⟩
    refine ⟨o, s.continuous.congr (fun x ↦ ?_)⟩
    exact (congrArg Subtype.val
      ((OrientationMonodromyProof.fibreEquiv d E (q.symm (2 • x))).symm_apply_apply
        ⟨s x, hs x⟩)).symm

end HolomorphicAnosov.Topology.FranksCover
