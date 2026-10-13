import HolomorphicAnosov.Topology.TorusCoordinateCover
import HolomorphicAnosov.Topology.BoundedPiDisplacementFixedPoint
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Unique fixed points of an original torus lift

Franks (1969), Lemma 1.2, pp.118–119. The counting argument below uses the
original periodic count and existence in every integer displacement class.
This keeps all smooth hypotheses in the original periodic-count provider.
-/

noncomputable section
namespace HolomorphicAnosov.FranksOriginalLift
open Set

/-- Coordinate zero in the torus means an actual integer vector. -/
theorem projection_eq_zero_iff {n : ℕ} (v : Fin n → ℝ) :
    Topology.coordinateProjection n v = 0 ↔ ∃ z : Fin n → ℤ, v = fun i ↦ (z i : ℝ) := by
  constructor
  · intro h
    have hcoord : ∀ i, ∃ z : ℤ, v i = (z : ℝ) := by
      intro i
      have hi := congrFun h i
      change ((v i : ℝ) : AddCircle (1 : ℝ)) = 0 at hi
      obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
      exact ⟨z, by simpa using hz.symm⟩
    choose z hz using hcoord
    exact ⟨z, funext hz⟩
  · rintro ⟨z, rfl⟩
    ext i
    change ((z i : ℝ) : AddCircle (1 : ℝ)) = 0
    exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z i, by simp⟩

/-- The kernel of a nonsingular integer torus endomorphism has the determinant
cardinality. Map an integer vector z to the torus class of L⁻¹z. Every kernel
point has a real representative v with Lv integral, so this map is onto.
Its kernel is the integer image of the same matrix. The first isomorphism
theorem and the integer-lattice determinant-index theorem compute its size.
This is the displacement-class enumeration in Franks (1969), Lemma 1.2,
written using the finite lattice quotient rather than local indices. -/
theorem torus_kernel_card {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ)
    (L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (T : UnitAddTorus (Fin n) →+ UnitAddTorus (Fin n))
    (hL : ∀ z : Fin n → ℤ,
      L (fun i ↦ (z i : ℝ)) = fun i ↦ (D.mulVec z i : ℝ))
    (hT : ∀ v, Topology.coordinateProjection n (L v) = T (Topology.coordinateProjection n v)) :
    Nat.card T.ker = D.det.natAbs := by
  classical
  let p := Topology.coordinateProjection n
  let cast : (Fin n → ℤ) →+ (Fin n → ℝ) := {
    toFun := fun z i ↦ (z i : ℝ)
    map_zero' := by ext; simp
    map_add' := by intros; ext; simp }
  have hcast : Function.Injective cast := by
    intro z w h
    ext i
    exact Int.cast_injective (congrFun h i)
  have hcastzero (z : Fin n → ℤ) : p (cast z) = 0 :=
    (projection_eq_zero_iff _).mpr ⟨z, rfl⟩
  let θ : (Fin n → ℤ) →+ T.ker := {
    toFun := fun z ↦ ⟨p (L.symm (cast z)), by
      rw [AddMonoidHom.mem_ker, ← hT, L.apply_symm_apply]
      exact hcastzero z⟩
    map_zero' := by apply Subtype.ext; simp
    map_add' := by intros; apply Subtype.ext; simp }
  have hθ : Function.Surjective θ := by
    intro y
    obtain ⟨v, hv⟩ := (Topology.coordinateProjection_cover n).toIsQuotientMap.surjective y.val
    have hLv : p (L v) = 0 := by rw [hT, hv]; exact y.property
    obtain ⟨z, hz⟩ := (projection_eq_zero_iff _).mp hLv
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change p (L.symm (cast z)) = y.val
    change L v = cast z at hz
    rw [← hz, L.symm_apply_apply, hv]
  let d : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) := D.mulVecLin
  have hLd (w : Fin n → ℤ) : L (cast w) = cast (d w) := hL w
  have hd : Function.Injective d := by
    intro z w h
    apply hcast
    apply L.injective
    exact (hL z).trans ((congrArg cast h).trans (hL w).symm)
  have hker : θ.ker = d.range.toAddSubgroup := by
    ext z
    change (θ z = 0) ↔ ∃ w, d w = z
    constructor
    · intro hz
      have hz' : p (L.symm (cast z)) = 0 := congrArg Subtype.val hz
      obtain ⟨w, hw⟩ := (projection_eq_zero_iff _).mp hz'
      refine ⟨w, hcast ?_⟩
      rw [← hLd w]
      change L.symm (cast z) = cast w at hw
      rw [← hw, L.apply_symm_apply]
    · rintro ⟨w, rfl⟩
      apply Subtype.ext
      change p (L.symm (cast (d w))) = 0
      rw [← hLd w, L.symm_apply_apply]
      exact hcastzero w
  have hc := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective θ hθ).toEquiv
  rw [hker] at hc
  have hdet := Submodule.natAbs_det_equiv d.range (LinearEquiv.ofInjective d hd)
  have heq : d.range.subtype.comp (LinearEquiv.ofInjective d hd).toLinearMap = d := by
    ext z i
    rfl
  change (LinearMap.det (d.range.subtype.comp
    (LinearEquiv.ofInjective d hd).toLinearMap)).natAbs = _ at hdet
  rw [heq] at hdet
  have hmatrix : LinearMap.det d = D.det := LinearMap.det_toLin' D
  rw [hmatrix] at hdet
  exact hc.symm.trans hdet.symm

/-- Equal-cardinality finite fixed sets turn a surjective fixed-point map into
an injective map. This is the counting step used after existence in every
linear displacement class, without a local-index sign assumption. -/
theorem fixed_map_injective_of_card {X Y : Type*} (f : X → X) (g : Y → Y)
    (h : X → Y) (hsem : Function.Semiconj h f g)
    (hfinite : {x | f x = x}.Finite)
    (hcard : Nat.card {x // f x = x} = Nat.card {y // g y = y})
    (honto : ∀ y, g y = y → ∃ x, f x = x ∧ h x = y) :
    ∀ x y, f x = x → f y = y → h x = h y → x = y := by
  let hfix : {x // f x = x} → {y // g y = y} :=
    fun x ↦ ⟨h x, ((hsem x).symm.trans (congrArg h x.property))⟩
  have : Finite {x // f x = x} := hfinite.to_subtype
  have hs : Function.Surjective hfix := by
    intro y
    obtain ⟨x, hx, hh⟩ := honto y y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hh⟩
  have hi := (Nat.bijective_iff_surjective_and_card hfix).mpr ⟨hs, hcard⟩
  intro x y hx hy hh
  exact congrArg Subtype.val (hi.1 (show hfix ⟨x,hx⟩ = hfix ⟨y,hy⟩ from Subtype.ext hh))

/-- Equal-cardinality fixed sets and a fixed-point lifting witness give a
bijection between the two fixed-point subtypes. -/
theorem fixed_map_bijective_of_card {X Y : Type*} (f : X → X) (g : Y → Y)
    (h : X → Y) (hsem : Function.Semiconj h f g)
    (hfinite : {x | f x = x}.Finite)
    (hcard : Nat.card {x // f x = x} = Nat.card {y // g y = y})
    (honto : ∀ y, g y = y → ∃ x, f x = x ∧ h x = y) :
    Function.Bijective (fun x : {x // f x = x} ↦
      (⟨h x, ((hsem x).symm.trans (congrArg h x.property))⟩ : {y // g y = y})) := by
  let hfix : {x // f x = x} → {y // g y = y} := fun x ↦
    ⟨h x, ((hsem x).symm.trans (congrArg h x.property))⟩
  have : Finite {x // f x = x} := hfinite.to_subtype
  have hs : Function.Surjective hfix := by
    intro y
    obtain ⟨x, hx, hh⟩ := honto y y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hh⟩
  exact (Nat.bijective_iff_surjective_and_card hfix).mpr ⟨hs, hcard⟩

/-- Bounded semiconjugacy makes the original lift a bounded perturbation of
the same linear map. The original and corrected lifts differ by at most K,
so subtracting the semiconjugacy identity costs K + ‖B‖K. -/
theorem lift_displacement_bound {n : ℕ}
    (G H : C((Fin n → ℝ), Fin n → ℝ))
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hsem : Function.Semiconj H G B) (K : ℝ)
    (hbound : ∀ x, ‖x - H x‖ ≤ K) (x : Fin n → ℝ) :
    ‖G x - B x‖ ≤ K + ‖B‖ * K := by
  have heq : G x - B x = (G x - H (G x)) + B (H x - x) := by
    rw [map_sub, hsem x]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (hbound (G x))
    ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (by simpa only [norm_sub_rev] using hbound x) (norm_nonneg _))))

/-- Every fixed point of the linear torus map has an original fixed preimage.
Choose a real representative v and its integer displacement z=v-Bv. The
bounded-displacement theorem fixes G+z. Applying H and its integer covariance
then gives (I-B)Hx=z=(I-B)v, hence Hx=v. This is the existence in every
Nielsen displacement class used in Franks (1969), Lemma 1.2, pp.118–119. -/
theorem fixed_preimage
    {n : ℕ} (f a h : UnitAddTorus (Fin n) → UnitAddTorus (Fin n))
    (G H : C((Fin n → ℝ), Fin n → ℝ))
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hL : ∀ v, L v = v - B v)
    (hprojG : ∀ v, Topology.coordinateProjection n (G v) =
      f (Topology.coordinateProjection n v))
    (hprojH : ∀ v, Topology.coordinateProjection n (H v) =
      h (Topology.coordinateProjection n v))
    (hprojB : ∀ v, Topology.coordinateProjection n (B v) =
      a (Topology.coordinateProjection n v))
    (hsem : Function.Semiconj H G B)
    (hdeck : ∀ v (z : Fin n → ℤ), H (v + fun i ↦ (z i : ℝ)) =
      H v + fun i ↦ (z i : ℝ))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ v, ‖v - H v‖ ≤ K)
    (y : UnitAddTorus (Fin n)) (hy : a y = y) :
    ∃ x, f x = x ∧ h x = y := by
  let p := Topology.coordinateProjection n
  obtain ⟨v, hv⟩ := (Topology.coordinateProjection_cover n).toIsQuotientMap.surjective y
  have hdisp : p (v - B v) = 0 := by rw [map_sub, hprojB, hv, hy, sub_self]
  obtain ⟨z, hz⟩ := (projection_eq_zero_iff _).mp hdisp
  let iz : Fin n → ℝ := fun i ↦ (z i : ℝ)
  let Gz : C((Fin n → ℝ), Fin n → ℝ) :=
    ⟨fun x ↦ G x + iz, G.continuous.add continuous_const⟩
  obtain ⟨x, hx⟩ := Topology.bounded_pi_displacement_fixed_point n Gz B L hL
    (K + ‖B‖ * K + ‖iz‖)
    (add_nonneg (add_nonneg hK (mul_nonneg (norm_nonneg _) hK)) (norm_nonneg _)) (by
      intro x
      change ‖G x + iz - B x‖ ≤ _
      have he : G x + iz - B x = (G x - B x) + iz := by abel
      rw [he]
      exact (norm_add_le _ _).trans
        (add_le_add (lift_displacement_bound G H B hsem K hbound x) le_rfl))
  change G x + iz = x at hx
  have hHx : L (H x) = L v := by
    rw [hL, hL, hz]
    have h := congrArg H hx
    rw [hdeck, hsem x] at h
    change B (H x) + iz = H x at h
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)
  have hHxeq : H x = v := L.injective hHx
  refine ⟨p x, ?_, ?_⟩
  · have hp := congrArg p hx
    rw [map_add, hprojG,
      (projection_eq_zero_iff iz).mpr ⟨z, rfl⟩, add_zero] at hp
    exact hp
  · rw [← hprojH, hHxeq, hv]

/-- Integer equivariance makes the real lift injective within each projection
fibre once its corrected images coincide. -/
theorem eq_of_projection_eq_of_image_eq {n : ℕ}
    (H : (Fin n → ℝ) → (Fin n → ℝ))
    (hdeck : ∀ v (z : Fin n → ℤ), H (v + fun i ↦ (z i : ℝ)) =
      H v + fun i ↦ (z i : ℝ))
    {x y : Fin n → ℝ} (hproj : Topology.coordinateProjection n x =
      Topology.coordinateProjection n y) (hH : H x = H y) : x = y := by
  have hp : Topology.coordinateProjection n (y - x) = 0 := by
    rw [map_sub, hproj, sub_self]
  obtain ⟨z, hz⟩ := (projection_eq_zero_iff _).mp hp
  have hy : y = x + fun i ↦ (z i : ℝ) := by
    rw [← hz]
    abel
  have hi : (fun i ↦ (z i : ℝ)) = 0 := by
    have hh := hH
    rw [hy, hdeck] at hh
    exact (add_eq_left.mp hh.symm)
  rw [hy, hi, add_zero]

/-- The integer displacement determinant counts fixed points of the linear
toral map. This is the preceding kernel computation for identity minus a. -/
theorem torus_fixed_card {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (a : UnitAddTorus (Fin n) →+ UnitAddTorus (Fin n))
    (hL : ∀ v, L v = v - B v)
    (hD : ∀ z : Fin n → ℤ,
      L (fun i ↦ (z i : ℝ)) = fun i ↦ (D.mulVec z i : ℝ))
    (hprojB : ∀ v, Topology.coordinateProjection n (B v) =
      a (Topology.coordinateProjection n v)) :
    Nat.card {y // a y = y} = D.det.natAbs := by
  let T : UnitAddTorus (Fin n) →+ UnitAddTorus (Fin n) := AddMonoidHom.id _ - a
  let e : {y // a y = y} ≃ T.ker := {
    toFun := fun y ↦ ⟨y.val, by
      change y.val - a y.val = 0
      rw [y.property, sub_self]⟩
    invFun := fun y ↦ ⟨y.val, by
      have hy : y.val - a y.val = 0 := y.property
      exact (sub_eq_zero.mp hy).symm⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  refine (Nat.card_congr e).trans (torus_kernel_card D L.toLinearEquiv T hD ?_)
  intro v
  change Topology.coordinateProjection n (L v) =
    Topology.coordinateProjection n v - a (Topology.coordinateProjection n v)
  rw [hL, map_sub, hprojB]

/-- Convert the rational fixed-count form exported by the periodic-count
provider into the natural cardinality form used by the lattice quotient. -/
theorem nat_card_eq_natAbs_of_rat_count {n : ℕ} (D : Matrix (Fin n) (Fin n) ℤ)
    (N : ℕ) (h : (N : ℚ) = |Matrix.det (D.map (Int.castRingHom ℚ))|) :
    N = D.det.natAbs := by
  have hdet : Matrix.det (D.map (Int.castRingHom ℚ)) = (D.det : ℚ) := by
    simpa using ((Int.castRingHom ℚ).map_det D).symm
  have hz : |Matrix.det (D.map (Int.castRingHom ℚ))| = (D.det.natAbs : ℚ) := by
    rw [hdet]
    calc
      |(D.det : ℚ)| = ((|D.det| : ℤ) : ℚ) := (Int.cast_abs).symm
      _ = ((D.det.natAbs : ℤ) : ℚ) := by rw [Int.natCast_natAbs]
      _ = (D.det.natAbs : ℚ) := by norm_num
  rw [hz] at h
  exact_mod_cast h

/-- The original lift has exactly one fixed point when its downstairs fixed
count is the linear determinant count.

Proof: H-id bounded makes G-B bounded. The bounded-displacement theorem gives
existence. Every linear torus fixed point has a fixed preimage by fixing G+z
in its integer displacement class. The kernel/cokernel determinant computation
shows both downstairs fixed sets have the same finite cardinal; hence their
H-induced map is injective. Any two upstairs fixed points have H-image zero
because I-B is invertible. Their projections therefore agree; integer deck
equivariance then forces the two original real points to agree.

Source: Franks (1969), Lemma 1.2, pp.118–119. The use of the supplied exact
periodic count and displacement classes in place of individual local signs
is an agent-written implementation. No global-product or periodic-density
result is used. The real coordinates are only topological covering coordinates.
-/
theorem unique_fixed_point {n : ℕ}
    (f h : UnitAddTorus (Fin n) → UnitAddTorus (Fin n))
    (a : UnitAddTorus (Fin n) →+ UnitAddTorus (Fin n))
    (G H : C((Fin n → ℝ), Fin n → ℝ))
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (D : Matrix (Fin n) (Fin n) ℤ)
    (L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hL : ∀ v, L v = v - B v)
    (hD : ∀ z : Fin n → ℤ,
      L (fun i ↦ (z i : ℝ)) = fun i ↦ (D.mulVec z i : ℝ))
    (hprojG : ∀ v, Topology.coordinateProjection n (G v) =
      f (Topology.coordinateProjection n v))
    (hprojH : ∀ v, Topology.coordinateProjection n (H v) =
      h (Topology.coordinateProjection n v))
    (hprojB : ∀ v, Topology.coordinateProjection n (B v) =
      a (Topology.coordinateProjection n v))
    (hsem : Function.Semiconj H G B)
    (hdeck : ∀ v (z : Fin n → ℤ), H (v + fun i ↦ (z i : ℝ)) =
      H v + fun i ↦ (z i : ℝ))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ v, ‖v - H v‖ ≤ K)
    (hfinite : {x | f x = x}.Finite)
    (hcount : Nat.card {x // f x = x} = D.det.natAbs) :
    ∃! x, G x = x := by
  have hdown : Function.Semiconj h f a := by
    intro x
    obtain ⟨v, rfl⟩ := (Topology.coordinateProjection_cover n).toIsQuotientMap.surjective x
    rw [← hprojG, ← hprojH, hsem, hprojB, hprojH]
  have hcard : Nat.card {x // f x = x} = Nat.card {y // a y = y} :=
    hcount.trans (torus_fixed_card D B L a hL hD hprojB).symm
  have hinj := fixed_map_injective_of_card f a h hdown hfinite hcard
    (fixed_preimage f a h G H B L hL hprojG hprojH hprojB hsem hdeck K hK hbound)
  have hzero (x : Fin n → ℝ) (hx : G x = x) : H x = 0 := by
    apply L.injective
    rw [map_zero, hL, ← hsem x, hx, sub_self]
  obtain ⟨x, hx⟩ := Topology.bounded_pi_displacement_fixed_point n G B L hL
    (K + ‖B‖ * K) (add_nonneg hK (mul_nonneg (norm_nonneg _) hK))
    (lift_displacement_bound G H B hsem K hbound)
  refine ⟨x, hx, ?_⟩
  intro y hy
  have hh : H y = H x := (hzero y hy).trans (hzero x hx).symm
  have hp : Topology.coordinateProjection n y = Topology.coordinateProjection n x := by
    apply hinj
    · rw [← hprojG, hy]
    · rw [← hprojG, hx]
    · rw [← hprojH, ← hprojH, hh]
  exact eq_of_projection_eq_of_image_eq H hdeck hp hh

end HolomorphicAnosov.FranksOriginalLift
