import HolomorphicAnosov.Topology.AmbientCircleBoundedCell
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusParameterization
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.MetricSpace.Bounded
import HolomorphicAnosov.Topology.SegmentProperAmbientCircleArc
import HolomorphicAnosov.Topology.AmbientCircleRegions
import HolomorphicAnosov.Topology.CairnsDiskCellRelativeChart
import HolomorphicAnosov.Topology.DiskChartBoundaryAdjustment



open Set
namespace HolomorphicAnosov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compatible homeomorphisms on two closed covers glue when the first map identifies
exactly the overlap. Continuity follows by closed pasting; injectivity follows from
the overlap condition, and surjectivity from the target cover. Images of closed sets
are the union of the two closed chart images, so the bijection is a homeomorphism. -/
theorem closed_cover_homeomorph_gluing {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (P Q : Set X) (U V : Set Y)
    (hP : IsClosed P) (hQ : IsClosed Q) (hU : IsClosed U) (hV : IsClosed V)
    (hcover : P ∪ Q = univ) (htarget : U ∪ V = univ)
    (F : P ≃ₜ U) (G : Q ≃ₜ V)
    (hagree : ∀ (x : X) (hxP : x ∈ P) (hxQ : x ∈ Q),
      (F ⟨x, hxP⟩ : Y) = (G ⟨x, hxQ⟩ : Y))
    (hoverlap : ∀ x : P, (F x : Y) ∈ V ↔ (x : X) ∈ Q) :
    ∃ H : X ≃ₜ Y, (∀ x : P, H x = F x) ∧ (∀ x : Q, H x = G x) := by
  classical
  have hother (x : X) (hx : x ∉ P) : x ∈ Q :=
    ((Set.ext_iff.mp hcover x).mpr (Set.mem_univ x)).resolve_left hx
  let h : X → Y := fun x ↦ if hx : x ∈ P then F ⟨x, hx⟩ else G ⟨x, hother x hx⟩
  have hF (x : P) : h x = (F x : Y) := by simp [h, x.property]
  have hG (x : Q) : h x = (G x : Y) := by
    by_cases hx : (x : X) ∈ P
    · simpa only [h, dite_eq_left hx] using hagree x hx x.property
    · simp [h, hx]
  have hcontP : ContinuousOn h P := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp F.continuous using 1
    exact funext hF
  have hcontQ : ContinuousOn h Q := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp G.continuous using 1
    exact funext hG
  have hcont : Continuous h := by
    rw [← continuousOn_univ, ← hcover]
    exact hcontP.union_of_isClosed hcontQ hP hQ
  have hinj : Function.Injective h := by
    intro x y heq
    by_cases hx : x ∈ P <;> by_cases hy : y ∈ P
    · exact congrArg Subtype.val (F.injective (Subtype.ext
        ((hF ⟨x, hx⟩).symm.trans (heq.trans (hF ⟨y, hy⟩)))))
    · have hxQ : x ∈ Q := (hoverlap ⟨x, hx⟩).mp (by
        rw [← hF, heq, hG ⟨y, hother y hy⟩]
        exact (G ⟨y, hother y hy⟩).property)
      exact congrArg Subtype.val (G.injective (Subtype.ext
        ((hG ⟨x, hxQ⟩).symm.trans (heq.trans (hG ⟨y, hother y hy⟩)))))
    · have hyQ : y ∈ Q := (hoverlap ⟨y, hy⟩).mp (by
        rw [← hF, ← heq, hG ⟨x, hother x hx⟩]
        exact (G ⟨x, hother x hx⟩).property)
      exact congrArg Subtype.val (G.injective (Subtype.ext
        ((hG ⟨x, hother x hx⟩).symm.trans (heq.trans (hG ⟨y, hyQ⟩)))))
    · exact congrArg Subtype.val (G.injective (Subtype.ext
        ((hG ⟨x, hother x hx⟩).symm.trans (heq.trans (hG ⟨y, hother y hy⟩)))))
  have hsurj : Function.Surjective h := by
    intro y
    have hy : y ∈ U ∪ V := htarget.symm ▸ mem_univ y
    rcases hy with hy | hy
    · refine ⟨F.symm ⟨y, hy⟩, ?_⟩
      rw [hF, F.apply_symm_apply]
    · refine ⟨G.symm ⟨y, hy⟩, ?_⟩
      rw [hG, G.apply_symm_apply]
  have hclosed : IsClosedMap h := by
    intro K hK
    let KP : Set P := Subtype.val ⁻¹' K
    let KQ : Set Q := Subtype.val ⁻¹' K
    have hKP : IsClosed KP := hK.preimage continuous_subtype_val
    have hKQ : IsClosed KQ := hK.preimage continuous_subtype_val
    have hFP : IsClosed ((fun x : P ↦ (F x : Y)) '' KP) :=
      (hU.isClosedMap_subtype_val.comp F.isClosedMap) KP hKP
    have hGQ : IsClosed ((fun x : Q ↦ (G x : Y)) '' KQ) :=
      (hV.isClosedMap_subtype_val.comp G.isClosedMap) KQ hKQ
    have himage : h '' K = ((fun x : P ↦ (F x : Y)) '' KP) ∪
        ((fun x : Q ↦ (G x : Y)) '' KQ) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        by_cases hxP : x ∈ P
        · exact Or.inl ⟨⟨x, hxP⟩, hx, (hF ⟨x, hxP⟩).symm⟩
        · exact Or.inr ⟨⟨x, hother x hxP⟩, hx, (hG ⟨x, hother x hxP⟩).symm⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ⟨x, hx, hF x⟩
        · exact ⟨x, hx, hG x⟩
    rw [himage]
    exact hFP.union hGQ
  have hh : IsHomeomorph h := isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨hcont, hclosed, hinj, hsurj⟩
  exact ⟨hh.homeomorph h, hF, hG⟩
end HolomorphicAnosov

/-! # Extending a sphere homeomorphism over a closed annulus

The radial formula is the annular version of Hirsch, Differential Topology (1976),
p.155, used for the prescribed boundary in Cairns (1951), preliminary 2(B), p.860.
-/

namespace HolomorphicAnosov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Set

/-- Every homeomorphism of a positive-radius sphere of a real normed space extends over
the closed exterior of that ball, preserving the norm at every point.

Source: Hirsch, Differential Topology (1976), p.155, radial extension formula.
Use polar coordinates on the punctured space, apply the sphere homeomorphism to
its angular factor and leave the positive radius fixed, and return to Cartesian
coordinates. This is a homeomorphism with inverse given by the inverse sphere
map. Since the norm is unchanged, both maps restrict to the closed exterior.
On the unit sphere normalization and multiplication by the radius are identities.
The argument includes empty spheres and makes no finite-dimensional assumption. -/
theorem sphere_exterior_boundary_extension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (r : ℝ) (hr : 0 < r)
    (b : Metric.sphere (0 : E) r ≃ₜ Metric.sphere (0 : E) r) :
    ∃ F : {x : E | r ≤ ‖x‖} ≃ₜ {x : E | r ≤ ‖x‖},
      (∀ x, ‖(F x : E)‖ = ‖(x : E)‖) ∧
      ∀ z : Metric.sphere (0 : E) r,
        ∀ hz : r ≤ ‖(z : E)‖,
          (F ⟨z, hz⟩ : E) = (b z : E) := by
  let e := homeomorphSphereProd E r hr
  let h := e.trans ((b.prodCongr (Homeomorph.refl (Ioi (0 : ℝ)))).trans e.symm)
  have hn (x : ({0}ᶜ : Set E)) : ‖(h x : E)‖ = ‖(x : E)‖ := by
    simp [h, e, norm_smul,
      mem_sphere_zero_iff_norm.mp (b (e x).1).property,
      abs_of_pos hr, hr.ne']
  have hin (x : {x : E | r ≤ ‖x‖}) : (x : E) ∈ ({0}ᶜ : Set E) := by
    change (x : E) ≠ 0
    intro hx
    have := x.property
    simp only [mem_ofPred_eq, hx, norm_zero] at this
    exact (not_le_of_gt hr) this
  let F : {x : E | r ≤ ‖x‖} ≃ₜ {x : E | r ≤ ‖x‖} :=
    { toFun := fun x ↦ ⟨h ⟨x, hin x⟩, by change r ≤ ‖(h ⟨x, hin x⟩ : E)‖; rw [hn]; exact x.property⟩
      invFun := fun x ↦ ⟨h.symm ⟨x, hin x⟩, by
        have he := hn (h.symm ⟨x, hin x⟩)
        rw [h.apply_symm_apply] at he
        change r ≤ ‖(h.symm ⟨x, hin x⟩ : E)‖
        rw [← he]
        exact x.property⟩
      left_inv := fun x ↦ Subtype.ext (congrArg (fun y : ({0}ᶜ : Set E) ↦ (y : E)) (h.symm_apply_apply ⟨x, hin x⟩))
      right_inv := fun x ↦ Subtype.ext (congrArg (fun y : ({0}ᶜ : Set E) ↦ (y : E)) (h.apply_symm_apply ⟨x, hin x⟩))
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (h.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (h.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_val }
  refine ⟨F, fun x ↦ hn _, ?_⟩
  intro z hz
  have hz1 : ‖(z : E)‖ = r := mem_sphere_zero_iff_norm.mp z.property
  have he : (e ⟨z, hin ⟨z, hz⟩⟩).1 = z := by
    apply Subtype.ext
    simp [e, hz1, smul_smul, hr.ne']
  change (h ⟨z, hin ⟨z, hz⟩⟩ : E) = _
  simp [h, he, e, hz1, hr.ne']


end HolomorphicAnosov

open Set Metric
namespace HolomorphicAnosov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A homeomorphism of the closed radius-r ball with a specified boundary sphere homeomorphism extends to an ambient normed-space homeomorphism.

Source: Cairns (1951), pp.860–861; Hirsch (1976), p.155.

Extend the sphere correspondence over the closed exterior by polar coordinates. The disk and exterior maps agree on their common sphere. If a disk point maps to the sphere, the inverse boundary correspondence supplies a sphere point with the same disk image, and injectivity forces the original point onto the sphere. Thus the maps identify precisely their overlap. Glue them on the closed cover by the ball and its closed exterior. -/
theorem closed_ball_ambient_extension (r : ℝ) (hr : 0 < r)
    (F : closedBall (0 : E) r ≃ₜ closedBall (0 : E) r)
    (b : sphere (0 : E) r ≃ₜ sphere (0 : E) r)
    (hboundary : ∀ z : sphere (0 : E) r,
      (F ⟨z, sphere_subset_closedBall z.property⟩ : E) = (b z : E)) :
    ∃ H : E ≃ₜ E, ∀ z : closedBall (0 : E) r, H z = F z := by
  obtain ⟨G, hnorm, hG⟩ := sphere_exterior_boundary_extension r hr b
  have hiff (x : closedBall (0 : E) r) : ‖(F x : E)‖ = r ↔ ‖(x : E)‖ = r := by
    constructor
    · intro hx
      let y : sphere (0 : E) r := ⟨F x, by simpa using hx⟩
      let z := b.symm y
      have hz : F ⟨z, sphere_subset_closedBall z.property⟩ = F x := by
        apply Subtype.ext
        exact (hboundary z).trans (congrArg Subtype.val (b.apply_symm_apply y))
      have heq : (z : E) = (x : E) := congrArg Subtype.val (F.injective hz)
      rw [← heq]
      exact mem_sphere_zero_iff_norm.mp z.property
    · intro hx
      have heq := hboundary (⟨x, by simpa using hx⟩ : sphere (0 : E) r)
      rw [heq]
      exact mem_sphere_zero_iff_norm.mp (b ⟨x, by simpa using hx⟩).property
  have hcover : closedBall (0 : E) r ∪ {z : E | r ≤ ‖z‖} = univ := by
    ext z
    simp only [mem_union, mem_closedBall, dist_zero_right, mem_ofPred_eq, mem_univ, iff_true]
    exact le_total ‖z‖ r
  obtain ⟨H, hH, _⟩ := closed_cover_homeomorph_gluing
    (closedBall (0 : E) r) {z : E | r ≤ ‖z‖}
    (closedBall (0 : E) r) {z : E | r ≤ ‖z‖}
    isClosed_closedBall (isClosed_le continuous_const continuous_norm)
    isClosed_closedBall (isClosed_le continuous_const continuous_norm)
    hcover hcover F G (by
      intro x hxP hxQ
      have hx : ‖x‖ = r := le_antisymm (by simpa using hxP) hxQ
      let z : sphere (0 : E) r := ⟨x, by simpa using hx⟩
      exact (hboundary z).trans (hG z hxQ).symm) (by
      intro x
      have hx : ‖(x : E)‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using x.property
      have hFx : ‖(F x : E)‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using (F x).property
      change r ≤ ‖(F x : E)‖ ↔ r ≤ ‖(x : E)‖
      constructor
      · intro h
        exact ((hiff x).mp (le_antisymm hFx h)).ge
      · intro h
        exact ((hiff x).mpr (le_antisymm hx h)).ge)
  exact ⟨H, hH⟩
end HolomorphicAnosov

namespace HolomorphicAnosov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def nestedSubsetHomeomorph {X : Type*} [TopologicalSpace X] {P R : Set X}
    (h : P ⊆ R) : {x : R | (x : X) ∈ P} ≃ₜ P where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- A homeomorphism of the closed radius-r ball with a specified boundary sphere homeomorphism extends to an ambient normed-space homeomorphism.

Source: Cairns (1951), pp.860–861; Hirsch (1976), p.155.

Extend the sphere correspondence over the closed exterior by polar coordinates. The disk and exterior maps agree on their common sphere. If a disk point maps to the sphere, the inverse boundary correspondence supplies a sphere point with the same disk image, and injectivity forces the original point onto the sphere. Thus the maps identify precisely their overlap. Glue them on the closed cover by the ball and its closed exterior. -/
theorem closed_ball_ambient_extension_of_boundary (r : ℝ) (hr : 0 < r)
    (F : closedBall (0 : E) r ≃ₜ closedBall (0 : E) r)
    (hboundary : ∀ z : closedBall (0 : E) r,
      ‖(z : E)‖ = r ↔ ‖(F z : E)‖ = r) :
    ∃ H : E ≃ₜ E, ∀ z : closedBall (0 : E) r, H z = F z := by
  let e := nestedSubsetHomeomorph (show sphere (0 : E) r ⊆ closedBall (0 : E) r from sphere_subset_closedBall)
  let b : sphere (0 : E) r ≃ₜ sphere (0 : E) r :=
    e.symm.trans ((F.subtype (fun x ↦ by
      change (x : E) ∈ sphere (0 : E) r ↔ (F x : E) ∈ sphere (0 : E) r
      simpa only [mem_sphere_zero_iff_norm] using hboundary x)).trans e)
  exact closed_ball_ambient_extension r hr F b (fun _ ↦ rfl)
end HolomorphicAnosov

namespace HolomorphicAnosov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A boundary-preserving disk chart on a set with a given ambient ball normalization extends to an ambient homeomorphism agreeing with that chart.

Source: Cairns (1951), pp.860–861; Hirsch (1976), p.155.

Restrict the ambient normalization to the closed set and conjugate the supplied chart by its inverse, obtaining a self-homeomorphism of the closed ball. The frontier equivalences say this self-homeomorphism preserves the sphere. Restrict it to the sphere to obtain the boundary correspondence, extend over the exterior by the preceding theorem, and precompose with the ambient normalization. On the original closed set the normalizations cancel, leaving the exact supplied chart. -/
theorem ambient_of_disk_chart (R : Set E) (r : ℝ) (hr : 0 < r)
    (G : E ≃ₜ E)
    (hGdisk : ∀ x : E, x ∈ R ↔ G x ∈ closedBall (0 : E) r)
    (hGsphere : ∀ x : E, x ∈ frontier R ↔ ‖G x‖ = r)
    (F : R ≃ₜ closedBall (0 : E) r)
    (hFboundary : ∀ x : R, (x : E) ∈ frontier R ↔ ‖(F x : E)‖ = r) :
    ∃ H : E ≃ₜ E, ∀ z : R, H z = F z := by
  let G₀ : R ≃ₜ closedBall (0 : E) r := G.subtype hGdisk
  let Tdisk := G₀.symm.trans F
  have hE (x : closedBall (0 : E) r) :
      ‖(x : E)‖ = r ↔ ‖(Tdisk x : E)‖ = r := by
    have hg := hGsphere (G₀.symm x)
    have hx : G (G₀.symm x) = (x : E) :=
      congrArg Subtype.val (G₀.apply_symm_apply x)
    rw [hx] at hg
    exact hg.symm.trans (hFboundary (G₀.symm x))
  obtain ⟨T, hT⟩ := closed_ball_ambient_extension_of_boundary r hr Tdisk hE
  refine ⟨G.trans T, ?_⟩
  intro z
  have ht := hT (G₀ z)
  change T (G z) = (F (G₀.symm (G₀ z)) : E) at ht
  simpa using ht
end HolomorphicAnosov

namespace HolomorphicAnosov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A closed disk chart and a compatible closed annulus chart glue to a chart of their surrounding region onto the radius-two closed ball.

Source: Cairns (1951), pp.860–861; Hirsch (1976), p.155.

Work inside the surrounding region and the radius-two ball. Pull back the inner disk and annulus as closed subsets, and transport the supplied charts through nested-subtype equivalences. They cover both domain and target. Agreement on the inner frontier and the boundary criterion for the disk chart identify their overlap precisely. Apply the closed-cover gluing theorem and project its two restriction equalities to the ambient space. -/
theorem disk_annulus_gluing (D R : Set E) (hD : IsClosed D) (hR : IsClosed R)
    (hDR : D ⊆ R)
    (F : D ≃ₜ closedBall (0 : E) 1)
    (hFboundary : ∀ x : D, ‖(F x : E)‖ = 1 ↔ (x : E) ∉ interior D)
    (Φ : ↥(R \ interior D) ≃ₜ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2})
    (hagree : ∀ (x : E) (hxD : x ∈ D) (hxA : x ∈ R \ interior D),
      (F ⟨x, hxD⟩ : E) = (Φ ⟨x, hxA⟩ : E)) :
    ∃ K : R ≃ₜ closedBall (0 : E) 2,
      (∀ x : D, (K ⟨x, hDR x.property⟩ : E) = (F x : E)) ∧
      (∀ x : ↥(R \ interior D), (K ⟨x, x.property.1⟩ : E) = (Φ x : E)) := by
  let A := R \ interior D
  let T : Set E := {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}
  let P : Set R := {x | (x : E) ∈ D}
  let Q : Set R := {x | (x : E) ∈ A}
  let U : Set (closedBall (0 : E) 2) := {x | (x : E) ∈ closedBall (0 : E) 1}
  let V : Set (closedBall (0 : E) 2) := {x | (x : E) ∈ T}
  have hA : A ⊆ R := fun _ hx ↦ hx.1
  have hball : closedBall (0 : E) 1 ⊆ closedBall (0 : E) 2 :=
    closedBall_subset_closedBall (by norm_num)
  have hT : T ⊆ closedBall (0 : E) 2 := fun _ hx ↦ by
    simpa only [mem_closedBall, dist_zero_right] using hx.2
  let F₀ : P ≃ₜ U := (nestedSubsetHomeomorph hDR).trans
    (F.trans (nestedSubsetHomeomorph hball).symm)
  let Φ₀ : Q ≃ₜ V := (nestedSubsetHomeomorph hA).trans
    (Φ.trans (nestedSubsetHomeomorph hT).symm)
  have hP : IsClosed P := hD.preimage continuous_subtype_val
  have hQ : IsClosed Q := (hR.sdiff isOpen_interior).preimage continuous_subtype_val
  have hU : IsClosed U := isClosed_closedBall.preimage continuous_subtype_val
  have hV : IsClosed V :=
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)).preimage continuous_subtype_val
  have hcover : P ∪ Q = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    by_cases hx : (x : E) ∈ D
    · exact Or.inl hx
    · exact Or.inr ⟨x.property, fun hi ↦ hx (interior_subset hi)⟩
  have htarget : U ∪ V = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    have hx : ‖(x : E)‖ ≤ 2 := by
      simpa only [mem_closedBall, dist_zero_right] using x.property
    by_cases hx1 : ‖(x : E)‖ ≤ 1
    · exact Or.inl (by simpa only [U, mem_ofPred_eq, mem_closedBall, dist_zero_right] using hx1)
    · exact Or.inr ⟨(lt_of_not_ge hx1).le, hx⟩
  obtain ⟨K, hKF, hKΦ⟩ := closed_cover_homeomorph_gluing P Q U V hP hQ hU hV
    hcover htarget F₀ Φ₀ (by
      intro x hxP hxQ
      apply Subtype.ext
      exact hagree x hxP hxQ) (by
      intro x
      change (1 ≤ ‖(F ⟨x.val, x.property⟩ : E)‖ ∧
        ‖(F ⟨x.val, x.property⟩ : E)‖ ≤ 2) ↔ ((x.val : E) ∈ R ∧ _)
      have hxF : ‖(F ⟨x.val, x.property⟩ : E)‖ ≤ 1 := by
        simpa only [mem_closedBall, dist_zero_right] using (F ⟨x.val, x.property⟩).property
      constructor
      · intro hx
        exact ⟨x.val.property, (hFboundary _).mp (le_antisymm hxF hx.1)⟩
      · intro hx
        exact ⟨((hFboundary _).mpr hx.2).ge, hxF.trans (by norm_num)⟩)
  refine ⟨K, ?_, ?_⟩
  · intro x
    exact congrArg Subtype.val (hKF ⟨⟨x, hDR x.property⟩, x.property⟩)
  · intro x
    exact congrArg Subtype.val (hKΦ ⟨⟨x, x.property.1⟩, x.property⟩)
end HolomorphicAnosov

namespace HolomorphicAnosov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compatible inner disk and exterior annulus charts, together with an ambient normalization of the surrounding region, yield the prescribed ambient extension of the inner disk chart.

Source: Cairns (1951), pp.860–861; Hirsch (1976), p.155.

Glue the disk and annulus charts to obtain a chart of the surrounding region. Its outer frontier maps to the radius-two sphere by the annulus image equality. Conversely, every sphere image has an annulus preimage on the outer frontier, and injectivity identifies that preimage with the original point. Thus the glued chart satisfies the frontier equivalence needed for ambient extension. Extend across the outer exterior and use the retained inner-disk restriction; surjectivity of the inner chart gives the exact image of the original disk. -/
theorem disk_annulus_ambient_extension (D R : Set E) (hD : IsClosed D) (hR : IsClosed R)
    (hDR : D ⊆ interior R)
    (F : D ≃ₜ closedBall (0 : E) 1)
    (hFboundary : ∀ x : D, ‖(F x : E)‖ = 1 ↔ (x : E) ∉ interior D)
    (Φ : ↥(R \ interior D) ≃ₜ {x : E | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2})
    (hagree : ∀ (x : E) (hxD : x ∈ D) (hxA : x ∈ R \ interior D),
      (F ⟨x, hxD⟩ : E) = (Φ ⟨x, hxA⟩ : E))
    (houter : (fun x : ↥(R \ interior D) ↦ (Φ x : E)) ''
      {x | (x : E) ∈ frontier R} = sphere (0 : E) 2)
    (G : E ≃ₜ E)
    (hGdisk : ∀ x : E, x ∈ R ↔ G x ∈ closedBall (0 : E) 2)
    (hGsphere : ∀ x : E, x ∈ frontier R ↔ ‖G x‖ = 2) :
    ∃ H : E ≃ₜ E, H '' D = closedBall (0 : E) 1 ∧
      ∀ x : D, H x = F x := by
  have hDR' : D ⊆ R := hDR.trans interior_subset
  obtain ⟨K, hKF, hKΦ⟩ := disk_annulus_gluing D R hD hR hDR' F hFboundary Φ hagree
  have hfrontA : frontier R ⊆ R \ interior D := by
    intro x hx
    refine ⟨hR.closure_eq ▸ hx.1, ?_⟩
    intro hi
    exact hx.2 (hDR (interior_subset hi))
  have hKb (x : R) : (x : E) ∈ frontier R ↔ ‖(K x : E)‖ = 2 := by
    constructor
    · intro hx
      have ha := hfrontA hx
      have him : (K x : E) ∈ sphere (0 : E) 2 := by
        rw [← houter]
        exact ⟨⟨x, ha⟩, hx, (hKΦ ⟨x, ha⟩).symm⟩
      exact mem_sphere_zero_iff_norm.mp him
    · intro hx
      have him : (K x : E) ∈ sphere (0 : E) 2 := mem_sphere_zero_iff_norm.mpr hx
      rw [← houter] at him
      obtain ⟨y, hy, heq⟩ := him
      have hK : K ⟨y, y.property.1⟩ = K x :=
        Subtype.ext ((hKΦ y).trans heq)
      have hyx : (y : E) = (x : E) := congrArg Subtype.val (K.injective hK)
      rwa [← hyx]
  obtain ⟨H, hH⟩ := ambient_of_disk_chart R 2 (by norm_num) G hGdisk hGsphere K hKb
  have hHF (x : D) : H x = (F x : E) :=
    (hH ⟨x, hDR' x.property⟩).trans (hKF x)
  refine ⟨H, ?_, hHF⟩
  apply subset_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [hHF ⟨x, hx⟩]
    exact (F ⟨x, hx⟩).property
  · intro y hy
    refine ⟨F.symm ⟨y, hy⟩, (F.symm ⟨y, hy⟩).property, ?_⟩
    rw [hHF, F.apply_symm_apply]
end HolomorphicAnosov

namespace HolomorphicAnosov
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- Every compact subset of the Euclidean plane lies in the interior of a nondegenerate compact convex coordinate rectangle.

Source: Cairns (1951), pp.860–861; Hirsch (1976), p.155.

Bound the norm of all points of the compact set by a strictly positive radius r. Take the coordinate box [-r,r] in each coordinate. Its compactness follows from the finite product of compact intervals and the Euclidean coordinate homeomorphism. It is convex as the linear preimage of a coordinate order interval. The strict box is open and lies inside the box; norm bounds dominate each coordinate, so the given compact set lies in the strict box and therefore in the interior. Zero belongs to the strict box, proving nonempty interior. -/
theorem enclosing_rectangle (D : Set Plane) (hD : IsCompact D) :
    ∃ R : Set Plane, IsCompact R ∧ Convex ℝ R ∧ (interior R).Nonempty ∧
      D ⊆ interior R ∧
      ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, ∃ a b : Fin 2 → ℝ,
        (∀ i, a i < b i) ∧ R = e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i} := by
  obtain ⟨r, hr, hbound⟩ := hD.isBounded.exists_pos_norm_lt
  let R : Set Plane := {x | ∀ i, -r ≤ x i ∧ x i ≤ r}
  let S : Set Plane := {x | ∀ i, -r < x i ∧ x i < r}
  have hrectangle : ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, ∃ a b : Fin 2 → ℝ,
      (∀ i, a i < b i) ∧ R = e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i} := by
    refine ⟨AffineIsometryEquiv.refl ℝ Plane, fun _ ↦ -r, fun _ ↦ r,
      fun _ ↦ by linarith, ?_⟩
    simp [R]
  have hcompact := Topology.cairns_polygonal_annulus_rectangle_compact R hrectangle
  have hopen : IsOpen S := by
    change IsOpen {x : Plane | ∀ i, -r < x i ∧ x i < r}
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) i)).inter
      (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) i) continuous_const)
  have hSR : S ⊆ R := fun x hx i ↦ ⟨(hx i).1.le, (hx i).2.le⟩
  have hSI : S ⊆ interior R := interior_maximal hSR hopen
  have hconv : Convex ℝ R := by
    have hc := (convex_Icc (fun _ : Fin 2 ↦ -r) (fun _ : Fin 2 ↦ r)).linear_preimage
      (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap
    convert hc using 1
    ext x
    simp only [R, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def,
      LinearEquiv.coe_coe, WithLp.coe_linearEquiv]
    exact forall_and
  refine ⟨R, hcompact, hconv, ⟨0, hSI ?_⟩, ?_, hrectangle⟩
  · intro i
    change -r < 0 ∧ 0 < r
    exact ⟨neg_neg_of_pos hr, hr⟩
  · intro x hx
    apply hSI
    intro i
    have hi : |x i| < r := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans_lt (hbound x hx)
    exact abs_lt.mp hi
end HolomorphicAnosov

namespace HolomorphicAnosov
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- A regular compact polygonal disk with connected interior and exterior, supplied with a prescribed disk chart, admits an ambient extension of that chart boundary.

Source: Cairns (1951), pp.860–861; Hirsch (1976), p.155.

Choose a containing rectangle by the enclosing-rectangle theorem. Apply polygonal-annulus parameterization with the prescribed inner boundary. The given disk chart and this annulus map agree there. Normalize the rectangle by the convex-body ambient gauge homeomorphism and scale by two. Apply the disk-annulus ambient-extension theorem. The resulting ambient map carries the disk onto the unit closed ball and restricts to the given boundary map. -/
theorem polygon_disk_ambient_extension (D : Set Plane)
    (hcompact : IsCompact D) (hregular : closure (interior D) = D)
    (hne : (interior D).Nonempty) (hi : IsPathConnected (interior D))
    (he : IsPathConnected Dᶜ)
    (hpolygon : ∃ n : ℕ, 3 ≤ n ∧ ∃ P : Polygon Plane n,
      Function.Injective P ∧
      (∀ i j : Fin n, i ≠ j → P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
        ({P i, P (finRotate n i)} ∩ {P j, P (finRotate n j)} : Set Plane)) ∧
      frontier D = P.boundary ℝ)
    (β : frontier D ≃ₜ sphere (0 : Plane) 1)
    (F : D ≃ₜ closedBall (0 : Plane) 1)
    (hFboundary : ∀ x : D, ‖(F x : Plane)‖ = 1 ↔ (x : Plane) ∉ interior D)
    (hF : ∀ (x : frontier D) (hx : (x : Plane) ∈ D),
      (F ⟨x, hx⟩ : Plane) = (β x : Plane)) :
    ∃ H : Plane ≃ₜ Plane, H '' D = closedBall (0 : Plane) 1 ∧
      ∀ x : frontier D, H x = (β x : Plane) := by
  obtain ⟨R, hR, hRc, hRne, hDR, hrectangle⟩ := enclosing_rectangle D hcompact
  obtain ⟨Φ, hinner, houter⟩ := Topology.cairns_polygonal_annulus_parameterization
    D R hcompact hregular hne hi he hpolygon hrectangle hDR β
  obtain ⟨g, hgi, hgd, hgf⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hRc hRne hR.isBounded
  rw [hR.isClosed.closure_eq] at hgd
  let G : Plane ≃ₜ Plane := g.trans (Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num))
  have hnorm (x : Plane) : ‖G x‖ = 2 * ‖g x‖ := by
    change ‖(2 : ℝ) • g x‖ = _
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hgd' (x : Plane) : x ∈ R ↔ ‖g x‖ ≤ 1 := by
    have hm : x ∈ R ↔ g x ∈ closedBall (0 : Plane) 1 := by
      rw [← hgd]
      exact ⟨fun hx ↦ ⟨x, hx, rfl⟩, fun ⟨y, hy, heq⟩ ↦ g.injective heq ▸ hy⟩
    simpa only [mem_closedBall, dist_zero_right] using hm
  have hgf' (x : Plane) : x ∈ frontier R ↔ ‖g x‖ = 1 := by
    rw [← mem_sphere_zero_iff_norm, ← hgf]
    exact ⟨fun hx ↦ ⟨x, hx, rfl⟩, fun ⟨y, hy, heq⟩ ↦ g.injective heq ▸ hy⟩
  obtain ⟨H, hHD, hHF⟩ := disk_annulus_ambient_extension D R hcompact.isClosed hR.isClosed
    hDR F hFboundary Φ (by
      intro x hxD hxA
      have hxfr : x ∈ frontier D := ⟨subset_closure hxD, hxA.2⟩
      obtain ⟨y, hy, hΦy⟩ := hinner ⟨x, hxfr⟩
      have hy' : y = (⟨x, hxA⟩ : ↥(R \ interior D)) := Subtype.ext hy
      rw [hy'] at hΦy
      exact (hF ⟨x, hxfr⟩ hxD).trans hΦy.symm) houter G (by
      intro x
      rw [mem_closedBall, dist_zero_right, hnorm, hgd']
      constructor <;> intro hx <;> linarith) (by
      intro x
      rw [hgf', hnorm]
      constructor <;> intro hx <;> linarith)
  refine ⟨H, hHD, ?_⟩
  intro x
  have hx : (x : Plane) ∈ D := by
    simpa only [hcompact.isClosed.closure_eq] using x.property.1
  exact (hHF ⟨x, hx⟩).trans (hF x hx)
end HolomorphicAnosov

namespace HolomorphicAnosov
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem polygon_image_linear_isometry {n : ℕ} (q : Polygon ℂ n)
    (e : ℂ ≃ₗᵢ[ℝ] Plane) :
    (Polygon.mk (e ∘ q.vertices)).boundary ℝ = e '' q.boundary ℝ ∧
    ∀ i, (Polygon.mk (e ∘ q.vertices)).edgeSet ℝ i = e '' q.edgeSet ℝ i := by
  have hedge (i : Fin n) :
      (Polygon.mk (e ∘ q.vertices)).edgeSet ℝ i = e '' q.edgeSet ℝ i := by
    simp only [Polygon.edgeSet, affineSegment_eq_segment, Function.comp_apply]
    exact (image_segment ℝ e.toLinearEquiv.toAffineEquiv.toAffineMap (q i)
      (q (finRotate n i))).symm
  refine ⟨?_, hedge⟩
  simp only [Polygon.boundary, hedge, image_iUnion]
end HolomorphicAnosov

namespace HolomorphicAnosov
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The Euclidean polygon disk extension transports to the complex plane with its usual norm and topology.

Source: Cairns (1951), pp.860–861; Hirsch (1976), p.155.

Use the real orthonormal basis (1,i) to identify the complex plane linearly and isometrically with Euclidean two-space. Homeomorphisms preserve compactness, closures, interiors, frontiers and path connectivity. A linear isometry carries each polygon segment to the corresponding segment, and injectivity preserves the simple edge intersection condition. Conjugate the given disk and boundary charts by this isometry, invoke the Euclidean extension, and conjugate its ambient homeomorphism back. Its disk image and boundary restriction become the original literal ones. -/
theorem complex_polygon_disk_ambient_extension {p D : Set ℂ}
    (hcompact : IsCompact D) (hregular : closure (interior D) = D)
    (hne : (interior D).Nonempty) (hi : IsPathConnected (interior D))
    (he : IsPathConnected Dᶜ) (hfront : frontier D = p)
    (hpoly : ∃ (n : ℕ) (q : Polygon ℂ (n + 3)),
      Function.Injective q.vertices ∧ q.HasNondegenerateEdges ∧
      (∀ i j : Fin (n + 3), i ≠ j → q.edgeSet ℝ i ∩ q.edgeSet ℝ j =
        ({q i, q (finRotate (n + 3) i)} : Set ℂ) ∩
        {q j, q (finRotate (n + 3) j)}) ∧ q.boundary ℝ = p)
    (β : p ≃ₜ sphere (0 : ℂ) 1)
    (F : D ≃ₜ closedBall (0 : ℂ) 1)
    (hFboundary : ∀ x : D, ‖(F x : ℂ)‖ = 1 ↔ (x : ℂ) ∉ interior D)
    (hF : ∀ (x : p) (hx : (x : ℂ) ∈ D), (F ⟨x, hx⟩ : ℂ) = (β x : ℂ)) :
    ∃ H : ℂ ≃ₜ ℂ, H '' D = closedBall (0 : ℂ) 1 ∧
      ∀ x : p, H x = (β x : ℂ) := by
  let e := Complex.orthonormalBasisOneI.repr
  let eh := e.toHomeomorph
  let D' : Set Plane := eh '' D
  have hD' : IsCompact D' := hcompact.image eh.continuous
  have hreg' : closure (interior D') = D' := by
    rw [← eh.image_interior, ← eh.image_closure, hregular]
  have hne' : (interior D').Nonempty := by
    rw [← eh.image_interior]
    exact hne.image eh
  have hi' : IsPathConnected (interior D') := by
    rw [← eh.image_interior]
    exact hi.image eh.continuous
  have he' : IsPathConnected D'ᶜ := by
    rw [← eh.image_compl]
    exact he.image eh.continuous
  have hfront' : frontier D' = eh '' p := by rw [← eh.image_frontier, hfront]
  have hpoly' : ∃ n : ℕ, 3 ≤ n ∧ ∃ P : Polygon Plane n,
      Function.Injective P ∧
      (∀ i j : Fin n, i ≠ j → P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
        ({P i, P (finRotate n i)} ∩ {P j, P (finRotate n j)} : Set Plane)) ∧
      frontier D' = P.boundary ℝ := by
    obtain ⟨n, q, hq, _, hs, hqp⟩ := hpoly
    let P : Polygon Plane (n + 3) := ⟨e ∘ q.vertices⟩
    obtain ⟨hPb, hPe⟩ := polygon_image_linear_isometry q e
    refine ⟨n + 3, by omega, P, e.injective.comp hq, ?_, ?_⟩
    · intro i j hij
      change (Polygon.mk (e ∘ q.vertices)).edgeSet ℝ i ∩
        (Polygon.mk (e ∘ q.vertices)).edgeSet ℝ j ⊆ _
      rw [hPe, hPe, ← Set.image_inter e.injective, hs i j hij]
      rintro z ⟨x, hx, rfl⟩
      constructor
      · rcases hx.1 with hx | hx <;> simp_all [P]
      · rcases hx.2 with hx | hx <;> simp_all [P]
    · rw [hfront', ← hqp]
      exact hPb.symm
  let bd : frontier D' ≃ₜ p := (Homeomorph.setCongr hfront').trans (eh.image p).symm
  let ec : sphere (0 : ℂ) 1 ≃ₜ sphere (0 : Plane) 1 :=
    eh.subtype (by intro x; simp [eh])
  let eb : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : Plane) 1 :=
    eh.subtype (by intro x; simp [eh])
  let ed : D ≃ₜ D' := eh.image D
  let β' := bd.trans (β.trans ec)
  let F' := ed.symm.trans (F.trans eb)
  have hF'boundary (x : D') : ‖(F' x : Plane)‖ = 1 ↔ (x : Plane) ∉ interior D' := by
    change ‖e (F (ed.symm x))‖ = 1 ↔ _
    rw [e.norm_map, hFboundary]
    have hx : eh (ed.symm x) = (x : Plane) := congrArg Subtype.val (ed.apply_symm_apply x)
    rw [← eh.image_interior, ← hx]
    simp only [eh.injective.mem_set_image]
  have hF'agree (x : frontier D') (hx : (x : Plane) ∈ D') :
      (F' ⟨x, hx⟩ : Plane) = (β' x : Plane) := by
    change e (F (ed.symm ⟨x, hx⟩)) = e (β (bd x))
    apply congrArg e
    exact hF (bd x) (ed.symm ⟨x, hx⟩).property
  obtain ⟨H', hHD', hH'⟩ := polygon_disk_ambient_extension D' hD' hreg' hne' hi' he'
    hpoly' β' F' hF'boundary hF'agree
  let H := eh.trans (H'.trans eh.symm)
  refine ⟨H, ?_, ?_⟩
  · change (fun x ↦ eh.symm (H' (eh x))) '' D = _
    rw [← image_image eh.symm, ← image_image H' eh, hHD']
    simp [eh]
  · intro x
    have hx : eh x ∈ frontier D' := by rw [hfront']; exact mem_image_of_mem eh x.property
    have h := hH' ⟨eh x, hx⟩
    change H' (eh x) = eh (β (bd ⟨eh x, hx⟩)) at h
    have hbd : bd ⟨eh x, hx⟩ = x := by apply Subtype.ext; exact eh.symm_apply_apply x
    rw [hbd] at h
    change eh.symm (H' (eh x)) = _
    rw [h, eh.symm_apply_apply]
end HolomorphicAnosov

open Set
namespace HolomorphicAnosov

/-- Two open complementary components with a bounded component and common frontier give a compact regular closed bounded region, with the specified interior, exterior and frontier and path-connected interior and exterior.

Source: Cairns (1951), pp.860–861; Hirsch (1976), p.155.

The component-image equality supplies witnesses for each component. Their distinctness follows from one being bounded and the other unbounded. Components meeting at a point coincide, hence these two components are disjoint; every complement point lies in one, so they partition the complement of p. The closure of an open component is its union with its frontier. These two closure identities give D=complement E and interior D=B, as well as frontier D=p and regular closure. The closure of bounded B is compact in the plane. Open connected subsets of the locally path-connected plane are path connected. -/
theorem cairns_polygon_region_geometry {p D B E : Set ℂ}
    (hcomponents : (fun z : ℂ ↦ connectedComponentIn pᶜ z) '' pᶜ = {B, E})
    (hB : IsConnected B) (hE : IsConnected E) (hBo : IsOpen B) (hEo : IsOpen E)
    (hBb : Bornology.IsBounded B) (hEb : ¬ Bornology.IsBounded E)
    (hclosure : closure B = D) (hfrontB : frontier B = p) (hfrontE : frontier E = p) :
    IsCompact D ∧ interior D = B ∧ Dᶜ = E ∧ frontier D = p ∧
      closure (interior D) = D ∧ (interior D).Nonempty ∧
      IsPathConnected (interior D) ∧ IsPathConnected Dᶜ := by
  have hne : B ≠ E := fun h ↦ hEb (h ▸ hBb)
  obtain ⟨b, hb, hbc⟩ : ∃ b ∈ pᶜ, connectedComponentIn pᶜ b = B := by
    have h : B ∈ (fun z : ℂ ↦ connectedComponentIn pᶜ z) '' pᶜ := by
      rw [hcomponents]
      simp
    exact h
  obtain ⟨e, he, hec⟩ : ∃ e ∈ pᶜ, connectedComponentIn pᶜ e = E := by
    have h : E ∈ (fun z : ℂ ↦ connectedComponentIn pᶜ z) '' pᶜ := by
      rw [hcomponents]
      simp
    exact h
  have hBsub : B ⊆ pᶜ := hbc ▸ connectedComponentIn_subset pᶜ b
  have hEsub : E ⊆ pᶜ := hec ▸ connectedComponentIn_subset pᶜ e
  have hdis : Disjoint B E := by
    rw [Set.disjoint_left]
    intro z hzB hzE
    apply hne
    rw [← hbc] at hzB
    rw [← hec] at hzE
    exact hbc.symm.trans ((connectedComponentIn_eq hzB).trans
      ((connectedComponentIn_eq hzE).symm.trans hec))
  have hunion : B ∪ E = pᶜ := by
    apply subset_antisymm (union_subset hBsub hEsub)
    intro z hz
    have h : connectedComponentIn pᶜ z ∈ ({B, E} : Set (Set ℂ)) := by
      rw [← hcomponents]
      exact ⟨z, hz, rfl⟩
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h
    · exact Or.inl (h ▸ mem_connectedComponentIn hz)
    · exact Or.inr (h ▸ mem_connectedComponentIn hz)
  have hclB : closure B = B ∪ p := by rw [closure_eq_self_union_frontier, hfrontB]
  have hclE : closure E = E ∪ p := by rw [closure_eq_self_union_frontier, hfrontE]
  have hDE : D = Eᶜ := by
    rw [← hclosure, hclB]
    ext z
    have hU := Set.ext_iff.mp hunion z
    have hd : z ∈ B → z ∉ E := fun hz ↦ Set.disjoint_left.mp hdis hz
    simp only [mem_union, mem_compl_iff] at *
    tauto
  have hi : interior D = B := by
    rw [hDE, interior_compl, hclE]
    ext z
    have hU := Set.ext_iff.mp hunion z
    have hd : z ∈ B → z ∉ E := fun hz ↦ Set.disjoint_left.mp hdis hz
    simp only [mem_union, mem_compl_iff] at *
    tauto
  refine ⟨hclosure ▸ hBb.isCompact_closure, hi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hDE, compl_compl]
  · rw [hDE, frontier_compl, hfrontE]
  · rw [hi, hclosure]
  · rw [hi]
    exact hB.nonempty
  · rw [hi]
    exact hBo.isConnected_iff_isPathConnected.mp hB
  · rw [hDE, compl_compl]
    exact hEo.isConnected_iff_isPathConnected.mp hE
end HolomorphicAnosov

open Set Metric
namespace HolomorphicAnosov

end HolomorphicAnosov

namespace HolomorphicAnosov

/-- Two bounded cells known to have ambient circle charts, with closures intersecting exactly in a nondegenerate common segment, have a disk chart of their union carrying the outer boundary onto the unit sphere.

Source: Cairns (1951), pp.860–861; Hirsch (1976), p.155.

Obtain the two bounded-cell charts and all prescribed boundary extensions from their supplied ambient circle maps. The common segment is contained in both boundaries and is a proper arc of each, since a circle cannot be homeomorphic to an interval. Apply the existing relative disk-cell gluing theorem using the closedness of the two cell closures. Its outer boundary is the union of the two circles minus the open seam. The segment with its endpoints removed equals that open segment by the affine interval parametrization, so the result is exactly the asserted boundary image. -/
theorem opposite_ambient_cells_disk_chart (c₁ c₂ U₁ U₂ : Set ℂ)
    (H₁ H₂ : ℂ ≃ₜ ℂ) (hH₁ : H₁ '' c₁ = sphere (0 : ℂ) 1)
    (hH₂ : H₂ '' c₂ = sphere (0 : ℂ) 1)
    (u₁ u₂ : ℂ) (hu₁ : u₁ ∉ c₁) (hu₂ : u₂ ∉ c₂)
    (hU₁ : U₁ = connectedComponentIn c₁ᶜ u₁)
    (hU₂ : U₂ = connectedComponentIn c₂ᶜ u₂)
    (hb₁ : Bornology.IsBounded U₁) (hb₂ : Bornology.IsBounded U₂)
    (a b : ℂ) (hab : a ≠ b)
    (hcinter : c₁ ∩ c₂ = segment ℝ a b)
    (hUinter : closure U₁ ∩ closure U₂ = segment ℝ a b) :
    ∃ F : ↥(closure U₁ ∪ closure U₂) ≃ₜ closedBall (0 : ℂ) 1,
      F '' {x | (x : ℂ) ∈ (c₁ ∪ c₂) \ openSegment ℝ a b} =
        {x : closedBall (0 : ℂ) 1 | (x : ℂ) ∈ sphere (0 : ℂ) 1} := by
  obtain ⟨hc₁, hcell₁, hext₁⟩ := ambientCircle_bounded_cell c₁ U₁ H₁ hH₁ u₁ hu₁ hU₁ hb₁
  obtain ⟨hc₂, hcell₂, hext₂⟩ := ambientCircle_bounded_cell c₂ U₂ H₂ hH₂ u₂ hu₂ hU₂ hb₂
  have hs₁ : segment ℝ a b ⊆ c₁ := by rw [← hcinter]; exact inter_subset_left
  have hs₂ : segment ℝ a b ⊆ c₂ := by rw [← hcinter]; exact inter_subset_right
  have cell_ambient (U c : Set ℂ)
      (hc : ∃ F : closure U ≃ₜ closedBall (0 : ℂ) 1,
        F '' {x : closure U | (x : ℂ) ∈ U} =
          {x : closedBall (0 : ℂ) 1 | (x : ℂ) ∈ ball (0 : ℂ) 1} ∧
        F '' {x : closure U | (x : ℂ) ∈ c} =
          {x : closedBall (0 : ℂ) 1 | (x : ℂ) ∈ sphere (0 : ℂ) 1}) :
      ∃ F : closure U ≃ₜ closedBall (0 : ℂ) 1,
        Subtype.val '' F '' {x : closure U | (x : ℂ) ∈ U} = ball (0 : ℂ) 1 ∧
        Subtype.val '' F '' {x : closure U | (x : ℂ) ∈ c} = sphere (0 : ℂ) 1 := by
    obtain ⟨F, hi, hb⟩ := hc
    refine ⟨F, ?_, ?_⟩
    · rw [hi]
      exact Subtype.image_preimage_coe _ _ |>.trans (inter_eq_right.mpr ball_subset_closedBall)
    · rw [hb]
      exact Subtype.image_preimage_coe _ _ |>.trans (inter_eq_right.mpr sphere_subset_closedBall)
  obtain ⟨F, hFi, hFb⟩ := Topology.cairns_disk_cell_relative_chart U₁ U₂ c₁ c₂
    (segment ℝ a b) a b hc₁ hc₂ (cell_ambient U₁ c₁ hcell₁) (cell_ambient U₂ c₂ hcell₂) hext₁ hext₂ hab
    (segment_embedded_arc a b hab)
    ⟨hs₁, segment_ne_ambient_circle c₁ H₁ hH₁ a b hab hs₁⟩
    ⟨hs₂, segment_ne_ambient_circle c₂ H₂ hH₂ a b hab hs₂⟩
    hcinter hUinter (isClosed_closure.union isClosed_closure)
  have hseg : segment ℝ a b \ {a, b} = openSegment ℝ a b := by
    ext x
    constructor
    · rintro ⟨hx, hxe⟩
      exact mem_openSegment_of_ne_left_right
        (fun h ↦ hxe (Or.inl h.symm)) (fun h ↦ hxe (Or.inr h.symm)) hx
    · intro hx
      refine ⟨openSegment_subset_segment ℝ _ _ hx, ?_⟩
      rintro (rfl | h)
      · exact hab (left_mem_openSegment_iff.mp hx)
      · subst x
        exact hab (right_mem_openSegment_iff.mp hx)
  refine ⟨F, ?_⟩
  simpa only [hseg] using hFb
end HolomorphicAnosov
namespace HolomorphicAnosov
/-- Cairns' final bounded-cell and exterior-annulus pasting step.

Source: Cairns (1951), preliminary 2(A,B), pp.860–861, expanded by the explicit
radial extension from Hirsch (1976), p.155. This auxiliary consumes the disk
chart of the bounded cell, as the finite two-cell caller constructs it. The
previous interface omitted this input although its natural-language proof
already used the bounded-cell map. The caller now supplies that map using
`opposite_ambient_cells_disk_chart`; its public statement is unchanged.

Obtain compactness, regular closure, interior and exterior path connectivity
from the stated two-component data. Correct the given disk chart to the
prescribed boundary values by radial circle extension. Transport to the
Euclidean plane, choose a surrounding rectangle, and apply the polygonal
annulus parameterization with this same inner boundary. Glue disk and annulus
on their common boundary, obtaining a rectangle chart to the radius-two disk.
Conjugate by the convex rectangle's ambient gauge chart; the resulting disk
self-homeomorphism preserves its sphere and extends radially outside it.
Conjugating back gives the ambient map with the required disk image and
literal prescribed boundary values. All new pasting steps are proved here;
existing annulus and cell-chart prerequisites remain their owners' work. -/
theorem cairns_polygon_ambient_extension
    {p D : Set ℂ}
    (hpoly : ∃ (n : ℕ) (q : Polygon ℂ (n + 3)),
      Function.Injective q.vertices ∧ q.HasNondegenerateEdges ∧
      (∀ i j : Fin (n + 3), i ≠ j →
        q.edgeSet ℝ i ∩ q.edgeSet ℝ j =
          ({q i, q (finRotate (n + 3) i)} : Set ℂ) ∩
          {q j, q (finRotate (n + 3) j)}) ∧ q.boundary ℝ = p)
    (hregions : ∃ B E : Set ℂ,
      (fun z : ℂ ↦ connectedComponentIn pᶜ z) '' pᶜ = {B, E} ∧
      IsConnected B ∧ IsConnected E ∧ IsOpen B ∧ IsOpen E ∧
      Bornology.IsBounded B ∧ ¬ Bornology.IsBounded E ∧
      closure B = D ∧ frontier B = p ∧ frontier E = p)
    (hcell : ∃ F : D ≃ₜ Metric.closedBall (0 : ℂ) 1,
      F '' {x : D | (x : ℂ) ∈ p} =
        {x : Metric.closedBall (0 : ℂ) 1 | (x : ℂ) ∈ Metric.sphere (0 : ℂ) 1})
    (β : p ≃ₜ Metric.sphere (0 : ℂ) 1) :
    ∃ H : ℂ ≃ₜ ℂ, H '' D = Metric.closedBall (0 : ℂ) 1 ∧
      ∀ z : p, H z = (β z : ℂ) := by
  obtain ⟨B, E, hcomponents, hB, hE, hBo, hEo, hBb, hEb, hclosure, hfrontB, hfrontE⟩ :=
    hregions
  obtain ⟨hcompact, hi, he, hfront, hregular, hne, hpath, hepath⟩ :=
    cairns_polygon_region_geometry hcomponents hB hE hBo hEo hBb hEb hclosure hfrontB hfrontE
  obtain ⟨F₀, hF₀⟩ := hcell
  have hpD : p ⊆ D := by
    rw [← hfrontB, ← hclosure]
    exact frontier_subset_closure
  have hF₀iff (x : D) : (x : ℂ) ∈ p ↔ ‖(F₀ x : ℂ)‖ = 1 := by
    have hm : (x : ℂ) ∈ p ↔ (F₀ x : ℂ) ∈ sphere (0 : ℂ) 1 := by
      rw [← show F₀ x ∈ F₀ '' {x : D | (x : ℂ) ∈ p} ↔
          (F₀ x : ℂ) ∈ sphere (0 : ℂ) 1 from by rw [hF₀]; rfl]
      exact ⟨fun hx ↦ ⟨x, hx, rfl⟩,
        fun ⟨y, hy, hxy⟩ ↦ F₀.injective hxy ▸ hy⟩
    simpa only [mem_sphere_zero_iff_norm] using hm
  obtain ⟨F, hF⟩ := disk_prescribed_boundary_extension p D hpD F₀ hF₀iff β
  have hFiff (x : D) : ‖(F x : ℂ)‖ = 1 ↔ (x : ℂ) ∈ p := by
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := β.surjective ⟨F x, mem_sphere_zero_iff_norm.mpr hx⟩
      have hf : F ⟨y, hpD y.property⟩ = F x :=
        Subtype.ext ((hF y (hpD y.property)).trans (congrArg Subtype.val hy))
      exact congrArg Subtype.val (F.injective hf) ▸ y.property
    · intro hx
      rw [hF ⟨x, hx⟩ x.property]
      exact mem_sphere_zero_iff_norm.mp (β ⟨x, hx⟩).property
  apply complex_polygon_disk_ambient_extension hcompact hregular hne hpath hepath hfront
    hpoly β F ?_ hF
  intro x
  rw [hFiff, ← hfront]
  exact ⟨fun hx ↦ hx.2, fun hx ↦ ⟨subset_closure x.property, hx⟩⟩

end HolomorphicAnosov
