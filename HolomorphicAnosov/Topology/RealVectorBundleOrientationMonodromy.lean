import HolomorphicAnosov.Topology.OrientationBundle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Orientation covering and monodromy of a finite-rank real vector bundle

DAG node `topo.real_vector_bundle_orientation_monodromy_g9`.
Sources: Hatcher, *Vector Bundles and K-Theory*, version 2.2 (November 2017),
Lemma 1.1 p. 8, Proposition 1.5 pp. 18–19, and orientation convention p. 25;
Hatcher, *Algebraic Topology*, Propositions 1.30–1.31/1.33 pp. 60–62 and
monodromy p. 69; pinned Mathlib Orientation, VectorBundle.Basic, and the
covering/path-lifting APIs cited in the node.

The fibre carrier is the actual ordered-basis quotient. Equality of the
basis orientations is exactly positive determinant by Mathlib's
`Module.Basis.orientation_eq_iff_det_pos`. This convention has ONE rank-zero
class, rather than the two rays of the unmodified empty-index Orientation type.
The total topology is defined using every original continuous linear chart,
not a chosen global frame or an assumed orientation-cover structure.
-/

namespace HolomorphicAnosov

noncomputable section

open Bundle Topology

namespace OrientationMonodromyProof

variable {d : ℕ} {V W Z : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  [AddCommGroup Z] [Module ℝ Z]

/-- Mapping actual ordered bases through successive fibre isomorphisms composes.
Source: Mathlib Basis.map and quotient induction. -/
theorem map_comp (L : V ≃ₗ[ℝ] W) (K : W ≃ₗ[ℝ] Z)
    (o : RealBasisOrientation d V) :
    realOrientationMap K (realOrientationMap L o) = realOrientationMap (L.trans K) o := by
  induction o using Quotient.inductionOn with
  | h b =>
    change Quotient.mk _ ((b.map L).map K) = Quotient.mk _ (b.map (L.trans K))
    congr 1

/-- Identity transport fixes every actual ordered-basis class. -/
theorem map_id (o : RealBasisOrientation d V) :
    realOrientationMap (LinearEquiv.refl ℝ V) o = o := by
  induction o using Quotient.inductionOn with
  | h b =>
    change Quotient.mk _ (b.map (LinearEquiv.refl ℝ V)) = Quotient.mk _ b
    congr 1

/-- Transport by an actual fibre isomorphism is an equivalence of quotient classes. -/
def orientationEquiv (L : V ≃ₗ[ℝ] W) :
    RealBasisOrientation d V ≃ RealBasisOrientation d W where
  toFun := realOrientationMap L
  invFun := realOrientationMap L.symm
  left_inv o := by simpa only [map_comp, LinearEquiv.self_trans_symm] using map_id o
  right_inv o := by simpa only [map_comp, LinearEquiv.symm_trans_self] using map_id o

/-- Empty ordered bases form a singleton, even though the full empty-index ray
type has two signs. Source: the ordered-basis convention of Hatcher p.25. -/
theorem zero_orientation_subsingleton : Subsingleton (RealBasisOrientation 0 V) := by
  refine ⟨fun o q ↦ ?_⟩
  induction o using Quotient.inductionOn with
  | h b =>
    induction q using Quotient.inductionOn with
    | h c =>
      have h : b = c := by ext i; exact Fin.elim0 i
      exact congrArg (Quotient.mk _) h

/-- The ordered-basis quotient embeds into Mathlib's orientation rays with
exactly the defining equality kernel. This also holds at rank zero. -/
def orientationRay (o : RealBasisOrientation d V) : Orientation ℝ V (Fin d) :=
  Quotient.lift Module.Basis.orientation (fun _ _ h ↦ h) o

theorem orientationRay_injective : Function.Injective (orientationRay (d := d) (V := V)) := by
  intro o q
  induction o using Quotient.inductionOn with
  | h b =>
    induction q using Quotient.inductionOn with
    | h c =>
      intro h
      exact Quotient.sound h

/-- Positive-rank ordered bases represent both and only the two orientation rays.
Source: Mathlib Basis.orientation_eq_or_eq_neg and adjustToOrientation. -/
def orientationBoolEquiv (hd : 0 < d) (b : Module.Basis (Fin d) ℝ V) :
    RealBasisOrientation d V ≃ Bool := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let label : RealBasisOrientation d V → Bool := fun o ↦
    decide (orientationRay o = b.orientation)
  apply Equiv.ofBijective label
  constructor
  · intro o q heq
    apply orientationRay_injective
    have he : (orientationRay o = b.orientation) ↔ (orientationRay q = b.orientation) :=
      by simpa only [label, decide_eq_decide] using heq
    rcases b.orientation_eq_or_eq_neg (orientationRay o) with ho | ho
    · exact ho.trans (he.mp ho).symm
    · by_cases hp : orientationRay q = b.orientation
      · exact (Module.Ray.ne_neg_self b.orientation ((he.mpr hp).symm.trans ho)).elim
      · exact ho.trans ((b.orientation_ne_iff_eq_neg (orientationRay q)).mp hp).symm
  · intro q
    cases q
    · refine ⟨Quotient.mk _ (b.adjustToOrientation (-b.orientation)), ?_⟩
      simp [label, orientationRay, Module.Basis.orientation_adjustToOrientation,
        (Module.Ray.ne_neg_self b.orientation).symm]
    · exact ⟨Quotient.mk _ b, by simp [label, orientationRay]⟩

/-- Comparison is unchanged by genuine source and receiving fibre coordinates.
Source: functoriality of Basis.map and injectivity of quotient transport. -/
theorem comparison_conjugate (A : V ≃ₗ[ℝ] Z) (C : W ≃ₗ[ℝ] Z)
    (L : V ≃ₗ[ℝ] W) (o : RealBasisOrientation d V) (q : RealBasisOrientation d W) :
    realOrientationComparison d (A.symm.trans (L.trans C))
      (realOrientationMap A o) (realOrientationMap C q) =
        realOrientationComparison d L o q := by
  classical
  have heq : realOrientationMap (A.symm.trans (L.trans C)) (realOrientationMap A o) =
      realOrientationMap C (realOrientationMap L o) := by
    rw [map_comp, map_comp]
    congr 1
    ext v
    simp
  unfold realOrientationComparison
  rw [heq]
  have hinj : Function.Injective (realOrientationMap (d := d) C) :=
    (orientationEquiv C).injective
  simp only [hinj.eq_iff]

/-- A continuous family of invertible model maps acts continuously on the
DISCRETE ordered-basis classes. Positivity of the determinant relative to the
basis at the given point supplies a neighbourhood with the same class. -/
theorem map_family_continuous {X : Type*} [TopologicalSpace X]
    (L : X → (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ))
    (hL : ∀ v, Continuous (fun x ↦ L x v)) :
    Continuous (fun z : X × RealBasisOrientation d (Fin d → ℝ) ↦
      realOrientationMap (L z.1) z.2) := by
  classical
  let : DiscreteTopology (RealBasisOrientation d (Fin d → ℝ)) := ⟨rfl⟩
  apply continuous_prod_of_discrete_right.mpr
  intro o
  induction o using Quotient.inductionOn with
  | h b =>
    apply continuous_iff_continuousAt.mpr
    intro x
    let ref := b.map (L x)
    have hmat : Continuous (fun y ↦ ref.toMatrix (b.map (L y))) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      simp only [Module.Basis.toMatrix_apply, Module.Basis.map_apply]
      exact (continuous_apply i).comp (ref.equivFunL.continuous.comp (hL (b j)))
    have hdet : Continuous (fun y ↦ ref.det (b.map (L y))) := by
      simpa only [Module.Basis.det_apply] using hmat.matrix_det
    have hpos : ∀ᶠ y in nhds x, 0 < ref.det (b.map (L y)) :=
      hdet.continuousAt.eventually_mem
        (IsOpen.mem_nhds isOpen_Ioi (by
          change 0 < ref.det ref
          rw [Module.Basis.det_self]
          norm_num))
    exact continuousAt_const.congr (hpos.mono (fun y hy ↦ by
      apply Quotient.sound
      exact (ref.orientation_eq_iff_det_pos (b.map (L y))).mpr hy))

section GenericTwoSheet
open Set Filter _root_.Topology
open scoped unitInterval
/-- A permutation of the genuine two-point carrier is identity or transposition. -/
theorem bool_perm_cases (perm : Equiv.Perm Bool) :
    perm = 1 ∨ perm = Equiv.swap false true := by
  have hi := perm.injective
  cases hf : perm false <;> cases ht : perm true
  · have := hi (hf.trans ht.symm)
    cases this
  · left
    ext b
    cases b <;> simp [hf, ht]
  · right
    ext b
    cases b <;> simp [hf, ht]
  · have := hi (hf.trans ht.symm)
    cases this

/-- On two points, a fixed point is equivalent to sign +1. -/
theorem bool_sign_eq_one_iff (perm : Equiv.Perm Bool) (b : Bool) :
    Equiv.Perm.sign perm = 1 ↔ perm b = b := by
  rcases bool_perm_cases perm with rfl | rfl
  · simp
  · rw [Equiv.Perm.sign_swap (by decide)]
    cases b <;> norm_num


variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : Y → X) (hp : IsCoveringMap p) (x₀ : X)

/-- The sign of the genuine endpoint permutation, transported to a two-point fibre. -/
def twoSheetSign (e : (p ⁻¹' {x₀}) ≃ Bool) : FundamentalGroup X x₀ →* ℤˣ :=
  Equiv.Perm.sign.comp (((Equiv.permCongrHom e).toMonoidHom).comp (hp.monodromyPerm x₀))

/-- Sign +1 is exactly the identity endpoint at ANY original fibre point. -/
theorem sign_one_iff_fixed (e : (p ⁻¹' {x₀}) ≃ Bool)
    (g : FundamentalGroup X x₀) (y : p ⁻¹' {x₀}) :
    twoSheetSign p hp x₀ e g = 1 ↔ hp.monodromy g y = y := by
  have h := bool_sign_eq_one_iff (e.permCongr (hp.monodromyPerm x₀ g)) (e y)
  change Equiv.Perm.sign (e.permCongr (hp.monodromyPerm x₀ g)) = 1 ↔ _
  simpa only [twoSheetSign, MonoidHom.comp_apply,
    Equiv.permCongr_apply, e.symm_apply_apply, e.injective.eq_iff,
    IsCoveringMap.coe_monodromyPerm] using h

/-- Actual continuous loop lifts exist from every point; uniqueness identifies
EVERY supplied lift with the monodromy endpoint and hence the sign criterion. -/
theorem loop_lift_endpoint_law (e : (p ⁻¹' {x₀}) ≃ Bool)
    (γ : Path x₀ x₀) (y₀ : Y) (hy : p y₀ = x₀) :
    (∃ lift : C(unitInterval, Y), (∀ t, p (lift t) = γ t) ∧ lift 0 = y₀) ∧
    ∀ lift : C(unitInterval, Y), (∀ t, p (lift t) = γ t) → lift 0 = y₀ →
      (lift 1 = y₀ ↔ twoSheetSign p hp x₀ e (FundamentalGroup.fromPath ⟦γ⟧) = 1) := by
  have hstart : γ 0 = p y₀ := γ.source.trans hy.symm
  obtain ⟨lift, hl, h0⟩ := hp.exists_path_lifts γ y₀ hstart
  refine ⟨⟨lift, fun t ↦ congrFun hl t, h0⟩, ?_⟩
  intro lift hl h0
  have hEq : lift = hp.liftPath γ y₀ hstart :=
    (hp.eq_liftPath_iff' hstart).mpr ⟨funext hl, h0⟩
  rw [hEq]
  have hfix := sign_one_iff_fixed p hp x₀ e (FundamentalGroup.fromPath ⟦γ⟧) ⟨y₀, hy⟩
  simpa only [IsCoveringMap.monodromy, Quotient.lift_mk, Subtype.mk.injEq,
    Subtype.ext_iff] using hfix.symm

/-- If the actual endpoint transport fixes a selected point, the loop class lies
in the image of the fundamental group of the covering space at that point. -/
theorem fixed_monodromy_mem_range (y₀ : Y) (hy : p y₀ = x₀)
    (g : FundamentalGroup X x₀) (hg : hp.monodromy g ⟨y₀, hy⟩ = ⟨y₀, hy⟩) :
    g ∈ (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hy).range := by
  obtain ⟨γ⟩ := g
  let lift := hp.liftPath γ y₀ (γ.source.trans hy.symm)
  have h1 : lift 1 = y₀ := by
    simpa only [IsCoveringMap.monodromy, Quotient.lift_mk, Subtype.ext_iff] using hg
  let Γ : Path y₀ y₀ := ⟨lift, hp.liftPath_zero .., h1⟩
  refine ⟨FundamentalGroup.fromPath ⟦Γ⟧, ?_⟩
  change FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hy
    (Path.Homotopic.Quotient.mk Γ) = Path.Homotopic.Quotient.mk γ
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact congrFun (hp.liftPath_lifts γ y₀ (γ.source.trans hy.symm)) t

/-- Trivial two-sheet monodromy supplies an actual continuous section by the
covering-map lifting criterion applied to the identity map of the base. -/
theorem section_of_trivial_sign [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    (e : (p ⁻¹' {x₀}) ≃ Bool) (hw : ∀ g, twoSheetSign p hp x₀ e g = 1) :
    ∃ s : X → Y, Continuous s ∧ ∀ x, p (s x) = x := by
  let y₀ := e.symm false
  have hrange : (FundamentalGroup.map (ContinuousMap.id X) x₀).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ y₀.property).range := by
    intro g _
    exact fixed_monodromy_mem_range p hp x₀ y₀.val y₀.property g
      ((sign_one_iff_fixed p hp x₀ e g y₀).mp (hw g))
  obtain ⟨s, ⟨_, hs⟩, _⟩ := hp.existsUnique_continuousMap_lifts_of_range_le
    (f := ContinuousMap.id X) y₀.property hrange
  exact ⟨s, s.continuous, fun x ↦ congrFun hs x⟩

/-- A section makes every loop lift close from its selected point. On a two-point
fibre this forces the whole endpoint permutation to be identity. -/
theorem trivial_sign_of_section (e : (p ⁻¹' {x₀}) ≃ Bool)
    (s : X → Y) (hs : Continuous s) (hps : ∀ x, p (s x) = x) :
    ∀ g, twoSheetSign p hp x₀ e g = 1 := by
  intro g
  obtain ⟨γ⟩ := g
  let lift : C(unitInterval, Y) := ⟨s ∘ γ, hs.comp γ.continuous⟩
  have h0 : lift 0 = s x₀ := by simp [lift, γ.source]
  have h1 : lift 1 = s x₀ := by simp [lift, γ.target]
  exact ((loop_lift_endpoint_law p hp x₀ e γ (s x₀) (hps x₀)).2 lift
    (fun t ↦ hps (γ t)) h0).mp h1

include hp in
/-- Full two-sheet monodromy kernel for the actual covering projection.
Only connectedness and local path connectedness of the base are required;
the total space need not be connected. The loop endpoint law is quantified
over every original fibre point and every actual continuous lift. -/
theorem two_sheet_monodromy [ConnectedSpace X] [LocallyPathConnectedSpace X]
    (hf : ∀ x, Nonempty ({y : Y // p y = x} ≃ Bool)) :
    ∃ w : FundamentalGroup X x₀ →* ℤˣ,
      (∀ (γ : Path x₀ x₀) (y₀ : Y), p y₀ = x₀ →
        (∃ lift : C(unitInterval, Y), (∀ t, p (lift t) = γ t) ∧ lift 0 = y₀) ∧
        ∀ lift : C(unitInterval, Y), (∀ t, p (lift t) = γ t) → lift 0 = y₀ →
          (lift 1 = y₀ ↔ w (FundamentalGroup.fromPath ⟦γ⟧) = 1)) ∧
      ((∀ g, w g = 1) ↔ ∃ s : X → Y, Continuous s ∧ ∀ x, p (s x) = x) ∧
      (SimplyConnectedSpace X → ∃ s : X → Y, Continuous s ∧ ∀ x, p (s x) = x) := by
  classical
  let : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  let e : (p ⁻¹' {x₀}) ≃ Bool := (hf x₀).some
  refine ⟨twoSheetSign p hp x₀ e, ?_, ?_, ?_⟩
  · intro γ y₀ hy
    exact loop_lift_endpoint_law p hp x₀ e γ y₀ hy
  · constructor
    · exact section_of_trivial_sign p hp x₀ e
    · rintro ⟨s, hs, hps⟩
      exact trivial_sign_of_section p hp x₀ e s hs hps
  · intro hsc
    let := hsc
    apply section_of_trivial_sign p hp x₀ e
    intro g
    rw [Subsingleton.elim g 1, map_one]


end GenericTwoSheet
end OrientationMonodromyProof

variable {B : Type*} [TopologicalSpace B] (d : ℕ) (E : B → Type*)
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
variable [∀ b, TopologicalSpace (E b)]
variable [TopologicalSpace (Bundle.TotalSpace (Fin d → ℝ) E)]

namespace OrientationMonodromyProof

omit [∀ b, TopologicalSpace (E b)] in
/-- Every mixed original linear chart transition is continuous on its genuine overlap
when evaluated on a fixed model vector. Source: composition of the two actual
partial homeomorphisms, without an atlas-membership premise. -/
theorem coordChange_apply_continuous
    (e e' : Trivialization (Fin d → ℝ) (Bundle.TotalSpace.proj :
      Bundle.TotalSpace (Fin d → ℝ) E → B)) [e.IsLinear ℝ] [e'.IsLinear ℝ]
    (v : Fin d → ℝ) :
    Continuous (fun x : ↥(e.baseSet ∩ e'.baseSet) ↦ e.coordChangeL ℝ e' x.val v) := by
  have hi : Continuous (fun x : ↥(e.baseSet ∩ e'.baseSet) ↦
      e.toOpenPartialHomeomorph.symm (x.val, v)) :=
    e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      (continuous_subtype_val.prodMk continuous_const)
      (fun x ↦ by rw [e.target_eq]; exact ⟨x.property.1, Set.mem_univ _⟩)
  have h := e'.continuousOn.comp_continuous hi (fun x ↦ by
    rw [e'.source_eq]
    simpa only [Set.mem_preimage, e.symm_coe_proj x.property.1] using x.property.2)
  have h' := continuous_snd.comp h
  exact h'.congr (fun x ↦ (e.coordChangeL_apply' e' x.property v).symm)

omit [∀ b, TopologicalSpace (E b)] in
/-- Every original inverse chart is continuous in the exact all-chart final topology.
Source: the defining supremum of coinduced topologies. -/
theorem chartInverse_continuous
    (e : Trivialization (Fin d → ℝ) (Bundle.TotalSpace.proj :
      Bundle.TotalSpace (Fin d → ℝ) E → B)) [he : e.IsLinear ℝ] :
    letI := realOrientationTopology d E
    Continuous (realOrientationChartInverse d E e) := by
  apply continuous_iff_coinduced_le.mpr
  exact le_iSup_of_le e (le_iSup_of_le he le_rfl)

omit [∀ b, TopologicalSpace (E b)] in
/-- The original-base projection is continuous; each defining inverse chart has
literal first coordinate equal to its original base point. -/
theorem projection_continuous :
    letI := realOrientationTopology d E
    Continuous (Sigma.fst : RealOrientationTotal d E → B) := by
  apply continuous_iSup_dom.mpr
  intro e
  apply continuous_iSup_dom.mpr
  intro he
  let := he
  apply continuous_coinduced_dom.mpr
  exact continuous_subtype_val.comp continuous_fst

/-- The actual ordered-basis coordinate equivalence over a single original chart. -/
def chartEquiv
    (e : Trivialization (Fin d → ℝ) (Bundle.TotalSpace.proj :
      Bundle.TotalSpace (Fin d → ℝ) E → B)) [e.IsLinear ℝ] :
    {z : RealOrientationTotal d E // z.fst ∈ e.baseSet} ≃
      e.baseSet × RealBasisOrientation d (Fin d → ℝ) where
  toFun z := (⟨z.val.fst, z.property⟩,
    realOrientationMap (e.linearEquivAt ℝ z.val.fst z.property) z.val.snd)
  invFun z := ⟨realOrientationChartInverse d E e z, z.1.property⟩
  left_inv z := by
    apply Subtype.ext
    change (⟨z.val.fst, realOrientationMap _ (realOrientationMap _ z.val.snd)⟩ :
      RealOrientationTotal d E) = z.val
    rw [map_comp, LinearEquiv.self_trans_symm, map_id]
  right_inv z := by
    apply Prod.ext
    · rfl
    · dsimp only [realOrientationChartInverse]
      exact (orientationEquiv (e.linearEquivAt ℝ z.1.val z.1.property)).apply_symm_apply z.2

omit [∀ b, TopologicalSpace (E b)] in
/-- On a genuine common chart domain, forward coordinates of another inverse
chart are continuous in the original base and discrete orientation label. -/
theorem chart_transition_continuous
    (e e' : Trivialization (Fin d → ℝ) (Bundle.TotalSpace.proj :
      Bundle.TotalSpace (Fin d → ℝ) E → B)) [e.IsLinear ℝ] [e'.IsLinear ℝ] :
    Continuous (fun z : ↥(e'.baseSet ∩ e.baseSet) ×
        RealBasisOrientation d (Fin d → ℝ) ↦
      (⟨z.1.val, z.1.property.2⟩,
        realOrientationMap (e'.coordChangeL ℝ e z.1.val).toLinearEquiv z.2) :
        ↥(e'.baseSet ∩ e.baseSet) × RealBasisOrientation d (Fin d → ℝ) →
          e.baseSet × RealBasisOrientation d (Fin d → ℝ)) := by
  exact (continuous_subtype_val.comp continuous_fst).subtype_mk _ |>.prodMk
    (map_family_continuous (fun x : ↥(e'.baseSet ∩ e.baseSet) ↦
      (e'.coordChangeL ℝ e x.val).toLinearEquiv)
      (fun v ↦ coordChange_apply_continuous d E e' e v))

omit [∀ b, TopologicalSpace (E b)] in
/-- Each original inverse orientation chart is open for the all-chart final
topology. Pulling its image back through any other chart gives the preimage of
an open set by the continuous overlap transition, extended from the open overlap. -/
theorem chartInverse_isOpenMap
    (e : Trivialization (Fin d → ℝ) (Bundle.TotalSpace.proj :
      Bundle.TotalSpace (Fin d → ℝ) E → B)) [e.IsLinear ℝ] :
    letI := realOrientationTopology d E
    IsOpenMap (realOrientationChartInverse d E e) := by
  classical
  let := realOrientationTopology d E
  intro s hs
  apply isOpen_iSup_iff.mpr
  intro e'
  apply isOpen_iSup_iff.mpr
  intro he'
  let := he'
  apply isOpen_coinduced.mpr
  let D : Set (e'.baseSet × RealBasisOrientation d (Fin d → ℝ)) :=
    {z | z.1.val ∈ e.baseSet}
  have hD : IsOpen D := e.open_baseSet.preimage
    (continuous_subtype_val.comp continuous_fst)
  let g : D → e.baseSet × RealBasisOrientation d (Fin d → ℝ) := fun z ↦
    chartEquiv d E e ⟨realOrientationChartInverse d E e' z.val, z.property⟩
  have hg : Continuous g := by
    have ht := chart_transition_continuous d E e e'
    have hc : Continuous (fun z : D ↦
        (⟨z.val.1.val, z.val.1.property, z.property⟩,
          z.val.2) : D → ↥(e'.baseSet ∩ e.baseSet) ×
            RealBasisOrientation d (Fin d → ℝ)) :=
      ((continuous_subtype_val.comp continuous_fst).comp continuous_subtype_val).subtype_mk _
        |>.prodMk (continuous_snd.comp continuous_subtype_val)
    apply (ht.comp hc).congr
    intro z
    apply Prod.ext
    · rfl
    · change realOrientationMap (e'.coordChangeL ℝ e z.val.1.val).toLinearEquiv z.val.2 =
        realOrientationMap (e.linearEquivAt ℝ z.val.1.val z.property)
          (realOrientationMap (e'.linearEquivAt ℝ z.val.1.val z.val.1.property).symm z.val.2)
      rw [map_comp, e'.coe_coordChangeL' e ⟨z.val.1.property, z.property⟩]
  have hpre : realOrientationChartInverse d E e' ⁻¹'
      (realOrientationChartInverse d E e '' s) = Subtype.val '' (g ⁻¹' s) := by
    ext z
    constructor
    · rintro ⟨y, hy, heq⟩
      have hz : z ∈ D := by
        have hb := congrArg Sigma.fst heq
        change y.1.val = z.1.val at hb
        change z.1.val ∈ e.baseSet
        rw [← hb]
        exact y.1.property
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      have hval : (chartEquiv d E e).symm y =
          ⟨realOrientationChartInverse d E e' z, hz⟩ := Subtype.ext heq
      have hgy : g ⟨z, hz⟩ = y := by
        change (chartEquiv d E e) _ = y
        rw [← hval, Equiv.apply_symm_apply]
      simpa only [Set.mem_preimage, hgy] using hy
    · rintro ⟨z, hz, rfl⟩
      refine ⟨g z, hz, ?_⟩
      exact congrArg Subtype.val ((chartEquiv d E e).symm_apply_apply
        ⟨realOrientationChartInverse d E e' z.val, z.property⟩)
  rw [hpre]
  exact hD.isOpenMap_subtype_val _ (hs.preimage hg)

omit [∀ b, TopologicalSpace (E b)] in
/-- Each native inverse chart is a homeomorphism onto the full preimage of its
original open base domain, in the stipulated all-chart orientation topology. -/
def chartHomeomorph
    (e : Trivialization (Fin d → ℝ) (Bundle.TotalSpace.proj :
      Bundle.TotalSpace (Fin d → ℝ) E → B)) [e.IsLinear ℝ] :
    letI := realOrientationTopology d E
    {z : RealOrientationTotal d E // z.fst ∈ e.baseSet} ≃ₜ
      e.baseSet × RealBasisOrientation d (Fin d → ℝ) := by
  letI := realOrientationTopology d E
  exact ((chartEquiv d E e).symm.toHomeomorphOfContinuousOpen
    ((chartInverse_continuous d E e).subtype_mk _)
    ((chartInverse_isOpenMap d E e).subtype_mk _)).symm

/-- The native projection is a covering in every rank. Rank zero has one sheet;
positive rank has two by the separately proved quotient classification. -/
theorem projection_isCoveringMap
    [FiberBundle (Fin d → ℝ) E] [VectorBundle ℝ (Fin d → ℝ) E] :
    letI := realOrientationTopology d E
    IsCoveringMap (Sigma.fst : RealOrientationTotal d E → B) := by
  let := realOrientationTopology d E
  let : DiscreteTopology (RealBasisOrientation d (Fin d → ℝ)) := ⟨rfl⟩
  intro b
  let e := trivializationAt (Fin d → ℝ) E b
  have he : IsEvenlyCovered (Sigma.fst : RealOrientationTotal d E → B) b
      (RealBasisOrientation d (Fin d → ℝ)) :=
    ⟨inferInstance, e.baseSet, mem_baseSet_trivializationAt (Fin d → ℝ) E b,
      e.open_baseSet, e.open_baseSet.preimage (projection_continuous d E),
      chartHomeomorph d E e, fun _ ↦ rfl⟩
  exact he.to_isEvenlyCovered_preimage

/-- The literal fibre over b identifies with its original ordered-basis quotient.
This equivalence uses dependent equality, not an alternate total-space carrier. -/
def fibreEquiv (b : B) :
    {z : RealOrientationTotal d E // z.fst = b} ≃ RealBasisOrientation d (E b) where
  toFun z := z.property ▸ z.val.snd
  invFun o := ⟨⟨b, o⟩, rfl⟩
  left_inv z := by rcases z with ⟨⟨c,o⟩,h⟩; dsimp only at h; subst c; rfl
  right_inv _ := rfl

/-- Every positive-rank original orientation fibre has exactly two elements. -/
theorem fibre_bool_equiv [FiberBundle (Fin d → ℝ) E] [VectorBundle ℝ (Fin d → ℝ) E]
    (hd : 0 < d) (b : B) :
    Nonempty ({z : RealOrientationTotal d E // z.fst = b} ≃ Bool) := by
  let e := trivializationAt (Fin d → ℝ) E b
  let eb := e.linearEquivAt ℝ b (mem_baseSet_trivializationAt (Fin d → ℝ) E b)
  exact ⟨(fibreEquiv d E b).trans
    (orientationBoolEquiv hd ((Pi.basisFun ℝ (Fin d)).map eb.symm))⟩

omit [∀ b, TopologicalSpace (E b)] in
/-- In genuine incoming and receiving charts the original continuous bundle
map has continuous fixed-vector coordinates, even when T is noninjective. -/
theorem bundleMap_coordinates_continuous
    (e e' : Trivialization (Fin d → ℝ) (Bundle.TotalSpace.proj :
      Bundle.TotalSpace (Fin d → ℝ) E → B)) [e.IsLinear ℝ] [e'.IsLinear ℝ]
    (T : B → B) (L : ∀ b, E b ≃ₗ[ℝ] E (T b))
    (hL : Continuous (fun z : Bundle.TotalSpace (Fin d → ℝ) E ↦
      (⟨T z.proj, L z.proj z.snd⟩ : Bundle.TotalSpace (Fin d → ℝ) E)))
    (v : Fin d → ℝ) :
    Continuous (fun x : ↥(e.baseSet ∩ T ⁻¹' e'.baseSet) ↦
      ((e.linearEquivAt ℝ x.val x.property.1).symm.trans
        ((L x.val).trans (e'.linearEquivAt ℝ (T x.val) x.property.2))) v) := by
  have hi : Continuous (fun x : ↥(e.baseSet ∩ T ⁻¹' e'.baseSet) ↦
      e.toOpenPartialHomeomorph.symm (x.val, v)) :=
    e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      (continuous_subtype_val.prodMk continuous_const)
      (fun x ↦ by rw [e.target_eq]; exact ⟨x.property.1, Set.mem_univ _⟩)
  have h := e'.continuousOn.comp_continuous (hL.comp hi) (fun x ↦ by
    rw [e'.source_eq]
    simpa only [Set.mem_preimage, Function.comp_apply,
      e.symm_coe_proj x.property.1] using x.property.2)
  apply (continuous_snd.comp h).congr
  intro x
  dsimp only [Function.comp_apply]
  rw [← e.mk_symm x.property.1]
  simp only [LinearEquiv.trans_apply,
    Trivialization.linearEquivAt_apply, Trivialization.linearEquivAt_symm_apply]

/-- The intrinsic comparison of a continuous orientation with its image under
a continuous bundle isomorphism is continuous into the discrete sign group.
The proof uses actual incoming/receiving charts on their genuine overlap and
finite-basis determinant positivity; T need not be injective. -/
theorem comparison_continuous
    [FiberBundle (Fin d → ℝ) E] [VectorBundle ℝ (Fin d → ℝ) E]
    (o : ∀ b, RealBasisOrientation d (E b))
    (ho : letI := realOrientationTopology d E
      Continuous (fun b ↦ (⟨b, o b⟩ : RealOrientationTotal d E)))
    (T : B → B) (hT : Continuous T) (L : ∀ b, E b ≃ₗ[ℝ] E (T b))
    (hL : Continuous (fun z : Bundle.TotalSpace (Fin d → ℝ) E ↦
      (⟨T z.proj, L z.proj z.snd⟩ : Bundle.TotalSpace (Fin d → ℝ) E))) :
    Continuous (fun b ↦ realOrientationComparison d (L b) (o b) (o (T b))) := by
  classical
  let := realOrientationTopology d E
  let : DiscreteTopology (RealBasisOrientation d (Fin d → ℝ)) := ⟨rfl⟩
  apply continuous_iff_continuousAt.mpr
  intro b
  let e := trivializationAt (Fin d → ℝ) E b
  let e' := trivializationAt (Fin d → ℝ) E (T b)
  let U : Set B := e.baseSet ∩ T ⁻¹' e'.baseSet
  have hU : IsOpen U := e.open_baseSet.inter (e'.open_baseSet.preimage hT)
  have hb : b ∈ U := ⟨mem_baseSet_trivializationAt (Fin d → ℝ) E b,
    mem_baseSet_trivializationAt (Fin d → ℝ) E (T b)⟩
  let A (x : U) := e.linearEquivAt ℝ x.val x.property.1
  let C (x : U) := e'.linearEquivAt ℝ (T x.val) x.property.2
  let M (x : U) : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) := (A x).symm.trans ((L x.val).trans (C x))
  have hu : Continuous (fun x : U ↦ realOrientationMap (A x) (o x.val)) :=
    continuous_snd.comp ((chartHomeomorph d E e).continuous.comp
      ((ho.comp continuous_subtype_val).subtype_mk (fun x ↦ x.property.1)))
  have hv : Continuous (fun x : U ↦ realOrientationMap (C x) (o (T x.val))) :=
    continuous_snd.comp ((chartHomeomorph d E e').continuous.comp
      ((ho.comp (hT.comp continuous_subtype_val)).subtype_mk (fun x ↦ x.property.2)))
  have hm0 (v : Fin d → ℝ) : Continuous (fun x : U ↦ M x v) := by
    exact bundleMap_coordinates_continuous d E e e' T L hL v
  have hm1 : Continuous (fun z : U × RealBasisOrientation d (Fin d → ℝ) ↦
      realOrientationMap (M z.1) z.2) := map_family_continuous M hm0
  have hm := hm1.comp (continuous_id.prodMk hu)
  let cmp : RealBasisOrientation d (Fin d → ℝ) ×
      RealBasisOrientation d (Fin d → ℝ) → ℤˣ :=
    fun z ↦ if z.1 = z.2 then 1 else -1
  have hcmp : Continuous cmp := continuous_of_discreteTopology
  have hc : Continuous (fun x : U ↦
      realOrientationComparison d (L x.val) (o x.val) (o (T x.val))) := by
    apply (hcmp.comp (hm.prodMk hv)).congr
    intro x
    exact comparison_conjugate (A x) (C x) (L x.val) (o x.val) (o (T x.val))
  exact (continuousOn_iff_continuous_domRestrict.mpr hc).continuousAt (hU.mem_nhds hb)

/-- Actual fibre charts provide actual ordered bases and hence nonempty quotient fibres. -/
theorem fibre_orientation_nonempty
    [FiberBundle (Fin d → ℝ) E] [VectorBundle ℝ (Fin d → ℝ) E] (b : B) :
    Nonempty (RealBasisOrientation d (E b)) := by
  let e := trivializationAt (Fin d → ℝ) E b
  let eb := e.linearEquivAt ℝ b (mem_baseSet_trivializationAt (Fin d → ℝ) E b)
  exact ⟨Quotient.mk _ ((Pi.basisFun ℝ (Fin d)).map eb.symm)⟩

/-- Singleton quotient fibres give a continuous section in the actual all-chart
topology. Locally the section is an original inverse chart with a constant label;
no global frame or continuity of a chosen chart selector is used. -/
theorem section_continuous_of_subsingleton
    [FiberBundle (Fin d → ℝ) E] [VectorBundle ℝ (Fin d → ℝ) E]
    (hs : ∀ b, Subsingleton (RealBasisOrientation d (E b)))
    (o : ∀ b, RealBasisOrientation d (E b)) :
    letI := realOrientationTopology d E
    Continuous (fun b ↦ (⟨b, o b⟩ : RealOrientationTotal d E)) := by
  classical
  let := realOrientationTopology d E
  apply continuous_iff_continuousAt.mpr
  intro b
  let e := trivializationAt (Fin d → ℝ) E b
  let q : RealBasisOrientation d (Fin d → ℝ) := Quotient.mk _ (Pi.basisFun ℝ (Fin d))
  have hc : Continuous (fun y : e.baseSet ↦ realOrientationChartInverse d E e (y, q)) :=
    (chartInverse_continuous d E e).comp (continuous_id.prodMk continuous_const)
  have heq : (fun y : e.baseSet ↦ realOrientationChartInverse d E e (y, q)) =
      (fun y : e.baseSet ↦ (⟨y.val, o y.val⟩ : RealOrientationTotal d E)) := by
    funext y
    change (⟨y.val, realOrientationMap _ q⟩ : RealOrientationTotal d E) = ⟨y.val, o y.val⟩
    congr 1
    exact (hs y.val).elim _ _
  rw [heq] at hc
  exact (continuousOn_iff_continuous_domRestrict.mpr hc).continuousAt
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt (Fin d → ℝ) E b))

/-- In rank zero every comparison is positive, since both actual ordered-basis
quotient orientations are the unique empty-basis class. -/
theorem zero_comparison {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V ≃ₗ[ℝ] W)
    (o : RealBasisOrientation 0 V) (q : RealBasisOrientation 0 W) :
    realOrientationComparison 0 L o q = 1 := by
  have h := (zero_orientation_subsingleton (V := W)).elim (realOrientationMap L o) q
  simp only [realOrientationComparison, h, ite_true]

omit [TopologicalSpace B] [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (Bundle.TotalSpace (Fin d → ℝ) E)] in
/-- Projection of a singleton-fibre orientation bundle is injective. -/
theorem projection_injective_of_subsingleton
    (hs : ∀ b, Subsingleton (RealBasisOrientation d (E b))) :
    Function.Injective (Sigma.fst : RealOrientationTotal d E → B) := by
  rintro ⟨b, o⟩ ⟨c, q⟩ h
  dsimp only at h
  subst c
  exact congrArg (Sigma.mk b) ((hs b).elim o q)


end OrientationMonodromyProof

/-- The orientation-cover monodromy and orientability criterion on the original bundle.

Source: the Hatcher and Mathlib composite listed in the module and the DAG node.
The following gives the full source architecture. Every theorem proof remains
postponed in Stage 2; the imported carriers, maps and topology have genuine data.

For a positive rank, each continuous linear chart identifies the original ordered-basis
quotient with two signs. The determinant-positive equality criterion proves that this
identification is representative-independent, and changing a standard basis vector's
sign supplies the second class. Basis.map, matrix composition, and determinant
multiplicativity give the cocycle in the original source-to-target order. Evaluating
chart transitions on the finite standard basis proves continuity of every matrix
entry; determinant continuity and nonzero-sign continuity give the discrete overlap
law. The inverse chart maps in the defined coinduced topology therefore promote to
actual local homeomorphisms. Their two model labels give exactly two sheets. Mixed
original charts obey the same overlap law, so this all-chart topology is independent
of the chosen original atlas or its refinement. Local sections are exactly continuous
choices of the quotient fibre orientations.

Connected locally path-connected B is path connected. Hatcher's path and homotopy
lifting gives endpoint transport on each two-point fibre, depending only on the loop
class. Concatenation composes these endpoint permutations in reverse chronological
order; on two points they commute and equal their inverses. Identifying identity and
transposition with +1 and -1 gives the homomorphism w into ℤˣ. The displayed endpoint
law characterizes this actual transport, rather than an arbitrary homomorphism. If w
is trivial, every based loop lifts closed from a chosen orientation over b0. Hatcher's
lifting criterion applied to id_B then supplies a continuous section; conversely a
section lifts every loop closed and a two-point permutation fixing one point is the
identity. Simple connectivity makes every loop class trivial and hence supplies a
section. No semilocal simple-connectivity or connected-total-cover premise is used.

For a continuous fibrewise linear isomorphism over continuous T, use the pullback
bundle T*E and Hatcher's same-base inverse lemma, rather than assume T injective.
In two actual oriented charts the matrix is e'_(T b) L_b e_b⁻¹. Its fixed-basis
entries are continuous, and its determinant is nonzero. The sign is continuous into
the discrete two-valued group, hence constant on connected B. Basis.orientation_map
identifies it with the defined intrinsic comparison, independently of both frames.

At rank zero the unique empty ordered basis makes the quotient singleton; every
linear map sends that class to itself. The topology is just the original base topology,
the section is canonical, w is constantly +1, and every comparison sign is +1.
The TWO-sheet statement is restricted to positive rank. Arbitrary infinite base
spaces, non-Hausdorff bases, and noninjective T are allowed.
-/
theorem real_vector_bundle_orientation_monodromy
    [ConnectedSpace B] [LocallyPathConnectedSpace B]
    [FiberBundle (Fin d → ℝ) E] [VectorBundle ℝ (Fin d → ℝ) E] (b₀ : B) :
    letI := realOrientationTopology d E
    let proj : RealOrientationTotal d E → B := Sigma.fst
    ∃ w : FundamentalGroup B b₀ →* ℤˣ,
      (0 < d → IsCoveringMap proj ∧
        ∀ b : B, Nonempty ({z : RealOrientationTotal d E // proj z = b} ≃ Bool)) ∧
      (∀ (γ : Path b₀ b₀) (o : RealBasisOrientation d (E b₀)),
        (∃ lift : C(unitInterval, RealOrientationTotal d E),
          (∀ t, proj (lift t) = γ t) ∧ lift 0 = ⟨b₀, o⟩) ∧
        ∀ lift : C(unitInterval, RealOrientationTotal d E),
          (∀ t, proj (lift t) = γ t) → lift 0 = ⟨b₀, o⟩ →
          (lift 1 = ⟨b₀, o⟩ ↔ w (FundamentalGroup.fromPath ⟦γ⟧) = 1)) ∧
      ((∀ g, w g = 1) ↔ ∃ o : ∀ b, RealBasisOrientation d (E b),
        Continuous (fun b ↦ (⟨b, o b⟩ : RealOrientationTotal d E))) ∧
      (SimplyConnectedSpace B → ∃ o : ∀ b, RealBasisOrientation d (E b),
        Continuous (fun b ↦ (⟨b, o b⟩ : RealOrientationTotal d E))) ∧
      (∀ (o : ∀ b, RealBasisOrientation d (E b)),
        Continuous (fun b ↦ (⟨b, o b⟩ : RealOrientationTotal d E)) →
        ∀ (T : B → B), Continuous T → ∀ (L : ∀ b, E b ≃ₗ[ℝ] E (T b)),
          Continuous (fun z : Bundle.TotalSpace (Fin d → ℝ) E ↦
            (⟨T z.proj, L z.proj z.snd⟩ : Bundle.TotalSpace (Fin d → ℝ) E)) →
          ∀ b c : B, realOrientationComparison d (L b) (o b) (o (T b)) =
            realOrientationComparison d (L c) (o c) (o (T c))) ∧
      (d = 0 → (∀ g, w g = 1) ∧
        (∀ b : B, Subsingleton (RealBasisOrientation d (E b))) ∧
        ∀ (T : B → B) (L : ∀ b, E b ≃ₗ[ℝ] E (T b))
          (o : ∀ b, RealBasisOrientation d (E b)) (b : B),
          realOrientationComparison d (L b) (o b) (o (T b)) = 1) := by
  classical
  by_cases hd : d = 0
  · subst d
    let := realOrientationTopology 0 E
    let o : ∀ b, RealBasisOrientation 0 (E b) :=
      fun b ↦ Classical.choice (OrientationMonodromyProof.fibre_orientation_nonempty 0 E b)
    have hs (b : B) : Subsingleton (RealBasisOrientation 0 (E b)) :=
      OrientationMonodromyProof.zero_orientation_subsingleton
    have hsec := OrientationMonodromyProof.section_continuous_of_subsingleton 0 E hs o
    have hinj := OrientationMonodromyProof.projection_injective_of_subsingleton 0 E hs
    refine ⟨1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hpos
      exact (Nat.lt_irrefl 0 hpos).elim
    · intro γ q
      constructor
      · refine ⟨⟨fun t ↦ ⟨γ t, o (γ t)⟩, hsec.comp γ.continuous⟩, fun _ ↦ rfl, ?_⟩
        apply hinj
        exact γ.source
      · intro lift hl hzero
        have hend : lift 1 = ⟨b₀, q⟩ := hinj ((hl 1).trans γ.target)
        exact ⟨fun _ ↦ rfl, fun _ ↦ hend⟩
    · exact ⟨fun _ ↦ ⟨o, hsec⟩, fun _ _ ↦ rfl⟩
    · exact fun _ ↦ ⟨o, hsec⟩
    · intro q hq T hT L hL b c
      rw [OrientationMonodromyProof.zero_comparison, OrientationMonodromyProof.zero_comparison]
    · intro _
      exact ⟨fun _ ↦ rfl, hs, fun T L q b ↦ OrientationMonodromyProof.zero_comparison _ _ _⟩
  · let := realOrientationTopology d E
    let p : RealOrientationTotal d E → B := Sigma.fst
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hp : IsCoveringMap p := OrientationMonodromyProof.projection_isCoveringMap d E
    have hf : ∀ b, Nonempty ({z : RealOrientationTotal d E // p z = b} ≃ Bool) :=
      OrientationMonodromyProof.fibre_bool_equiv d E hdpos
    obtain ⟨w, hlift, hw, hsc⟩ := OrientationMonodromyProof.two_sheet_monodromy p hp b₀ hf
    have convertSection : (∃ s : B → RealOrientationTotal d E,
        Continuous s ∧ ∀ b, p (s b) = b) ↔
        ∃ o : ∀ b, RealBasisOrientation d (E b),
          Continuous (fun b ↦ (⟨b, o b⟩ : RealOrientationTotal d E)) := by
      constructor
      · rintro ⟨s, hs, hps⟩
        let o : ∀ b, RealBasisOrientation d (E b) :=
          fun b ↦ OrientationMonodromyProof.fibreEquiv d E b ⟨s b, hps b⟩
        refine ⟨o, hs.congr (fun b ↦ ?_)⟩
        exact (congrArg Subtype.val ((OrientationMonodromyProof.fibreEquiv d E b).symm_apply_apply ⟨s b, hps b⟩)).symm
      · rintro ⟨o, ho⟩
        exact ⟨fun b ↦ ⟨b, o b⟩, ho, fun _ ↦ rfl⟩
    refine ⟨w, fun _ ↦ ⟨hp, hf⟩, ?_, hw.trans convertSection,
      fun hs ↦ convertSection.mp (hsc hs), ?_, ?_⟩
    · intro γ o
      exact hlift γ ⟨b₀, o⟩ rfl
    · intro o ho T hT L hL b c
      exact (inferInstance : PreconnectedSpace B).constant
        (OrientationMonodromyProof.comparison_continuous d E o ho T hT L hL)
    · exact fun hzero ↦ (hd hzero).elim



end

end HolomorphicAnosov
