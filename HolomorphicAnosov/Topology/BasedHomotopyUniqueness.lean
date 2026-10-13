import HolomorphicAnosov.Topology.CWComplex.HomotopyExtension
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import HolomorphicAnosov.Topology.CWComplex.RealizationSpanningTree
import HolomorphicAnosov.Topology.CWPointVertexRefinement
import HolomorphicAnosov.Topology.CompactCWFiniteSubcomplex
import HolomorphicAnosov.Topology.NullhomotopicSphereDiskExtension
import HolomorphicAnosov.Topology.UnitSphereSimplyConnected
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Based homotopy uniqueness for maps from a connected CW complex

Source: Hatcher, *Algebraic Topology*, Proposition 1B.9, pp. 90–91.
The statement allows an arbitrary basepoint in the original Hausdorff CW space.
The universal-cover assumption is expressed by a surjective covering map with
contractible total space. No CW structure or separation assumption is imposed on the target.
-/

namespace HolomorphicAnosov

universe u v w

/-- Hatcher 1B.9, pp.90–91: equality of the actual based induced maps
produces an endpoint-fixed homotopy for EVERY original root loop. The casts
use exactly the supplied endpoint equalities, without a conjugating path.
This follows by applying the homomorphism equality to its path class and
using equality in Mathlib's actual endpoint-homotopy quotient. -/
theorem based_loop_images_homotopic
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    (k₀ : K) (y₀ : Y) (f g : C(K, Y))
    (hf : f k₀ = y₀) (hg : g k₀ = y₀)
    (hπ₁ : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg)
    (γ : Path k₀ k₀) :
    Path.Homotopic ((γ.map f.continuous).cast hf.symm hf.symm)
      ((γ.map g.continuous).cast hg.symm hg.symm) := by
  apply Path.Homotopic.Quotient.eq.mp
  have h := DFunLike.congr_fun hπ₁
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
  simpa only [FundamentalGroup.mapOfEq_apply,
    ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast] using h

/-- Hatcher 1B.9, p.91, higher-cell uniqueness paragraph: a sphere map
lifts through the GIVEN surjective covering, and the actual contraction of
its total space supplies a joint nullhomotopy. This helper is generic in
its simply connected, locally path-connected source, with no separation
assumption on the target and no equivariant-lift premise. -/
theorem covering_contractible_nullhomotopy
    {Z : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace Z] [TopologicalSpace Y] [TopologicalSpace E]
    [SimplyConnectedSpace Z] [LocallyPathConnectedSpace Z] [ContractibleSpace E]
    (p : E → Y) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (b : C(Z, Y)) (z₀ : Z) :
    ∃ ystar : Y, ∃ H : unitInterval × Z → Y, Continuous H ∧
      (∀ z, H (0, z) = b z) ∧ (∀ z, H (1, z) = ystar) := by
  obtain ⟨e₀, he₀⟩ := hsurj (b z₀)
  obtain ⟨L, hL, _⟩ := hp.existsUnique_continuousMap_lifts b z₀ e₀ he₀
  obtain ⟨estar, ⟨C⟩⟩ := id_nullhomotopic E
  refine ⟨p estar, fun q ↦ p (C (q.1, L q.2)), ?_, ?_, ?_⟩
  · exact hp.continuous.comp (C.continuous.comp
      (continuous_fst.prodMk (L.continuous.comp continuous_snd)))
  · intro z
    simpa only [C.apply_zero, ContinuousMap.id_apply, Function.comp_apply] using congrFun hL.2 z
  · intro z
    simp only [C.apply_one, ContinuousMap.const_apply]

/-- Hatcher 1B.9, p.91: every prescribed native maximum-norm sphere of
dimension at least two has a continuous filling on its SAME closed disk.
Use the published sphere theorem for the actual sphere carrier, choose one
sphere point, lift and contract by the preceding proved helper, then apply
the published nullhomotopy-to-disk extension with its full boundary equation.
This includes d=3 and does not assert a filling for circle maps (d=2). -/
theorem covering_contractible_native_sphere_filling
    {Y : Type v} {E : Type w} [TopologicalSpace Y] [TopologicalSpace E]
    [ContractibleSpace E] (d : ℕ) (hd : 3 ≤ d)
    (p : E → Y) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (b : C({v : Fin d → ℝ // ‖v‖ = 1}, Y)) :
    ∃ B : {v : Fin d → ℝ // ‖v‖ ≤ 1} → Y, Continuous B ∧
      ∀ s, B ⟨s.val, le_of_eq s.property⟩ = b s := by
  have hdim : d - 1 + 1 = d := by omega
  have htop := unit_sphere_simply_connected (d - 1) (by omega)
  rw [hdim] at htop
  have : SimplyConnectedSpace {v : Fin d → ℝ // ‖v‖ = 1} := htop.2.2.1
  have : LocallyPathConnectedSpace {v : Fin d → ℝ // ‖v‖ = 1} := htop.2.2.2.1
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let z₀ : {v : Fin d → ℝ // ‖v‖ = 1} :=
    ⟨fun _ ↦ 1, by simp only [pi_norm_const, norm_one]⟩
  apply nullhomotopic_sphere_disk_extension d (by omega) b b.continuous
  exact covering_contractible_nullhomotopy p hp hsurj b z₀



/-- Native maximum-norm cube splitting: the appended-coordinate norm is
exactly the maximum of the head norm and the last-coordinate absolute value.
This is the Fin-block guard used by Hatcher A.6's cell-prism normalization. -/
theorem native_norm_snoc (n : ℕ) (z : Fin n → ℝ) (a : ℝ) :
    ‖Fin.snoc (α := fun _ : Fin (n + 1) ↦ ℝ) z a‖ = max ‖z‖ |a| := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg z) (le_max_left _ _))).2
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.snoc_last, Real.norm_eq_abs] using le_max_right ‖z‖ |a|
    · simpa only [Fin.snoc_castSucc] using
        (norm_le_pi_norm z j).trans (le_max_left ‖z‖ |a|)
  · apply max_le
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (Fin.snoc (α := fun _ : Fin (n + 1) ↦ ℝ) z a))).2
      intro i
      simpa only [Fin.snoc_castSucc] using norm_le_pi_norm (Fin.snoc (α := fun _ : Fin (n + 1) ↦ ℝ) z a) i.castSucc
    · simpa only [Fin.snoc_last, Real.norm_eq_abs] using
        norm_le_pi_norm (Fin.snoc (α := fun _ : Fin (n + 1) ↦ ℝ) z a) (Fin.last n)

/-- The literal native characteristic disk/prism homeomorphism in the
source higher-prism proof: head coordinates are unchanged and the last
coordinate is affinely identified with I. No Euclidean radial adapter,
regular-cell premise, or change in the original maximum norm is used. -/
noncomputable def nativeDiskPrismHomeomorph (n : ℕ) :
    {v : Fin (n + 1) → ℝ // ‖v‖ ≤ 1} ≃ₜ
      ({z : Fin n → ℝ // ‖z‖ ≤ 1} × unitInterval) where
  toFun v :=
    (⟨fun i ↦ v.val i.castSucc,
      (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i ↦
        (norm_le_pi_norm v.val i.castSucc).trans v.property⟩,
     ⟨(v.val (Fin.last n) + 1) / 2, by
       have h := (norm_le_pi_norm v.val (Fin.last n)).trans v.property
       rw [Real.norm_eq_abs, abs_le] at h
       constructor <;> linarith [h.1, h.2]⟩)
  invFun q := ⟨Fin.snoc (α := fun _ : Fin (n + 1) ↦ ℝ) q.1.val (2 * (q.2 : ℝ) - 1), by
    rw [native_norm_snoc, max_le_iff]
    refine ⟨q.1.property, ?_⟩
    rw [abs_le]
    constructor <;> linarith [q.2.property.1, q.2.property.2]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [Fin.snoc_last]
      ring
    · simp only [Fin.snoc_castSucc]
  right_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      simp only [Fin.snoc_castSucc]
    · apply Subtype.ext
      simp only [Fin.snoc_last]
      ring
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply continuous_pi
      intro i
      exact (continuous_apply i.castSucc).comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact (((continuous_apply (Fin.last n)).comp continuous_subtype_val).add
        continuous_const).div_const 2
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.finSnoc
    · exact continuous_subtype_val.comp continuous_fst
    · exact (continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub
        continuous_const

/-- The full prism boundary is precisely the original native sphere,
including all face intersections and the zero-head-coordinate case. -/
theorem nativeDiskPrism_boundary (n : ℕ)
    (q : {z : Fin n → ℝ // ‖z‖ ≤ 1} × unitInterval) :
    ‖((nativeDiskPrismHomeomorph n).symm q).val‖ = 1 ↔
      ‖q.1.val‖ = 1 ∨ q.2 = 0 ∨ q.2 = 1 := by
  change ‖Fin.snoc (α := fun _ : Fin (n + 1) ↦ ℝ) q.1.val (2 * (q.2 : ℝ) - 1)‖ = 1 ↔ _
  rw [native_norm_snoc]
  have ht : |2 * (q.2 : ℝ) - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [q.2.property.1, q.2.property.2]
  constructor
  · intro he
    by_cases hz : ‖q.1.val‖ = 1
    · exact Or.inl hz
    right
    have ha : |2 * (q.2 : ℝ) - 1| = 1 := by
      rcases le_total ‖q.1.val‖ |2 * (q.2 : ℝ) - 1| with h | h
      · simpa only [max_eq_right h] using he
      · exact False.elim (hz (by simpa only [max_eq_left h] using he))
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at ha
    rcases ha with ha | ha
    · right
      apply Subtype.ext
      change (q.2 : ℝ) = 1
      linarith
    · left
      apply Subtype.ext
      change (q.2 : ℝ) = 0
      linarith
  · rintro (hz | hzero | hone)
    · rw [hz, max_eq_left ht]
    · rw [hzero]
      norm_num [max_eq_right q.1.property]
    · rw [hone]
      norm_num [max_eq_right q.1.property]



/-- Hatcher 1B.9, p.91, applied to the entire original characteristic
prism boundary. A supplied continuous boundary map has a filling that agrees
at EVERY boundary point, including bottom/side/top overlaps. The source
cube-block adapter is the proved literal homeomorphism above; no regularity
or injectivity of an attaching map is used. This closes the higher-dimensional
filling step once its closed-pasted boundary prescription has been constructed.
-/
theorem covering_contractible_native_prism_filling
    {Y : Type v} {E : Type w} [TopologicalSpace Y] [TopologicalSpace E]
    [ContractibleSpace E] (n : ℕ) (hn : 2 ≤ n)
    (p : E → Y) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (b : C({q : {z : Fin n → ℝ // ‖z‖ ≤ 1} × unitInterval //
      ‖q.1.val‖ = 1 ∨ q.2 = 0 ∨ q.2 = 1}, Y)) :
    ∃ F : C({z : Fin n → ℝ // ‖z‖ ≤ 1} × unitInterval, Y),
      ∀ q : {q : {z : Fin n → ℝ // ‖z‖ ≤ 1} × unitInterval //
        ‖q.1.val‖ = 1 ∨ q.2 = 0 ∨ q.2 = 1}, F q.val = b q := by
  let e := nativeDiskPrismHomeomorph n
  let sphereMap : {v : Fin (n + 1) → ℝ // ‖v‖ = 1} →
      {q : {z : Fin n → ℝ // ‖z‖ ≤ 1} × unitInterval //
        ‖q.1.val‖ = 1 ∨ q.2 = 0 ∨ q.2 = 1} := fun s ↦
    ⟨e ⟨s.val, le_of_eq s.property⟩, by
      apply (nativeDiskPrism_boundary n _).mp
      change ‖(e.symm (e ⟨s.val, le_of_eq s.property⟩)).val‖ = 1
      rw [e.symm_apply_apply]
      exact s.property⟩
  have hc : Continuous sphereMap := by
    apply Continuous.subtype_mk
    exact e.continuous.comp (continuous_subtype_val.subtype_mk _)
  let bSphere : C({v : Fin (n + 1) → ℝ // ‖v‖ = 1}, Y) :=
    ⟨fun s ↦ b (sphereMap s), b.continuous.comp hc⟩
  obtain ⟨B, hB, hboundary⟩ := covering_contractible_native_sphere_filling
    (n + 1) (by omega) p hp hsurj bSphere
  refine ⟨⟨fun q ↦ B (e.symm q), hB.comp e.symm.continuous⟩, ?_⟩
  intro q
  let s : {v : Fin (n + 1) → ℝ // ‖v‖ = 1} :=
    ⟨(e.symm q.val).val, (nativeDiskPrism_boundary n q.val).mpr q.property⟩
  have hpoint : (⟨s.val, le_of_eq s.property⟩ :
      {v : Fin (n + 1) → ℝ // ‖v‖ ≤ 1}) = e.symm q.val := rfl
  have h := hboundary s
  rw [hpoint] at h
  change B (e.symm q.val) = b (sphereMap s) at h
  change B (e.symm q.val) = b q
  rw [h]
  congr 1
  apply Subtype.ext
  change e ⟨s.val, le_of_eq s.property⟩ = q.val
  rw [hpoint, e.apply_symm_apply]



/-- Hatcher 1B.9/p.523, the final all-skeleton descent. Compatible actual
homotopies on the original natural-number skeleta define a based homotopy
on the original carrier. Every closed m-cell is in the m-skeleton; hence
its global characteristic prism is literally the continuous m-stage prism.
The preceding ordinary-product criterion proves joint continuity. The choice
of a containing skeleton introduces no bound, local finiteness, convergence,
or changed topology, and the endpoints/basepoint equations pass pointwise.
-/
theorem cw_based_homotopy_of_compatible_skeleta
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)]
    (k₀ : K) (f g : C(K, Y))
    (H : ∀ n : ℕ, C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K), Y))
    (hzero : ∀ n x, H n (0, x) = f x.val)
    (hone : ∀ n x, H n (1, x) = g x.val)
    (hfixed : ∀ n t x, x.val = k₀ → H n (t, x) = f k₀)
    (hcompat : ∀ (m n : ℕ) (hmn : m ≤ n) t x,
      H m (t, x) = H n (t, ⟨x.val, Topology.CWComplex.skeleton_mono
        (by exact_mod_cast hmn) x.property⟩)) :
    Nonempty (ContinuousMap.HomotopyRel f g {k₀}) := by
  classical
  let S : ℕ → Set K := fun n ↦ (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)
  have hm : ∀ m n : ℕ, m ≤ n → S m ⊆ S n := by
    intro m n hmn
    exact Topology.CWComplex.skeleton_mono (by exact_mod_cast hmn)
  have hcover : ∀ x : K, ∃ n : ℕ, x ∈ S n := by
    intro x
    have hx : x ∈ ⋃ n : ℕ, S n := by
      rw [show (⋃ n : ℕ, S n) = Set.univ from
        Topology.CWComplex.iUnion_skeleton_eq_complex]
      exact Set.mem_univ _
    exact Set.mem_iUnion.mp hx
  let index : K → ℕ := fun x ↦ (hcover x).choose
  have hindex : ∀ x, x ∈ S (index x) := fun x ↦ (hcover x).choose_spec
  let U : unitInterval × K → Y := fun q ↦ H (index q.2) (q.1, ⟨q.2, hindex q.2⟩)
  have hagree : ∀ n t (x : S n), U (t, x.val) = H n (t, x) := by
    intro n t x
    let N := max (index x.val) n
    have hi := hcompat (index x.val) N (le_max_left _ _) t
      (⟨x.val, hindex x.val⟩ : S (index x.val))
    have hn := hcompat n N (le_max_right _ _) t x
    exact hi.trans hn.symm
  have hcont : Continuous U := by
    apply cw_prism_continuous_of_characteristic
    intro n i
    let χ : C(Metric.closedBall (0 : Fin n → ℝ) 1, S n) :=
      ⟨fun z ↦ ⟨Topology.RelCWComplex.map n i z.val,
        Topology.CWComplex.closedCell_subset_skeleton n i
          ⟨z.val, z.property, rfl⟩⟩,
       ((Topology.RelCWComplex.continuousOn n i).domRestrict).subtype_mk _⟩
    have hc := (H n).continuous.comp
      (continuous_fst.prodMk (χ.continuous.comp continuous_snd))
    convert hc using 1
    funext q
    exact hagree n q.1 (χ q.2)
  refine ⟨{
    toFun := U
    continuous_toFun := hcont
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro x
    exact hzero (index x) ⟨x, hindex x⟩
  · intro x
    exact hone (index x) ⟨x, hindex x⟩
  · intro t x hx
    have hx' : x = k₀ := Set.mem_singleton_iff.mp hx
    change U (t, x) = f x
    rw [hx']
    exact hfixed (index k₀) t ⟨k₀, hindex k₀⟩ rfl



/-- The zero-dimensional edge case in Hatcher 1B.9. A Hausdorff CW
space with no positive cells is discrete by its ACTUAL closed-cell criterion;
connectedness therefore makes it a singleton. This uses no cardinality or
local-finiteness assumption on the zero-cell index set. -/
theorem cw_zero_dimensional_subsingleton
    {K : Type u} [TopologicalSpace K] [T2Space K] [ConnectedSpace K]
    [Topology.CWComplex (Set.univ : Set K)]
    (hdim : ∀ n : ℕ, 0 < n → IsEmpty (Topology.RelCWComplex.cell (Set.univ : Set K) n)) :
    Subsingleton K := by
  have : DiscreteTopology K := discreteTopology_iff_forall_isClosed.mpr (by
    intro A
    apply (Topology.CWComplex.closed Set.univ A (Set.subset_univ _)).mpr
    intro n i
    cases n with
    | zero =>
      rw [Topology.CWComplex.closedCell_zero_eq_singleton]
      exact isClosed_inter_singleton
    | succ n =>
      have := hdim (n + 1) (Nat.zero_lt_succ n)
      exact isEmptyElim i)
  exact PreconnectedSpace.trivial_of_discrete

/-- On a singleton source the supplied basedness equations identify both
maps pointwise. The actual relative reflexive homotopy fixes the chosen
point at all times. -/
theorem based_homotopy_of_subsingleton
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [Subsingleton K] (k₀ : K) (y₀ : Y) (f g : C(K, Y))
    (hf : f k₀ = y₀) (hg : g k₀ = y₀) :
    Nonempty (ContinuousMap.HomotopyRel f g {k₀}) := by
  have heq : f = g := by
    ext x
    rw [Subsingleton.elim x k₀, hf, hg]
  subst g
  exact ⟨ContinuousMap.HomotopyRel.refl f {k₀}⟩




/-- Hatcher p.14's closed-piece pasting mechanism, with actual compatible
maps on the closed-piece subtypes. Choose a containing piece for each point;
overlap agreement proves the result equals EVERY prescribed piece map.
Finite closed pasting then gives continuity, with no separation condition
on the target. This is the mechanism used for bottom/top/lateral prescriptions.
-/
theorem finite_closed_cover_glue
    {X : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
    (S : ι → Set X) (hclosed : ∀ i, IsClosed (S i))
    (hcover : ∀ x : X, ∃ i, x ∈ S i) (φ : ∀ i, C(S i, Y))
    (hcompat : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j),
      φ i ⟨x, hi⟩ = φ j ⟨x, hj⟩) :
    ∃ F : C(X, Y), ∀ i (x : S i), F x.val = φ i x := by
  classical
  let choose : X → ι := fun x ↦ (hcover x).choose
  have hchoose : ∀ x, x ∈ S (choose x) := fun x ↦ (hcover x).choose_spec
  let F : X → Y := fun x ↦ φ (choose x) ⟨x, hchoose x⟩
  have hF : ∀ i (x : S i), F x.val = φ i x := by
    intro i x
    exact hcompat (choose x.val) i x.val (hchoose x.val) x.property
  have hc : Continuous F := by
    apply (locallyFinite_of_finite S).continuous
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact hcover x
    · exact hclosed
    · intro i
      apply continuousOn_iff_continuous_domRestrict.mpr
      convert (φ i).continuous using 1
      funext x
      exact hF i x
  exact ⟨⟨F, hc⟩, hF⟩




/-- Hatcher p.14's bottom/top/lateral closed-piece prescription on the
EXACT native prism boundary. The two endpoint equations ensure all overlaps
agree. The boundary is covered by three closed sets; the preceding finite
closed-cover theorem constructs the continuous map without separation of Y.
All boundary equations are literal, including every identified corner.
-/
theorem native_prism_boundary_pasting
    {Y : Type v} [TopologicalSpace Y] (n : ℕ)
    (f₀ f₁ : C({z : Fin n → ℝ // ‖z‖ ≤ 1}, Y))
    (side : C(unitInterval × {s : Fin n → ℝ // ‖s‖ = 1}, Y))
    (h₀ : ∀ s, side (0, s) = f₀ ⟨s.val, le_of_eq s.property⟩)
    (h₁ : ∀ s, side (1, s) = f₁ ⟨s.val, le_of_eq s.property⟩) :
    ∃ B : C({q : {z : Fin n → ℝ // ‖z‖ ≤ 1} × unitInterval //
      ‖q.1.val‖ = 1 ∨ q.2 = 0 ∨ q.2 = 1}, Y),
      (∀ z, B ⟨(z, 0), Or.inr (Or.inl rfl)⟩ = f₀ z) ∧
      (∀ z, B ⟨(z, 1), Or.inr (Or.inr rfl)⟩ = f₁ z) ∧
      ∀ t s, B ⟨(⟨s.val, le_of_eq s.property⟩, t), Or.inl s.property⟩ = side (t, s) := by
  let boundary := {q : {z : Fin n → ℝ // ‖z‖ ≤ 1} × unitInterval //
    ‖q.1.val‖ = 1 ∨ q.2 = 0 ∨ q.2 = 1}
  let S : Fin 3 → Set boundary :=
    ![{q | q.val.2 = 0}, {q | q.val.2 = 1}, {q | ‖q.val.1.val‖ = 1}]
  have hclosed : ∀ i, IsClosed (S i) := by
    intro i
    fin_cases i
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_eq (by fun_prop) continuous_const
  have hcover : ∀ q : boundary, ∃ i, q ∈ S i := by
    intro q
    rcases q.property with h | h | h
    · exact ⟨2, h⟩
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  let φ : ∀ i, C(S i, Y) := fun i ↦ by
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun j ↦ Fin.elim0 j) k) j) i
    · exact ⟨fun q ↦ f₀ q.val.val.1,
        f₀.continuous.comp (continuous_fst.comp
          (continuous_subtype_val.comp continuous_subtype_val))⟩
    · exact ⟨fun q ↦ f₁ q.val.val.1,
        f₁.continuous.comp (continuous_fst.comp
          (continuous_subtype_val.comp continuous_subtype_val))⟩
    · exact ⟨fun q ↦ side (q.val.val.2, ⟨q.val.val.1.val, q.property⟩), by
        apply side.continuous.comp
        apply Continuous.prodMk
        · exact continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
        · apply Continuous.subtype_mk
          exact continuous_subtype_val.comp (continuous_fst.comp
            (continuous_subtype_val.comp continuous_subtype_val))⟩
  have hcompat : ∀ i j q (hi : q ∈ S i) (hj : q ∈ S j),
      φ i ⟨q, hi⟩ = φ j ⟨q, hj⟩ := by
    intro i j q hi hj
    fin_cases i <;> fin_cases j
    · rfl
    · have hzero : q.val.2 = 0 := hi
      have hone : q.val.2 = 1 := hj
      exact False.elim (zero_ne_one (hzero.symm.trans hone))
    · change f₀ q.val.1 = side (q.val.2, ⟨q.val.1.val, hj⟩)
      have ht : q.val.2 = 0 := hi
      rw [ht]
      simpa using (h₀ ⟨q.val.1.val, hj⟩).symm
    · have hone : q.val.2 = 1 := hi
      have hzero : q.val.2 = 0 := hj
      exact False.elim (zero_ne_one (hzero.symm.trans hone))
    · rfl
    · change f₁ q.val.1 = side (q.val.2, ⟨q.val.1.val, hj⟩)
      have ht : q.val.2 = 1 := hi
      rw [ht]
      simpa using (h₁ ⟨q.val.1.val, hj⟩).symm
    · change side (q.val.2, ⟨q.val.1.val, hi⟩) = f₀ q.val.1
      have ht : q.val.2 = 0 := hj
      rw [ht]
      exact h₀ _
    · change side (q.val.2, ⟨q.val.1.val, hi⟩) = f₁ q.val.1
      have ht : q.val.2 = 1 := hj
      rw [ht]
      exact h₁ _
    · rfl
  obtain ⟨B, hB⟩ := finite_closed_cover_glue S hclosed hcover φ hcompat
  refine ⟨B, ?_, ?_, ?_⟩
  · intro z
    exact hB 0 ⟨⟨(z, 0), Or.inr (Or.inl rfl)⟩, rfl⟩
  · intro z
    exact hB 1 ⟨⟨(z, 1), Or.inr (Or.inr rfl)⟩, rfl⟩
  · intro t s
    exact hB 2 ⟨⟨(⟨s.val, le_of_eq s.property⟩, t), Or.inl s.property⟩, s.property⟩




/-- Hatcher p.523's nonregular characteristic-prism gluing. Compatible
continuous maps on ALL original closed characteristic prisms descend to the
original ordinary product. Compatibility quantifies actual coincident images,
including noninjective boundary representatives; no closed cell is treated as
a disk. Choose one representative of each point, use compatibility for every
other representative, then the proved characteristic-prism criterion gives
continuity. This is a kernel construction, not a quotient-space assumption.
-/
theorem cw_glue_characteristic_prisms
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)]
    (P : ∀ (n : ℕ) (_i : Topology.RelCWComplex.cell (Set.univ : Set K) n),
      C(unitInterval × Metric.closedBall (0 : Fin n → ℝ) 1, Y))
    (hcompat : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell (Set.univ : Set K) n)
      (m : ℕ) (j : Topology.RelCWComplex.cell (Set.univ : Set K) m)
      t (z : Metric.closedBall (0 : Fin n → ℝ) 1)
      (w : Metric.closedBall (0 : Fin m → ℝ) 1),
      Topology.RelCWComplex.map n i z.val = Topology.RelCWComplex.map m j w.val →
      P n i (t, z) = P m j (t, w)) :
    ∃ H : C(unitInterval × K, Y),
      ∀ n i t z, H (t, Topology.RelCWComplex.map n i z.val) = P n i (t, z) := by
  classical
  let Rep := Σ n : ℕ, Σ i : Topology.RelCWComplex.cell (Set.univ : Set K) n,
    Metric.closedBall (0 : Fin n → ℝ) 1
  let eval : Rep → K := fun r ↦ Topology.RelCWComplex.map r.1 r.2.1 r.2.2.val
  have hsurj : Function.Surjective eval := by
    intro x
    have hx : x ∈ ⋃ (n : ℕ) (i : Topology.RelCWComplex.cell (Set.univ : Set K) n),
        Topology.CWComplex.closedCell n i := by
      rw [Topology.CWComplex.union]
      exact Set.mem_univ _
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, z, hz, hzx⟩ := Set.mem_iUnion.mp hx
    exact ⟨⟨n, i, ⟨z, hz⟩⟩, hzx⟩
  let choose : K → Rep := fun x ↦ (hsurj x).choose
  have hchoose : ∀ x, eval (choose x) = x := fun x ↦ (hsurj x).choose_spec
  let H : unitInterval × K → Y := fun q ↦
    P (choose q.2).1 (choose q.2).2.1 (q.1, (choose q.2).2.2)
  have hagree : ∀ n i t z,
      H (t, Topology.RelCWComplex.map n i z.val) = P n i (t, z) := by
    intro n i t z
    exact hcompat _ _ n i t _ z (hchoose _)
  have hc : Continuous H := by
    apply cw_prism_continuous_of_characteristic
    intro n i
    convert (P n i).continuous using 1
    funext q
    exact hagree n i q.1 q.2
  exact ⟨⟨H, hc⟩, hagree⟩




/-- Hatcher's edge orientation on the ORIGINAL native characteristic disk.
The one-cell frontier is its two characteristic endpoints, including loop
and parallel-cell cases. Incidence identifies the two chosen vertices, so
one of the signs gives the actual oriented endpoint equations. -/
theorem cw_edge_orientation
    {K : Type u} [TopologicalSpace K] [T2Space K]
    {C : Set K} [Topology.CWComplex C]
    (e : Topology.RelCWComplex.cell C 1)
    (v w : Topology.RelCWComplex.cell C 0)
    (hlink : (Topology.CWComplex.OneSkeletonGraph C).IsLink e v w) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      Topology.RelCWComplex.map 1 e (fun _ ↦ -σ) = Topology.RelCWComplex.map 0 v 0 ∧
      Topology.RelCWComplex.map 1 e (fun _ ↦ σ) = Topology.RelCWComplex.map 0 w 0 := by
  have h := (Topology.CWComplex.OneSkeletonGraph.isLink_iff_pair e v w).mp hlink
  rw [Topology.CWComplex.cellFrontier_one_eq, Set.image_pair] at h
  have hpair := Set.pair_eq_pair_iff.mp h
  rcases hpair with h | h
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · convert h.1 using 1; congr 1; ext i; norm_num; exact Fin.elim0 i
    · convert h.2 using 1; congr 1; ext i; norm_num; exact Fin.elim0 i
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · convert h.2 using 1 <;> congr 1 <;> ext i <;> norm_num; exact Fin.elim0 i
    · convert h.1 using 1; congr 1; ext i; norm_num; exact Fin.elim0 i

/-- The native one-cell characteristic map really gives a continuous
oriented path on I. The whole affine argument is in the original closed
ball, so characteristic ContinuousOn applies on its correct domain. No
characteristic map is assumed continuous globally or injective on frontier.
-/
theorem cw_oriented_edge_path
    {K : Type u} [TopologicalSpace K] [T2Space K]
    {C : Set K} [Topology.CWComplex C]
    (e : Topology.RelCWComplex.cell C 1)
    (v w : Topology.RelCWComplex.cell C 0)
    (hlink : (Topology.CWComplex.OneSkeletonGraph C).IsLink e v w) :
    ∃ (σ : ℝ) (γ : Path (Topology.RelCWComplex.map 0 v 0)
      (Topology.RelCWComplex.map 0 w 0)),
      (σ = 1 ∨ σ = -1) ∧ ∀ t : unitInterval,
        γ t = Topology.RelCWComplex.map 1 e (fun _ ↦ σ * (2 * (t : ℝ) - 1)) := by
  obtain ⟨σ, hσ, hstart, hend⟩ := cw_edge_orientation e v w hlink
  let coord : unitInterval → (Fin 1 → ℝ) := fun t _ ↦ σ * (2 * (t : ℝ) - 1)
  have hc : Continuous coord := by
    apply continuous_pi
    intro i
    exact continuous_const.mul ((continuous_const.mul continuous_subtype_val).sub continuous_const)
  have hrange : Set.MapsTo coord Set.univ (Metric.closedBall (0 : Fin 1 → ℝ) 1) := by
    intro t _
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
    intro i
    change ‖σ * (2 * (t : ℝ) - 1)‖ ≤ 1
    rw [norm_mul, Real.norm_eq_abs σ]
    have hs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    rw [hs, one_mul, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [t.property.1, t.property.2]
  let γ : Path (Topology.RelCWComplex.map 0 v 0)
      (Topology.RelCWComplex.map 0 w 0) := {
    toFun := fun t ↦ Topology.RelCWComplex.map 1 e (coord t)
    continuous_toFun := continuousOn_univ.mp
      ((Topology.RelCWComplex.continuousOn 1 e).comp hc.continuousOn hrange)
    source' := by simpa [coord] using hstart
    target' := by simpa [coord, show (2 : ℝ) - 1 = 1 by norm_num] using hend }
  exact ⟨σ, γ, hσ, fun _ ↦ rfl⟩




/-- Actual finite root-arc recursion from the selected parent/depth fields.
Each successive ORIGINAL edge occupies [d(parent),d(child)] in root-height;
the prefix is the same parent arc. This is an agent-written scheduling
variant of Hatcher 1A.1's rooted edge contraction; no contraction is assumed.
The returned continuous map has its literal child endpoint and is constant
at the root before height zero. The recursion strictly decreases depth.
-/
noncomputable def rootedArc
    {V : Type u} {X : Type v} [TopologicalSpace X]
    (r : V) (d : V → ℕ) (hdr : d r = 0) (pt : V → X)
    (parent : {v : V // v ≠ r} → V)
    (hdepth : ∀ v, d (parent v) + 1 = d v.val)
    (edge : ∀ v : {v : V // v ≠ r}, Path (pt (parent v)) (pt v.val))
    (v : V) : {c : C(ℝ, X) // c (d v : ℝ) = pt v ∧ ∀ h : ℝ, h ≤ 0 → c h = pt r} := by
  classical
  by_cases hv : v = r
  · subst v
    exact ⟨ContinuousMap.const ℝ (pt r), rfl, fun _ _ ↦ rfl⟩
  · let w : {v : V // v ≠ r} := ⟨v, hv⟩
    let prev := rootedArc r d hdr pt parent hdepth edge (parent w)
    let γ := edge w
    let c : C(ℝ, X) := ⟨fun h ↦ if h ≤ (d (parent w) : ℝ) then prev.val h
        else γ.extend (h - (d (parent w) : ℝ)), by
      apply continuous_if_le continuous_id continuous_const
      · exact prev.val.continuous.continuousOn
      · exact (γ.extend.continuous.comp (continuous_id.sub continuous_const)).continuousOn
      · intro h heq
        change h = (d (parent w) : ℝ) at heq
        rw [heq, prev.property.1, sub_self, γ.extend_zero]⟩
    refine ⟨c, ?_, ?_⟩
    · have hd := hdepth w
      have hdreal : (d (parent w) : ℝ) + 1 = (d v : ℝ) := by exact_mod_cast hd
      have hlt : ¬ (d v : ℝ) ≤ (d (parent w) : ℝ) := by linarith
      change (if (d v : ℝ) ≤ (d (parent w) : ℝ) then _ else _) = pt v
      rw [ite_eq_right hlt, show (d v : ℝ) - (d (parent w) : ℝ) = 1 by linarith,
        γ.extend_one]
    · intro h hh
      have hle : h ≤ (d (parent w) : ℝ) := hh.trans (Nat.cast_nonneg _)
      change (if h ≤ (d (parent w) : ℝ) then _ else _) = pt r
      rw [ite_eq_left hle]
      exact prev.property.2 h hh
termination_by d v
decreasing_by
  have hd : d (parent ⟨v, hv⟩) + 1 = d v := hdepth ⟨v, hv⟩
  omega


/-- The recursive child arc literally retains its parent arc at every height
up to the parent depth. This is the endpoint agreement needed for the
characteristic-edge contraction, including time one and depth-zero parents. -/
theorem rootedArc_parent_prefix
    {V : Type u} {X : Type v} [TopologicalSpace X]
    (r : V) (d : V → ℕ) (hdr : d r = 0) (pt : V → X)
    (parent : {v : V // v ≠ r} → V)
    (hdepth : ∀ v, d (parent v) + 1 = d v.val)
    (edge : ∀ v : {v : V // v ≠ r}, Path (pt (parent v)) (pt v.val))
    (v : {v : V // v ≠ r}) (h : ℝ) (hh : h ≤ (d (parent v) : ℝ)) :
    (rootedArc r d hdr pt parent hdepth edge v.val).val h =
      (rootedArc r d hdr pt parent hdepth edge (parent v)).val h := by
  rw [rootedArc]
  simp only [dite_eq_right v.property]
  exact ite_eq_left hh

/-- On the added height interval the child arc is exactly the supplied
original oriented edge, including its parent and child endpoints. -/
theorem rootedArc_child_segment
    {V : Type u} {X : Type v} [TopologicalSpace X]
    (r : V) (d : V → ℕ) (hdr : d r = 0) (pt : V → X)
    (parent : {v : V // v ≠ r} → V)
    (hdepth : ∀ v, d (parent v) + 1 = d v.val)
    (edge : ∀ v : {v : V // v ≠ r}, Path (pt (parent v)) (pt v.val))
    (v : {v : V // v ≠ r}) (s : unitInterval) :
    (rootedArc r d hdr pt parent hdepth edge v.val).val
      ((d (parent v) : ℝ) + s.val) = edge v s := by
  rw [rootedArc]
  simp only [dite_eq_right v.property]
  change (if (d (parent v) : ℝ) + s.val ≤ (d (parent v) : ℝ)
    then (rootedArc r d hdr pt parent hdepth edge (parent v)).val
      ((d (parent v) : ℝ) + s.val)
    else (edge v).extend ((d (parent v) : ℝ) + s.val - (d (parent v) : ℝ))) = edge v s
  by_cases hs : s.val = 0
  · have hs0 : s = 0 := Subtype.ext hs
    subst s
    change (if (d (parent v) : ℝ) + 0 ≤ (d (parent v) : ℝ) then _ else _) = _
    simp only [add_zero, le_refl, ite_eq_left]
    simpa using (rootedArc r d hdr pt parent hdepth edge (parent v)).property.1.trans
      (edge v).source.symm
  · have hpos : 0 < s.val := lt_of_le_of_ne s.property.1 (Ne.symm hs)
    rw [ite_eq_right (by linarith), add_sub_cancel_left, Path.extend_extends']


/-- Every finite root arc stays in any set containing the root and all the
selected actual edge paths. No closure or limiting argument is involved. -/
theorem rootedArc_mem
    {V : Type u} {X : Type v} [TopologicalSpace X]
    (r : V) (d : V → ℕ) (hdr : d r = 0) (pt : V → X)
    (parent : {v : V // v ≠ r} → V)
    (hdepth : ∀ v, d (parent v) + 1 = d v.val)
    (edge : ∀ v : {v : V // v ≠ r}, Path (pt (parent v)) (pt v.val))
    (P : Set X) (hroot : pt r ∈ P) (hedge : ∀ v t, edge v t ∈ P)
    (v : V) (h : ℝ) : (rootedArc r d hdr pt parent hdepth edge v).val h ∈ P := by
  classical
  rw [rootedArc]
  split_ifs with hv
  · subst v
    exact hroot
  · change (if h ≤ (d (parent ⟨v, hv⟩) : ℝ) then
      (rootedArc r d hdr pt parent hdepth edge (parent ⟨v, hv⟩)).val h
      else (edge ⟨v, hv⟩).extend (h - (d (parent ⟨v, hv⟩) : ℝ))) ∈ P
    split_ifs
    · exact rootedArc_mem r d hdr pt parent hdepth edge P hroot hedge (parent ⟨v, hv⟩) h
    · have hr : (edge ⟨v, hv⟩).extend (h - (d (parent ⟨v, hv⟩) : ℝ)) ∈
          Set.range (edge ⟨v, hv⟩) := by
        rw [← Path.extend_range]
        exact Set.mem_range_self _
      obtain ⟨t, ht⟩ := hr
      rw [← ht]
      exact hedge _ t
termination_by d v
decreasing_by
  have hd : d (parent ⟨v, hv⟩) + 1 = d v := hdepth ⟨v, hv⟩
  omega


/-- Hatcher 1A.1's rooted-tree contraction on each actual oriented edge.
The finite root arcs above furnish continuous vertex tracks and continuous
edge squares. All four faces are verified literally, and the root is fixed.
This is the finite-path radial scheduling variant of the published edge-layer
collapse, not a contraction assumption on the tree or its weak CW topology. -/
theorem rooted_tree_edge_tracks
    {V : Type u} {X : Type v} [TopologicalSpace X]
    (r : V) (d : V → ℕ) (hdr : d r = 0) (pt : V → X)
    (parent : {v : V // v ≠ r} → V)
    (hdepth : ∀ v, d (parent v) + 1 = d v.val)
    (edge : ∀ v : {v : V // v ≠ r}, Path (pt (parent v)) (pt v.val)) :
    ∃ (Cv : V → C(unitInterval, X))
      (Ce : {v : V // v ≠ r} → C(unitInterval × unitInterval, X)),
      (∀ v, Cv v 0 = pt v) ∧
      (∀ v, Cv v 1 = pt r) ∧
      (∀ t, Cv r t = pt r) ∧
      (∀ v s, Ce v (0, s) = edge v s) ∧
      (∀ v s, Ce v (1, s) = pt r) ∧
      (∀ v t, Ce v (t, 0) = Cv (parent v) t) ∧
      (∀ v t, Ce v (t, 1) = Cv v.val t) ∧
      (∀ P : Set X, pt r ∈ P → (∀ v t, edge v t ∈ P) →
        (∀ v t, Cv v t ∈ P) ∧ (∀ v q, Ce v q ∈ P)) := by
  let arc := fun v ↦ (rootedArc r d hdr pt parent hdepth edge v).val
  let Cv : V → C(unitInterval, X) := fun v ↦
    ⟨fun t ↦ arc v ((1 - t.val) * (d v : ℝ)),
      (arc v).continuous.comp
        ((continuous_const.sub continuous_subtype_val).mul continuous_const)⟩
  let Ce : {v : V // v ≠ r} → C(unitInterval × unitInterval, X) := fun v ↦
    ⟨fun q ↦ arc v.val ((1 - q.1.val) * ((d (parent v) : ℝ) + q.2.val)),
      (arc v.val).continuous.comp
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          (continuous_const.add (continuous_subtype_val.comp continuous_snd)))⟩
  refine ⟨Cv, Ce, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    change arc v ((1 - (0 : unitInterval).val) * (d v : ℝ)) = pt v
    simpa [arc] using (rootedArc r d hdr pt parent hdepth edge v).property.1
  · intro v
    change arc v ((1 - (1 : unitInterval).val) * (d v : ℝ)) = pt r
    simpa [arc] using (rootedArc r d hdr pt parent hdepth edge v).property.2 0 le_rfl
  · intro t
    change arc r ((1 - t.val) * (d r : ℝ)) = pt r
    rw [hdr]
    simpa [arc] using (rootedArc r d hdr pt parent hdepth edge r).property.2 0 le_rfl
  · intro v s
    change arc v.val ((1 - (0 : unitInterval).val) * ((d (parent v) : ℝ) + s.val)) = _
    simpa [arc] using rootedArc_child_segment r d hdr pt parent hdepth edge v s
  · intro v s
    change arc v.val ((1 - (1 : unitInterval).val) * ((d (parent v) : ℝ) + s.val)) = _
    simpa [arc] using (rootedArc r d hdr pt parent hdepth edge v.val).property.2 0 le_rfl
  · intro v t
    change arc v.val ((1 - t.val) * ((d (parent v) : ℝ) + (0 : unitInterval).val)) =
      arc (parent v) ((1 - t.val) * (d (parent v) : ℝ))
    simp only [show (0 : unitInterval).val = (0 : ℝ) from rfl, add_zero]
    apply rootedArc_parent_prefix
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith [t.property.1])
  · intro v t
    change arc v.val ((1 - t.val) * ((d (parent v) : ℝ) + (1 : unitInterval).val)) =
      arc v.val ((1 - t.val) * (d v.val : ℝ))
    have hd : (d (parent v) : ℝ) + 1 = (d v.val : ℝ) := by exact_mod_cast hdepth v
    rw [show (1 : unitInterval).val = (1 : ℝ) from rfl, hd]
  · intro P hr he
    constructor
    · intro v t
      exact rootedArc_mem r d hdr pt parent hdepth edge P hr he v _
    · intro v q
      exact rootedArc_mem r d hdr pt parent hdepth edge P hr he v.val _


/-- Any boundary point of an original one-cell is an actual zero-cell point.
The characteristic map may identify its two endpoints; no regularity is used. -/
theorem cw_one_cell_boundary_is_vertex
    {K : Type u} [TopologicalSpace K] {C : Set K} [Topology.CWComplex C]
    (e : Topology.RelCWComplex.cell C 1) (z : Fin 1 → ℝ) (hz : ‖z‖ = 1) :
    ∃ v : Topology.RelCWComplex.cell C 0,
      Topology.RelCWComplex.map 1 e z = Topology.RelCWComplex.map 0 v 0 := by
  have hx : Topology.RelCWComplex.map 1 e z ∈ Topology.CWComplex.cellFrontier 1 e :=
    ⟨z, by simpa [Metric.mem_sphere, dist_zero_right] using hz, rfl⟩
  obtain ⟨v, w, hvw⟩ := Topology.CWComplex.exists_cellFrontier_one_eq e
  rw [hvw, Topology.CWComplex.closedCell_zero_eq_singleton,
    Topology.CWComplex.closedCell_zero_eq_singleton] at hx
  rcases hx with hx | hx
  · exact ⟨v, by simpa using hx⟩
  · exact ⟨w, by simpa using hx⟩

/-- An interior characteristic point of a one-cell cannot be a zero-cell
point, by disjointness of the original open cells. -/
theorem cw_one_cell_interior_ne_vertex
    {K : Type u} [TopologicalSpace K] {C : Set K} [Topology.CWComplex C]
    (e : Topology.RelCWComplex.cell C 1) (z : Fin 1 → ℝ) (hz : ‖z‖ < 1)
    (v : Topology.RelCWComplex.cell C 0) :
    Topology.RelCWComplex.map 1 e z ≠ Topology.RelCWComplex.map 0 v 0 := by
  intro heq
  have hx : Topology.RelCWComplex.map 1 e z ∈ Topology.CWComplex.openCell 1 e :=
    ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz, rfl⟩
  have hv : Topology.RelCWComplex.map 0 v 0 ∈ Topology.CWComplex.openCell 0 v := by
    rw [Topology.CWComplex.openCell_zero_eq_singleton]
    simp
  exact (Set.disjoint_left.mp (Topology.CWComplex.disjoint_openCell_of_ne
    (by intro h; have := congrArg Sigma.fst h; simp at this))) hx (heq.symm ▸ hv)

/-- Compatibility of edge squares at every coincident characteristic point.
Interior coincidences force the same original edge and coordinate; boundary
coincidences reduce to the literal common vertex track. This includes loop
endpoints and distinct parallel original edges. -/
theorem cw_one_cell_prism_compatibility
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    {C : Set K} [Topology.CWComplex C]
    (Cv : Topology.RelCWComplex.cell C 0 → C(unitInterval, Y))
    (Pe : Topology.RelCWComplex.cell C 1 →
      C(unitInterval × Metric.closedBall (0 : Fin 1 → ℝ) 1, Y))
    (hb : ∀ e (z : Metric.closedBall (0 : Fin 1 → ℝ) 1) v t,
      ‖z.val‖ = 1 → Topology.RelCWComplex.map 1 e z.val =
        Topology.RelCWComplex.map 0 v 0 → Pe e (t, z) = Cv v t)
    (e f : Topology.RelCWComplex.cell C 1) (t : unitInterval)
    (z w : Metric.closedBall (0 : Fin 1 → ℝ) 1)
    (heq : Topology.RelCWComplex.map 1 e z.val = Topology.RelCWComplex.map 1 f w.val) :
    Pe e (t, z) = Pe f (t, w) := by
  have hzle : ‖z.val‖ ≤ 1 := by
    have h := z.property
    change dist z.val 0 ≤ 1 at h
    rwa [dist_zero_right] at h
  have hwle : ‖w.val‖ ≤ 1 := by
    have h := w.property
    change dist w.val 0 ≤ 1 at h
    rwa [dist_zero_right] at h
  by_cases hz : ‖z.val‖ < 1
  · have hw : ‖w.val‖ < 1 := by
      by_contra hn
      have hw1 : ‖w.val‖ = 1 := le_antisymm hwle (le_of_not_gt hn)
      obtain ⟨v, hv⟩ := cw_one_cell_boundary_is_vertex f w.val hw1
      exact cw_one_cell_interior_ne_vertex e z.val hz v (heq.trans hv)
    have he : e = f := by
      have hni : ¬ Disjoint (Topology.CWComplex.openCell 1 e)
          (Topology.CWComplex.openCell 1 f) := Set.not_disjoint_iff.mpr
        ⟨Topology.RelCWComplex.map 1 e z.val,
          ⟨z.val, by simpa [Metric.mem_ball, dist_zero_right] using hz, rfl⟩,
          ⟨w.val, by simpa [Metric.mem_ball, dist_zero_right] using hw, heq.symm⟩⟩
      have hs := Topology.CWComplex.eq_of_not_disjoint_openCell hni
      exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
    subst f
    have hzw : z = w := Subtype.ext ((Topology.RelCWComplex.map 1 e).injOn
      (by rw [Topology.RelCWComplex.source_eq]; simpa [Metric.mem_ball, dist_zero_right] using hz)
      (by rw [Topology.RelCWComplex.source_eq]; simpa [Metric.mem_ball, dist_zero_right] using hw) heq)
    rw [hzw]
  · have hz1 : ‖z.val‖ = 1 := le_antisymm hzle (le_of_not_gt hz)
    obtain ⟨v, hv⟩ := cw_one_cell_boundary_is_vertex e z.val hz1
    have hw1 : ‖w.val‖ = 1 := by
      by_contra hn
      have hw : ‖w.val‖ < 1 := lt_of_le_of_ne hwle hn
      exact cw_one_cell_interior_ne_vertex f w.val hw v (heq.symm.trans hv)
    exact (hb e z v t hz1 hv).trans (hb f w v t hw1 (heq.symm.trans hv)).symm


/-- A complete one-dimensional weak-CW gluing step. Actual continuous
vertex tracks and characteristic-edge squares with literal boundary agreement
define an ordinary jointly continuous map on the inherited CW carrier.
No finite-edge, regular-cell, or local-finiteness assumption is added. -/
theorem cw_one_dimensional_glue_edge_tracks
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] (C : Set K) [Topology.CWComplex C]
    (hhigh : ∀ n, IsEmpty (Topology.RelCWComplex.cell C (n + 2)))
    (Cv : Topology.RelCWComplex.cell C 0 → C(unitInterval, Y))
    (Pe : Topology.RelCWComplex.cell C 1 →
      C(unitInterval × Metric.closedBall (0 : Fin 1 → ℝ) 1, Y))
    (hb : ∀ e (z : Metric.closedBall (0 : Fin 1 → ℝ) 1) v t,
      ‖z.val‖ = 1 → Topology.RelCWComplex.map 1 e z.val =
        Topology.RelCWComplex.map 0 v 0 → Pe e (t, z) = Cv v t) :
    ∃ H : C(unitInterval × C, Y),
      (∀ v t, H (t, ⟨Topology.RelCWComplex.map 0 v 0,
        Topology.RelCWComplex.closedCell_subset_complex 0 v
          ⟨0, by simp, rfl⟩⟩) = Cv v t) ∧
      (∀ e t z, H (t, ⟨Topology.RelCWComplex.map 1 e z.val,
        Topology.RelCWComplex.closedCell_subset_complex 1 e
          ⟨z.val, z.property, rfl⟩⟩) = Pe e (t, z)) := by
  let P : ∀ n, ∀ i : Topology.RelCWComplex.cell C n,
      C(unitInterval × Metric.closedBall (0 : Fin n → ℝ) 1, Y) := fun n ↦
    match n with
    | 0 => fun i ↦ (Cv i).comp ContinuousMap.fst
    | 1 => Pe
    | n + 2 => fun i ↦ by have := hhigh n; exact isEmptyElim i
  have hv_inj : Function.Injective (fun v : Topology.RelCWComplex.cell C 0 ↦
      Topology.RelCWComplex.map 0 v 0) := by
    intro v w heq
    apply Topology.RelCWComplex.injective_map_zero C
    simpa only [show (![] : Fin 0 → ℝ) = 0 from Subsingleton.elim _ _] using heq
  have hboundary : ∀ (e : Topology.RelCWComplex.cell C 1)
      (z : Metric.closedBall (0 : Fin 1 → ℝ) 1) (v : Topology.RelCWComplex.cell C 0),
      Topology.RelCWComplex.map 1 e z.val = Topology.RelCWComplex.map 0 v 0 →
      ‖z.val‖ = 1 := by
    intro e z v heq
    have hzle : ‖z.val‖ ≤ 1 := by
      have h := z.property
      change dist z.val 0 ≤ 1 at h
      rwa [dist_zero_right] at h
    by_contra hn
    exact cw_one_cell_interior_ne_vertex e z.val (lt_of_le_of_ne hzle hn) v heq
  have hcompat : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell C n)
      (m : ℕ) (j : Topology.RelCWComplex.cell C m) (t : unitInterval)
      (z : Metric.closedBall (0 : Fin n → ℝ) 1)
      (w : Metric.closedBall (0 : Fin m → ℝ) 1),
      Topology.RelCWComplex.map n i z.val = Topology.RelCWComplex.map m j w.val →
      P n i (t, z) = P m j (t, w) := by
    intro n i m j t z w heq
    cases n with
    | zero =>
      have hz : z.val = 0 := Subsingleton.elim _ _
      rw [hz] at heq
      cases m with
      | zero =>
        have hw : w.val = 0 := Subsingleton.elim _ _
        rw [hw] at heq
        have hi := hv_inj heq
        subst j
        rfl
      | succ m =>
        cases m with
        | zero => exact (hb j w i t (hboundary j w i heq.symm) heq.symm).symm
        | succ m => have := hhigh m; exact isEmptyElim j
    | succ n =>
      cases n with
      | zero =>
        cases m with
        | zero =>
          have hw : w.val = 0 := Subsingleton.elim _ _
          rw [hw] at heq
          exact hb i z j t (hboundary i z j heq) heq
        | succ m =>
          cases m with
          | zero => exact cw_one_cell_prism_compatibility Cv Pe hb i j t z w heq
          | succ m => have := hhigh m; exact isEmptyElim j
      | succ n => have := hhigh n; exact isEmptyElim i
  obtain ⟨H, hH⟩ := cw_subtype_glue_characteristic_prisms C P hcompat
  refine ⟨H, ?_, ?_⟩
  · intro v t
    exact hH 0 v t ⟨0, by simp⟩
  · intro e t z
    exact hH 1 e t z


/-- Exact inverse oriented coordinate on the native one-cell disk. The
endpoints go to 0 or 1; the whole characteristic vector is recovered, not
merely its norm or its image in a replacement graph. -/
theorem native_one_disk_oriented_coordinate (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ s : C(Metric.closedBall (0 : Fin 1 → ℝ) 1, unitInterval),
      (∀ z, z.val = fun _ ↦ σ * (2 * (s z).val - 1)) ∧
      (∀ z, ‖z.val‖ = 1 → s z = 0 ∨ s z = 1) := by
  have hzbound : ∀ z : Metric.closedBall (0 : Fin 1 → ℝ) 1, |z.val 0| ≤ 1 := by
    intro z
    have h := z.property
    change dist z.val 0 ≤ 1 at h
    rw [dist_zero_right] at h
    exact (norm_le_pi_norm z.val 0).trans h
  have hguard : ∀ z : Metric.closedBall (0 : Fin 1 → ℝ) 1,
      (σ * z.val 0 + 1) / 2 ∈ unitInterval := by
    intro z
    have hz := abs_le.mp (hzbound z)
    rcases hσ with hσ | hσ <;> rw [hσ] <;> constructor <;> linarith
  let s : C(Metric.closedBall (0 : Fin 1 → ℝ) 1, unitInterval) :=
    ⟨fun z ↦ ⟨(σ * z.val 0 + 1) / 2, hguard z⟩,
      (((continuous_const.mul ((continuous_apply 0).comp continuous_subtype_val)).add
        continuous_const).div_const 2).subtype_mk hguard⟩
  refine ⟨s, ?_, ?_⟩
  · intro z
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change z.val 0 = σ * (2 * ((σ * z.val 0 + 1) / 2) - 1)
    rcases hσ with hσ | hσ <;> rw [hσ] <;> ring
  · intro z hz
    have hconst : z.val = fun _ ↦ z.val 0 := by
      funext i
      exact congrArg z.val (Subsingleton.elim _ _)
    have hzabs : |z.val 0| = 1 := by
      rw [hconst, pi_norm_const, Real.norm_eq_abs] at hz
      exact hz
    have hzi : z.val 0 = 1 ∨ z.val 0 = -1 := (abs_eq (by norm_num)).mp hzabs
    rcases hσ with hσ | hσ <;> rcases hzi with hzi | hzi
    · right; apply Subtype.ext; change (σ * z.val 0 + 1) / 2 = 1; rw [hσ, hzi]; norm_num
    · left; apply Subtype.ext; change (σ * z.val 0 + 1) / 2 = 0; rw [hσ, hzi]; norm_num
    · left; apply Subtype.ext; change (σ * z.val 0 + 1) / 2 = 0; rw [hσ, hzi]; norm_num
    · right; apply Subtype.ext; change (σ * z.val 0 + 1) / 2 = 1; rw [hσ, hzi]; norm_num


/-- Root-preserving contraction of the inclusion of an actual rooted CW tree.
The data are ONLY the original one-dimensional cells, selected parent edge
bijection, and decreasing natural depths. Continuous finite root arcs give
edge squares, their endpoints give overlap compatibility, and the proved
ordinary-product weak-CW gluing supplies the global continuous contraction.
There is no assumed contraction, HEP, local finiteness, regularity, or finite
depth bound. This is Hatcher 1A.1's collapse with finite-root-path radial
scheduling, whose reparameterization is proved in the preceding helpers. -/
theorem rooted_cw_tree_inclusion_contraction
    {K : Type u} [TopologicalSpace K] [T2Space K]
    (C : Set K) [Topology.CWComplex C]
    (hhigh : ∀ n, IsEmpty (Topology.RelCWComplex.cell C (n + 2)))
    (r : Topology.RelCWComplex.cell C 0)
    (d : Topology.RelCWComplex.cell C 0 → ℕ) (hdr : d r = 0)
    (parent : {v : Topology.RelCWComplex.cell C 0 // v ≠ r} →
      Topology.RelCWComplex.cell C 0)
    (hdepth : ∀ v, d (parent v) + 1 = d v.val)
    (edge : {v : Topology.RelCWComplex.cell C 0 // v ≠ r} ≃
      Topology.RelCWComplex.cell C 1)
    (hlink : ∀ v, (Topology.CWComplex.OneSkeletonGraph C).IsLink
      (edge v) (parent v) v.val) :
    ∃ H : C(unitInterval × C, K),
      (∀ x, H (0, x) = x.val) ∧
      (∀ x, H (1, x) = Topology.RelCWComplex.map 0 r 0) ∧
      (∀ t, H (t, ⟨Topology.RelCWComplex.map 0 r 0,
        Topology.RelCWComplex.closedCell_subset_complex 0 r ⟨0, by simp, rfl⟩⟩) =
        Topology.RelCWComplex.map 0 r 0) ∧
      (∀ q, H q ∈ C) := by
  classical
  let pt := fun v : Topology.RelCWComplex.cell C 0 ↦ Topology.RelCWComplex.map 0 v 0
  have hinj : Function.Injective pt := by
    intro v w heq
    apply Topology.RelCWComplex.injective_map_zero C
    simpa only [show (![] : Fin 0 → ℝ) = 0 from Subsingleton.elim _ _] using heq
  have hpaths : ∀ v : {v : Topology.RelCWComplex.cell C 0 // v ≠ r},
      ∃ (σ : ℝ) (γ : Path (pt (parent v)) (pt v.val)),
      (σ = 1 ∨ σ = -1) ∧ ∀ t : unitInterval,
        γ t = Topology.RelCWComplex.map 1 (edge v) (fun _ ↦ σ * (2 * t.val - 1)) := by
    intro v
    exact cw_oriented_edge_path (edge v) (parent v) v.val (hlink v)
  choose σ γ hσ hγ using hpaths
  have hcoords : ∀ v : {v : Topology.RelCWComplex.cell C 0 // v ≠ r},
      ∃ s : C(Metric.closedBall (0 : Fin 1 → ℝ) 1, unitInterval),
      (∀ z, z.val = fun _ ↦ σ v * (2 * (s z).val - 1)) ∧
      (∀ z, ‖z.val‖ = 1 → s z = 0 ∨ s z = 1) :=
    fun v ↦ native_one_disk_oriented_coordinate (σ v) (hσ v)
  choose s hrecover hends using hcoords
  have hpoint : ∀ v z, γ v (s v z) = Topology.RelCWComplex.map 1 (edge v) z.val := by
    intro v z
    rw [hγ, ← hrecover]
  obtain ⟨Cv, Ce, hCv0, hCv1, hCvr, hCe0, hCe1, hCel, hCer, hRange⟩ :=
    rooted_tree_edge_tracks r d hdr pt parent hdepth γ
  let Pe : Topology.RelCWComplex.cell C 1 →
      C(unitInterval × Metric.closedBall (0 : Fin 1 → ℝ) 1, K) := fun e ↦
    (Ce (edge.symm e)).comp
      (ContinuousMap.fst.prodMk ((s (edge.symm e)).comp ContinuousMap.snd))
  have hb : ∀ e (z : Metric.closedBall (0 : Fin 1 → ℝ) 1) w t,
      ‖z.val‖ = 1 → Topology.RelCWComplex.map 1 e z.val = pt w →
      Pe e (t, z) = Cv w t := by
    intro e z w t hz heq
    let v := edge.symm e
    have hv : γ v (s v z) = pt w := by
      rw [hpoint]
      simpa only [v, edge.apply_symm_apply] using heq
    change Ce v (t, s v z) = Cv w t
    rcases hends v z hz with hs | hs
    · rw [hs, Path.source] at hv
      have hw := hinj hv
      rw [hs, hCel, hw]
    · rw [hs, Path.target] at hv
      have hw := hinj hv
      rw [hs, hCer, hw]
  obtain ⟨H, hH0, hH1⟩ := cw_one_dimensional_glue_edge_tracks C hhigh Cv Pe hb
  have hrepr : ∀ x : C,
      (∃ v : Topology.RelCWComplex.cell C 0, x.val = pt v) ∨
      ∃ e : Topology.RelCWComplex.cell C 1,
        ∃ z : Metric.closedBall (0 : Fin 1 → ℝ) 1,
          x.val = Topology.RelCWComplex.map 1 e z.val := by
    intro x
    have hx : x.val ∈ ⋃ n : ℕ, ⋃ i : Topology.RelCWComplex.cell C n,
        Topology.CWComplex.closedCell n i := by
      rw [Topology.CWComplex.union]
      exact x.property
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, z, hz, hzx⟩ := Set.mem_iUnion.mp hx
    cases n with
    | zero =>
      left
      refine ⟨i, ?_⟩
      have hz0 : z = 0 := Subsingleton.elim _ _
      simpa only [hz0] using hzx.symm
    | succ n =>
      cases n with
      | zero => exact Or.inr ⟨i, ⟨z, hz⟩, hzx.symm⟩
      | succ n => have := hhigh n; exact isEmptyElim i
  have hptmem : pt r ∈ C :=
    Topology.RelCWComplex.closedCell_subset_complex 0 r ⟨0, by simp, rfl⟩
  have hγmem : ∀ v t, γ v t ∈ C := by
    intro v t
    rw [hγ]
    apply Topology.RelCWComplex.closedCell_subset_complex 1 (edge v)
    refine ⟨(fun _ ↦ σ v * (2 * t.val - 1)), ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_const, norm_mul,
      Real.norm_eq_abs]
    have hs : |σ v| = 1 := by rcases hσ v with hs | hs <;> rw [hs] <;> norm_num
    rw [hs, one_mul, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [t.property.1, t.property.2]
  have hrange := hRange C hptmem hγmem
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · intro x
    rcases hrepr x with ⟨v, hv⟩ | ⟨e, z, hz⟩
    · have hx : x = ⟨Topology.RelCWComplex.map 0 v 0,
        Topology.RelCWComplex.closedCell_subset_complex 0 v ⟨0, by simp, rfl⟩⟩ :=
        Subtype.ext hv
      rw [hx, hH0, hCv0]
    · have hx : x = ⟨Topology.RelCWComplex.map 1 e z.val,
        Topology.RelCWComplex.closedCell_subset_complex 1 e ⟨z.val, z.property, rfl⟩⟩ :=
        Subtype.ext hz
      rw [hx, hH1]
      change Ce (edge.symm e) (0, s (edge.symm e) z) = _
      rw [hCe0, hpoint, edge.apply_symm_apply]
  · intro x
    rcases hrepr x with ⟨v, hv⟩ | ⟨e, z, hz⟩
    · have hx : x = ⟨Topology.RelCWComplex.map 0 v 0,
        Topology.RelCWComplex.closedCell_subset_complex 0 v ⟨0, by simp, rfl⟩⟩ :=
        Subtype.ext hv
      rw [hx, hH0]
      exact hCv1 v
    · have hx : x = ⟨Topology.RelCWComplex.map 1 e z.val,
        Topology.RelCWComplex.closedCell_subset_complex 1 e ⟨z.val, z.property, rfl⟩⟩ :=
        Subtype.ext hz
      rw [hx, hH1]
      exact hCe1 _ _
  · intro t
    rw [hH0]
    exact hCvr t
  · intro q
    rcases hrepr q.2 with ⟨v, hv⟩ | ⟨e, z, hz⟩
    · have hx : q.2 = ⟨Topology.RelCWComplex.map 0 v 0,
        Topology.RelCWComplex.closedCell_subset_complex 0 v ⟨0, by simp, rfl⟩⟩ :=
        Subtype.ext hv
      change H (q.1, q.2) ∈ C
      rw [hx, hH0]
      exact hrange.1 v q.1
    · have hx : q.2 = ⟨Topology.RelCWComplex.map 1 e z.val,
        Topology.RelCWComplex.closedCell_subset_complex 1 e ⟨z.val, z.property, rfl⟩⟩ :=
        Subtype.ext hz
      change H (q.1, q.2) ∈ C
      rw [hx, hH1]
      exact hrange.2 (edge.symm e) (q.1, s (edge.symm e) z)


/-- Application to the ORIGINAL labelled spanning-tree output. The original
zero-cell labels and selected parent-edge labels are explicitly reindexed to
the literal CW subcomplex cell types. Its inherited topology and characteristic
maps remain unchanged; all contraction data are constructed, not assumed.
The only imported source theorem here is the existing spanning-tree provider. -/
theorem cw_spanning_tree_inclusion_contraction
    {K : Type u} [TopologicalSpace K] [T2Space K] [ConnectedSpace K]
    [Topology.CWComplex (Set.univ : Set K)]
    (r : Topology.RelCWComplex.cell (Set.univ : Set K) 0) :
    ∃ T : Topology.CWComplex.Subcomplex (Set.univ : Set K),
      Topology.CWComplex.skeleton (Set.univ : Set K) 0 ≤ T ∧
      T ≤ Topology.CWComplex.skeleton (Set.univ : Set K) 1 ∧
      ∃ (hr : Topology.RelCWComplex.map 0 r 0 ∈ (T : Set K))
        (H : C(unitInterval × (T : Set K), K)),
        (∀ x, H (0, x) = x.val) ∧
        (∀ x, H (1, x) = Topology.RelCWComplex.map 0 r 0) ∧
        (∀ t, H (t, ⟨Topology.RelCWComplex.map 0 r 0, hr⟩) =
          Topology.RelCWComplex.map 0 r 0) ∧
        (∀ q, H q ∈ (T : Set K)) := by
  classical
  obtain ⟨d, parent, edge, T, _, hdr, hlink, hdepth, hinj,
    _, _, _, _, _, hI0, hI1, hhigh, _, _, hzero, hone⟩ := cw_realization_spanning_tree r
  let e0 : Topology.RelCWComplex.cell (Set.univ : Set K) 0 ≃
      Topology.RelCWComplex.cell (T : Set K) 0 := {
    toFun := fun v ↦ ⟨v, by rw [hI0]; trivial⟩
    invFun := fun v ↦ v.val
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ Subtype.ext rfl }
  let nr : {v : Topology.RelCWComplex.cell (T : Set K) 0 // v ≠ e0 r} ≃
      {v : Topology.RelCWComplex.cell (Set.univ : Set K) 0 // v ≠ r} := {
    toFun := fun v ↦ ⟨v.val.val, by
      intro h
      apply v.property
      exact Subtype.ext h⟩
    invFun := fun v ↦ ⟨e0 v.val, by
      intro h
      exact v.property (congrArg Subtype.val h)⟩
    left_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ ↦ Subtype.ext rfl }
  let selected : {v : Topology.RelCWComplex.cell (Set.univ : Set K) 0 // v ≠ r} →
      Topology.RelCWComplex.cell (T : Set K) 1 :=
    fun v ↦ ⟨edge v, by rw [hI1]; exact ⟨v, rfl⟩⟩
  have hselected : Function.Bijective selected := by
    constructor
    · intro v w heq
      exact hinj (congrArg Subtype.val heq)
    · intro e
      have he : e.val ∈ Set.range edge := by
        have he := e.property
        change e.val ∈ T.I 1 at he
        simpa only [hI1] using he
      obtain ⟨v, hv⟩ := he
      exact ⟨v, Subtype.ext hv⟩
  let e1 := nr.trans (Equiv.ofBijective selected hselected)
  let dT : Topology.RelCWComplex.cell (T : Set K) 0 → ℕ := fun v ↦ d v.val
  let parentT := fun v : {v : Topology.RelCWComplex.cell (T : Set K) 0 // v ≠ e0 r} ↦
    e0 (parent (nr v))
  have hdT : ∀ v, dT (parentT v) + 1 = dT v.val := by
    intro v
    exact hdepth (nr v)
  have hlT : ∀ v, (Topology.CWComplex.OneSkeletonGraph (T : Set K)).IsLink
      (e1 v) (parentT v) v.val := by
    intro v
    change Topology.RelCWComplex.cellFrontier (C := Set.univ) 1 (edge (nr v)) =
      Topology.RelCWComplex.closedCell (C := Set.univ) 0 (parent (nr v)) ∪
        Topology.RelCWComplex.closedCell (C := Set.univ) 0 v.val.val
    exact (hlink (nr v)).symm
  have hhighT : ∀ n, IsEmpty (Topology.RelCWComplex.cell (T : Set K) (n + 2)) := by
    intro n
    refine ⟨fun i ↦ ?_⟩
    have hi := i.property
    change i.val ∈ T.I (n + 2) at hi
    simp only [hhigh n, Set.mem_empty_iff_false] at hi
  obtain ⟨H, hH0, hH1, hHr, hHmem⟩ := rooted_cw_tree_inclusion_contraction
    (T : Set K) hhighT (e0 r) dT hdr parentT hdT e1 hlT
  have hr : Topology.RelCWComplex.map 0 r 0 ∈ (T : Set K) :=
    Topology.RelCWComplex.closedCell_subset_complex 0 (e0 r) ⟨0, by simp, rfl⟩
  exact ⟨T, hzero, hone, hr, H, hH0, hH1, hHr, hHmem⟩


/-- The actual HEP application that collapses a given map on a constructed
rooted subcomplex. Its endpoint map is constant on that SAME subcomplex, and
the original-to-endpoint homotopy fixes the root point. No equality or
constancy is assumed away from the explicitly contracting carrier. -/
theorem cw_collapse_map_on_contracting_subcomplex
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set K))
    (r : (B : Set K)) (C : C(unitInterval × (B : Set K), K))
    (hC0 : ∀ x, C (0, x) = x.val) (hC1 : ∀ x, C (1, x) = r.val)
    (hCr : ∀ t, C (t, r) = r.val) (f : C(K, Y)) :
    ∃ f' : C(K, Y), Nonempty (ContinuousMap.HomotopyRel f f' {r.val}) ∧
      ∀ b : (B : Set K), f' b.val = f r.val := by
  let h : C(unitInterval × (B : Set K), Y) := f.comp C
  have h₀ : ∀ b : (B : Set K), h (0, b) = f b.val := by
    intro b
    change f (C (0, b)) = f b.val
    rw [hC0]
  obtain ⟨H, hH0, hHB, _⟩ := cw_pair_homotopy_extension B f h h₀
  let f' : C(K, Y) := H.comp ((ContinuousMap.const K (1 : unitInterval)).prodMk
    (ContinuousMap.id K))
  refine ⟨f', ⟨{
    toFun := H
    continuous_toFun := H.continuous
    map_zero_left := hH0
    map_one_left := fun _ ↦ rfl
    prop' := ?_ }⟩, ?_⟩
  · intro t x hx
    have hx' : x = r.val := Set.mem_singleton_iff.mp hx
    subst x
    change H (t, r.val) = f r.val
    rw [hHB]
    change f (C (t, r)) = f r.val
    rw [hCr]
  · intro b
    change H (1, b.val) = f r.val
    rw [hHB]
    change f (C (1, b)) = f r.val
    rw [hC1]


/-- Hatcher 1B.9's actual successor-cell filling. On the original (n+1)-cell
its whole boundary sphere maps into the original n-skeleton, including every
noninjective attaching identification. Paste the actual f/g bottom and top
with the GIVEN n-stage side, then fill the entire prism using the supplied
contractible covering. All bottom/top/side equations are retained literally.
This constructs the cell input needed for successor weak-CW descent. -/
theorem cw_successor_characteristic_prism_filling
    {K : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace E]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)] [ContractibleSpace E]
    (n : ℕ) (hn : 1 ≤ n) (p : E → Y) (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) (f g : C(K, Y))
    (H : C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K), Y))
    (hH0 : ∀ x, H (0, x) = f x.val) (hH1 : ∀ x, H (1, x) = g x.val)
    (i : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1)) :
    ∃ P : C(unitInterval × Metric.closedBall (0 : Fin (n + 1) → ℝ) 1, Y),
      (∀ z, P (0, z) = f (Topology.RelCWComplex.map (n + 1) i z.val)) ∧
      (∀ z, P (1, z) = g (Topology.RelCWComplex.map (n + 1) i z.val)) ∧
      (∀ t (z : Metric.closedBall (0 : Fin (n + 1) → ℝ) 1) (hz : ‖z.val‖ = 1),
        P (t, z) = H (t, ⟨Topology.RelCWComplex.map (n + 1) i z.val,
          Topology.CWComplex.cellFrontier_subset_skeleton n i
            ⟨z.val, by simpa [Metric.mem_sphere, dist_zero_right] using hz, rfl⟩⟩)) := by
  let χ : C({z : Fin (n + 1) → ℝ // ‖z‖ ≤ 1}, K) :=
    ⟨fun z ↦ Topology.RelCWComplex.map (n + 1) i z.val,
      (Topology.RelCWComplex.continuousOn (n + 1) i).comp_continuous
        continuous_subtype_val (by intro z; simpa [Metric.mem_closedBall, dist_zero_right] using z.property)⟩
  let χs : C({z : Fin (n + 1) → ℝ // ‖z‖ = 1},
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)) :=
    ⟨fun z ↦ ⟨Topology.RelCWComplex.map (n + 1) i z.val,
      Topology.CWComplex.cellFrontier_subset_skeleton n i
        ⟨z.val, by simpa [Metric.mem_sphere, dist_zero_right] using z.property, rfl⟩⟩,
      by
        apply Continuous.subtype_mk
        exact (Topology.RelCWComplex.continuousOn (n + 1) i).comp_continuous
          continuous_subtype_val (by
            intro z
            simpa [Metric.mem_closedBall, dist_zero_right] using le_of_eq z.property)⟩
  let side : C(unitInterval × {z : Fin (n + 1) → ℝ // ‖z‖ = 1}, Y) :=
    H.comp (ContinuousMap.fst.prodMk (χs.comp ContinuousMap.snd))
  have hside0 : ∀ z, side (0, z) = (f.comp χ) ⟨z.val, le_of_eq z.property⟩ :=
    fun z ↦ hH0 (χs z)
  have hside1 : ∀ z, side (1, z) = (g.comp χ) ⟨z.val, le_of_eq z.property⟩ :=
    fun z ↦ hH1 (χs z)
  obtain ⟨B, hB0, hB1, hBs⟩ := native_prism_boundary_pasting (n + 1)
    (f.comp χ) (g.comp χ) side hside0 hside1
  obtain ⟨F, hF⟩ := covering_contractible_native_prism_filling (n + 1)
    (by omega) p hp hsurj B
  let toNative : C(Metric.closedBall (0 : Fin (n + 1) → ℝ) 1,
      {z : Fin (n + 1) → ℝ // ‖z‖ ≤ 1}) :=
    ⟨fun z ↦ ⟨z.val, by
      have h := z.property
      change dist z.val 0 ≤ 1 at h
      rwa [dist_zero_right] at h⟩, by
        apply Continuous.subtype_mk
        exact continuous_subtype_val⟩
  let P : C(unitInterval × Metric.closedBall (0 : Fin (n + 1) → ℝ) 1, Y) :=
    F.comp ((toNative.comp ContinuousMap.snd).prodMk ContinuousMap.fst)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro z
    change F (toNative z, 0) = f (χ (toNative z))
    exact (hF ⟨(toNative z, 0), Or.inr (Or.inl rfl)⟩).trans (hB0 _)
  · intro z
    change F (toNative z, 1) = g (χ (toNative z))
    exact (hF ⟨(toNative z, 1), Or.inr (Or.inr rfl)⟩).trans (hB1 _)
  · intro t z hz
    change F (toNative z, t) = side (t, ⟨z.val, hz⟩)
    exact (hF ⟨(toNative z, t), Or.inl hz⟩).trans (hBs t ⟨z.val, hz⟩)


/-- An actual (n+1)-cell point in the n-skeleton has a boundary native
coordinate. This is proved from open-cell disjointness; the attaching map
need not be injective on that boundary. -/
theorem cw_successor_coordinate_boundary_of_lower
    {K : Type u} [TopologicalSpace K] [T2Space K]
    [Topology.CWComplex (Set.univ : Set K)] (n : ℕ)
    (i : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1))
    (z : Metric.closedBall (0 : Fin (n + 1) → ℝ) 1)
    (hx : Topology.RelCWComplex.map (n + 1) i z.val ∈
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)) :
    ‖z.val‖ = 1 := by
  have hzle : ‖z.val‖ ≤ 1 := by
    have h := z.property
    change dist z.val 0 ≤ 1 at h
    rwa [dist_zero_right] at h
  by_contra hn
  have hz : ‖z.val‖ < 1 := lt_of_le_of_ne hzle hn
  have hcell : Topology.RelCWComplex.map (n + 1) i z.val ∈
      Topology.CWComplex.openCell (n + 1) i :=
    ⟨z.val, by simpa [Metric.mem_ball, dist_zero_right] using hz, rfl⟩
  exact (Set.disjoint_left.mp (Topology.CWComplex.disjoint_skeleton_openCell
    (C := Set.univ) (n := (n : ℕ∞)) (j := i) (by exact_mod_cast Nat.lt_succ_self n))) hx hcell

/-- Whole-point compatibility for the new successor prisms. Off the lower
skeleton an interior coincidence forces the same original cell and coordinate.
On the lower skeleton BOTH prisms have their prescribed original H value.
This explicitly retains all nonregular frontier identifications. -/
theorem cw_successor_prisms_compatible
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)] (n : ℕ)
    (H : C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K), Y))
    (P : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1) →
      C(unitInterval × Metric.closedBall (0 : Fin (n + 1) → ℝ) 1, Y))
    (hP : ∀ i t z (hx : Topology.RelCWComplex.map (n + 1) i z.val ∈
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)),
      P i (t, z) = H (t, ⟨Topology.RelCWComplex.map (n + 1) i z.val, hx⟩))
    (i j : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1))
    (t : unitInterval) (z w : Metric.closedBall (0 : Fin (n + 1) → ℝ) 1)
    (heq : Topology.RelCWComplex.map (n + 1) i z.val =
      Topology.RelCWComplex.map (n + 1) j w.val) : P i (t, z) = P j (t, w) := by
  by_cases hx : Topology.RelCWComplex.map (n + 1) i z.val ∈
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)
  · have hy : Topology.RelCWComplex.map (n + 1) j w.val ∈
        (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K) := heq ▸ hx
    rw [hP i t z hx, hP j t w hy]
    apply congrArg (fun x ↦ H (t, x))
    exact Subtype.ext heq
  · have hinterior : ∀ (e : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1))
        (q : Metric.closedBall (0 : Fin (n + 1) → ℝ) 1),
        Topology.RelCWComplex.map (n + 1) e q.val ∉
          (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K) →
        ‖q.val‖ < 1 := by
      intro e q hq
      have hle : ‖q.val‖ ≤ 1 := by
        have h := q.property
        change dist q.val 0 ≤ 1 at h
        rwa [dist_zero_right] at h
      apply lt_of_le_of_ne hle
      intro he
      apply hq
      exact Topology.CWComplex.cellFrontier_subset_skeleton n e
        ⟨q.val, by simpa [Metric.mem_sphere, dist_zero_right] using he, rfl⟩
    have hz := hinterior i z hx
    have hw := hinterior j w (by simpa only [← heq] using hx)
    have hij : i = j := by
      have hni : ¬ Disjoint (Topology.CWComplex.openCell (n + 1) i)
          (Topology.CWComplex.openCell (n + 1) j) := Set.not_disjoint_iff.mpr
        ⟨Topology.RelCWComplex.map (n + 1) i z.val,
          ⟨z.val, by simpa [Metric.mem_ball, dist_zero_right] using hz, rfl⟩,
          ⟨w.val, by simpa [Metric.mem_ball, dist_zero_right] using hw, heq.symm⟩⟩
      exact eq_of_heq (Sigma.mk.inj_iff.mp
        (Topology.CWComplex.eq_of_not_disjoint_openCell hni)).2
    subst j
    have hzw : z = w := Subtype.ext ((Topology.RelCWComplex.map (n + 1) i).injOn
      (by rw [Topology.RelCWComplex.source_eq]; simpa [Metric.mem_ball, dist_zero_right] using hz)
      (by rw [Topology.RelCWComplex.source_eq]; simpa [Metric.mem_ball, dist_zero_right] using hw) heq)
    rw [hzw]


/-- Successor-skeleton weak-CW descent on the original carrier. The lower
skeleton plus the new characteristic disks covers the successor skeleton.
Choose an actual representative, prove all overlaps agree (including the
noninjective frontier), and apply the inherited characteristic-prism criterion.
This performs the whole successor gluing without a regular-cell replacement,
locally finite cover assumption, or a manufactured quotient-topology input. -/
theorem cw_successor_prism_gluing
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)] (n : ℕ)
    (f g : C(K, Y))
    (H : C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K), Y))
    (hH0 : ∀ x, H (0, x) = f x.val) (hH1 : ∀ x, H (1, x) = g x.val)
    (P : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1) →
      C(unitInterval × Metric.closedBall (0 : Fin (n + 1) → ℝ) 1, Y))
    (hP0 : ∀ i z, P i (0, z) = f (Topology.RelCWComplex.map (n + 1) i z.val))
    (hP1 : ∀ i z, P i (1, z) = g (Topology.RelCWComplex.map (n + 1) i z.val))
    (hP : ∀ i t z (hx : Topology.RelCWComplex.map (n + 1) i z.val ∈
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)),
      P i (t, z) = H (t, ⟨Topology.RelCWComplex.map (n + 1) i z.val, hx⟩)) :
    ∃ H' : C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) ((n + 1 : ℕ) : ℕ∞) : Set K), Y),
      (∀ x, H' (0, x) = f x.val) ∧ (∀ x, H' (1, x) = g x.val) ∧
      ∀ t (x : (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)),
        H' (t, ⟨x.val, Topology.CWComplex.skeleton_mono
          (by exact_mod_cast Nat.le_succ n) x.property⟩) = H (t, x) := by
  classical
  let S : Set K := Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞)
  let S' : Set K := Topology.CWComplex.skeleton (Set.univ : Set K) ((n + 1 : ℕ) : ℕ∞)
  have hSS : S ⊆ S' := Topology.CWComplex.skeleton_mono (by exact_mod_cast Nat.le_succ n)
  let Rep := S ⊕ (Σ i : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1),
    Metric.closedBall (0 : Fin (n + 1) → ℝ) 1)
  let eval : Rep → S' := Sum.elim
    (fun x ↦ ⟨x.val, hSS x.property⟩)
    (fun q ↦ ⟨Topology.RelCWComplex.map (n + 1) q.1 q.2.val,
      Topology.CWComplex.closedCell_subset_skeleton (n + 1) q.1
        ⟨q.2.val, q.2.property, rfl⟩⟩)
  let values : Rep → unitInterval → Y := Sum.elim (fun x t ↦ H (t, x))
    (fun q t ↦ P q.1 (t, q.2))
  have hsurj : Function.Surjective eval := by
    intro x
    have hx : x.val ∈ S ∪ ⋃ i : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1),
        Topology.CWComplex.closedCell (n + 1) i := by
      rw [Topology.CWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ]
      exact x.property
    rcases hx with hx | hx
    · exact ⟨Sum.inl ⟨x.val, hx⟩, Subtype.ext rfl⟩
    · obtain ⟨i, z, hz, hzx⟩ := Set.mem_iUnion.mp hx
      exact ⟨Sum.inr ⟨i, ⟨z, hz⟩⟩, Subtype.ext hzx⟩
  have hcompat : ∀ r s : Rep, eval r = eval s → ∀ t, values r t = values s t := by
    intro r s heq t
    have he := congrArg Subtype.val heq
    cases r with
    | inl x =>
      cases s with
      | inl y =>
        have hxy : x = y := Subtype.ext he
        rw [hxy]
      | inr q =>
        have hx : Topology.RelCWComplex.map (n + 1) q.1 q.2.val ∈ S := by
          change x.val = Topology.RelCWComplex.map (n + 1) q.1 q.2.val at he
          rw [← he]
          exact x.property
        change H (t, x) = P q.1 (t, q.2)
        rw [hP _ _ _ hx]
        apply congrArg (fun x ↦ H (t, x))
        exact Subtype.ext he
    | inr q =>
      cases s with
      | inl x =>
        have hx : Topology.RelCWComplex.map (n + 1) q.1 q.2.val ∈ S := by
          change Topology.RelCWComplex.map (n + 1) q.1 q.2.val = x.val at he
          rw [he]
          exact x.property
        change P q.1 (t, q.2) = H (t, x)
        rw [hP _ _ _ hx]
        apply congrArg (fun x ↦ H (t, x))
        exact Subtype.ext he
      | inr q' => exact cw_successor_prisms_compatible n H P hP q.1 q'.1 t q.2 q'.2 he
  let choose : S' → Rep := fun x ↦ (hsurj x).choose
  let U : unitInterval × S' → Y := fun q ↦ values (choose q.2) q.1
  have hagree : ∀ r t, U (t, eval r) = values r t := by
    intro r t
    exact hcompat _ _ (hsurj (eval r)).choose_spec t
  have hcont : Continuous U := by
    apply cw_subtype_prism_continuous_of_characteristic S'
    intro m i
    have hi := i.property
    have hi' : (m : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) + 1 := by
      simpa only [Topology.RelCWComplex.skeleton, Topology.RelCWComplex.skeletonLT,
        Topology.RelCWComplex.Subcomplex.mk', Set.mem_ofPred_eq] using hi
    have hm : m < n + 2 := by exact_mod_cast hi'
    by_cases hmn : m ≤ n
    · let χ : C(Metric.closedBall (0 : Fin m → ℝ) 1, S) :=
        ⟨fun z ↦ ⟨Topology.RelCWComplex.map (C := Set.univ) m i.val z.val,
          Topology.CWComplex.skeleton_mono (by exact_mod_cast hmn)
            (Topology.CWComplex.closedCell_subset_skeleton m i.val
              ⟨z.val, z.property, rfl⟩)⟩,
          by
            apply Continuous.subtype_mk
            exact (Topology.RelCWComplex.continuousOn m i.val).domRestrict⟩
      convert H.continuous.comp (continuous_fst.prodMk (χ.continuous.comp continuous_snd)) using 1
      funext q
      exact hagree (Sum.inl (χ q.2)) q.1
    · have hm1 : m = n + 1 := by omega
      subst m
      convert (P i.val).continuous using 1
      funext q
      exact hagree (Sum.inr ⟨i.val, q.2⟩) q.1
  refine ⟨⟨U, hcont⟩, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨r, hr⟩ := hsurj x
    rw [← hr]
    change U (0, eval r) = f (eval r).val
    rw [hagree]
    cases r with
    | inl x => exact hH0 x
    | inr q => exact hP0 q.1 q.2
  · intro x
    obtain ⟨r, hr⟩ := hsurj x
    rw [← hr]
    change U (1, eval r) = g (eval r).val
    rw [hagree]
    cases r with
    | inl x => exact hH1 x
    | inr q => exact hP1 q.1 q.2
  · intro t x
    exact hagree (Sum.inl x) t


/-- Hatcher 1B.9's full successor extension, with the actual prescribed
lower-stage map unchanged. The named covering fillers produce every new
prism; actual coordinate-boundary and coincidence lemmas prove all its
identifications before weak-CW gluing. No relative-extension premise is added. -/
theorem cw_successor_homotopy_extension
    {K : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace E]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)] [ContractibleSpace E]
    (n : ℕ) (hn : 1 ≤ n) (p : E → Y) (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) (f g : C(K, Y))
    (H : C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K), Y))
    (hH0 : ∀ x, H (0, x) = f x.val) (hH1 : ∀ x, H (1, x) = g x.val) :
    ∃ H' : C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) ((n + 1 : ℕ) : ℕ∞) : Set K), Y),
      (∀ x, H' (0, x) = f x.val) ∧ (∀ x, H' (1, x) = g x.val) ∧
      ∀ t (x : (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)),
        H' (t, ⟨x.val, Topology.CWComplex.skeleton_mono
          (by exact_mod_cast Nat.le_succ n) x.property⟩) = H (t, x) := by
  classical
  have hfill := fun i : Topology.RelCWComplex.cell (Set.univ : Set K) (n + 1) ↦
    cw_successor_characteristic_prism_filling n hn p hp hsurj f g H hH0 hH1 i
  choose P hP0 hP1 hPs using hfill
  have hPlower : ∀ i t z (hx : Topology.RelCWComplex.map (n + 1) i z.val ∈
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)),
      P i (t, z) = H (t, ⟨Topology.RelCWComplex.map (n + 1) i z.val, hx⟩) := by
    intro i t z hx
    exact hPs i t z (cw_successor_coordinate_boundary_of_lower n i z hx)
  exact cw_successor_prism_gluing n f g H hH0 hH1 P hP0 hP1 hPlower


/-- Hatcher 1B.9's recursive assembly after the actual one-skeleton input.
Each successor is constructed by the preceding theorem and agrees on the
entire previous skeleton. The natural-number recursion covers arbitrary
unbounded dimension; characteristic prisms establish ordinary-product
continuity by compact-open currying. The original basepoint stays fixed by
agreement with the first stage, not by an added relative filling premise. -/
theorem cw_based_homotopy_from_one_skeleton
    {K : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace E]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)] [ContractibleSpace E]
    (k₀ : K) (hk : k₀ ∈
      (Topology.CWComplex.skeleton (Set.univ : Set K) 1 : Set K))
    (p : E → Y) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (f g : C(K, Y))
    (H₁ : C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) 1 : Set K), Y))
    (h₀ : ∀ x, H₁ (0, x) = f x.val) (h₁ : ∀ x, H₁ (1, x) = g x.val)
    (hfixed : ∀ t, H₁ (t, ⟨k₀, hk⟩) = f k₀) :
    Nonempty (ContinuousMap.HomotopyRel f g {k₀}) := by
  classical
  let S : ℕ → Set K := fun n ↦
    Topology.CWComplex.skeleton (Set.univ : Set K) ((n + 1 : ℕ) : ℕ∞)
  have hmono : ∀ m n : ℕ, m ≤ n → S m ⊆ S n := by
    intro m n h
    exact Topology.CWComplex.skeleton_mono (by exact_mod_cast Nat.add_le_add_right h 1)
  let Stage := fun n ↦ {H : C(unitInterval × S n, Y) //
    (∀ x, H (0, x) = f x.val) ∧ (∀ x, H (1, x) = g x.val)}
  let next : ∀ n, Stage n → Stage (n + 1) := fun n s ↦
    ⟨(cw_successor_homotopy_extension (n + 1) (by omega) p hp hsurj f g
      s.val s.property.1 s.property.2).choose,
     (cw_successor_homotopy_extension (n + 1) (by omega) p hp hsurj f g
      s.val s.property.1 s.property.2).choose_spec.1,
     (cw_successor_homotopy_extension (n + 1) (by omega) p hp hsurj f g
      s.val s.property.1 s.property.2).choose_spec.2.1⟩
  let stages : ∀ n, Stage n := Nat.rec ⟨H₁, h₀, h₁⟩ next
  have hsucc : ∀ n t (x : S n),
      (stages (n + 1)).val (t, ⟨x.val, hmono n (n + 1) (Nat.le_succ n) x.property⟩) =
      (stages n).val (t, x) := by
    intro n t x
    exact (cw_successor_homotopy_extension (n + 1) (by omega) p hp hsurj f g
      (stages n).val (stages n).property.1 (stages n).property.2).choose_spec.2.2 t x
  have hcompat : ∀ m n (hmn : m ≤ n) t (x : S m),
      (stages n).val (t, ⟨x.val, hmono m n hmn x.property⟩) =
      (stages m).val (t, x) := by
    intro m n
    induction n with
    | zero =>
      intro hmn t x
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      rfl
    | succ n ih =>
      intro hmn t x
      by_cases hmn' : m ≤ n
      · exact (hsucc n t ⟨x.val, hmono m n hmn' x.property⟩).trans (ih hmn' t x)
      · have hm : m = n + 1 := by omega
        subst m
        rfl
  have hcover : ∀ x : K, ∃ n, x ∈ S n := by
    intro x
    have hx : x ∈ ⋃ n : ℕ,
        (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K) := by
      rw [Topology.CWComplex.iUnion_skeleton_eq_complex]
      trivial
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact ⟨n, Topology.CWComplex.skeleton_mono
      (by exact_mod_cast Nat.le_succ n) hn⟩
  let index : K → ℕ := fun x ↦ (hcover x).choose
  have hindex : ∀ x, x ∈ S (index x) := fun x ↦ (hcover x).choose_spec
  let U : unitInterval × K → Y := fun q ↦
    (stages (index q.2)).val (q.1, ⟨q.2, hindex q.2⟩)
  have hagree : ∀ n t (x : S n), U (t, x.val) = (stages n).val (t, x) := by
    intro n t x
    let N := max (index x.val) n
    have hi := hcompat (index x.val) N (le_max_left _ _) t
      (⟨x.val, hindex x.val⟩ : S (index x.val))
    have hn := hcompat n N (le_max_right _ _) t x
    exact hi.symm.trans hn
  have hcont : Continuous U := by
    apply cw_prism_continuous_of_characteristic
    intro n i
    let χ : C(Metric.closedBall (0 : Fin n → ℝ) 1, S n) :=
      ⟨fun z ↦ ⟨Topology.RelCWComplex.map n i z.val,
        Topology.CWComplex.skeleton_mono (by exact_mod_cast Nat.le_succ n)
          (Topology.CWComplex.closedCell_subset_skeleton n i ⟨z.val, z.property, rfl⟩)⟩,
        by
          apply Continuous.subtype_mk
          exact (Topology.RelCWComplex.continuousOn n i).domRestrict⟩
    convert (stages n).val.continuous.comp
      (continuous_fst.prodMk (χ.continuous.comp continuous_snd)) using 1
    funext q
    exact hagree n q.1 (χ q.2)
  refine ⟨{
    toFun := U
    continuous_toFun := hcont
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro x
    exact (stages (index x)).property.1 ⟨x, hindex x⟩
  · intro x
    exact (stages (index x)).property.2 ⟨x, hindex x⟩
  · intro t x hx
    have hx' : x = k₀ := Set.mem_singleton_iff.mp hx
    subst x
    change U (t, k₀) = f k₀
    exact (hagree 0 t ⟨k₀, hk⟩).trans (hfixed t)


/-- A homotopy through based maps induces the literal endpoint-fixed
homotopy on every original root loop. Both endpoint casts are kept; no
unbased homotopy or change of fundamental-group basepoint is used. -/
theorem based_loop_images_homotopic_of_relative
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    (k₀ : K) (y₀ : Y) (f g : C(K, Y)) (hf : f k₀ = y₀) (hg : g k₀ = y₀)
    (H : ContinuousMap.HomotopyRel f g {k₀}) (γ : Path k₀ k₀) :
    ((γ.map f.continuous).cast hf.symm hf.symm).Homotopic
      ((γ.map g.continuous).cast hg.symm hg.symm) := by
  refine ⟨{
    toFun := fun q ↦ H (q.1, γ q.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (γ.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    exact H.map_zero_left (γ t)
  · intro t
    exact H.map_one_left (γ t)
  · intro t s hs
    change H (t, γ s) = f (γ s)
    have hγs : γ s = k₀ := by
      rcases hs with hs | hs
      · rw [hs, γ.source]
      · rw [hs, γ.target]
    rw [hγs]
    exact H.prop' t k₀ (by simp)

/-- The initial equality of based induced maps survives the two constructed
root-fixed HEP collapses. This is derived by composing actual loop homotopies,
not by assuming equality of the collapsed maps' induced homomorphisms. -/
theorem based_loop_images_homotopic_after_relative
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    (k₀ : K) (y₀ : Y) (f g f' g' : C(K, Y))
    (hf : f k₀ = y₀) (hg : g k₀ = y₀) (hf' : f' k₀ = y₀) (hg' : g' k₀ = y₀)
    (hπ₁ : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg)
    (Hf : ContinuousMap.HomotopyRel f f' {k₀})
    (Hg : ContinuousMap.HomotopyRel g g' {k₀}) (γ : Path k₀ k₀) :
    ((γ.map f'.continuous).cast hf'.symm hf'.symm).Homotopic
      ((γ.map g'.continuous).cast hg'.symm hg'.symm) :=
  (based_loop_images_homotopic_of_relative k₀ y₀ f f' hf hf' Hf γ).symm.trans
    ((based_loop_images_homotopic k₀ y₀ f g hf hg hπ₁ γ).trans
      (based_loop_images_homotopic_of_relative k₀ y₀ g g' hg hg' Hg γ))


/-- Removing the two collapsed rooted paths from a root-edge-root loop.
Their images are literally constant, so Mathlib's actual path-unit homotopies
reduce each loop image to the original edge image, with all endpoint casts.
This is Hatcher 1B.9's edge-square mechanism after the constructed tree collapse. -/
theorem based_edge_images_homotopic_of_root_loops
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    (k₀ a b : K) (y₀ : Y) (f g : C(K, Y))
    (hf : f k₀ = y₀) (hg : g k₀ = y₀)
    (hfa : f a = y₀) (hfb : f b = y₀) (hga : g a = y₀) (hgb : g b = y₀)
    (α : Path k₀ a) (β : Path k₀ b) (γ : Path a b)
    (hαf : ∀ t, f (α t) = y₀) (hβf : ∀ t, f (β t) = y₀)
    (hαg : ∀ t, g (α t) = y₀) (hβg : ∀ t, g (β t) = y₀)
    (hloops : ∀ L : Path k₀ k₀,
      ((L.map f.continuous).cast hf.symm hf.symm).Homotopic
        ((L.map g.continuous).cast hg.symm hg.symm)) :
    ((γ.map f.continuous).cast hfa.symm hfb.symm).Homotopic
      ((γ.map g.continuous).cast hga.symm hgb.symm) := by
  let L : Path k₀ k₀ := (α.trans γ).trans β.symm
  have reduce : ∀ (h : C(K, Y)) (hk : h k₀ = y₀) (ha : h a = y₀) (hb : h b = y₀),
      (∀ t, h (α t) = y₀) → (∀ t, h (β t) = y₀) →
      ((L.map h.continuous).cast hk.symm hk.symm).Homotopic
        ((γ.map h.continuous).cast ha.symm hb.symm) := by
    intro h hk ha hb hα hβ
    let q : Path y₀ y₀ := (γ.map h.continuous).cast ha.symm hb.symm
    have hA : (α.map h.continuous).cast hk.symm ha.symm = Path.refl y₀ := by
      ext t
      exact hα t
    have hB : (β.symm.map h.continuous).cast hb.symm hk.symm = Path.refl y₀ := by
      ext t
      exact hβ (unitInterval.symm t)
    have hL : (L.map h.continuous).cast hk.symm hk.symm =
        ((Path.refl y₀).trans q).trans (Path.refl y₀) := by
      change (((α.trans γ).trans β.symm).map h.continuous).cast hk.symm hk.symm = _
      rw [Path.map_trans, Path.map_trans]
      change (((α.map h.continuous).cast hk.symm ha.symm).trans q).trans
        ((β.symm.map h.continuous).cast hb.symm hk.symm) = _
      rw [hA, hB]
    rw [hL]
    exact (Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans q)
  exact (reduce f hf hfa hfb hαf hβf).symm.trans
    ((hloops L).trans (reduce g hg hga hgb hαg hβg))


/-- Actual vertex/edge representatives on any one-dimensional inherited CW
carrier. The empty higher cell types are used, not a graph-realization model. -/
theorem cw_one_dimensional_carrier_cases
    {K : Type u} [TopologicalSpace K] (C : Set K) [Topology.CWComplex C]
    (hhigh : ∀ n, IsEmpty (Topology.RelCWComplex.cell C (n + 2))) (x : C) :
    (∃ v : Topology.RelCWComplex.cell C 0,
      x.val = Topology.RelCWComplex.map 0 v 0) ∨
    ∃ e : Topology.RelCWComplex.cell C 1,
      ∃ z : Metric.closedBall (0 : Fin 1 → ℝ) 1,
        x.val = Topology.RelCWComplex.map 1 e z.val := by
  have hx : x.val ∈ ⋃ n : ℕ, ⋃ i : Topology.RelCWComplex.cell C n,
      Topology.CWComplex.closedCell n i := by
    rw [Topology.CWComplex.union]
    exact x.property
  obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨i, z, hz, hzx⟩ := Set.mem_iUnion.mp hx
  cases n with
  | zero =>
    left
    refine ⟨i, ?_⟩
    have hz0 : z = 0 := Subsingleton.elim _ _
    simpa only [hz0] using hzx.symm
  | succ n =>
    cases n with
    | zero => exact Or.inr ⟨i, ⟨z, hz⟩, hzx.symm⟩
    | succ n => have := hhigh n; exact isEmptyElim i

/-- Hatcher 1B.9's actual one-skeleton homotopy after the constructed tree
collapse. Root paths are the time-reversed constructed tree tracks and stay
inside that SAME tree. Every original edge closes to an original root loop;
the supplied root-loop homotopies and literal constant root paths give an
endpoint-fixed edge square. Native oriented coordinates recover every
characteristic point, and weak-CW edge gluing gives the original stage one.
No extra path- or fundamental-group equality is assumed. -/
theorem cw_one_skeleton_homotopy_of_collapsed_root_loops
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)]
    (r : Topology.RelCWComplex.cell (Set.univ : Set K) 0)
    (T : Topology.CWComplex.Subcomplex (Set.univ : Set K))
    (hT0 : Topology.CWComplex.skeleton (Set.univ : Set K) 0 ≤ T)
    (hr : Topology.RelCWComplex.map 0 r 0 ∈ (T : Set K))
    (C : C(unitInterval × (T : Set K), K))
    (hC0 : ∀ x, C (0, x) = x.val)
    (hC1 : ∀ x, C (1, x) = Topology.RelCWComplex.map 0 r 0)
    (hCmem : ∀ q, C q ∈ (T : Set K)) (y₀ : Y) (f g : C(K, Y))
    (hfc : ∀ x : (T : Set K), f x.val = y₀)
    (hgc : ∀ x : (T : Set K), g x.val = y₀)
    (hloops : ∀ L : Path (Topology.RelCWComplex.map 0 r 0)
        (Topology.RelCWComplex.map 0 r 0),
      ((L.map f.continuous).cast (hfc ⟨_, hr⟩).symm (hfc ⟨_, hr⟩).symm).Homotopic
        ((L.map g.continuous).cast (hgc ⟨_, hr⟩).symm (hgc ⟨_, hr⟩).symm)) :
    ∃ H : C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) 1 : Set K), Y),
      (∀ x, H (0, x) = f x.val) ∧ (∀ x, H (1, x) = g x.val) ∧
      ∀ t (hk : Topology.RelCWComplex.map 0 r 0 ∈
          (Topology.CWComplex.skeleton (Set.univ : Set K) 1 : Set K)),
        H (t, ⟨Topology.RelCWComplex.map 0 r 0, hk⟩) = y₀ := by
  classical
  let S : Set K := Topology.CWComplex.skeleton (Set.univ : Set K) 1
  have hhigh : ∀ n, IsEmpty (Topology.RelCWComplex.cell S (n + 2)) := by
    intro n
    refine ⟨fun i ↦ ?_⟩
    have hi : ((n + 2 : ℕ) : ℕ∞) < (1 : ℕ∞) + 1 := by
      simpa only [S, Topology.RelCWComplex.skeleton, Topology.RelCWComplex.skeletonLT,
        Topology.RelCWComplex.Subcomplex.mk', Set.mem_ofPred_eq] using i.property
    norm_cast at hi
  have hvmem : ∀ v : Topology.RelCWComplex.cell (Set.univ : Set K) 0,
      Topology.RelCWComplex.map 0 v 0 ∈ (T : Set K) := by
    intro v
    exact hT0 (Topology.CWComplex.closedCell_subset_skeleton 0 v ⟨0, by simp, rfl⟩)
  let rootpath : ∀ v : Topology.RelCWComplex.cell (Set.univ : Set K) 0,
      Path (Topology.RelCWComplex.map 0 r 0) (Topology.RelCWComplex.map 0 v 0) :=
    fun v ↦ {
      toFun := fun t ↦ C (unitInterval.symm t, ⟨_, hvmem v⟩)
      continuous_toFun := C.continuous.comp (unitInterval.continuous_symm.prodMk continuous_const)
      source' := by simpa using hC1 ⟨_, hvmem v⟩
      target' := by simpa using hC0 ⟨_, hvmem v⟩ }
  have hrootpaths : ∀ v t, rootpath v t ∈ (T : Set K) := fun v t ↦ hCmem _
  have hsquares : ∀ e : Topology.RelCWComplex.cell S 1,
      ∃ Pe : C(unitInterval × Metric.closedBall (0 : Fin 1 → ℝ) 1, Y),
      (∀ z, Pe (0, z) = f (Topology.RelCWComplex.map 1 e z.val)) ∧
      (∀ z, Pe (1, z) = g (Topology.RelCWComplex.map 1 e z.val)) ∧
      (∀ t z, ‖z.val‖ = 1 → Pe (t, z) = y₀) := by
    intro e
    obtain ⟨v, w, hvw⟩ := Topology.CWComplex.exists_cellFrontier_one_eq e.val
    have hlink : (Topology.CWComplex.OneSkeletonGraph (Set.univ : Set K)).IsLink e.val v w := hvw
    obtain ⟨σ, γ, hσ, hγ⟩ := cw_oriented_edge_path e.val v w hlink
    obtain ⟨s, hrecover, hends⟩ := native_one_disk_oriented_coordinate σ hσ
    have hhom := based_edge_images_homotopic_of_root_loops
      (Topology.RelCWComplex.map 0 r 0) (Topology.RelCWComplex.map 0 v 0)
      (Topology.RelCWComplex.map 0 w 0) y₀ f g
      (hfc ⟨_, hr⟩) (hgc ⟨_, hr⟩)
      (hfc ⟨_, hvmem v⟩) (hfc ⟨_, hvmem w⟩)
      (hgc ⟨_, hvmem v⟩) (hgc ⟨_, hvmem w⟩)
      (rootpath v) (rootpath w) γ
      (fun t ↦ hfc ⟨_, hrootpaths v t⟩) (fun t ↦ hfc ⟨_, hrootpaths w t⟩)
      (fun t ↦ hgc ⟨_, hrootpaths v t⟩) (fun t ↦ hgc ⟨_, hrootpaths w t⟩) hloops
    obtain ⟨Q⟩ := hhom
    let Pe : C(unitInterval × Metric.closedBall (0 : Fin 1 → ℝ) 1, Y) :=
      Q.toContinuousMap.comp (ContinuousMap.fst.prodMk (s.comp ContinuousMap.snd))
    have hpoint : ∀ z, γ (s z) = Topology.RelCWComplex.map 1 e z.val := by
      intro z
      rw [hγ, ← hrecover]
      rfl
    refine ⟨Pe, ?_, ?_, ?_⟩
    · intro z
      change Q (0, s z) = f (Topology.RelCWComplex.map 1 e z.val)
      exact (Q.map_zero_left (s z)).trans (congrArg f (hpoint z))
    · intro z
      change Q (1, s z) = g (Topology.RelCWComplex.map 1 e z.val)
      exact (Q.map_one_left (s z)).trans (congrArg g (hpoint z))
    · intro t z hz
      change Q (t, s z) = y₀
      rcases hends z hz with hs | hs
      · rw [hs, Path.Homotopy.source]
      · rw [hs, Path.Homotopy.target]
  choose Pe hP0 hP1 hPb using hsquares
  let Cv : Topology.RelCWComplex.cell S 0 → C(unitInterval, Y) :=
    fun _ ↦ ContinuousMap.const unitInterval y₀
  obtain ⟨H, hH0, hH1⟩ := cw_one_dimensional_glue_edge_tracks S hhigh Cv Pe
    (fun e z _ t hz _ ↦ hPb e t z hz)
  have hreps := cw_one_dimensional_carrier_cases S hhigh
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x
    rcases hreps x with ⟨v, hv⟩ | ⟨e, z, hz⟩
    · have hx : x = ⟨Topology.RelCWComplex.map 0 v 0,
        Topology.RelCWComplex.closedCell_subset_complex 0 v ⟨0, by simp, rfl⟩⟩ := Subtype.ext hv
      rw [hx, hH0]
      exact (hfc ⟨_, hvmem v.val⟩).symm
    · have hx : x = ⟨Topology.RelCWComplex.map 1 e z.val,
        Topology.RelCWComplex.closedCell_subset_complex 1 e ⟨z.val, z.property, rfl⟩⟩ := Subtype.ext hz
      rw [hx, hH1]
      exact hP0 e z
  · intro x
    rcases hreps x with ⟨v, hv⟩ | ⟨e, z, hz⟩
    · have hx : x = ⟨Topology.RelCWComplex.map 0 v 0,
        Topology.RelCWComplex.closedCell_subset_complex 0 v ⟨0, by simp, rfl⟩⟩ := Subtype.ext hv
      rw [hx, hH0]
      exact (hgc ⟨_, hvmem v.val⟩).symm
    · have hx : x = ⟨Topology.RelCWComplex.map 1 e z.val,
        Topology.RelCWComplex.closedCell_subset_complex 1 e ⟨z.val, z.property, rfl⟩⟩ := Subtype.ext hz
      rw [hx, hH1]
      exact hP1 e z
  · intro t hk
    let vr : Topology.RelCWComplex.cell S 0 := ⟨r, by
      simp [Topology.RelCWComplex.skeleton, Topology.RelCWComplex.skeletonLT,
        Topology.RelCWComplex.Subcomplex.mk']⟩
    exact hH0 vr t


/-- Based continuous maps into a space with contractible universal cover are based-homotopic
when their actual induced fundamental-group homomorphisms agree.

`Topology.CWComplex univ` is a CW structure on the entire supplied space, with its existing
Hausdorff topology. `k₀` is arbitrary and is not required to be a cell vertex.
`IsCoveringMap p` is supplemented by surjectivity because Mathlib permits empty covering fibres.
The contractible total space is in particular simply connected, so these are exactly the
universal-cover data in this statement, not an assumed homotopy between `f` and `g`.
`FundamentalGroup.mapOfEq` uses the stated endpoint equalities to identify the target basepoint;
no connecting path or conjugation is chosen. The conclusion fixes `{k₀}` at every time.

Sources: Hatcher, Proposition 1B.9, pp. 90–91; Proposition 1A.1, p. 84;
Proposition 0.16 and its preceding closed-piece argument, pp. 14–15;
Appendix A.1, p. 520, closed-cell product criterion p. 523, A.14–A.15, pp. 530–531,
and A.17, pp. 532–533. Arbitrary-point CW refinement follows Fritsch–Piccinini,
*Cellular Structures in Topology* (1990), Lemma 2.3.7, p. 67.
DAG node: `topo.cw_map_based_homotopy_uniqueness`.

Complete natural-language proof from the node:
1. The chosen point k₀ makes K nonempty. Apply the point-refinement result to the given Hausdorff
CW space, obtaining a CW structure on the same carrier with the same topology and with k₀ a
zero-cell. The maps f,g, their basedness, and their induced π₁ homomorphisms are therefore
literally unchanged. Write Kⁿ for the new skeleta. It is enough to construct a homotopy with this
structure; a vertex condition is proved, not added to the theorem statement.

2. Follow the multiple-vertex uniqueness paragraph of Hatcher Proposition1B.9 p.91, using its
actual maximal-tree contraction. Apply topo.cw_realization_spanning_tree_g8 to the refined CW
structure and its root k₀. This supplies the selected original-edge subcomplex T⊆K¹, all vertices,
depths d, parent edges with d(parent(v))+1=d(v), and finite simple root paths q_v. Its finite-walk
premise is already the published connected-CW bridge; do not repeat the former two-colour
higher-cell connectivity argument. Give the carriers K¹ and T the inherited characteristic maps
and topology. They are closed Hausdorff subcomplexes; the CW closed-cell criterion restricts to
these carriers because closed sets in a closed subspace are closed in K. This verifies the
inherited topological CW structures used below, without assuming an unrelated CWComplex univ
instance on a subtype. Expand the written rooted X_i/Y_i construction of Proposition1A.1 p.84 for
this very selected tree, not some separately chosen contractible tree. Let Y_i contain exactly the
vertices of depth at most i and their selected parent edges of child depth at most i, so Y₀={k₀},
Y_i⊆Y_(i+1), and their union is T. The source X_i layers contain exactly the vertices with d≤i;
choosing its one adjoining edge for each new vertex to be the already selected parent edge gives
precisely these Y_i. Every added selected edge has a distinct child of depth i+1 and a parent in
Y_i, and no added edge is a loop or a duplicate label. Fix the native characteristic-domain guard
for all the edge paths used below. The original one-cell map map₁,e is supplied as continuous only
on closedBall(0,1) in Fin1→ℝ, identified with [−1,1]. Choose σ_e∈{−1,1} to put the chosen initial
endpoint at s=0, and define χ_e(s)=map₁,e(fun _↦σ_e(2s−1)) for s∈I. For a selected edge take its
parent as initial and child as final; for an edge outside T choose either orientation, with
initial u and final v. A loop permits either sign since the two endpoints agree. The inequality
|σ_e(2s−1)|≤1 proves that the entire affine parameter is in the original closed ball, and the
original ContinuousOn characteristic-map field composed with this continuous affine map gives a
continuous path χ_e. The original endpoint/frontier identification gives its stated vertices. Its
interior parametrizes exactly the original open cell. The affine inverse on the native ball is
s=(1+σ_e z(0))/2, so these are the same original characteristic maps with a boundary-preserving
interval reparameterization. Form each q_v by concatenating these χ_e along the finite selected
root-edge array, with q_k₀ constant. Use this same χ_e throughout the layer collapses, root loops
and middle homotopies. In particular on a selected edge χ_e(s) runs from parent at coordinate0 to
child at coordinate1. Contract Y_(i+1) to Y_i by fixing Y_i and, on every added interval, sending
its coordinate s to (1−u)s for contraction parameter u∈[0,1]. At u=0 this is identity and at u=1
it is the parent endpoint. Characteristic endpoints agree with the corresponding child track and
fixed parent; edge interiors are disjoint. The per-cell quotient descent and Hatcher
closed-cell-product continuity criterion established in step8 give a jointly continuous layer
collapse, even when there are infinitely many edges in that layer.
Now use precisely Hatcher's dyadic scheduling: perform the collapse Y_(i+1)→Y_i during
[2^−(i+1),2^−i]. Define c(0,z)=z. A point in Y_n is stationary until time2^−n, then undergoes the
layer n→n−1 collapse and the successive lower-layer collapses, reaching Y₀ at time1. Different
choices of n containing z give the same track: all earlier higher-layer collapses fix Y_n, and the
lower stages use the same maps. Thus this defines c:I×T→T, with c(0,z)=z, c(1,z)=k₀ and
c(t,k₀)=k₀. Check joint continuity at the accumulating time0 in the source CW topology. The
closure of a fixed selected edge of child depth n lies in Y_n, and its whole track lies in the
finite union of that edge and its finite parent paths. Its characteristic-prism pullback is
stationary on [0,2^−n] and thereafter is a finite pasting of continuous interval-coordinate
collapses and their finite compositions; they agree at all dyadic endpoints. A vertex has the same
finite-stage property. Hence every characteristic-prism pullback is continuous, including at
time0. Apply the per-cell native-disk-to-closed-cell quotient descent from step8 to these
characteristic-prism pullbacks. They give continuous restrictions to I times each actual closed
edge or vertex. The Hatcher p.523/A.15 closed-cell-product criterion, with its compact-open
curry/evaluation proof expanded in step8, then establishes continuity of c on the ordinary product
I×T. This is the source rooted deformation retraction and fixes the root throughout; it uses
neither a metric on an infinite tree nor a globally finite number of layers.

3. Use the exact CW-pair homotopy-extension statement with X=K¹, subcomplex B=T, target K¹,
initial map id_(K¹), and prescribed map (t,z)↦c(t,z) followed by T inclusion. Its initial value on
T is that identity restriction. The point {k₀} is a zero-cell subcomplex of T and c fixes it, so
the extension h:I×K¹→K¹ has h(0,x)=x, h(t,z)=c(t,z) for z∈T, and h(t,k₀)=k₀. This is Hatcher1B.9
p.91's extension of the tree contraction, supplied by the written Proposition0.16 p.15 and the
closed-piece composition argument p.14; it is not asserted that all of K¹ deformation retracts to
the root. Put F=f|_(K¹)∘h(1,−) and G=g|_(K¹)∘h(1,−). Both are continuous and send the whole T,
including every vertex, to y₀. Composing f and g with h(t,−) gives based homotopies from their
restrictions to F and G, with the root fixed throughout.

4. Apply the single-vertex argument in the written proof of Proposition1B.9 pp.90–91 after this
tree collapse. For an oriented edge e outside T, use precisely χ_e:I→K¹ from step2 with initial
vertex u and final vertex v, and let ℓ_e=q_u·χ_e·q_v⁻¹ be its based root loop in K¹, using
chronological path concatenation. The based homotopy f∘h(t,−) composed with ℓ_e is an
endpoint-fixed homotopy from f(ℓ_e) to F(ℓ_e); likewise g∘h gives g(ℓ_e) to G(ℓ_e). Since f_*=g_*
on π₁(K,k₀), their images of this loop, viewed in K through inclusion, have the same class.
Therefore [F(ℓ_e)]=[G(ℓ_e)] at y₀. The actual mapOfEq formula transports the common endpoint
equality f(k₀)=g(k₀)=y₀, not an arbitrary base-change path; the chronological description can be
converted using the common reversed FundamentalGroup multiplication p*q=q.trans p. Since F and G
are constant on T, the two images of q_u and q_v⁻¹ are constant paths. The named initial/final
constant-path homotopies remove these pieces, giving [F∘χ_e]=[G∘χ_e] as classes of paths from y₀
to y₀. Equality in the actual path-homotopy quotient supplies a continuous endpoint-fixed homotopy
J_e between these two edge paths. For an edge of T take the constant homotopy at y₀. Every J_e has
both interval endpoints constantly y₀ at every homotopy time, so all prescriptions agree at shared
vertices, including loop edges and distinct parallel original labels. This replaces the former
moving-vertex tracks and conjugated square-boundary filling argument; it does not infer equality
of paths from equality of their classes.

5. Set B(t,v)=y₀ on every vertex and B(t,χ_e(s))=J_e(t,s) on each open edge, using the same
affine-reparameterized χ_e from step2. All vertex values and identified characteristic-boundary
points agree, and interiors are unique and disjoint, so this defines B:I×K¹→Y. On the native
one-cell characteristic prism its pullback is J_e(t,(1+σ_e z(0))/2); the native condition |z(0)|≤1
gives that inverse parameter in I, so continuity follows from the continuous J_e and affine
inverse. A vertex prism is constant. Thus the interval-parametrized prescriptions really have
continuous pullbacks to every original native characteristic prism, rather than assuming an
original characteristic map was defined on [0,1]. The per-cell quotient descent from step8 turns
these native pullbacks into continuous restrictions to I times every actual closed cell. Hatcher
p.523/A.15, with the compact-open curry/evaluation proof of that criterion in step8, therefore
makes B jointly continuous for the inherited ordinary product topology, without finiteness or
local finiteness. Its endpoints are B(0,−)=F, B(1,−)=G, and B(t,k₀)=y₀. Follow Hatcher p.91 by
concatenating the first based tree-collapse homotopy, this collapsed-edge homotopy, and the
reverse second tree-collapse homotopy. Explicitly H₁(t,x)=f(h(3t,x)) for0≤t≤1/3, B(3t−1,x)
for1/3≤t≤2/3, and g(h(3−3t,x)) for2/3≤t≤1. At the breakpoints the values agree exactly as F and G.
These are three closed time slabs in I×K¹; finite closed pasting proves joint continuity. Hence H₁
has endpoint maps f|_(K¹),g|_(K¹) and keeps k₀ fixed. Continue with the unchanged higher-prism
argument below, exactly as Hatcher's written uniqueness proof does.

6. Suppose H_{n−1} has been constructed for n≥2, with endpoints f,g on Kⁿ⁻¹ and with k₀ fixed.
Keep the original native characteristic disk D_n=closedBall(0:Fin n→ℝ,1), its sphere
S_(n−1)=sphere(0:Fin n→ℝ,1), and the actual n-cell characteristic map χ:D_n→K. Its continuousOn
characteristic field becomes continuity on the disk subtype by ContinuousOn.domRestrict. On the
original product D_n×I let B be the boundary union D_n×{0}∪D_n×{1}∪S_(n−1)×I, with its induced
topology, as used by the boundary adapter in step7. Inside B denote the bottom, top and lateral
faces by B₀,B₁,L. The disk and time coordinates are continuous product projections after
continuous subtype inclusions. In particular ξ:B→Fin n→ℝ and τ:B→I are continuous. Thus
L=ξ⁻¹(S_(n−1)) is closed by the metric-sphere and closed-preimage leaves. The interval endpoint
singletons {0},{1} are closed: at an unequal point a metric ball of radius half its positive
distance from the endpoint lies in the complement. Their inverse images give the closed faces B₀
and B₁. The three faces cover B, the bottom and top are disjoint, and their intersections with L
are exactly the original sphere points at times0 and1.
Prescribe u₀(z,0)=f(χ(z)), u₁(z,1)=g(χ(z)), and v_L(z,t)=H_{n−1}(t,⟨χ(z),h_z⟩) on L. For a lateral
point, χ(z) is in the characteristic frontier; the frontier-in-lower-skeleton leaf places it in
skeletonLT univ n, which equals Kⁿ⁻¹. This supplies precisely h_z. The characteristic map composed
with the disk projection is continuous; Continuous.subtype_mk with h_z makes its restriction to L
a continuous map into that original lower-skeleton subtype. Pairing it with the time projection is
continuous by the product topology, so composition with the jointly continuous H_{n−1} proves v_L
continuous. The bottom and top formulas are continuous by the same projections, characteristic
restriction and composition. No H_{n−1} value is evaluated outside Kⁿ⁻¹. On B₀∩L the endpoint
equation H_{n−1}(0,−)=f gives v_L=u₀, and on B₁∩L the equation H_{n−1}(1,−)=g gives v_L=u₁.
Bottom/top compatibility is vacuous. Different lower-skeleton membership witnesses give the same
subtype point by extensionality.
Define b_pr:B→Y by taking the bottom formula when t=0, the top formula when t=1, and otherwise the
lateral formula, whose domain membership follows from the defining boundary union. The preceding
equalities make its restrictions to all three closed faces exactly the continuous prescriptions,
including every face intersection. This ordered definition is total without choosing any extra
point of Y. Index the faces by Fin3; locallyFinite_of_finite gives local finiteness, and
LocallyFinite.continuousOn_iUnion applied to their closed cover and those continuous restrictions
gives continuity on all B. This is the actual closed-piece pasting used in Hatcher p.14, applied
directly through the existing Mathlib leaves; no saved three-face or skeleton interface is a
premise. The resulting boundary map has exactly f∘χ on the bottom, g∘χ on the top, and
H_{n−1}(t,χ(z)) on the side. For any boundary point whose characteristic image lies in Kⁿ⁻¹, the
same old-skeleton relative equation also holds on an endpoint face by its endpoint equation. At a
fixed time, different characteristic-boundary representatives with the same image in K give
identical f or g values at endpoints, and at other times give the identical lower-skeleton point
and hence the identical H_{n−1} value. Thus all original boundary equations and nonregular-cell
identifications are preserved before filling or gluing; no boundary injectivity or separation
hypothesis on Y is used.

7. Follow the higher-prism uniqueness paragraph of Hatcher Proposition1B.9 p.91: lift the actual
continuous boundary map to the contractible universal cover and contract that lift, then fill it
by the reviewed source disk-extension theorem. Keep the original native disks D_m={v:Fin
m→ℝ:||v||∞≤1} and spheres S_(m−1)={v:||v||∞=1}. For the n-cell of step6, n≥2, identify D_(n+1)
with D_n×I by the coordinate map Φ(v)=(head(v),(v(last)+1)/2), with inverse Ψ(z,t) obtained by
concatenating z and the last coordinate2t−1. The native finite-product closed-ball theorem at
radius1 proves both maps are defined and inverse: all original coordinates have absolute value≤1
exactly when z∈D_n and t∈I. Coordinate projections, affine arithmetic and the product continuity
criterion prove both maps continuous for the original maximum-norm/subspace topologies. The
positive-radius open-ball theorem identifies the open native ball with ||z||∞<1 and0<t<1. Since
n≥2, the positive finite head block has norm1 exactly when one head coordinate has absolute
value1. Consequently Φ carries the entire native S_n exactly onto the full prism boundary
D_n×{0}∪D_n×{1}∪S_(n−1)×I: a sphere coordinate of absolute value1 is either in the head block or
the last coordinate, and conversely every such boundary point has an original coordinate of
absolute value1. This includes every overlap of boundary faces. This is the cube-block
normalization of the product characteristic domains in Bredon IV§12 p.211 and Hatcher AppendixA.6
p.524, not a new Euclidean radial or Minkowski-functional cylinder adapter.
Let b_pr denote precisely the boundary prescription of step6, and define b:S_n→Y by
b(s)=b_pr(Φ(s)). Its continuity follows by composing that already closed-pasted boundary map with
the boundary restriction of Φ. The existing unit-sphere theorem applies to this actual native
maximum-norm S_n: it is simply connected and locally path-connected because n≥2. It is nonempty;
for example the vector with last coordinate1 and all head coordinates0 belongs to it. Choose that
sphere point s₀ and choose e₀ over b(s₀) by surjectivity of the universal covering p. The exact
simply-connected covering-lift theorem gives a continuous L:S_n→E with p∘L=b and L(s₀)=e₀.
Contractibility of E supplies a jointly continuous C:I×E→E with C(0,e)=e and C(1,e)=e* for one e*.
Thus H_E(t,s)=C(t,L(s)) is the actual supplied jointly continuous sphere nullhomotopy, with
H_E(0,s)=L(s) and H_E(1,s)=e*.
Apply topo.nullhomotopic_sphere_disk_extension with d=n+1, target E, boundary map L, constant e*
and the full map H_E. Its exact native statement supplies a continuous B_E:D_(n+1)→E whose
restriction to every point of S_n is L. This provider follows Hatcher printed pp.14–15's
closed-bottom/side pasting and local disk-prism retraction, rather than the previous compact
radial-cone descent. Define the original cell-prism filling F_n(z,t)=p(B_E(Ψ(z,t))). It is
continuous because Ψ, B_E and p are continuous. For every point of the full original prism
boundary, Ψ(z,t)∈S_n, hence F_n(z,t)=p(L(Ψ(z,t)))=b(Ψ(z,t))=b_pr(z,t). Thus it has exactly f∘χ on
every bottom point, exactly g∘χ on every top point, and exactly H_(n−1)(t,χ(z)) on every side
point, including all face intersections and all identified characteristic-boundary
representatives. No injectivity of χ on its frontier is assumed; the exact boundary equations are
the ones used for the gluing in step8. Only n≥2 invokes this sphere-lift route; the
one-dimensional homotopy was already obtained from equality of based edge-loop classes. This
replaces only the higher filling component, not the remaining arbitrary-basepoint or all-skeleton
source expansions. No compact cone, cone-center quotient or additional cylinder norm-comparison
proof is used.

8. Choose the fillings for all n-cells and define H_n to equal H_{n−1} on the old skeleton and
each filling on its open cell. Identifications of lateral representatives are respected because
there the filling equals H_{n−1} at the attaching point; identified endpoint representatives have
values f or g of that same point. Interior representatives are unique within a cell and interiors
of distinct cells are disjoint. This proves well-definedness without any separately assumed
overlap of arbitrary fillings. Every skeleton S is a closed Hausdorff subcomplex with the
inherited characteristic maps and topology, by the subcomplex cell-map and structure results. Its
ambient CW closed-set criterion restricts to its subtype because closed sets in a closed subspace
are closed in K. Thus no independent CWComplex univ instance on a changed carrier is assumed.
First establish the exact nonregular-cell interface. For an original d-cell e of S let D_d be the
subtype of closedBall(0:Fin d→ℝ,1), with its original maximum-norm topology, and let C_e be its
actual closed-cell image in S, with the induced topology. The finite-coordinate module is finite
dimensional even for d=0; finite_dimensional_proper_real_g8 makes its existing real normed space
proper; isCompact_closedBall and isCompact_iff_compactSpace give CompactSpace D_d. The original
characteristic map is ContinuousOn this native ball, hence continuous on D_d by
continuousOn_iff_continuous_domRestrict. Restrict its codomain to C_e: the closed-cell-image
identity supplies membership, continuous_subtype_mk gives continuity, and that very image identity
gives surjectivity. Thus q_e:D_d→C_e is a continuous surjection from a compact space to a
Hausdorff subspace of S, so compact_hausdorff_surjection_quotient_g8 makes it a quotient map. No
injectivity on the characteristic boundary and no regular-cell identification C_e≃D_d is used. If
U:I×S→Y has continuous original characteristic-prism pullbacks, apply
quotient_map_locally_compact_product_descent_g8 literally to the function U_e:I×C_e→Y and q_e,
with locally compact parameter I. Its pullback (t,z)↦U(t,q_e(z)) is exactly that
characteristic-prism map, after the harmless product-coordinate interchange if it was given on
D_d×I. Therefore U_e is continuous. The theorem used here is function-continuity descent, not an
asserted bundled product-quotient API. This works also for a vertex disk D_0 and for every
noninjective attaching map.
Now follow the written continuity proof at Hatcher Appendix p.523, using Proposition A.1 p.520 and
the compact-open proof of A.14–A.15 pp.530–531. Closed cells are compact, hence closed in
Hausdorff S. The CW closed-set criterion says that S is generated by these closed cells. In
particular S is compactly generated: if a subset has closed intersection with every compact
subspace, it has closed intersection with each closed cell, and the CW test makes it closed in S;
conversely a closed subset has closed restriction to every subspace. A compact C⊆S is contained in
a finite subcomplex F by topo.compact_cw_subset_finite_subcomplex, including the empty-C case. F
is a finite union of its closed cells. If the restrictions U_e above are continuous, their
restrictions to the finitely many closed sets I×(C∩C_e) cover I×C and agree since they are
restrictions of U. Each C_e is closed in S, so these are closed in the original product I×C. The
finite-family locally-finite and closed-pasting leaves give continuity of U|_(I×C). This uses
finiteness only for the subcomplex containing this particular compact C, never finiteness, local
finiteness or a dimension bound on S.
Use exactly the first paragraph of the written A.15 proof to pass from these compact restrictions
to joint continuity. For each x∈S the time track t↦U(t,x) is continuous, since x lies in a closed
cell with continuous U_e. Hence the curried function Û:S→C(I,Y), Û(x)(t)=U(t,x), is well-defined
with the compact-open topology. A.14(b), in continuous_map_curry_uncurry_g8, makes Û|_C continuous
from the just proved continuity on I×C. Its written subbasic proof uses a compact time set L and
an open set O⊆Y: when U(L,x)⊆O, the open preimage of O contains L×{x}; compactness of L supplies a
product neighborhood contained in that preimage. Thus the subbasic compact-open preimage is open,
without any separation assumption on Y. Since S is compactly generated, testing preimages of
closed subsets of C(I,Y) on all compact C now proves Û continuous on S. A.14(a),(c) then uncurries
on the original ordinary product I×S. Its written evaluation proof chooses a compact neighborhood
L of a time t inside the open preimage of O under the continuous track; choose an open V with
t∈V⊆L. Then M(L,O)×V is an open neighborhood of the track and time in the compact-open ordinary
product and evaluates into O. Local compactness of I gives this neighborhood, so
continuous_eval_compactOpen and continuous_map_curry_uncurry_g8 prove U(t,x)=eval(Û(x),t) jointly
continuous. These are the actual written curry/evaluation arguments, not a new global
disjoint-union quotient construction or a change to a compactly generated product topology. This
is the source p.523 closed-cell-product criterion, proved by the A.15 compact-restriction
argument; the full A.15 proof additionally obtains compact generation of the ordinary product by
applying this same criterion to the identity into its compactly generated refinement and then
testing on compact products.
Apply this criterion to the constructed H_n. Every old-cell prism is continuous by H_{n−1}, and
every new n-cell prism is the continuous filling from step7; exact lateral and endpoint agreements
already established ensure these are its literal pullbacks. The per-cell descent therefore
supplies the required closed-cell-product restrictions, and the source compact-generation/curry
proof gives continuity of H_n:I×S→Y in the inherited ordinary topology. The old homotopy, endpoint
maps and root vertex track are preserved exactly. The same criterion is available above for the
selected tree T and K¹. All native-ball, codomain-range and zero-dimensional guards have been
expanded here as interface checks; Hatcher does not print those Mathlib coordinate formulas.

9. Induct over the natural-number skeleta to obtain compatible H_n, starting with H₁; for a
zero-dimensional connected complex the single vertex and its constant track already solve the
problem. Every point of K lies in a finite-dimensional open cell and hence in a skeleton, by the
finite-skeleton exhaustion. Define H(t,x)=H_n(t,x) for any such n. Compatibility makes the value
independent of n. For an original m-cell, its entire closed cell lies in skeletonLT K (m+1)=Kᵐ by
cw_closed_cell_skeleton_bound_g8, including its noninjective frontier. Thus the full native
characteristic-prism pullback of H is exactly the continuous H_m pullback, or H₁ when m≤1, because
every later stage agrees on that entire skeleton. Apply the per-cell disk-to-closed-cell quotient
descent from step8: these pullbacks give continuous restrictions of H to I times every original
closed cell. The written Hatcher p.523/A.15 compact-generation criterion proved there, using
compact-subset finite support and compact-open curry/evaluation, now gives continuity of H:I×K→Y
in the original ordinary product topology. No global characteristic disjoint-union quotient is
constructed. No finiteness of K, bound on its dimension, uniform convergence, infinite time
concatenation or local finiteness is needed; a compact set only requires its own finite
subcomplex. Endpoint and based equations pass pointwise from the chosen finite stage: H(0,x)=f(x),
H(1,x)=g(x), H(t,k₀)=y₀.

10. This H is a homotopy through based maps on the original topology of K. Empty K cannot occur
because k₀ was chosen; the dimension-one case requires only the boundary-loop fillings; arbitrary
loop edges, parallel edges and noninjective attaching maps were retained. A connected K with no
positive-dimensional cells is one point. Y need not be given a CW structure for this uniqueness
direction: the universal covering with contractible total space supplies precisely the
higher-dimensional extension property used in Hatcher’s proof. No equality of induced maps at an
unchosen basepoint and no extra vertex assumption were introduced.
-/
theorem cw_map_based_homotopy_uniqueness
    {K : Type u} {Y : Type v} {E : Type w}
    [TopologicalSpace K] [TopologicalSpace Y] [TopologicalSpace E]
    [T2Space K] [ConnectedSpace K] [Topology.CWComplex (Set.univ : Set K)]
    [ContractibleSpace E]
    (k₀ : K) (y₀ : Y) (p : E → Y)
    (hp : IsCoveringMap p) (hp_surjective : Function.Surjective p)
    (f g : C(K, Y)) (hf : f k₀ = y₀) (hg : g k₀ = y₀)
    (hπ₁ : FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg) :
    Nonempty (ContinuousMap.HomotopyRel f g {k₀}) := by
  classical
  by_cases hzero : ∀ n : ℕ, 0 < n →
      IsEmpty (Topology.RelCWComplex.cell (Set.univ : Set K) n)
  · have : Subsingleton K := cw_zero_dimensional_subsingleton hzero
    exact based_homotopy_of_subsingleton k₀ y₀ f g hf hg
  · -- Refine the original CW presentation, preserving the SAME topology,
    -- maps, fundamental group and arbitrarily chosen original basepoint.
    obtain ⟨new, _, _, _, ⟨r, hrvertex⟩, _, _, _, _⟩ :=
      cw_point_vertex_refinement K inferInstance k₀
    let : Topology.CWComplex (Set.univ : Set K) := new
    let : Topology.RelCWComplex (Set.univ : Set K) ∅ :=
      @Topology.CWComplex.instRelCWComplex K _ Set.univ new
    have hrpt : Topology.RelCWComplex.map (C := Set.univ) 0 r 0 = k₀ := by
      let χr := @Topology.CWComplex.map K _ Set.univ new 0 r
      have hs : (0 : Fin 0 → ℝ) ∈ χr.source := by
        rw [@Topology.CWComplex.source_eq K _ Set.univ new 0 r]
        simp
      have hmem : χr 0 ∈ χr.target := χr.map_source hs
      change χr.target = {k₀} at hrvertex
      rw [hrvertex] at hmem
      exact Set.mem_singleton_iff.mp hmem
    subst k₀
    obtain ⟨T, hT0, _, hr, C, hC0, hC1, hCr, hCmem⟩ :=
      cw_spanning_tree_inclusion_contraction r
    obtain ⟨f', ⟨Hf⟩, hfc⟩ := cw_collapse_map_on_contracting_subcomplex T
      ⟨_, hr⟩ C hC0 hC1 hCr f
    obtain ⟨g', ⟨Hg⟩, hgc⟩ := cw_collapse_map_on_contracting_subcomplex T
      ⟨_, hr⟩ C hC0 hC1 hCr g
    have hf' : f' (Topology.RelCWComplex.map (C := Set.univ) 0 r 0) = y₀ := (hfc ⟨_, hr⟩).trans hf
    have hg' : g' (Topology.RelCWComplex.map (C := Set.univ) 0 r 0) = y₀ := (hgc ⟨_, hr⟩).trans hg
    have hloops := based_loop_images_homotopic_after_relative
      (Topology.RelCWComplex.map (C := Set.univ) 0 r 0) y₀ f g f' g' hf hg hf' hg' hπ₁ Hf Hg
    obtain ⟨H₁, hH0, hH1, hHfixed⟩ := cw_one_skeleton_homotopy_of_collapsed_root_loops
      r T hT0 hr C hC0 hC1 hCmem y₀ f' g'
      (fun x ↦ (hfc x).trans hf) (fun x ↦ (hgc x).trans hg) hloops
    have hk : Topology.RelCWComplex.map (C := Set.univ) 0 r 0 ∈
        (Topology.CWComplex.skeleton (Set.univ : Set K) 1 : Set K) :=
      Topology.CWComplex.skeleton_mono (by norm_num : (0 : ℕ∞) ≤ 1)
        (Topology.CWComplex.closedCell_subset_skeleton 0 r ⟨0, by simp, rfl⟩)
    obtain ⟨Hwhole⟩ := cw_based_homotopy_from_one_skeleton
      (Topology.RelCWComplex.map (C := Set.univ) 0 r 0) hk p hp hp_surjective f' g' H₁ hH0 hH1
      (fun t ↦ (hHfixed t hk).trans hf'.symm)
    exact ⟨(Hf.trans Hwhole).trans Hg.symm⟩




end HolomorphicAnosov
