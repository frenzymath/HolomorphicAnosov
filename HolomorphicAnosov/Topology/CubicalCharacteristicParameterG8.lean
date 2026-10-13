import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Cubical characteristic parameter for a cylinder cell

Source: Hatcher, *Algebraic Topology*, product-cell construction pp.8–9 and Theorem A.6,
p.524, specialized to the maximum norm on the plain function space `Fin d → ℝ`.
DAG node: `topo.mapping_cylinder_cubical_characteristic_parameter_g8`.

The explicit change of parameters separates the initial coordinate from the tail and rescales
`[-1,1]` to `[0,1]`. It parametrizes the product characteristic disk before any mapping-cylinder
quotient is taken. The quotient identifications belong to the consuming mapping-cylinder node;
this node asserts precisely the disk/prism homeomorphism and its interior and boundary faces.
All map data below are actual coordinate formulas; only named proof certificates are deferred.
-/

namespace HolomorphicAnosov.CubicalCharacteristicParameterG8

noncomputable section

/-- The literal max-norm closed unit disk. Source: Hatcher pp.8–9/A.6 p.524,
with the product characteristic domain specialized to Mathlib's finite-Pi maximum norm. -/
abbrev ClosedDisk (d : ℕ) := ↥(Metric.closedBall (0 : Fin d → ℝ) 1)

/-- Coordinate splitting and affine interval rescaling on the ambient coordinate space.
Source: the explicit product-cell specialization of Hatcher pp.8–9/A.6 p.524. -/
def diskPrismForward (d : ℕ) (v : Fin (d + 1) → ℝ) : (Fin d → ℝ) × ℝ :=
  (Fin.tail v, (v 0 + 1) / 2)

/-- The inverse ambient formula adjoins the coordinate `2t-1` before the tail.
Source: the inverse coordinate calculation in Hatcher's product-cell specialization. -/
def diskPrismBackward (d : ℕ) (p : (Fin d → ℝ) × ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons (2 * p.2 - 1) p.1

/-- Membership and homeomorphism certificates for the two explicit ambient maps.

Source: Hatcher pp.8–9 and Theorem A.6 p.524, explicit maximum-norm coordinate specialization.
Proof: The finite-Pi weak norm inequality at radius one says that `‖v‖≤1` exactly when
every coordinate has absolute value at most one. Split the successor index into coordinate
zero and its tail. The zero-coordinate bound is equivalent to `(v 0+1)/2 ∈ [0,1]`,
and the tail bounds give a member of the closed `d`-disk. Conversely `0≤t≤1` gives
`|2t-1|≤1`, and the tail's coordinate bounds combine with this to put `Fin.cons (2t-1) z`
in the closed `(d+1)`-disk. Affine cancellation gives `2*((v 0+1)/2)-1=v 0` and
`((2t-1)+1)/2=t`; `Fin.cons_self_tail` and `Fin.tail_cons` give both inverse laws.
Every forward coordinate is an evaluation or an affine combination of evaluations; each
backward coordinate is either the affine time coordinate or a tail evaluation. Finite-Pi
continuity, continuous real arithmetic and product formation prove ambient continuity in
both directions. No nonempty-tail hypothesis is needed: for `d=0`, its norm is zero and
the weak coordinate condition is vacuous.
-/
theorem diskPrism_coordinates (d : ℕ) :
    (∀ v : ClosedDisk (d + 1),
      (diskPrismForward d v).1 ∈ Metric.closedBall (0 : Fin d → ℝ) 1 ∧
      (diskPrismForward d v).2 ∈ unitInterval) ∧
    (∀ p : ClosedDisk d × unitInterval,
      diskPrismBackward d (p.1.val, p.2.val) ∈
        Metric.closedBall (0 : Fin (d + 1) → ℝ) 1) ∧
    (∀ v, diskPrismBackward d (diskPrismForward d v) = v) ∧
    (∀ p, diskPrismForward d (diskPrismBackward d p) = p) ∧
    Continuous (diskPrismForward d) ∧ Continuous (diskPrismBackward d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    have hv : ∀ i, |v.val i| ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right,
        pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num), Real.norm_eq_abs] using v.property
    constructor
    · change Fin.tail v.val ∈ Metric.closedBall (0 : Fin d → ℝ) 1
      simpa only [Metric.mem_closedBall, dist_zero_right,
        pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num), Real.norm_eq_abs, Fin.tail]
        using (fun i : Fin d ↦ hv i.succ)
    · change 0 ≤ (v.val 0 + 1) / 2 ∧ (v.val 0 + 1) / 2 ≤ 1
      have h := abs_le.mp (hv 0)
      constructor <;> linarith
  · intro p
    have hp : ∀ i, |p.1.val i| ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right,
        pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num), Real.norm_eq_abs] using p.1.property
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change ‖2 * p.2.val - 1‖ ≤ 1
      rw [Real.norm_eq_abs, abs_le]
      have ht := p.2.property
      constructor <;> linarith [ht.1, ht.2]
    · exact hp j
  · intro v
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change 2 * ((v 0 + 1) / 2) - 1 = v 0
      ring
    · rfl
  · intro p
    apply Prod.ext
    · rfl
    · change ((2 * p.2 - 1) + 1) / 2 = p.2
      ring
  · exact (continuous_pi (fun i ↦ continuous_apply i.succ)).prodMk
      (((continuous_apply 0).add continuous_const).div_const 2)
  · apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact (continuous_const.mul continuous_snd).sub continuous_const
    · exact (continuous_apply j).comp continuous_fst

/-- The specified characteristic-parameter homeomorphism, with concrete forward and inverse
formulas on the closed subtypes. Source: Hatcher's product cells pp.8–9/A.6 p.524. -/
def diskPrismHomeomorph (d : ℕ) : ClosedDisk (d + 1) ≃ₜ (ClosedDisk d × unitInterval) where
  toFun v := (⟨(diskPrismForward d v).1, (diskPrism_coordinates d).1 v |>.1⟩,
    ⟨(diskPrismForward d v).2, (diskPrism_coordinates d).1 v |>.2⟩)
  invFun p := ⟨diskPrismBackward d (p.1.val, p.2.val),
    (diskPrism_coordinates d).2.1 p⟩
  left_inv v := Subtype.ext ((diskPrism_coordinates d).2.2.1 v)
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst ((diskPrism_coordinates d).2.2.2.1 (p.1.val, p.2.val))
    · exact congrArg Prod.snd ((diskPrism_coordinates d).2.2.2.1 (p.1.val, p.2.val))
  continuous_toFun :=
    (((diskPrism_coordinates d).2.2.2.2.1.comp continuous_subtype_val).fst.subtype_mk _).prodMk
      (((diskPrism_coordinates d).2.2.2.2.1.comp
        continuous_subtype_val).snd.subtype_mk _)
  continuous_invFun :=
    ((diskPrism_coordinates d).2.2.2.2.2.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- The first output is exactly the original coordinate tail.
Source: the defining characteristic formula of this node, Hatcher's product-cell specialization. -/
theorem diskPrismHomeomorph_fst_val (d : ℕ) (v : ClosedDisk (d + 1)) :
    ((diskPrismHomeomorph d v).1 : Fin d → ℝ) = Fin.tail v.val := rfl

/-- The time coordinate is exactly the initial coordinate rescaled to `[0,1]`.
Source: the defining characteristic formula of this node, Hatcher's product-cell specialization. -/
theorem diskPrismHomeomorph_snd_val (d : ℕ) (v : ClosedDisk (d + 1)) :
    ((diskPrismHomeomorph d v).2 : ℝ) = (v.val 0 + 1) / 2 := rfl

/-- The inverse adjoins the coordinate `2t-1` to the given tail.
Source: the inverse characteristic formula of this node, Hatcher's product-cell specialization. -/
theorem diskPrismHomeomorph_symm_val (d : ℕ) (p : ClosedDisk d × unitInterval) :
    ((diskPrismHomeomorph d).symm p : Fin (d + 1) → ℝ) =
      Fin.cons (2 * (p.2 : ℝ) - 1) (p.1 : Fin d → ℝ) := rfl

/-- The exact interior coordinate criterion, with no restriction on dimension.

Source: Hatcher pp.8–9/A.6 p.524, specialized product characteristic-cell interior.
Proof: The finite-Pi strict norm criterion is valid at positive radius one, even with an
empty coordinate index. Splitting the successor coordinates gives the tail bound `‖z‖<1`
and `|v 0|<1`. The latter means `-1<v 0<1`, equivalent under affine rescaling to
`0<(v 0+1)/2<1`. These are exactly the displayed open disk and open time interval.
-/
theorem diskPrismHomeomorph_interior_iff (d : ℕ) (v : ClosedDisk (d + 1)) :
    v.val ∈ Metric.ball (0 : Fin (d + 1) → ℝ) 1 ↔
      ((diskPrismHomeomorph d v).1 : Fin d → ℝ) ∈ Metric.ball 0 1 ∧
        ((diskPrismHomeomorph d v).2 : ℝ) ∈ Set.Ioo 0 1 := by
  rw [diskPrismHomeomorph_fst_val, diskPrismHomeomorph_snd_val]
  simp only [Metric.mem_ball, dist_zero_right, Set.mem_Ioo]
  change ‖v.val‖ < 1 ↔ ‖Fin.tail v.val‖ < 1 ∧
    0 < (v.val 0 + 1) / 2 ∧ (v.val 0 + 1) / 2 < 1
  rw [pi_norm_lt_iff (by norm_num)]
  constructor
  · intro h
    have h0 := abs_lt.mp (show |v.val 0| < 1 from h 0)
    have ht : ∀ i : Fin d, ‖v.val i.succ‖ < 1 := fun i => h i.succ
    refine ⟨?_, ?_, ?_⟩
    · exact (pi_norm_lt_iff (by norm_num)).2 ht
    · have h0' : -1 < v.val 0 := by
        exact h0.1
      linarith
    · have h0' : v.val 0 < 1 := by
        exact h0.2
      linarith
  · rintro ⟨ht, hlow, hupp⟩ i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · have h0 : -1 < v.val 0 := by linarith
      have h1 : v.val 0 < 1 := by linarith
      simpa [Real.norm_eq_abs, abs_lt] using And.intro h0 h1
    · exact (pi_norm_lt_iff (by norm_num)).1 ht j

/-- The sphere is precisely the bottom, top or lateral face, with face intersections retained.

Source: Hatcher pp.8–9/A.6 p.524, product characteristic-cell boundary specialization.
Proof: Inside the closed disk the sphere is the closed disk minus its open ball. Negate
the interior criterion. The time already lies in `[0,1]`, so failure of its strict
inequalities is exactly time zero or one. The tail already lies in the closed disk, so
failure of its open-ball condition is exactly membership in its unit sphere. Conversely
each of these three alternatives prevents membership in the open prism. The equivalence
includes shared corners, and at `d=0` the lateral radius-one sphere is empty.
-/
theorem diskPrismHomeomorph_boundary_iff (d : ℕ) (v : ClosedDisk (d + 1)) :
    v.val ∈ Metric.sphere (0 : Fin (d + 1) → ℝ) 1 ↔
      ((diskPrismHomeomorph d v).2 : ℝ) = 0 ∨
      ((diskPrismHomeomorph d v).2 : ℝ) = 1 ∨
      ((diskPrismHomeomorph d v).1 : Fin d → ℝ) ∈ Metric.sphere 0 1 := by
  have hv := v.property
  have hz := (diskPrismHomeomorph d v).1.property
  have ht := (diskPrismHomeomorph d v).2.property
  have hi := diskPrismHomeomorph_interior_iff d v
  simp only [Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere,
    Set.mem_Ioo, Set.mem_Icc] at hv hz ht hi ⊢
  constructor
  · intro h
    by_cases h0 : ((diskPrismHomeomorph d v).2 : ℝ) = 0
    · exact Or.inl h0
    by_cases h1 : ((diskPrismHomeomorph d v).2 : ℝ) = 1
    · exact Or.inr (Or.inl h1)
    right; right
    by_contra hne
    have hin := hi.mpr ⟨lt_of_le_of_ne hz hne,
      lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
    linarith
  · intro h
    by_contra hne
    obtain ⟨ha, hb, hc⟩ := hi.mp (lt_of_le_of_ne hv hne)
    rcases h with h | h | h <;> linarith

/-- The entire open source disk maps onto the entire open prism.

Source: Hatcher pp.8–9/A.6 p.524, characteristic-product interior specialization.
Proof: The interior criterion gives containment. For every member of the open prism,
apply the homeomorphism inverse; cancellation and that same criterion put its inverse
in the open disk. Thus every point of the displayed prism is attained, giving equality.
-/
theorem diskPrismHomeomorph_image_interior (d : ℕ) :
    diskPrismHomeomorph d '' {v : ClosedDisk (d + 1) |
      v.val ∈ Metric.ball (0 : Fin (d + 1) → ℝ) 1} =
      {p : ClosedDisk d × unitInterval |
        p.1.val ∈ Metric.ball (0 : Fin d → ℝ) 1 ∧ p.2.val ∈ Set.Ioo 0 1} := by
  ext p
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (diskPrismHomeomorph_interior_iff d v).mp hv
  · intro hp
    refine ⟨(diskPrismHomeomorph d).symm p, ?_, (diskPrismHomeomorph d).apply_symm_apply p⟩
    apply (diskPrismHomeomorph_interior_iff d _).mpr
    simpa using hp

/-- The entire sphere maps onto the union of the full bottom, top and lateral faces.

Source: Hatcher pp.8–9/A.6 p.524, characteristic-product boundary specialization.
Proof: The boundary criterion gives containment in the three-face union. For every point
of that union, use the inverse homeomorphism and its cancellation law in the same criterion
to obtain a source-sphere point mapping to it. This proves exact image equality and keeps
all intersections between faces, rather than asserting a disjoint union.
-/
theorem diskPrismHomeomorph_image_boundary (d : ℕ) :
    diskPrismHomeomorph d '' {v : ClosedDisk (d + 1) |
      v.val ∈ Metric.sphere (0 : Fin (d + 1) → ℝ) 1} =
      {p : ClosedDisk d × unitInterval | p.2.val = 0} ∪
      {p : ClosedDisk d × unitInterval | p.2.val = 1} ∪
      {p : ClosedDisk d × unitInterval | p.1.val ∈ Metric.sphere (0 : Fin d → ℝ) 1} := by
  ext p
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa only [Set.mem_union, Set.mem_ofPred_eq, or_assoc] using
      (diskPrismHomeomorph_boundary_iff d v).mp hv
  · intro hp
    refine ⟨(diskPrismHomeomorph d).symm p, ?_, (diskPrismHomeomorph d).apply_symm_apply p⟩
    apply (diskPrismHomeomorph_boundary_iff d _).mpr
    simpa only [Homeomorph.apply_symm_apply, Set.mem_union, Set.mem_ofPred_eq, or_assoc] using hp

/-- The inverse maps an open prism point precisely to an open source-disk point.

Source: Hatcher pp.8–9/A.6 p.524, explicit inverse product parameter.
Proof: Apply the interior criterion to the inverse image of `p` and cancel the forward
homeomorphism followed by its inverse. The tail and time are then exactly those of `p`.
-/
theorem diskPrismHomeomorph_symm_interior_iff (d : ℕ) (p : ClosedDisk d × unitInterval) :
    ((diskPrismHomeomorph d).symm p).val ∈
      Metric.ball (0 : Fin (d + 1) → ℝ) 1 ↔
      p.1.val ∈ Metric.ball (0 : Fin d → ℝ) 1 ∧ p.2.val ∈ Set.Ioo 0 1 := by
  simpa using diskPrismHomeomorph_interior_iff d ((diskPrismHomeomorph d).symm p)

/-- For a zero-dimensional tail, the open source disk is characterized only by strict time.

Source: Hatcher's zero-cell product with the interval, pp.8–9/A.6 p.524.
Proof: Specialize the interior criterion to `d=0`. The empty coordinate function has
norm zero, and hence is always in the open radius-one ball. Remove this automatically
true tail condition; precisely the open interval condition remains.
-/
theorem diskPrismHomeomorph_interior_iff_zero (v : ClosedDisk 1) :
    v.val ∈ Metric.ball (0 : Fin 1 → ℝ) 1 ↔
      ((diskPrismHomeomorph 0 v).2 : ℝ) ∈ Set.Ioo 0 1 := by
  rw [diskPrismHomeomorph_interior_iff]
  constructor
  · rintro ⟨_, ht⟩
    exact ht
  · intro ht
    have hzero : ((diskPrismHomeomorph 0 v).1 : Fin 0 → ℝ) = 0 := by
      funext i
      exact Fin.elim0 i
    exact ⟨by rw [hzero]; simp [Metric.mem_ball], ht⟩

/-- In dimension zero there is no lateral face.

Source: Hatcher's zero-cell product with the interval, pp.8–9/A.6 p.524.
Proof: The only function on `Fin 0` has norm zero. It cannot have distance one from zero,
so its unit sphere is empty. Therefore no point in the zero-disk prism lies on a lateral face.
-/
theorem lateral_face_zero :
    {p : ClosedDisk 0 × unitInterval | p.1.val ∈ Metric.sphere (0 : Fin 0 → ℝ) 1} = ∅  := by
  ext p
  have hzero : p.1.val = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
  simp [hzero]

/-- At dimension zero, the one-dimensional source sphere maps exactly to the two endpoint faces.

Source: Hatcher's zero-cell product with the interval, pp.8–9/A.6 p.524.
Proof: Apply the full boundary image theorem with `d=0` and remove its lateral face using
the preceding empty-sphere fact. The two remaining faces are precisely the two interval
endpoints; the unique zero-dimensional tail creates no extra boundary point.
-/
theorem diskPrismHomeomorph_image_boundary_zero :
    diskPrismHomeomorph 0 '' {v : ClosedDisk 1 |
      v.val ∈ Metric.sphere (0 : Fin 1 → ℝ) 1} =
      {p : ClosedDisk 0 × unitInterval | p.2.val = 0} ∪
      {p : ClosedDisk 0 × unitInterval | p.2.val = 1} := by
  have h := diskPrismHomeomorph_image_boundary 0
  rw [lateral_face_zero, Set.union_empty] at h
  exact h

end

end HolomorphicAnosov.CubicalCharacteristicParameterG8

