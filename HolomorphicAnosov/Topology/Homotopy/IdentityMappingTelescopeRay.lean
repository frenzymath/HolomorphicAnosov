import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeSequence
import Mathlib.Topology.Homotopy.Equiv

/-!
# Identity mapping telescopes

Source: Hatcher, *Algebraic Topology*, Proposition A.11 proof, p.528,
identity telescope identification. DAG: `topo.identity_mapping_telescope_ray_g3`.
-/

universe u

namespace HolomorphicAnosov.MappingTelescope.Sequence

open Set ContinuousMap

/-- The ordinary quotient-cylinder telescope of identity maps on any topological space
is homeomorphic to its product with the closed real ray and homotopy equivalent to the space.

Source: Hatcher, Proposition A.11 proof, p.528. Send `[n,x,t]` to `(x,n+t)`.
The inverse uses the natural floor of the nonnegative height and its remainder. At integer
heights the two adjacent cylinder representatives agree by the endpoint seam. On each
closed strip the inverse is the cylinder map applied to `(x,s-n)`, extended continuously
by clipping the second coordinate to the unit interval. The strips cover the ray and are
locally finite: a neighborhood bounded above by an integer N meets only strips indexed
below N. Locally finite closed pasting proves inverse continuity. Scaling the ray
coordinate from zero to its value supplies the inverse homotopy to the projection onto P.
No separation or nonemptiness hypothesis is used. -/
theorem identity_mapping_telescope_ray (P : Type u) [TopologicalSpace P] :
    Nonempty (telescope (X := fun _ : ℕ ↦ P) (fun _ ↦ ContinuousMap.id P) ≃ₜ
      P × Set.Ici (0 : ℝ)) ∧
    Nonempty (telescope (X := fun _ : ℕ ↦ P) (fun _ ↦ ContinuousMap.id P) ≃ₕ P) := by
  -- Hatcher A.11: each identity cylinder has the coordinates (x, n + t).
  let fid : ∀ _ : ℕ, C(P, P) := fun _ ↦ ContinuousMap.id P
  let rayRaw : C(Cylinder (fun _ : ℕ ↦ P), P × Set.Ici (0 : ℝ)) :=
    ⟨fun a ↦ (a.2.1, ⟨(a.1 : ℝ) + a.2.2.val,
        add_nonneg (Nat.cast_nonneg _) a.2.2.prop.1⟩),
      continuous_sigma fun n ↦ continuous_fst.prodMk
        (((continuous_const : Continuous (fun _ : P × TelescopeInterval => (n : ℝ))).add
          (continuous_subtype_val.comp continuous_snd)).subtype_mk
            (fun a ↦ add_nonneg (Nat.cast_nonneg n) a.2.prop.1))⟩
  have hray : ∀ a b, setoid fid a b → rayRaw a = rayRaw b := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      rcases hab with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [rayRaw]
      · apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [rayRaw]
    | refl => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ h k => exact h.trans k
  let toRay : C(telescope fid, P × Set.Ici (0 : ℝ)) :=
    ⟨Quotient.lift rayRaw hray, rayRaw.continuous.quotient_lift hray⟩
  let fromRay : P × Set.Ici (0 : ℝ) → telescope fid := fun z ↦
    cylinder fid ⌊z.2.val⌋₊ (z.1, ⟨z.2.val - (⌊z.2.val⌋₊ : ℝ),
      sub_nonneg.mpr (Nat.floor_le z.2.prop),
      (sub_le_iff_le_add.mpr (by linarith [Nat.lt_floor_add_one z.2.val]))⟩)
  have hto_from : Function.RightInverse fromRay toRay := by
    intro z
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (⌊z.2.val⌋₊ : ℝ) + (z.2.val - (⌊z.2.val⌋₊ : ℝ)) = z.2.val
      ring
  have hfrom_to : Function.LeftInverse fromRay toRay := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      rcases z with ⟨n, x, t⟩
      change fromRay (x, ⟨(n : ℝ) + t.val, _⟩) = cylinder fid n (x, t)
      by_cases ht : t.val = 1
      · have hn : ⌊(n : ℝ) + t.val⌋₊ = n + 1 := by
          rw [ht, ← Nat.cast_add_one]
          exact Nat.floor_natCast _
        dsimp only [fromRay]
        simp only [hn]
        have he : (⟨(n : ℝ) + t.val - ((n + 1 : ℕ) : ℝ), by
            constructor <;> simp [ht]⟩ : unitInterval) = 0 := by
          apply Subtype.ext
          simp [ht]
        rw [he]
        have ht' : t = 1 := Subtype.ext ht
        rw [ht']
        exact (levelTop_eq fid n x).symm
      · have hn : ⌊(n : ℝ) + t.val⌋₊ = n := by
          apply (Nat.floor_eq_iff (add_nonneg (Nat.cast_nonneg n) t.prop.1)).mpr
          constructor
          · linarith [t.prop.1]
          · exact add_lt_add_right (lt_of_le_of_ne t.prop.2 ht) _
        dsimp only [fromRay]
        simp only [hn]
        congr 2
        apply Subtype.ext
        dsimp
        ring
  have hfrom_cont : Continuous fromRay := by
    let strips : ℕ → Set (P × Set.Ici (0 : ℝ)) := fun n ↦
      {z | (n : ℝ) ≤ z.2.val ∧ z.2.val ≤ (n : ℝ) + 1}
    have hlf : LocallyFinite strips := by
      intro z
      obtain ⟨N, hN⟩ := exists_nat_gt z.2.val
      refine ⟨{w | w.2.val < (N : ℝ)},
        (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const).mem_nhds hN, ?_⟩
      apply (Set.finite_Iio N).subset
      intro n hn
      obtain ⟨w, hw, hwN⟩ := hn
      exact_mod_cast (lt_of_le_of_lt hw.1 hwN)
    apply hlf.continuous
    · ext z
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨⌊z.2.val⌋₊, Nat.floor_le z.2.prop, (Nat.lt_floor_add_one z.2.val).le⟩
    · intro n
      exact (isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)).inter
        (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const)
    · intro n
      let c : C(P × Set.Ici (0 : ℝ), telescope fid) :=
        ⟨fun z ↦ cylinder fid n (z.1, ⟨max 0 (min 1 (z.2.val - (n : ℝ))),
          le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩),
         (cylinder fid n).continuous.comp (continuous_fst.prodMk
           ((continuous_const.max (continuous_const.min
             ((continuous_subtype_val.comp continuous_snd).sub continuous_const))).subtype_mk _))⟩
      apply c.continuous.continuousOn.congr
      intro z hz
      apply hfrom_to.injective
      rw [hto_from]
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change z.2.val = (n : ℝ) + max 0 (min 1 (z.2.val - (n : ℝ)))
        have h0 : 0 ≤ z.2.val - (n : ℝ) := sub_nonneg.mpr hz.1
        have h1 : z.2.val - (n : ℝ) ≤ 1 := by linarith [hz.2]
        rw [min_eq_right h1, max_eq_right h0]
        ring
  have hhome : Nonempty (telescope fid ≃ₜ P × Set.Ici (0 : ℝ)) := by
    exact ⟨{ toFun := toRay
             invFun := fromRay
             left_inv := hfrom_to
             right_inv := hto_from
             continuous_toFun := toRay.continuous
             continuous_invFun := hfrom_cont }⟩
  have hid : Nonempty (telescope (X := fun _ : ℕ ↦ P)
      (fun _ ↦ ContinuousMap.id P) ≃ₕ P) := by
    let r : C(P × Set.Ici (0 : ℝ), P) := ⟨Prod.fst, continuous_fst⟩
    let z : Set.Ici (0 : ℝ) := ⟨0, by exact le_refl (0 : ℝ)⟩
    let i : C(P, P × Set.Ici (0 : ℝ)) :=
      ⟨fun x ↦ (x, z), continuous_id.prodMk (continuous_const (y := z))⟩
    have h : (i.comp r).Homotopic (ContinuousMap.id (P × Set.Ici (0 : ℝ))) := by
      refine ⟨{ toFun := fun z ↦ (z.2.1,
                  ⟨(z.1 : ℝ) * z.2.2.val, mul_nonneg z.1.prop.1 z.2.2.prop⟩)
                continuous_toFun := continuous_snd.fst.prodMk
                  (((continuous_subtype_val.comp continuous_fst).mul
                    (continuous_subtype_val.comp continuous_snd.snd)).subtype_mk _)
                map_zero_left := ?_
                map_one_left := ?_ }⟩
      · intro x
        ext
        · rfl
        · exact zero_mul _
      · intro x
        ext
        · rfl
        · exact one_mul _
    let e : (P × Set.Ici (0 : ℝ)) ≃ₕ P :=
      { toFun := r, invFun := i, left_inv := h,
        right_inv := ContinuousMap.Homotopic.refl (ContinuousMap.id P) }
    obtain ⟨ehome⟩ := hhome
    exact ⟨ehome.toHomotopyEquiv.trans e⟩
  exact ⟨hhome, hid⟩

end HolomorphicAnosov.MappingTelescope.Sequence

