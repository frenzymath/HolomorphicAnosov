import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Basic

/-!
# Characteristic continuity and prism gluing for CW complexes

These are the shared characteristic-map continuity and compatible-prism descent
lemmas used by both the CW homotopy-extension and based-homotopy modules.
Sources: Hatcher, Algebraic Topology, Appendix A.2, pp.520–521, and A.17,
pp.532–533.
-/

namespace HolomorphicAnosov

universe u v

/-- Hatcher p.523's closed-cell map criterion on the original Hausdorff CW
carrier. For a closed target set, its pullback intersected with each closed
cell is the image of a closed subset of the compact characteristic disk,
so is compact and closed in the original carrier. The CW weak-topology
field now proves global continuity. No target separation is needed. -/
theorem cw_continuous_of_characteristic
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)] (f : K → Y)
    (hc : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell (Set.univ : Set K) n),
      Continuous (fun z : Metric.closedBall (0 : Fin n → ℝ) 1 ↦
        f (Topology.RelCWComplex.map n i z.val))) : Continuous f := by
  rw [continuous_iff_isClosed]
  intro T hT
  apply (Topology.CWComplex.closed Set.univ (f ⁻¹' T) (Set.subset_univ _)).mpr
  intro n i
  let disk := Metric.closedBall (0 : Fin n → ℝ) 1
  have : CompactSpace disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let χ : C(disk, K) := ⟨fun z ↦ Topology.RelCWComplex.map n i z.val,
    (Topology.RelCWComplex.continuousOn n i).domRestrict⟩
  have hclosed : IsClosed ((fun z : disk ↦ f (χ z)) ⁻¹' T) :=
    hT.preimage (hc n i)
  have hcompact := hclosed.isCompact.image χ.continuous
  have heq : f ⁻¹' T ∩ Topology.CWComplex.closedCell (C := Set.univ) n i =
      χ '' ((fun z : disk ↦ f (χ z)) ⁻¹' T) := by
    ext x
    constructor
    · rintro ⟨hxT, hxcell⟩
      obtain ⟨z, hz, hzx⟩ := hxcell
      exact ⟨⟨z, hz⟩, by change f (Topology.RelCWComplex.map n i z) ∈ T; rw [hzx]; exact hxT, hzx⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, ⟨z.val, z.property, rfl⟩⟩
  rw [heq]
  exact hcompact.isClosed

/-- Hatcher p.523/A.14's actual ordinary-product continuity mechanism.
Given continuous pullbacks on ALL characteristic prisms, every time track
is continuous. Curry to the compact-open path space, apply the just proved
CW map criterion to its characteristic pullbacks (continuous by currying),
then uncurry using local compactness of I. This proves ordinary-product
continuity directly, with no finiteness/local-finiteness or altered product.
The compact characteristic-disk step is explicit in the preceding theorem.
-/
theorem cw_prism_continuous_of_characteristic
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [Topology.CWComplex (Set.univ : Set K)]
    (H : unitInterval × K → Y)
    (hc : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell (Set.univ : Set K) n),
      Continuous (fun q : unitInterval × Metric.closedBall (0 : Fin n → ℝ) 1 ↦
        H (q.1, Topology.RelCWComplex.map n i q.2.val))) : Continuous H := by
  have htrack : ∀ x : K, Continuous (fun t : unitInterval ↦ H (t, x)) := by
    intro x
    have hx : x ∈ ⋃ (n : ℕ) (i : Topology.RelCWComplex.cell (Set.univ : Set K) n),
        Topology.CWComplex.closedCell n i := by
      rw [Topology.CWComplex.union]
      exact Set.mem_univ _
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, z, hz, hzx⟩ := Set.mem_iUnion.mp hx
    have ht := (hc n i).comp (continuous_id.prodMk
      (continuous_const : Continuous (fun _ : unitInterval ↦ (⟨z, hz⟩ :
        Metric.closedBall (0 : Fin n → ℝ) 1))))
    change Continuous (fun t : unitInterval ↦ H (t, Topology.RelCWComplex.map n i z)) at ht
    rw [hzx] at ht
    exact ht
  let curryH : K → C(unitInterval, Y) := fun x ↦ ⟨fun t ↦ H (t, x), htrack x⟩
  have hcurried : Continuous curryH := by
    apply cw_continuous_of_characteristic
    intro n i
    let prism : C(Metric.closedBall (0 : Fin n → ℝ) 1 × unitInterval, Y) :=
      ⟨fun q ↦ H (q.2, Topology.RelCWComplex.map n i q.1.val),
        (hc n i).comp continuous_swap⟩
    convert prism.curry.continuous using 1
    funext z
    apply ContinuousMap.ext
    intro t
    rfl
  have huncurry := (ContinuousMap.uncurry (⟨curryH, hcurried⟩ : C(K, C(unitInterval, Y)))).continuous
  exact huncurry.comp continuous_swap
/-- The actual inherited-subspace version of the closed-cell criterion.
This uses CWComplex C in its ORIGINAL ambient carrier, so applies to an
infinite subcomplex without manufacturing a replacement topology. -/
theorem cw_subtype_continuous_of_characteristic
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] (C : Set K) [Topology.CWComplex C] (f : C → Y)
    (hc : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell C n),
      Continuous (fun z : Metric.closedBall (0 : Fin n → ℝ) 1 ↦
        f ⟨Topology.RelCWComplex.map n i z.val,
          Topology.RelCWComplex.closedCell_subset_complex n i ⟨z.val, z.property, rfl⟩⟩)) :
    Continuous f := by
  rw [continuous_iff_isClosed]
  intro T hT
  have hclosed : IsClosed (Subtype.val '' (f ⁻¹' T) : Set K) := by
    apply (Topology.CWComplex.closed C _ (by rintro _ ⟨x, _, rfl⟩; exact x.property)).mpr
    intro n i
    let disk := Metric.closedBall (0 : Fin n → ℝ) 1
    have : CompactSpace disk := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    let χ : C(disk, K) := ⟨fun z ↦ Topology.RelCWComplex.map n i z.val,
      (Topology.RelCWComplex.continuousOn n i).domRestrict⟩
    let χC : C(disk, C) := ⟨fun z ↦ ⟨χ z,
      Topology.RelCWComplex.closedCell_subset_complex n i ⟨z.val, z.property, rfl⟩⟩,
      χ.continuous.subtype_mk _⟩
    have hpre : IsClosed ((fun z : disk ↦ f (χC z)) ⁻¹' T) := hT.preimage (hc n i)
    have hcompact := hpre.isCompact.image χ.continuous
    have heq : (Subtype.val '' (f ⁻¹' T) : Set K) ∩
        Topology.CWComplex.closedCell (C := C) n i =
        χ '' ((fun z : disk ↦ f (χC z)) ⁻¹' T) := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, z, hz, hzy⟩
        refine ⟨⟨z, hz⟩, ?_, hzy⟩
        have he : χC ⟨z, hz⟩ = y := Subtype.ext hzy
        change f (χC ⟨z, hz⟩) ∈ T
        rw [he]
        exact hy
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨χC z, hz, rfl⟩, ⟨z.val, z.property, rfl⟩⟩
    rw [heq]
    exact hcompact.isClosed
  convert hclosed.preimage continuous_subtype_val using 1
  exact (Set.preimage_image_eq _ Subtype.val_injective).symm

/-- Ordinary-product continuity on the literal carrier of any subcomplex.
Compact-open currying uses the same CW C, its inherited subspace topology,
and the original finite characteristic disks. No local finiteness is used. -/
theorem cw_subtype_prism_continuous_of_characteristic
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] (C : Set K) [Topology.CWComplex C] (H : unitInterval × C → Y)
    (hc : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell C n),
      Continuous (fun q : unitInterval × Metric.closedBall (0 : Fin n → ℝ) 1 ↦
        H (q.1, ⟨Topology.RelCWComplex.map n i q.2.val,
          Topology.RelCWComplex.closedCell_subset_complex n i
            ⟨q.2.val, q.2.property, rfl⟩⟩))) : Continuous H := by
  have htrack : ∀ x : C, Continuous (fun t : unitInterval ↦ H (t, x)) := by
    intro x
    have hx : x.val ∈ ⋃ (n : ℕ) (i : Topology.RelCWComplex.cell C n),
        Topology.CWComplex.closedCell n i := by
      rw [Topology.CWComplex.union]
      exact x.property
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, z, hz, hzx⟩ := Set.mem_iUnion.mp hx
    have ht := (hc n i).comp (continuous_id.prodMk
      (continuous_const : Continuous (fun _ : unitInterval ↦ (⟨z, hz⟩ :
        Metric.closedBall (0 : Fin n → ℝ) 1))))
    convert ht using 1
    funext t
    apply congrArg (fun y : C ↦ H (t, y))
    exact Subtype.ext hzx.symm
  let curryH : C → C(unitInterval, Y) := fun x ↦ ⟨fun t ↦ H (t, x), htrack x⟩
  have hcurried : Continuous curryH := by
    apply cw_subtype_continuous_of_characteristic C
    intro n i
    let prism : C(Metric.closedBall (0 : Fin n → ℝ) 1 × unitInterval, Y) :=
      ⟨fun q ↦ H (q.2, ⟨Topology.RelCWComplex.map n i q.1.val,
        Topology.RelCWComplex.closedCell_subset_complex n i
          ⟨q.1.val, q.1.property, rfl⟩⟩),
        (hc n i).comp continuous_swap⟩
    convert prism.curry.continuous using 1
    funext z
    apply ContinuousMap.ext
    intro t
    rfl
  have huncurry := (ContinuousMap.uncurry (⟨curryH, hcurried⟩ :
    C(C, C(unitInterval, Y)))).continuous
  exact huncurry.comp continuous_swap


/-- Descent of compatible original characteristic prisms to the inherited
CW carrier. Compatibility is on actual characteristic images, not abstract
faces, so the statement covers nonregular attaching maps without alteration. -/
theorem cw_subtype_glue_characteristic_prisms
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] (C : Set K) [Topology.CWComplex C]
    (P : ∀ (n : ℕ) (_i : Topology.RelCWComplex.cell C n),
      C(unitInterval × Metric.closedBall (0 : Fin n → ℝ) 1, Y))
    (hcompat : ∀ (n : ℕ) (i : Topology.RelCWComplex.cell C n)
      (m : ℕ) (j : Topology.RelCWComplex.cell C m)
      t (z : Metric.closedBall (0 : Fin n → ℝ) 1)
      (w : Metric.closedBall (0 : Fin m → ℝ) 1),
      Topology.RelCWComplex.map n i z.val = Topology.RelCWComplex.map m j w.val →
      P n i (t, z) = P m j (t, w)) :
    ∃ H : C(unitInterval × C, Y), ∀ n i t z,
      H (t, ⟨Topology.RelCWComplex.map n i z.val,
        Topology.RelCWComplex.closedCell_subset_complex n i ⟨z.val, z.property, rfl⟩⟩) =
      P n i (t, z) := by
  classical
  let Rep := Σ n : ℕ, Σ i : Topology.RelCWComplex.cell C n,
    Metric.closedBall (0 : Fin n → ℝ) 1
  let eval : Rep → C := fun r ↦ ⟨Topology.RelCWComplex.map r.1 r.2.1 r.2.2.val,
    Topology.RelCWComplex.closedCell_subset_complex _ _
      ⟨r.2.2.val, r.2.2.property, rfl⟩⟩
  have hsurj : Function.Surjective eval := by
    intro x
    have hx : x.val ∈ ⋃ (n : ℕ) (i : Topology.RelCWComplex.cell C n),
        Topology.CWComplex.closedCell n i := by
      rw [Topology.CWComplex.union]
      exact x.property
    obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i, z, hz, hzx⟩ := Set.mem_iUnion.mp hx
    exact ⟨⟨n, i, ⟨z, hz⟩⟩, Subtype.ext hzx⟩
  let choose : C → Rep := fun x ↦ (hsurj x).choose
  have hchoose : ∀ x, eval (choose x) = x := fun x ↦ (hsurj x).choose_spec
  let H : unitInterval × C → Y := fun q ↦
    P (choose q.2).1 (choose q.2).2.1 (q.1, (choose q.2).2.2)
  have hagree : ∀ n i t z,
      H (t, ⟨Topology.RelCWComplex.map n i z.val,
        Topology.RelCWComplex.closedCell_subset_complex n i ⟨z.val, z.property, rfl⟩⟩) =
      P n i (t, z) := by
    intro n i t z
    exact hcompat _ _ n i t _ z (congrArg Subtype.val (hchoose _))
  have hc : Continuous H := by
    apply cw_subtype_prism_continuous_of_characteristic C
    intro n i
    convert (P n i).continuous using 1
    funext q
    exact hagree n i q.1 q.2
  exact ⟨⟨H, hc⟩, hagree⟩

end HolomorphicAnosov
