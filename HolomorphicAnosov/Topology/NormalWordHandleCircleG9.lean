import HolomorphicAnosov.Topology.GallierXuSidePointDisk
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.Homotopy.Lifting

/-!
# A circle map detecting a handle in a surface normal word

This file constructs the circle-valued obstruction associated with the first handle of a positive-genus normal word.
-/

noncomputable section
open Set
namespace HolomorphicAnosov.Topology.GallierXu

/-- The real trapezoid with vertex values `0, 1, 1, 0`. -/
def handleTentG9 (x : ℝ) : ℝ := max 0 (min 1 (min x (3-x)))

@[fun_prop] theorem continuous_handleTent_g9 : Continuous handleTentG9 := by
  unfold handleTentG9
  fun_prop

@[simp] theorem handleTent_zero_g9 : handleTentG9 0 = 0 := by norm_num [handleTentG9]

theorem handleTent_of_three_le_g9 (x : ℝ) (hx : 3 ≤ x) : handleTentG9 x = 0 := by
  unfold handleTentG9
  apply max_eq_left
  exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))

theorem handleTent_first_g9 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    handleTentG9 t = t := by
  simp only [handleTentG9,min_eq_left (show t ≤ 3-t by linarith [ht.2]),
    min_eq_right ht.2,max_eq_right ht.1]

theorem handleTent_second_g9 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    handleTentG9 (1+t) = 1 := by
  unfold handleTentG9
  rw [min_eq_left (le_min (by linarith [ht.1]) (by linarith [ht.2]))]
  norm_num

theorem handleTent_third_g9 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    handleTentG9 (2+(1-t)) = t := by
  have he : 3-(2+(1-t)) = t := by ring
  simp only [handleTentG9,he,min_eq_right (show t ≤ 2+(1-t) by linarith [ht.2]),
    min_eq_right ht.2,max_eq_right ht.1]

/-- The trapezoid descends to a circle of period `n`. -/
def handleCircleArgumentG9 (n : ℕ) (hn : 4 ≤ n) : C(Circle,ℝ) := by
  letI : Fact (0 < (n : ℝ)) := ⟨by exact_mod_cast (show 0 < n by omega)⟩
  let hper : handleTentG9 0 = handleTentG9 n := by
    rw [handleTent_zero_g9,handleTent_of_three_le_g9 _ (by exact_mod_cast (show 3 ≤ n by omega))]
  let f : C(AddCircle (n : ℝ),ℝ) :=
    ⟨AddCircle.liftIco (n : ℝ) 0 handleTentG9,
      AddCircle.liftIco_zero_continuous hper continuous_handleTent_g9.continuousOn⟩
  let e := (AddCircle.homeomorphCircle (show (n : ℝ) ≠ 0 by positivity)).symm
  exact f.comp ⟨e,e.continuous⟩

/-- The value of the periodic argument at the original boundary parameter. -/
theorem handleCircleArgument_exp_g9 (n : ℕ) (hn : 4 ≤ n) (x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) n) :
    handleCircleArgumentG9 n hn (Circle.exp (2*Real.pi*x/n)) = handleTentG9 x := by
  let : Fact (0 < (n : ℝ)) := ⟨by exact_mod_cast (show 0 < n by omega)⟩
  let e := AddCircle.homeomorphCircle (show (n : ℝ) ≠ 0 by positivity)
  have he : e (x : AddCircle (n : ℝ)) = Circle.exp (2*Real.pi*x/n) := by
    rw [AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk]
    congr 1
    ring
  rw [← he]
  change AddCircle.liftIco (n : ℝ) 0 handleTentG9 (e.symm (e (x : AddCircle (n : ℝ)))) = _
  rw [e.symm_apply_apply]
  by_cases hxn : x < n
  · exact AddCircle.liftIco_zero_coe_apply ⟨hx.1,hxn⟩
  · have hxeq : x = n := le_antisymm hx.2 (le_of_not_gt hxn)
    subst x
    rw [show ((n : ℝ) : AddCircle (n : ℝ)) = 0 by simp]
    rw [show (0 : AddCircle (n : ℝ)) = ((0 : ℝ) : AddCircle (n : ℝ)) by simp]
    rw [AddCircle.liftIco_zero_coe_apply (by exact ⟨le_rfl,Fact.out⟩),handleTent_zero_g9,
      handleTent_of_three_le_g9 _ (by exact_mod_cast (show 3 ≤ n by omega))]

/-- A Tietze extension of the prescribed real boundary values to the parameter disk. (Bredon, I.10.4) -/
theorem handleArgument_disk_extension_g9 (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : C(Disk,ℝ), ∀ z : Circle, A ⟨z,by simp⟩ = handleCircleArgumentG9 n hn z := by
  let i : Circle → Disk := fun z ↦ ⟨z,by simp⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  have hinj : Function.Injective i := fun a b h ↦ Subtype.ext (congrArg (fun z : Disk ↦ (z : ℂ)) h)
  obtain ⟨A,hA⟩ := (handleCircleArgumentG9 n hn).exists_extension (hi.isClosedEmbedding hinj)
  exact ⟨A,fun z ↦ congrArg (fun f : C(Circle,ℝ) ↦ f z) hA⟩

/-- A normal word with a first handle followed by the remaining word. -/
def handleWordG9 (L : Word) : Word := [(0,true),(1,true),(0,false),(1,false)] ++ L

@[simp] theorem handleWord_length_g9 (L : Word) : (handleWordG9 L).length = 4+L.length := by
  simp only [handleWordG9,List.length_append,List.length_cons,List.length_nil]

/-- Label zero occurs only on the two first-handle `a` sides. -/
theorem handleWord_label_zero_g9 (L : Word) (hL : ∀ d ∈ L, d.1 ≠ 0)
    (i : Fin (handleWordG9 L).length) :
    ((handleWordG9 L).get i).1 = 0 ↔ i.val = 0 ∨ i.val = 2 := by
  change ((handleWordG9 L)[i.val]).1 = 0 ↔ i.val = 0 ∨ i.val = 2
  by_cases hi : i.val < 4
  · have hs : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases hs with hi' | hi' | hi' | hi' <;> simp [handleWordG9,hi']
  · have hin : 4 ≤ i.val := le_of_not_gt hi
    have hiL : i.val-4 < L.length := by
      have h := i.isLt
      simp only [handleWord_length_g9] at h
      omega
    have hget : (handleWordG9 L).get i = L[i.val-4] := by
      change ([(0,true),(1,true),(0,false),(1,false)] ++ L)[i.val] = L[i.val-4]
      rw [List.getElem_append_right (by simpa using hin)]
      rfl
    have hz : ((handleWordG9 L).get i).1 ≠ 0 := by
      rw [hget]
      exact hL _ (List.getElem_mem _)
    change ((handleWordG9 L).get i).1 = 0 ↔ _
    simp only [hz,false_iff,not_or]
    omega

/-- The disk extension agrees with the trapezoid on every original side parameter. -/
theorem handleArgument_side_g9 (L : Word)
    (A : C(Disk,ℝ))
    (hA : ∀ z : Circle, A ⟨z,by simp⟩ =
      handleCircleArgumentG9 (handleWordG9 L).length (by simp) z)
    (i : Fin (handleWordG9 L).length) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    A (sidePointDisk (P := [handleWordG9 L]) 0 i t) =
      handleTentG9 ((i.val : ℝ) + if ((handleWordG9 L).get i).2 then t else 1-t) := by
  let x : ℝ := (i.val : ℝ) + if ((handleWordG9 L).get i).2 then t else 1-t
  have hi : (i.val : ℝ) + 1 ≤ (handleWordG9 L).length := by exact_mod_cast i.isLt
  have hx : x ∈ Icc (0 : ℝ) (handleWordG9 L).length := by
    dsimp [x]
    split_ifs <;> constructor <;> nlinarith [ht.1,ht.2,(show (0 : ℝ) ≤ i.val by positivity)]
  change A ⟨(Circle.exp (2*Real.pi*x/(handleWordG9 L).length) : ℂ),_⟩ = handleTentG9 x
  rw [hA,handleCircleArgument_exp_g9 _ _ _ hx]

/-- Exponentiation of the disk extension gives the handle loop on the two `a` sides and the constant map elsewhere. -/
theorem handleCircle_side_g9 (L : Word) (hL : ∀ d ∈ L, d.1 ≠ 0)
    (A : C(Disk,ℝ))
    (hA : ∀ z : Circle, A ⟨z,by simp⟩ =
      handleCircleArgumentG9 (handleWordG9 L).length (by simp) z)
    (i : Fin (handleWordG9 L).length) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Circle.exp (2*Real.pi*A (sidePointDisk (P := [handleWordG9 L]) 0 i t)) =
      if ((handleWordG9 L).get i).1 = 0 then Circle.exp (2*Real.pi*t) else 1 := by
  rw [handleArgument_side_g9 L A hA i t ht]
  change Circle.exp (2*Real.pi*handleTentG9 ((i.val : ℝ) +
      if ((handleWordG9 L)[i.val]).2 then t else 1-t)) =
    if ((handleWordG9 L)[i.val]).1 = 0 then Circle.exp (2*Real.pi*t) else 1
  by_cases hi : i.val < 3
  · have hs : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hs with hi' | hi' | hi'
    · simp only [handleWordG9,hi']
      simpa using congrArg (fun r : ℝ ↦ Circle.exp (2*Real.pi*r)) (handleTent_first_g9 t ht)
    · simp only [handleWordG9,hi']
      simp [handleTent_second_g9 t ht,Circle.exp_two_pi]
    · simp only [handleWordG9,hi']
      simpa using congrArg (fun r : ℝ ↦ Circle.exp (2*Real.pi*r)) (handleTent_third_g9 t ht)
  · have hi3 : 3 ≤ i.val := le_of_not_gt hi
    have hz : ((handleWordG9 L)[i.val]).1 ≠ 0 := by
      intro hz
      have h := (handleWord_label_zero_g9 L hL i).mp hz
      omega
    rw [ite_eq_right hz,handleTent_of_three_le_g9,mul_zero,Circle.exp_zero]
    have hi3' : (3 : ℝ) ≤ i.val := by exact_mod_cast hi3
    split_ifs <;> linarith [ht.1,ht.2]

/-- The first-handle circle map descends through the polygon edge relation. -/
theorem handleWord_circle_map_g9 (L : Word) (hL : ∀ d ∈ L, d.1 ≠ 0) :
    ∃ F : C(Realization [handleWordG9 L],Circle),
      ∀ (i : Fin (handleWordG9 L).length) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
        F (project [handleWordG9 L] (0,sidePointDisk (P := [handleWordG9 L]) 0 i t)) =
          if ((handleWordG9 L).get i).1 = 0 then Circle.exp (2*Real.pi*t) else 1 := by
  obtain ⟨A,hA⟩ := handleArgument_disk_extension_g9 (handleWordG9 L).length (by simp)
  let f : FaceDisks [handleWordG9 L] → Circle := fun x ↦ Circle.exp (2*Real.pi*A x.2)
  have hrel (x y : FaceDisks [handleWordG9 L]) (h : edgeIdentification [handleWordG9 L] x y) :
      f x = f y := by
    obtain ⟨xf,x⟩ := x
    obtain ⟨yf,y⟩ := y
    have hxf : xf = 0 := by apply Fin.ext; change xf.val = 0; have h := xf.isLt; change xf.val < 1 at h; omega
    have hyf : yf = 0 := by apply Fin.ext; change yf.val = 0; have h := yf.isLt; change yf.val < 1 at h; omega
    subst xf
    subst yf
    obtain ⟨i,j,t,ht,hl,hx,hy⟩ := h
    have hxd : x = sidePointDisk (P := [handleWordG9 L]) 0 i t := Subtype.ext hx
    have hyd : y = sidePointDisk (P := [handleWordG9 L]) 0 j t := Subtype.ext hy
    change Circle.exp (2*Real.pi*A x) = Circle.exp (2*Real.pi*A y)
    rw [hxd,hyd,handleCircle_side_g9 L hL A hA i t ht,handleCircle_side_g9 L hL A hA j t ht]
    change ((handleWordG9 L).get i).1 = ((handleWordG9 L).get j).1 at hl
    rw [hl]
  have heq (x y : FaceDisks [handleWordG9 L])
      (h : Relation.EqvGen (edgeIdentification [handleWordG9 L]) x y) : f x = f y := by
    induction h with
    | rel a b hab => exact hrel a b hab
    | refl a => rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ih1 ih2 => exact ih1.trans ih2
  let F : Realization [handleWordG9 L] → Circle := Quotient.lift f heq
  have hF : Continuous F := by
    exact (show Continuous f by fun_prop).quotient_lift heq
  refine ⟨⟨F,hF⟩,?_⟩
  intro i t ht
  exact handleCircle_side_g9 L hL A hA i t ht

/-- The first handle side is a closed path in the polygon quotient. -/
theorem handleWord_first_side_closed_g9 (L : Word) :
    project [handleWordG9 L] (0,sidePointDisk (P := [handleWordG9 L]) 0 ⟨0,by simp⟩ 0) =
      project [handleWordG9 L] (0,sidePointDisk (P := [handleWordG9 L]) 0 ⟨0,by simp⟩ 1) := by
  let i₀ : Fin (handleWordG9 L).length := ⟨0,by simp⟩
  let i₁ : Fin (handleWordG9 L).length := ⟨1,by simp only [handleWord_length_g9]; omega⟩
  let i₂ : Fin (handleWordG9 L).length := ⟨2,by simp only [handleWord_length_g9]; omega⟩
  let i₃ : Fin (handleWordG9 L).length := ⟨3,by simp only [handleWord_length_g9]; omega⟩
  have hget0 : (handleWordG9 L).get i₀ = (0,true) := rfl
  have hget1 : (handleWordG9 L).get i₁ = (1,true) := rfl
  have hget2 : (handleWordG9 L).get i₂ = (0,false) := rfl
  have hget3 : (handleWordG9 L).get i₃ = (1,false) := rfl
  have h23 : sidePointDisk (P := [handleWordG9 L]) 0 i₂ 0 = sidePointDisk (P := [handleWordG9 L]) 0 i₃ 1 := by
    apply Subtype.ext
    change (Circle.exp (2*Real.pi*((2:ℝ)+(1-0))/(handleWordG9 L).length) : ℂ) =
      Circle.exp (2*Real.pi*((3:ℝ)+(1-1))/(handleWordG9 L).length)
    norm_num
  have h12 : sidePointDisk (P := [handleWordG9 L]) 0 i₁ 1 = sidePointDisk (P := [handleWordG9 L]) 0 i₂ 1 := by
    apply Subtype.ext
    change (Circle.exp (2*Real.pi*((i₁.val:ℝ)+if ((handleWordG9 L).get i₁).2 then 1 else 1-1)/(handleWordG9 L).length) : ℂ) =
      Circle.exp (2*Real.pi*((i₂.val:ℝ)+if ((handleWordG9 L).get i₂).2 then 1 else 1-1)/(handleWordG9 L).length)
    rw [hget1,hget2]
    norm_num [i₁,i₂]
  calc
    _ = project [handleWordG9 L] (0,sidePointDisk (P := [handleWordG9 L]) 0 i₂ 0) :=
      project_sidePointDisk_eq (P := [handleWordG9 L]) 0 0 i₀ i₂ 0 (by norm_num) (by rfl)
    _ = project [handleWordG9 L] (0,sidePointDisk (P := [handleWordG9 L]) 0 i₃ 1) := by rw [h23]
    _ = project [handleWordG9 L] (0,sidePointDisk (P := [handleWordG9 L]) 0 i₁ 1) :=
      project_sidePointDisk_eq (P := [handleWordG9 L]) 0 0 i₃ i₁ 1 (by norm_num) (by rfl)
    _ = project [handleWordG9 L] (0,sidePointDisk (P := [handleWordG9 L]) 0 i₂ 1) := by rw [h12]
    _ = _ := project_sidePointDisk_eq (P := [handleWordG9 L]) 0 0 i₂ i₀ 1 (by norm_num) (by rfl)

/-- A circle map that winds once around the circle has no real lift. (Hatcher, Prop. 1.34) -/
theorem circle_map_no_lift_of_once_loop_g9 {X : Type*} [TopologicalSpace X]
    (F : C(X,Circle)) (p : C(unitInterval,X)) (hp : p 0 = p 1)
    (hF : ∀ t : unitInterval, F (p t) = Circle.exp (2*Real.pi*(t : ℝ))) :
    ¬ ∃ b : C(X,ℝ), ∀ x, Circle.exp (b x) = F x := by
  rintro ⟨b,hb⟩
  let r : C(unitInterval,ℝ) := b.comp p
  let s : C(unitInterval,ℝ) := ⟨fun t ↦ r 0 + 2*Real.pi*(t : ℝ),by fun_prop⟩
  have hr0 : Circle.exp (r 0) = 1 := by
    change Circle.exp (b (p 0)) = 1
    rw [hb,hF]
    simp
  have hcomp : Circle.exp ∘ r = Circle.exp ∘ s := by
    funext t
    change Circle.exp (b (p t)) = Circle.exp (r 0 + 2*Real.pi*(t : ℝ))
    rw [hb,hF,Circle.exp_add,hr0,one_mul]
  have hrs := Circle.isCoveringMap_exp.eq_of_comp_eq r.continuous s.continuous hcomp 0 (by simp [s])
  have he := congrFun hrs (1 : unitInterval)
  have hrend : r 0 = r 1 := congrArg b hp
  change r 1 = r 0 + 2*Real.pi*(1 : unitInterval).val at he
  norm_num at he
  linarith [Real.pi_pos]

/-- The first handle gives a nonliftable circle map that is constant on all other boundary edges. -/
theorem handleWord_circle_obstruction_g9 (L : Word) (hL : ∀ d ∈ L, d.1 ≠ 0) :
    ∃ F : C(Realization [handleWordG9 L],Circle),
      (∀ a : ℕ, a ≠ 0 → ∀ q ∈ edgeImage [handleWordG9 L] a, F q = 1) ∧
      ¬ ∃ b : C(Realization [handleWordG9 L],ℝ), ∀ x, Circle.exp (b x) = F x := by
  obtain ⟨F,hF⟩ := handleWord_circle_map_g9 L hL
  refine ⟨F,?_,?_⟩
  · intro a ha q hq
    obtain ⟨⟨face,x⟩,i,t,ht,hl,hx,rfl⟩ := hq
    have hface : face = 0 := by apply Fin.ext; change face.val = 0; have h := face.isLt; change face.val < 1 at h; omega
    subst face
    have hx' : x = sidePointDisk (P := [handleWordG9 L]) 0 i t := Subtype.ext hx
    rw [hx',hF i t ht]
    change ((handleWordG9 L).get i).1 = a at hl
    rw [hl,ite_eq_right ha]
  · let i₀ : Fin (handleWordG9 L).length := ⟨0,by simp⟩
    let p : C(unitInterval,Realization [handleWordG9 L]) :=
      ⟨fun t ↦ project [handleWordG9 L] (0,sidePointDisk (P := [handleWordG9 L]) 0 i₀ t),by
        exact continuous_quotient_mk'.comp (continuous_const.prodMk
          ((continuous_sidePointDisk (P := [handleWordG9 L]) 0 i₀).comp continuous_subtype_val))⟩
    apply circle_map_no_lift_of_once_loop_g9 F p (handleWord_first_side_closed_g9 L)
    intro t
    change F (project [handleWordG9 L] (0,sidePointDisk (P := [handleWordG9 L]) 0 i₀ t)) = _
    rw [hF i₀ t t.property]
    rfl

/-- A positive-genus normal word begins with a first handle and has no other side with its first generator label. -/
theorem normalWord_first_handle_g9 (g b : ℕ) :
    ∃ L : Word, normalWord (g+1) b = handleWordG9 L ∧ ∀ d ∈ L, d.1 ≠ 0 := by
  let L : Word :=
    ((List.range g).flatMap fun i ↦
      [(2*(i+1),true),(2*(i+1)+1,true),(2*(i+1),false),(2*(i+1)+1,false)]) ++
    ((List.range b).flatMap fun j ↦
      [(2*(g+1)+2*j,true),(2*(g+1)+2*j+1,true),(2*(g+1)+2*j,false)])
  refine ⟨L,?_,?_⟩
  · unfold normalWord
    rw [List.range_succ_eq_map]
    simp [handleWordG9,L,List.flatMap_map]
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨i,hi,hd⟩ := List.mem_flatMap.mp hd
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> omega
    · obtain ⟨j,hj,hd⟩ := List.mem_flatMap.mp hd
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
      rcases hd with rfl | rfl | rfl <;> omega

/-- Every positive-genus normal form admits a boundary-constant circle map with no real lift. -/
theorem normalWord_circle_obstruction_g9 (g b : ℕ) (hg : 0 < g) :
    ∃ F : C(Realization [normalWord g b],Circle),
      (∀ j : Fin b, ∀ q ∈ edgeImage [normalWord g b] (2*g+2*j.val+1), F q = 1) ∧
      ¬ ∃ a : C(Realization [normalWord g b],ℝ), ∀ x, Circle.exp (a x) = F x := by
  cases g with
  | zero => omega
  | succ g =>
    obtain ⟨L,hword,hL⟩ := normalWord_first_handle_g9 g b
    rw [hword]
    obtain ⟨F,hF,hnolift⟩ := handleWord_circle_obstruction_g9 L hL
    exact ⟨F,fun j ↦ hF _ (by omega),hnolift⟩

end HolomorphicAnosov.Topology.GallierXu

