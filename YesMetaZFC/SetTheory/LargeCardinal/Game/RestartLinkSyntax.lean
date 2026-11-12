import YesMetaZFC.SetTheory.LargeCardinal.Game.RecoverySyntax
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.Model.SetTheory.Relations.CollectCode

/-! # 同一恢复记录中的三图延伸方程

旧元数增一，实数图和标签图包含旧图的实际像，第三图恰好追加一个点。
所有包含和追加均在新存档的原关系中解释。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- 新旧元数、新旧实数图、新旧标签图、新旧恢复图和本次新增值。
def tg_restart_link0_m : Formula 1 9 := set[9] ⟪
  ⌜KP.succ0_m⌝ₚ(⌜(.bound 0 : Term 9)⌝ₛ,⌜(.bound 1 : Term 9)⌝ₛ) ∧
  ⌜(.bound 3 : Term 9)⌝ₛ ⊆ ⌜(.bound 2 : Term 9)⌝ₛ ∧
  ⌜(.bound 5 : Term 9)⌝ₛ ⊆ ⌜(.bound 4 : Term 9)⌝ₛ ∧
  ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 9)⌝ₛ,⌜(.bound 8 : Term 9)⌝ₛ,⌜(.bound 6 : Term 9)⌝ₛ) ∧
  (∀ p, p ∈ ⌜(.bound 6 : Term 9)⌝ₛ ↔ p ∈ ⌜(.bound 7 : Term 9)⌝ₛ ∨
    ⌜kpair0_m⌝ₚ(p,⌜(.bound 1 : Term 9)⌝ₛ,⌜(.bound 8 : Term 9)⌝ₛ))⟫

theorem tg_restart_link0_closed_l : tg_restart_link0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_restart_link0_m,Definitional.Formula.FreeClosed]

-- v 依次保存原边所送的树、长度、实数图、标签图和恢复图；w 是同一新存档的完整记录。
def Tg_restart_link_d (I : kpair_convention_l.Interpretation M) (X R : M.Domain)
    (v : Fin 5 → M.Domain) (w : Fin 54 → M.Domain) : Prop :=
  v 0 = w 19 ∧ ∃ x, Rr_truth_d I X R tg_restart_link0_m
    (fun i => [w 22,v 1,w 40,v 2,w 41,v 3,w 42,v 4,x].get i)

theorem Tg_restart_link_d.of_native_l (I : kpair_convention_l.Interpretation M)
    {X R : M.Domain} (nx : ∃ x, M.mem x X) (hE : Extensional (smdl_structure_l I (R := R) nx))
    (v : Fin 5 → (smdl_structure_l I (R := R) nx).Domain)
    (w : Fin 54 → (smdl_structure_l I (R := R) nx).Domain)
    (x : (smdl_structure_l I (R := R) nx).Domain) (name : v 0 = w 19)
    (succ : (smdl_structure_l I (R := R) nx).SuccessorOf (w 22) (v 1))
    (real : (smdl_structure_l I (R := R) nx).MemberSubset (v 2) (w 40))
    (labels : (smdl_structure_l I (R := R) nx).MemberSubset (v 3) (w 41))
    (entry : Rd_entry_d (v 1) x (w 42))
    (graph : ∀ p, (smdl_structure_l I (R := R) nx).mem p (w 42) ↔
      (smdl_structure_l I (R := R) nx).mem p (v 4) ∨ KPair_d (smdl_structure_l I (R := R) nx) p (v 1) x) :
    Tg_restart_link_d I X R (fun i => (v i).val) (fun i => (w i).val) := by
  let ρ : Env (smdl_structure_l I (R := R) nx) 9 :=
    ⟨fun i => [w 22,v 1,w 40,v 2,w 41,v 3,w 42,v 4,x].get i,fun _ => x⟩
  have truth : Formula.satisfies ρ tg_restart_link0_m := by
    simp only [tg_restart_link0_m,Formula.satisfies_conj_iff,KP.succ0_sat_l hE,
      Formula.satisfies_subset_iff,rd_entry0_sat_l hE,Formula.satisfies_forall_iff,
      Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,Formula.satisfies_disj_iff,
      kpair0_sat_l hE,Definitional.Term.eval_weaken]
    exact ⟨succ,real,labels,entry,graph⟩
  have values : (fun i => (ρ.bound i).val) =
      (fun i => [(w 22).val,(v 1).val,(w 40).val,(v 2).val,(w 41).val,(v 3).val,
        (w 42).val,(v 4).val,x.val].get i) :=
    funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))))))))
  exact ⟨congrArg Subtype.val name,x.val,Eq.mp (congrArg (Rr_truth_d I X R tg_restart_link0_m) values)
    ((rr_truth_native_l I nx tg_restart_link0_m tg_restart_link0_closed_l ρ.bound).mpr truth)⟩

/-- 恢复图的实际末点回收任意外层配对，因此精确追加方程可读到整个所属模型。 -/
theorem tg_recovered_graph_l (hE : Extensional M) {C : M.Domain} (ct : M.TransitiveSet C)
    (nc : Nonempty {x // M.mem x C}) (ε : Env (rt_model_l C nc) 29)
    (recovered : Formula.satisfies ε tc_recovered0_m) :
    Rd_entry_d (ε.bound 9).val (ε.bound 1).val (ε.bound 2).val ∧
      ∀ p, M.mem p (ε.bound 2).val ↔ M.mem p (ε.bound 26).val ∨
        KPair_d M p (ε.bound 9).val (ε.bound 1).val := by
  have ext := rt_model_ext_l hE ct nc
  simp only [tc_recovered0_m,tc_recovered_m,Formula.satisfies_conj_iff] at recovered
  obtain ⟨_,_,_,_,_,_,_,_,_,_,entry,ends⟩ := recovered
  have entry := (rt_entry_l ct nc hE _ _ _).mp ((rd_entry0_sat_l ext ..).mp entry)
  simp only [Formula.satisfies_forall_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_disj_iff,kpair0_sat_l ext,Definitional.Term.eval_weaken] at ends
  have pair (p : (rt_model_l C nc).Domain) : KPair_d (rt_model_l C nc) p (ε.bound 9) (ε.bound 1) ↔
      KPair_d M p.val (ε.bound 9).val (ε.bound 1).val := by
    let ρ : Env (rt_model_l C nc) 3 := ⟨fun i => [p,ε.bound 9,ε.bound 1].get i,fun _ => p⟩
    exact (kpair0_sat_l ext ρ (.bound 0) (.bound 1) (.bound 2)).symm.trans
      ((rt_model_delta_l ct nc (kpair0_delta_l ..) ρ).trans (kpair0_sat_l hE ..))
  refine ⟨entry,fun p => ⟨?_,?_⟩⟩
  · intro hp
    let p₀ : (rt_model_l C nc).Domain := ⟨p,ct _ (ε.bound 2).property p hp⟩
    exact ((ends p₀).mp hp).imp_right (pair p₀).mp
  · rintro (hp | hp)
    · exact (ends ⟨p,ct _ (ε.bound 26).property p hp⟩).mpr (Or.inl hp)
    · obtain ⟨q,hq,mem⟩ := entry
      exact kpair_unique_l M hE hq hp ▸ mem

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原继续方程在传递目标中的精确像

全称追加方程不能只读正条目。已有末项回收实际配对，使整个背景中的图成员双向对应；
因此长度后继、两张图的包含及恢复图的精确单点追加均由同一原方程推出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private theorem tg_restart_source_l (hE : Extensional M) {Y : M.Domain} (yt : M.TransitiveSet Y)
    (ny : Nonempty {x // M.mem x Y}) (ρ : Env (rt_model_l Y ny) 9)
    (valid : Formula.satisfies ρ tg_restart_link0_m) :
    M.SuccessorOf (ρ.bound 0).val (ρ.bound 1).val ∧
    M.MemberSubset (ρ.bound 3).val (ρ.bound 2).val ∧ M.MemberSubset (ρ.bound 5).val (ρ.bound 4).val ∧
    Rd_entry_d (ρ.bound 1).val (ρ.bound 8).val (ρ.bound 6).val ∧
    ∀ p, M.mem p (ρ.bound 6).val ↔ M.mem p (ρ.bound 7).val ∨ KPair_d M p (ρ.bound 1).val (ρ.bound 8).val := by
  have ext := rt_model_ext_l hE yt ny
  simp only [tg_restart_link0_m,Formula.satisfies_conj_iff,KP.succ0_sat_l ext,
    Formula.satisfies_subset_iff,rd_entry0_sat_l ext,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,Formula.satisfies_disj_iff,
    kpair0_sat_l ext,Definitional.Term.eval_weaken] at valid
  obtain ⟨succ,real,labels,entry,graph⟩ := valid
  have entry := (rt_entry_l yt ny hE (ρ.bound 1) (ρ.bound 8) (ρ.bound 6)).mp entry
  have sub {A B : (rt_model_l Y ny).Domain} (h : (rt_model_l Y ny).MemberSubset A B) : M.MemberSubset A.val B.val :=
    fun x hx => h ⟨x,yt A.val A.property x hx⟩ hx
  have pair (p : (rt_model_l Y ny).Domain) :
      KPair_d (rt_model_l Y ny) p (ρ.bound 1) (ρ.bound 8) ↔ KPair_d M p.val (ρ.bound 1).val (ρ.bound 8).val := by
    let η : Env (rt_model_l Y ny) 3 := ⟨fun i => [p,ρ.bound 1,ρ.bound 8].get i,fun _ => p⟩
    exact (kpair0_sat_l ext η (.bound 0) (.bound 1) (.bound 2)).symm.trans
      ((rt_model_delta_l yt ny (kpair0_delta_l ..) η).trans (kpair0_sat_l hE ..))
  refine ⟨(rt_successor_l yt ny hE (ρ.bound 0) (ρ.bound 1)).mp succ,sub real,sub labels,entry,?_⟩
  intro p
  constructor
  · intro hp
    let p₀ : (rt_model_l Y ny).Domain := ⟨p,yt _ (ρ.bound 6).property p hp⟩
    exact ((graph p₀).mp hp).imp_right (pair p₀).mp
  · rintro (hp | hp)
    · exact (graph ⟨p,yt _ (ρ.bound 7).property p hp⟩).mpr (Or.inl hp)
    · obtain ⟨q,hq,mem⟩ := entry
      exact kpair_unique_l M hE hq hp ▸ mem

private theorem tg_restart_mem_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d Y S : M.Domain} (target : Smem_d I d Y S) (yt : M.TransitiveSet Y) (v : Fin 9 → M.Domain)
    (truth : Rr_truth_d I Y S tg_restart_link0_m v) :
    M.SuccessorOf (v 0) (v 1) ∧ M.MemberSubset (v 3) (v 2) ∧ M.MemberSubset (v 5) (v 4) ∧
    Rd_entry_d (v 1) (v 8) (v 6) ∧ ∀ p, M.mem p (v 6) ↔ M.mem p (v 7) ∨ KPair_d M p (v 1) (v 8) := by
  have bound := truth.elim fun members _ => members
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨v 0,bound 0⟩⟩
  let η : Env (rt_model_l Y ny) 9 := ⟨fun i => ⟨v i,bound i⟩,fun _ => ⟨v 0,bound 0⟩⟩
  have valid : Formula.satisfies η tg_restart_link0_m := (smem_formula_l I target ny tg_restart_link0_m η).mpr
    ((rr_truth_native_l I target.1.2.1 tg_restart_link0_m tg_restart_link0_closed_l
      (fun i => ⟨v i,bound i⟩)).mp truth)
  exact tg_restart_source_l hE yt ny η valid

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 只需两组实际五坐标像，目标中得到同一树及完整精确追加。 -/
theorem Tg_restart_link_d.image_l {ω c X R d Y S j : M.Domain} {v : Fin 5 → M.Domain} {w : Fin 54 → M.Domain}
    (link : Tg_restart_link_d I X R v w) (hw : M.IsOmega ω)
    (model : Smdl_d I c X R) (target : Smem_d I d Y S) (yt : M.TransitiveSet Y)
    (map : Smap_d I ω c d X Y j) (a b : Fin 5 → M.Domain)
    (iv : ∀ i, Rd_entry_d (v i) (a i) j)
    (iw : ∀ i, Rd_entry_d (w ([22,19,40,41,42].get i)) (b i) j) :
    a 0 = b 1 ∧ M.SuccessorOf (b 0) (a 1) ∧ M.MemberSubset (a 2) (b 2) ∧ M.MemberSubset (a 3) (b 3) ∧
    ∃ x, Rd_entry_d (a 1) x (b 4) ∧ ∀ p, M.mem p (b 4) ↔ M.mem p (a 4) ∨ KPair_d M p (a 1) x := by
  obtain ⟨name,x,truth⟩ := link
  obtain ⟨y,_,hy⟩ := map.1.1.2.2 x (truth.elim fun bound _ => bound 8)
  have moved : Rr_truth_d I Y S tg_restart_link0_m
      (fun i => [b 0,a 1,b 2,a 2,b 3,a 3,b 4,a 4,y].get i) :=
    truth.map_l I hZF hw model target.1 map tg_restart_link0_closed_l
      (Fin.cases (iw 0) (Fin.cases (iv 1) (Fin.cases (iw 2) (Fin.cases (iv 2)
        (Fin.cases (iw 3) (Fin.cases (iv 3) (Fin.cases (iw 4) (Fin.cases (iv 4)
          (Fin.cases hy (fun i => Fin.elim0 i))))))))))
  obtain ⟨succ,real,labels,entry,graph⟩ := tg_restart_mem_l I hZF.1 target yt _ moved
  exact ⟨map.1.1.1.2 (w 19) (a 0) (b 1) (name ▸ iv 0) (iw 1),succ,real,labels,y,entry,graph⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一恢复记录的三图方程句法

直接编码原关系中的实际重启方程，原档案和工作复制档案共用此对象语言。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_restart_link_m {d} (X R : Term d) (v : Fin 5 → Term d) (w : Fin 54 → Term d) : Formula 1 d :=
  .conj (Formula.extensionalEq (v 0) (w 19)) (.existsE
    (rr_truth_m (𝒞 := kpair_convention_l) tg_restart_link0_m X.weaken R.weaken
      (fun i => [(w 22).weaken,(v 1).weaken,(w 40).weaken,(v 2).weaken,(w 41).weaken,
        (v 3).weaken,(w 42).weaken,(v 4).weaken,.newest].get i)))

@[simp] theorem tg_restart_link_closed_l {d} (X R : Term d) (v : Fin 5 → Term d) (w : Fin 54 → Term d)
    (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hv : ∀ i, (v i).freeSupport = []) (hw : ∀ i, (w i).freeSupport = []) :
    (tg_restart_link_m X R v w).FreeClosed := by
  simp only [tg_restart_link_m,Definitional.Formula.FreeClosed]
  refine ⟨by simp -implicitDefEqProofs [hv,hw] ,rr_truth_closed_l _ tg_restart_link0_closed_l _ _ _ ?_ ?_ ?_⟩
  · simpa using hX
  · simpa using hR
  · simp -implicitDefEqProofs [Fin.forall_fin_succ,hv,hw]

theorem tg_restart_link_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (X R : Term d) (v : Fin 5 → Term d) (w : Fin 54 → Term d) :
    Formula.satisfies ρ (tg_restart_link_m X R v w) ↔
      Tg_restart_link_d I (X.eval ρ) (R.eval ρ) (fun i => (v i).eval ρ) (fun i => (w i).eval ρ) := by
  simp only [tg_restart_link_m,Tg_restart_link_d,Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE,Formula.satisfies_exists_iff,
    rr_truth_sat_l I _ _ tg_restart_link0_closed_l,Definitional.Term.eval_weaken]
  apply and_congr_right
  intro _
  apply exists_congr
  intro x
  have same (t : Term d) := Definitional.Term.eval_weaken ρ x t
  have values : (fun i : Fin 9 => ([(w 22).weaken,(v 1).weaken,(w 40).weaken,(v 2).weaken,
      (w 41).weaken,(v 3).weaken,(w 42).weaken,(v 4).weaken,.newest].get i).eval (ρ.push x)) =
      (fun i => [(w 22).eval ρ,(v 1).eval ρ,(w 40).eval ρ,(v 2).eval ρ,
        (w 41).eval ρ,(v 3).eval ρ,(w 42).eval ρ,(v 4).eval ρ,x].get i) :=
    funext (Fin.cases (same (w 22)) (Fin.cases (same (v 1)) (Fin.cases (same (w 40))
      (Fin.cases (same (v 2)) (Fin.cases (same (w 41)) (Fin.cases (same (v 3))
        (Fin.cases (same (w 42)) (Fin.cases (same (v 4)) (Fin.cases rfl (fun i => Fin.elim0 i))))))))))
  exact values ▸ Iff.rfl

end YesMetaZFC.SetTheory.LargeCardinal
