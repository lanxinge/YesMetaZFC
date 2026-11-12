import YesMetaZFC.SetTheory.LargeCardinal.Demand.RankStep
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RealTrace
import YesMetaZFC.SetTheory.LargeCardinal.Demand.BranchDepth

/-! # 已发请求中的完整实数前缀

只读取原合法辅助请求已经保存的 digits 图；回答与请求追加均保留旧事件。
这里不为原关系模型补设 ZF 或 KP。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
include hE

theorem td_issued_real_l (ρ : Env M 47) (issued : Formula.satisfies ρ td_issued0_m) :
    ∃ x, Fn0_d (ρ.bound 19) (ρ.bound 6) x ∧
      ∀ i y, Rd_entry_d i y x → Tg_event_d I (ρ.bound 4) i (ρ.bound 3) (ρ.bound 20) y := by
  have aux := ((td_issued_sat_l I hE ρ).mp issued).auxiliary
  simp only [td_issued_aux0_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    fseq_end_sat_l I hE] at aux
  obtain ⟨h,ending,aux⟩ := aux
  simp only [td_aux_m,Formula.satisfies_bind,td_aux0_m,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff] at aux
  obtain ⟨_,_,_,_,_,_,_,_,x,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,digits,_⟩ := aux
  simp only [tg_digits_m,Formula.satisfies_conj_iff,fn0_sat_l hE,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,Formula.satisfies_mem_iff,Formula.satisfies_iff_iff,
    rd_entry0_sat_l hE,tg_event_sat_l I hE,Definitional.Term.eval_weaken] at digits
  have fn : Fn0_d (ρ.bound 19) (ρ.bound 6) x := digits.1
  refine ⟨x,fn,fun i y iy => ?_⟩
  have event : Tg_event_d I (ρ.bound 4) i (ρ.bound 3) h y := (digits.2 i y (fn.bound_l iy).1).mp iy
  exact event.end_l ending

theorem td_issued_real_unique_l (ρ : Env M 47) (issued : Formula.satisfies ρ td_issued0_m)
    {i x y : M.Domain} (left : Tg_event_d I (ρ.bound 4) i (ρ.bound 3) (ρ.bound 20) x)
    (right : Tg_event_d I (ρ.bound 4) i (ρ.bound 3) (ρ.bound 20) y) : x = y := by
  have data := (td_issued_sat_l I hE ρ).mp issued
  have control := data.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at control
  have clock := (tg_index_sat_l I hE ..).mp control.2.2.2.2.2.2.2.2.1
  obtain ⟨a,ha,ax⟩ := left
  obtain ⟨b,hb,bv⟩ := right
  have eq := clock i (ρ.bound 3) a b ha hb
  subst b
  exact data.history.2.2 a (data.history.bound_l ax).1 x (data.history.bound_l ax).2
    y (data.history.bound_l bv).2 ax bv

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一原对局的实数条目

背景指标经完整数字图进入当前模型，原根字母经实际根图进入同一历史。
记录谓词完全由对象公式表示，供内部阶段归纳和替换构造原对局。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def td_real_event0_m : Formula 1 5 := tg_event_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
theorem td_real_event0_closed_l : td_real_event0_m.FreeClosed := by simp -implicitDefEqProofs [td_real_event0_m]

def Td_real_d (I : kpair_convention_l.Interpretation M) (v : Fin 66 → M.Domain) (i x : M.Domain) : Prop :=
  ∃ n y, Rd_entry_d i n (v 4) ∧ Rd_entry_d x y (v 3) ∧
    Rr_truth_d I (v 0) (v 1) td_real_event0_m (fun j => [v 23,n,v 22,v 39,y].get j)

def td_real_m {d} (v : Fin 66 → Term d) (i x : Term d) : Formula 1 d :=
  set[d] ⟪∃ n y, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ,n,⌜v 4⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(⌜x⌝ₛ,y,⌜v 3⌝ₛ) ∧
    ⌜fun X R c n b h y => rr_truth_m (𝒞 := kpair_convention_l) td_real_event0_m X R
      (fun j => [c,n,b,h,y].get j)⌝ₚ(⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜v 23⌝ₛ,n,⌜v 22⌝ₛ,⌜v 39⌝ₛ,y)⟫

@[simp] theorem td_real_closed_l {d} (v : Fin 66 → Term d) (i x : Term d)
    (hv : ∀ j, (v j).freeSupport = []) (hi : i.freeSupport = []) (hx : x.freeSupport = []) :
    (td_real_m v i x).FreeClosed := by
  simp -implicitDefEqProofs [td_real_m,Definitional.Formula.FreeClosed,hv,hi,hx]
  apply rr_truth_closed_l td_real_event0_m td_real_event0_closed_l <;> simp [hv,Fin.forall_fin_succ]

theorem td_real_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (v : Fin 66 → Term d) (i x : Term d) :
    Formula.satisfies ρ (td_real_m v i x) ↔ Td_real_d I (fun j => (v j).eval ρ) (i.eval ρ) (x.eval ρ) := by
  simp only [td_real_m,Td_real_d,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE,rr_truth_sat_l I _ td_real_event0_m td_real_event0_closed_l,Definitional.Term.eval_weaken]
  apply exists_congr; intro n
  apply exists_congr; intro y
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply iff_of_eq; congr 1
  funext j
  match j with
  | ⟨0,_⟩ => simp only [List.get_eq_getElem,List.getElem_cons_zero,Definitional.Term.eval_weaken]
  | ⟨1,_⟩ => rfl
  | ⟨2,_⟩ => simp only [List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ,Definitional.Term.eval_weaken]
  | ⟨3,_⟩ => simp only [List.get_eq_getElem,List.getElem_cons_zero,List.getElem_cons_succ,Definitional.Term.eval_weaken]
  | ⟨4,_⟩ => rfl

def Td_real_record_d (I : kpair_convention_l.Interpretation M) (s i x : M.Domain) : Prop :=
  ∃ v : Fin 66 → M.Domain, Rt_tuple_d v s ∧ Td_real_d I v i x

def td_real_record_m {d} (s i x : Term d) : Formula 1 d :=
  let e : Term d → Term (66+d) := fun t => t.rename (Fin.natAdd 66)
  let v : Fin 66 → Term (66+d) := fun j => .bound (j.castAdd d)
  rb_exists_m (.conj (rt_tuple_m v (e s)) (td_real_m v (e i) (e x)))

@[simp] theorem td_real_record_closed_l {d} (s i x : Term d)
    (hs : s.freeSupport = []) (hi : i.freeSupport = []) (hx : x.freeSupport = []) :
    (td_real_record_m s i x).FreeClosed := by
  simp -implicitDefEqProofs [td_real_record_m,Definitional.Formula.FreeClosed,hi,hx]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hs)

theorem td_real_record_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (s i x : Term d) :
    Formula.satisfies ρ (td_real_record_m s i x) ↔ Td_real_record_d I (s.eval ρ) (i.eval ρ) (x.eval ρ) := by
  simp only [td_real_record_m,Td_real_record_d,rb_exists_sat_l,Formula.satisfies_conj_iff,
    rt_tuple_sat_l hE,td_real_sat_l I hE,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 当前原历史的实数字母：存在与唯一

节点自身的源证书供应外延性和配对，完整数字图识别背景指标。
所有原根字母的比较都通过实际根嵌入，不要求节点或根的隶属呈示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_state_d.native_base_l {g : Fin 10 → M.Domain} {v : Fin 19 → M.Domain} {a : Fin 47 → M.Domain}
    (state : Td_state_d hZF g v a) :
    let N := smdl_structure_l I (R := v 1) state.model.2.1
    Extensional N ∧ ∀ x y : N.Domain, ∃ p, Pair_d N p x y := by
  obtain ⟨Y,R,_,_,_,model,source,_⟩ := (state.tree.sources (v 5) (v 2) state.node).objects
  obtain ⟨ey,er⟩ := smdl_unique_l I model state.model
  subst Y R
  have ext := source.ext.native_l I state.model.2.1
  let ρ : Env (smdl_structure_l I (R := v 1) state.model.2.1) 0 :=
    ⟨Fin.elim0,fun _ => ⟨a 0,state.issued.1 0⟩⟩
  exact ⟨ext,(sc_pair_union_l ext ρ (source.theory.algebra state.model.2.1 ρ)).1⟩

theorem Td_state_d.real_unique_l {g : Fin 10 → M.Domain} {v : Fin 66 → M.Domain}
    (state : Td_state_d hZF g (fun i => v (i.castAdd 47)) (fun i => v (Fin.natAdd 19 i)))
    (root : Smdl_d I (g 1) (g 3) (g 4)) {i x y : M.Domain}
    (hx : Td_real_d I v i x) (hy : Td_real_d I v i y) : x = y := by
  have map := state.tree.diagram.elementary (g 2) (v 5) (v 3) (g 1) (g 3) (g 4)
    (v 2) (v 0) (v 1) state.origin state.root_node state.node root state.model
  obtain ⟨ext,pair⟩ := state.native_base_l hZF
  let N := smdl_structure_l I (R := v 1) state.model.2.1
  let J := kpair_interpretation_l N ext pair
  let ρ : Env N 47 := ⟨fun i => ⟨v (Fin.natAdd 19 i),state.issued.1 i⟩,
    fun _ => ⟨v 19,state.issued.1 0⟩⟩
  have issued : Formula.satisfies ρ td_issued0_m :=
    (rr_truth_native_l I state.model.2.1 td_issued0_m td_issued0_closed_l ρ.bound).mp state.issued
  obtain ⟨n,z,ni,xz,bounds,event⟩ := hx
  obtain ⟨n',z',ni',yz',bounds',event'⟩ := hy
  have eq := state.numbers.injection.1.1.2 i n' n ni' ni
  subst n'
  have left : Tg_event_d J (ρ.bound 4) ⟨n,bounds 1⟩ (ρ.bound 3) (ρ.bound 20) ⟨z,bounds 4⟩ :=
    (tg_event_sat_l J ext _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mp event
  have right : Tg_event_d J (ρ.bound 4) ⟨n,bounds 1⟩ (ρ.bound 3) (ρ.bound 20) ⟨z',bounds' 4⟩ :=
    (tg_event_sat_l J ext _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mp event'
  have eq : z = z' := congrArg Subtype.val (td_issued_real_unique_l J ext ρ issued left right)
  exact map.1.2 x y z' (eq ▸ xz) yz'

/-- 每个已完成的背景轮号都有一个原根字母，其像就是当前原历史中的实数落子。 -/
theorem Td_state_d.real_total_l {g : Fin 10 → M.Domain} {v : Fin 66 → M.Domain} {A : M.Domain}
    (state : Td_state_d hZF g (fun i => v (i.castAdd 47)) (fun i => v (Fin.natAdd 19 i)))
    (root : Zc_model_d I (g 0) (g 1) (g 3) (g 4))
    (letters : ∀ x, M.mem x A ↔ M.mem x (g 3) ∧ Rd_entry_d x (g 8) (g 4))
    {i : M.Domain} (hi : M.mem i (v 12)) : ∃ x, M.mem x A ∧ Td_real_d I v i x := by
  have map := state.tree.diagram.elementary (g 2) (v 5) (v 3) (g 1) (g 3) (g 4)
    (v 2) (v 0) (v 1) state.origin state.root_node state.node root.model state.model
  have native := ZFC.models_zf_l ((root.map_l hZF state.tree.omega state.model map).native_l I hZF state.tree.omega)
  have hN := ZF.modelsKP native
  let N := smdl_structure_l I (R := v 1) state.model.2.1
  let ρ : Env N 47 := ⟨fun i => ⟨v (Fin.natAdd 19 i),state.issued.1 i⟩,fun _ => ⟨v 19,state.issued.1 0⟩⟩
  have issued : Formula.satisfies ρ td_issued0_m :=
    (rr_truth_native_l I state.model.2.1 td_issued0_m td_issued0_closed_l ρ.bound).mp state.issued
  obtain ⟨s,fn,events⟩ := td_issued_real_l (kp_pair_l hN) hN.1 ρ issued
  have hiω := state.tree.omega.transitive (ZF.modelsKP hZF) (v 12) state.round i hi
  obtain ⟨n,hn,index⟩ := state.numbers.injection.1.2.2 i hiω
  have inside : N.mem ⟨n,hn⟩ (ρ.bound 19) := (state.numbers.predecessors _ _ state.index _).mpr ⟨i,hi,index⟩
  obtain ⟨y,hy,iy⟩ := fn.2.1 ⟨n,hn⟩ inside
  have event := events _ _ iy
  have rank := (rr_rank_native_l I state.model.2.1 hN
    (⟨v 15,state.slice.rank.1⟩ : N.Domain) ⟨v 16,state.slice.rank.2.1⟩).mp state.slice.rank
  have low : Rd_entry_d y.val (v 16) (v 1) :=
    (v_transitive_l (kp_pair_l hN) rank) (ρ.bound 6) state.letters_low y hy
  obtain ⟨x,_,image⟩ := (state.slice.image y.val).mp low
  have image := state.slice.root x y.val image
  have hx : M.mem x A := (letters x).mpr ⟨map.1.1.input_mem_of_pairMember image,
    (map.relation_l I hZF state.tree.omega root.model state.model image state.letters_root).mpr hy⟩
  refine ⟨x,hx,n,y.val,index,image,Fin.cases (ρ.bound 4).property (Fin.cases hn
    (Fin.cases (ρ.bound 3).property (Fin.cases (ρ.bound 20).property (Fin.cases y.property (fun i => Fin.elim0 i))))),?_⟩
  exact (tg_event_sat_l (kp_pair_l hN) hN.1 _ (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)).mpr event

end YesMetaZFC.SetTheory.LargeCardinal
