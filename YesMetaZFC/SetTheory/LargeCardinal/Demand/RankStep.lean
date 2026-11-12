import YesMetaZFC.SetTheory.LargeCardinal.Demand.Setup
import YesMetaZFC.SetTheory.LargeCardinal.Demand.HistoryConstruction
import YesMetaZFC.SetTheory.LargeCardinal.Game.CatalogRead
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ControlRecord
import YesMetaZFC.Model.SetTheory.Relations.CollectCode

/-! # 合法 demanding 请求的实际 24 槽载荷

载荷保存原辅助走法的 E 表行，并由同一 P 表取出源前缀程序。
B、U、E 始终来自弹性行；查询表的双池不被混入这些坐标。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

-- ℓ,k,κ,u,d,q,n,m,B,U,E,g₀,g₁,g₂,g₃,b,z,σ₀,…,σ₆。
def Td_issue_payload_d (I : kpair_convention_l.Interpretation M)
    (ω δ E P a : M.Domain) (v : Fin 24 → M.Domain) : Prop :=
  Td_move_d a (v 0) (v 1) (v 2) (v 3) ∧ M.mem (v 1) ω ∧ M.mem (v 2) δ ∧
  Td_arity_d I (v 1) (v 4) (v 5) (v 6) (v 7) ∧
  M.mem (v 4) ω ∧ M.mem (v 5) ω ∧ M.mem (v 6) ω ∧ M.mem (v 7) ω ∧ M.IsLimitOrdinal (v 2) ∧
  Tg_ee_data_d E (v 2) (v 5) (v 8) (v 9) (v 10) ⟨v 11,v 12,v 13,v 14⟩ ∧
  Tg_program_data_d P (v 5) (v 15) (v 16)
    (Fin.cases (v 17) (Fin.cases (v 18) (Fin.cases (v 19) (Fin.cases (v 20)
      (Fin.cases (v 21) (Fin.cases (v 22) (fun _ => v 23)))))))

def td_issue_payload_m {d} (ω δ E P a : Term d) (v : Fin 24 → Term d) : Formula 1 d := set[d] ⟪
  ⌜td_move_m⌝ₚ(⌜a⌝ₛ,⌜v 0⌝ₛ,⌜v 1⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ) ∧ ⌜v 1⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜v 2⌝ₛ ∈ ⌜δ⌝ₛ ∧
  ⌜td_arity_m⌝ₚ(⌜v 1⌝ₛ,⌜v 4⌝ₛ,⌜v 5⌝ₛ,⌜v 6⌝ₛ,⌜v 7⌝ₛ) ∧
  ⌜v 4⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜v 5⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜v 6⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜v 7⌝ₛ ∈ ⌜ω⌝ₛ ∧
  ⌜Formula.isLimitOrdinal⌝ₚ(⌜v 2⌝ₛ) ∧
  ⌜tg_ee_data_m⌝ₚ(⌜E⌝ₛ,⌜v 2⌝ₛ,⌜v 5⌝ₛ,⌜v 8⌝ₛ,⌜v 9⌝ₛ,⌜v 10⌝ₛ,⌜v 11⌝ₛ,⌜v 12⌝ₛ,⌜v 13⌝ₛ,⌜v 14⌝ₛ) ∧
  ⌜fun P q b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P q b z
    (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜P⌝ₛ,⌜v 5⌝ₛ,⌜v 15⌝ₛ,⌜v 16⌝ₛ,⌜v 17⌝ₛ,⌜v 18⌝ₛ,⌜v 19⌝ₛ,⌜v 20⌝ₛ,⌜v 21⌝ₛ,⌜v 22⌝ₛ,⌜v 23⌝ₛ)⟫

@[simp] theorem td_issue_payload_closed_l {d} (ω δ E P a : Term d) (v : Fin 24 → Term d)
    (hw : ω.freeSupport = []) (hd : δ.freeSupport = []) (hE : E.freeSupport = [])
    (hP : P.freeSupport = []) (ha : a.freeSupport = []) (hv : ∀ i, (v i).freeSupport = []) :
    (td_issue_payload_m ω δ E P a v).FreeClosed := by
  simp -implicitDefEqProofs [td_issue_payload_m,Definitional.Formula.FreeClosed,hw,hd,hE,hP,ha,hv,
    Fin.forall_fin_succ]

theorem td_issue_payload_sat_l (I : kpair_convention_l.Interpretation M) (ext : Extensional M)
    {d} (ρ : Env M d) (ω δ E P a : Term d) (v : Fin 24 → Term d) :
    Formula.satisfies ρ (td_issue_payload_m ω δ E P a v) ↔
      Td_issue_payload_d I (ω.eval ρ) (δ.eval ρ) (E.eval ρ) (P.eval ρ) (a.eval ρ)
        (fun i => (v i).eval ρ) := by
  simp only [td_issue_payload_m,Td_issue_payload_d,Formula.satisfies_conj_iff,
    td_move_sat_l ext,Formula.satisfies_mem_iff,td_arity_sat_l I ext,
    Formula.satisfies_isLimitOrdinal_iff,tg_ee_data_sat_l ext,tg_program_data_sat_l ext,
    tt_eval_cases_l]

/-- 同一原辅助走法给出弹性行，实际有限 q 在原程序表中取出全部七槽。 -/
theorem Td_setup_d.issue_payload_l (hZFC : M.Models ZFC) {p : Tg_params_d M.Domain}
    {X n h a : M.Domain} (setup : Td_setup_d hZFC p X)
    (aux : Td_aux_d (ZFC.models_zf_l hZFC) p n h a) :
    ∃ v : Fin 24 → M.Domain, Td_issue_payload_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC)))
      p.ω p.δ p.E p.P a v := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨ℓ,k,κ,u,d,q,N,m,_,_,_,_,_,_,_,_,_,_,_,B,U,E,g₀,g₁,g₂,g₃,
    move,hk,hκ,arity,_,_,request,_,_,data,_⟩ := aux
  obtain ⟨d₀,q₀,N₀,m₀,arity₀,hd,hq,hN,hm⟩ := td_arity_exists_l hZF setup.omega hk
  obtain ⟨ed,eq,en,em⟩ := arity₀.unique_l hZF arity
  subst d₀ q₀ N₀ m₀
  obtain ⟨H,_,table,_⟩ := setup.programs
  obtain ⟨b,z,σ,_,program,_⟩ := table.get_l hZFC hq
  have eq : Fin.cases (σ 0) (Fin.cases (σ 1) (Fin.cases (σ 2) (Fin.cases (σ 3)
      (Fin.cases (σ 4) (Fin.cases (σ 5) (fun _ => σ 6)))))) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  let v : Fin 24 → M.Domain := fun i =>
    [ℓ,k,κ,u,d,q,N,m,B,U,E,g₀,g₁,g₂,g₃,b,z,σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6].get i
  exact ⟨v,move,hk,hκ,arity,hd,hq,hN,hm,request.1,data,eq.symm ▸ program⟩

def td_issue_result_m {d} (ω δ E P a : Term d) : Formula 1 d :=
  let lift (t : Term d) : Term (d+24) := t.rename (fun i => ⟨24+i.val,by omega⟩)
  rt_exists_m 24 (td_issue_payload_m (lift ω) (lift δ) (lift E) (lift P) (lift a)
    (fun i => .bound ⟨i.val,by omega⟩))

@[simp] theorem td_issue_result_closed_l {d} (ω δ E P a : Term d)
    (hw : ω.freeSupport = []) (hd : δ.freeSupport = []) (hE : E.freeSupport = [])
    (hP : P.freeSupport = []) (ha : a.freeSupport = []) :
    (td_issue_result_m ω δ E P a).FreeClosed := by
  apply (rt_exists_closed_l _).mpr
  apply td_issue_payload_closed_l
  · simpa only [Definitional.Term.freeSupport_rename] using hw
  · simpa only [Definitional.Term.freeSupport_rename] using hd
  · simpa only [Definitional.Term.freeSupport_rename] using hE
  · simpa only [Definitional.Term.freeSupport_rename] using hP
  · simpa only [Definitional.Term.freeSupport_rename] using ha
  · exact fun _ => rfl

theorem td_issue_result_sat_l (I : kpair_convention_l.Interpretation M) (ext : Extensional M)
    {d} (ρ : Env M d) (ω δ E P a : Term d) :
    Formula.satisfies ρ (td_issue_result_m ω δ E P a) ↔
      ∃ v, Td_issue_payload_d I (ω.eval ρ) (δ.eval ρ) (E.eval ρ) (P.eval ρ) (a.eval ρ) v := by
  rw [td_issue_result_m,rt_exists_sat_l]
  apply exists_congr
  intro v
  rw [td_issue_payload_sat_l I ext]
  have old (t : Term d) :
      (t.rename (fun i => (⟨24+i.val,by omega⟩ : Fin (d+24)))).eval (rt_push_d ρ 24 v) = t.eval ρ := by
    rw [Definitional.Term.eval_rename]
    cases t with
    | bound i => exact rt_push_old_l ρ v i
    | free i => exact congrFun (rt_push_free_l ρ v) i
  have new : (fun i : Fin 24 => (Term.bound (⟨i.val,by omega⟩ : Fin (d+24))).eval (rt_push_d ρ 24 v)) = v :=
    funext (rt_push_new_l ρ v)
  rw [old ω,old δ,old E,old P,old a,new]

def td_issue_control_m {d} (p : Tg_params_d (Term d)) : Formula 1 d :=
  let q := p.map_l (fun t => t.weaken.weaken.weaken)
  set[d] ⟪∀ n h a, ⌜fun n h a => td_aux_m q n h a⌝ₚ(n,h,a) →
    ⌜td_issue_result_m⌝ₚ(⌜p.ω⌝ₛ,⌜p.δ⌝ₛ,⌜p.E⌝ₛ,⌜p.P⌝ₛ,a)⟫

@[simp] theorem td_issue_control_closed_l {d} (p : Tg_params_d (Term d)) (hp : p.closed_l) :
    (td_issue_control_m p).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l,Tg_params_d.map_l,Definitional.Term.freeSupport_weaken] using hp
  have aux := td_aux_closed_l _ (.bound 2) (.bound 1) (.bound 0) hp' rfl rfl rfl
  rcases hp with ⟨hw,_,_,_,_,hd,_,_,_,hE,hP,_⟩
  simp -implicitDefEqProofs [td_issue_control_m,Definitional.Formula.FreeClosed,hw,hd,hE,hP]
  exact aux

theorem Td_setup_d.issue_control_l (hZFC : M.Models ZFC) {d} (ρ : Env M d)
    (p : Tg_params_d (Term d)) {X : M.Domain}
    (setup : Td_setup_d hZFC (p.map_l (fun t => t.eval ρ)) X) :
    Formula.satisfies ρ (td_issue_control_m p) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [td_issue_control_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    td_aux_sat_l hZF,td_issue_result_sat_l I hZF.1,Tg_params_d.map_l,Definitional.Term.eval_weaken]
  intro n h a aux
  exact setup.issue_payload_l hZFC aux

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 已落下的原 demanding 请求及其真实程序载荷

前十九槽是同一控制记录，其后三槽为轮号、历史、原走法；再接二十四槽
实际 payload，末槽为当前时刻。原前缀及全部 Td_aux 规则一起保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def td_issued_payload_d {α : Type u} (v : Fin 47 → α) : Fin 24 → α :=
  fun i => v ⟨22+i.val,by omega⟩

def td_issued_aux0_m : Formula 1 47 := .existsE (.conj
  (fseq_end_m (𝒞 := kpair_convention_l) (.bound 1) (.bound 21) .newest (.bound 22))
  (td_aux_m (tg_control_params_d (fun i => (.bound (i.castAdd 28).succ : Term 48)))
    (.bound 20) .newest (.bound 22)))

theorem td_issued_aux0_closed_l : td_issued_aux0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_issued_aux0_m,Definitional.Formula.FreeClosed,tg_control_params_d]
  exact td_aux_closed_l _ _ _ _ ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ rfl rfl rfl

structure Td_issued_d (I : kpair_convention_l.Interpretation M) (v : Fin 47 → M.Domain) : Prop where
  control : Formula.satisfies (⟨fun i => v (i.castAdd 28),fun _ => v 0⟩ : Env M 19) td_control0_m
  round : M.mem (v 19) (v 0)
  time : M.mem (v 46) (v 0)
  history : Fn0_d (v 46) (v 12) (v 20)
  position : M.mem (v 20) (v 18)
  clock : M.IsOrdinalDivision I (v 46) (v 4) (v 19) (v 2)
  event : Tg_event_d I (v 4) (v 19) (v 1) (v 20) (v 21)
  payload : Td_issue_payload_d I (v 0) (v 5) (v 9) (v 10) (v 21) (td_issued_payload_d v)
  auxiliary : Formula.satisfies (⟨v,fun _ => v 0⟩ : Env M 47) td_issued_aux0_m

def td_issued0_m : Formula 1 47 := .conj
  (td_control0_m.rename (fun i => i.castAdd 28))
  (.conj (let v : Fin 47 → Term 47 := Term.bound
    set[47] ⟪⌜v 19⌝ₛ ∈ ⌜v 0⌝ₛ ∧ ⌜v 46⌝ₛ ∈ ⌜v 0⌝ₛ ∧ ⌜fn0_m⌝ₚ(⌜v 46⌝ₛ,⌜v 12⌝ₛ,⌜v 20⌝ₛ) ∧
      ⌜v 20⌝ₛ ∈ ⌜v 18⌝ₛ ∧ ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(⌜v 46⌝ₛ,⌜v 4⌝ₛ,⌜v 19⌝ₛ,⌜v 2⌝ₛ) ∧
      ⌜tg_event_m⌝ₚ(⌜v 4⌝ₛ,⌜v 19⌝ₛ,⌜v 1⌝ₛ,⌜v 20⌝ₛ,⌜v 21⌝ₛ)⟫)
    (.conj (td_issue_payload_m (.bound 0) (.bound 5) (.bound 9) (.bound 10) (.bound 21)
      (td_issued_payload_d Term.bound)) td_issued_aux0_m))

theorem td_issued0_closed_l : td_issued0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_issued0_m,Definitional.Formula.FreeClosed,
    td_control0_closed_l,td_issued_aux0_closed_l,td_issued_payload_d]

theorem td_issued_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) (ρ : Env M 47) :
    Formula.satisfies ρ td_issued0_m ↔ Td_issued_d I ρ.bound := by
  simp only [td_issued0_m,Formula.satisfies_conj_iff,Formula.satisfies_rename,Formula.satisfies_mem_iff,
    fn0_sat_l hE,Formula.satisfies_isOrdinalDivision_iff I hE,tg_event_sat_l I hE,
    td_issue_payload_sat_l I hE]
  have head := Formula.closed_env_l td_control0_m td_control0_closed_l
    (ρ := ρ.reindex (fun i => i.castAdd 28))
    (η := ⟨fun i => ρ.bound (i.castAdd 28),fun _ => ρ.bound 0⟩) rfl
  have aux := Formula.closed_env_l td_issued_aux0_m td_issued_aux0_closed_l
    (ρ := ρ) (η := ⟨ρ.bound,fun _ => ρ.bound 0⟩) rfl
  exact ⟨fun ⟨a,⟨b,c,d,e,f,g⟩,h,i⟩ => ⟨head.mp a,b,c,d,e,f,g,h,aux.mp i⟩,
    fun h => ⟨head.mpr h.control,⟨h.round,h.time,h.history,h.position,h.clock,h.event⟩,h.payload,aux.mpr h.auxiliary⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 47 槽 issued 句的语义读取接口。读者只消费实际外延性与给定解释。 -/
theorem td_issued_read_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (ρ : Env M 47) (h : Formula.satisfies ρ td_issued0_m) : Td_issued_d I ρ.bound :=
  (td_issued_sat_l I hE ρ).mp h

/-- 47 槽 issued 句的语义生产接口；不构造额外见证，直接回写已有记录。 -/
theorem td_issued_produce_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    (ρ : Env M 47) (h : Td_issued_d I ρ.bound) : Formula.satisfies ρ td_issued0_m :=
  (td_issued_sat_l I hE ρ).mpr h

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 合法有限历史中旧回答的回读

先限制到回答时刻，再追加历史中同一项；所得前缀的合法性给出原
Td_answer。高度码从当时的实际 Q 行读取，不把旧模型的查询语义作为
当前模型中的假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_rules_d.answer_at_l {p : Tg_params_d M.Domain} {X F L G J h i n v : M.Domain}
    (rules : Td_rules_d hZF p X F L J) (space : Fseq_space_d I p.ω X F)
    (legal : Cg_legal_d (M := M) F L G) (hh : M.mem h G)
    (hi : M.mem i p.ω) (fn : Fn0_d i X h) (hn : M.mem n p.ω)
    (event : Tg_event_d I p.c n p.a h v) :
    ∃ s, M.MemberSubset s h ∧ Td_answer_d hZF p n s v := by
  obtain ⟨j,div,value⟩ := event
  have hKP := ZF.modelsKP hZF
  have fj := (fn.bound_l value).1
  have hj := rules.omega.transitive hKP i hi j fj
  obtain ⟨s,cut⟩ := ZF.exists_restriction hZF I h j
  have fs := cut.isSetFunctionFromTo (fn0_function_l hKP fn)
    ((rules.omega.members_areOrdinals hKP i hi).transitive j fj)
  have sub := (ds_restrict_iff_l I fs (fn0_function_l hKP fn).1).mp cut
  obtain ⟨k,t,hk,ft,endt⟩ := ZF.fseq_end_exists_l I hZF rules.omega hj fs (fn.bound_l value).2
  have th := ds_append_sub_l I hZF.1 fs endt sub value
  have check := ((rules.checks t).mp
    (((legal h).mp hh).2 t ((space t).mpr ⟨k,hk,ft⟩) th)).2
  obtain ⟨hc,_⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three hi
  have step := (td_step_read_l hZF (rules.omega.members_areOrdinals hKP j hj)
    (rules.omega.members_areOrdinals hKP p.c hc) ⟨p.b,rules.three.predecessor_mem⟩ hn div).mp
      (check.end_l hZF (fn0_of_function_l hKP fs) endt)
  have ae : p.a ≠ p.e := fun eq => rules.empty p.e (eq ▸ rules.one.predecessor_mem)
  have ab : p.a ≠ p.b := fun eq => KP.mem_irrefl_d hKP p.a (eq.symm ▸ rules.two.predecessor_mem)
  exact ⟨s,sub,step.elim (fun h => (ae h.1).elim)
    (fun h => h.elim And.right (fun h => (ab h.1).elim))⟩

/-- 旧回答事件及原表行共同给出高度码；输入只需原 issued 和被读取事件。 -/
theorem td_issued_height_l (ι : Env M 47) (issued : Formula.satisfies ι td_issued0_m)
    {a b ℓ j κ u τ w d q n m B U D : M.Domain}
    (request : Tg_event_d I (ι.bound 4) (ι.bound 22) (ι.bound 1) (ι.bound 20) a)
    (move : Td_move_d a ℓ j κ u)
    (answer : Tg_event_d I (ι.bound 4) (ι.bound 22) (ι.bound 2) (ι.bound 20) b)
    (pair : KPair_d M b τ w) (arity : Td_arity_d I j d q n m)
    (earlier : M.mem (ι.bound 22) (ι.bound 19))
    (rank : V_d I τ B) (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = τ)
    (pool : Tt_pool_d I (ι.bound 0) m U D) :
    ∃ ph, Tg_height_query_d I (ι.bound 0) n m U D ph ∧ M.mem ph w := by
  have hKP := ZF.modelsKP hZF
  have state := (td_issued_sat_l I hZF.1 ι).mp issued
  have control := state.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at control
  let p := tg_control_params_d (fun i => ι.bound (i.castAdd 28))
  have rules : Td_rules_d hZF p (ι.bound 12) (ι.bound 13) (ι.bound 14) (ι.bound 16) :=
    (td_rules_sat_l hZF ..).mp control.2.2.1
  have position := (cg_control_sat_l I hZF.1 false ..).mp control.2.1
  obtain ⟨h,sub,valid⟩ := rules.answer_at_l hZF position.space position.legal
    ((position.positions _).mp state.position).1 state.time state.history
      (rules.omega.transitive hKP _ state.round _ earlier) answer
  obtain ⟨a',ℓ',j',κ',u',τ',w',d',q',n',m',_,_,_,_,_,_,_,C,V,Du,Dw,pn,pm,pp,pb,ph,
    _,_,_,_,_,_,_,_,_,request',move',pair',arity',_,hτ,queryRequest,queryRow,_,reply⟩ := valid
  obtain ⟨hc,_⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three state.time
  have request' : Tg_event_d I (ι.bound 4) (ι.bound 22) (ι.bound 1) (ι.bound 20) a' := by
    obtain ⟨i,div,p,pair,hp⟩ := request'
    exact ⟨i,div,p,pair,sub p hp⟩
  have eq := request'.unique_l hZF (rules.omega.members_areOrdinals hKP _ hc)
    (fn0_function_l hKP state.history).1 request
  subst a'
  obtain ⟨eℓ,ej,eκ,eu⟩ := move'.unique_l move
  subst ℓ' j' κ' u'
  obtain ⟨eτ,ew⟩ := kpair_injective_l M pair' pair
  subst τ' w'
  obtain ⟨ed,eq,en,em⟩ := arity'.unique_l hZF arity
  subst d' q' n' m'
  have tables := control.1
  simp only [td_tables_m,Formula.satisfies_conj_iff] at tables
  have read := tables.1.2.2.2
  simp only [Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    tg_query_request_sat_l hZF,td_query_data_sat_l hZF.1] at read
  have row := read τ hτ j (ι.bound 1) C V Du Dw pn pm pp pb ph queryRequest queryRow
  simp only [Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,td_arity_sat_l I hZF.1,
    v_sat_l I hZF.1,tt_constants0_sat_l hZF.1,tt_pool_sat_l I hKP,
    tg_height_query_sat_l I hKP] at row
  obtain ⟨d',q',n',m',arity',base,constants',_,pool',_,_,_,_,height,_⟩ := row
  change Td_arity_d I j d' q' n' m' at arity'
  obtain ⟨ed,eq,en,em⟩ := arity'.unique_l hZF arity
  subst d' q' n' m'
  have eB : C = B := ZF.v_unique_l I hZF base rank
  subst C
  have eU := hZF.1.eq_of_same_members V U (fun x => (constants' x).trans (constants x).symm)
  subst V
  have eD : Dw = D := pool'.unique_l hZF.1 I pool
  subst Dw
  obtain ⟨_,_,_,_,_,_,member⟩ := reply
  exact ⟨ph,height,member⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原控制实际产生完整请求

任意合法辅助末步读取自身 E 行及固定 P 表，组装全部四十七槽。
首轮和后续轮使用同一构造；首轮的重置性来自零轮没有历史可回指。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_control_issue_l (ρ : Env M 19) (control : Formula.satisfies ρ td_control0_m)
    {n h a j t : M.Domain}
    (hn : M.mem n (ρ.bound 0)) (hj : M.mem j (ρ.bound 0))
    (fn : Fn0_d j (ρ.bound 12) h) (position : M.mem h (ρ.bound 18))
    (clock : M.IsOrdinalDivision I j (ρ.bound 4) n (ρ.bound 2))
    (event : Tg_event_d I (ρ.bound 4) n (ρ.bound 1) h a)
    (ending : Fseq_end_d I (ρ.bound 0) h t a)
    (aux : Td_aux_d hZF (tg_control_params_d ρ.bound) n t a) :
    ∃ ψ : Env M 47,
      (∀ i : Fin 19, ψ.bound (i.castAdd 28) = ρ.bound i) ∧
      ψ.bound 19 = n ∧ ψ.bound 20 = h ∧ ψ.bound 21 = a ∧ ψ.bound 46 = j ∧
      Formula.satisfies ψ td_issued0_m := by
  have data := control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at data
  have rules := (td_rules_sat_l hZF ..).mp data.2.2.1
  have parsed := aux
  obtain ⟨ℓ,k,κ,u,d,q,N,m,_,_,_,_,_,_,_,_,_,_,_,B,U,E,g₀,g₁,g₂,g₃,
    move,hk,hκ,arity,_,_,request,_,_,ee,_⟩ := parsed
  obtain ⟨d',q',N',m',arity',hd,hq,hN,hm⟩ := td_arity_exists_l hZF rules.omega hk
  obtain ⟨rfl,rfl,rfl,rfl⟩ := arity'.unique_l hZF arity
  have tables := data.1
  simp only [td_tables_m,Formula.satisfies_conj_iff] at tables
  have programs := tables.1.2.2.1
  simp only [Formula.satisfies_forallMem_iff,Formula.satisfies_exists_iff,
    tg_program_data_sat_l hZF.1,tt_eval_cases_l,Definitional.Term.eval_weaken] at programs
  obtain ⟨b,z,s₀,s₁,s₂,s₃,s₄,s₅,s₆,program⟩ := programs q' hq
  let ψ : Env M 47 := ⟨fun i =>
    [ρ.bound 0,ρ.bound 1,ρ.bound 2,ρ.bound 3,ρ.bound 4,ρ.bound 5,ρ.bound 6,
      ρ.bound 7,ρ.bound 8,ρ.bound 9,ρ.bound 10,ρ.bound 11,ρ.bound 12,ρ.bound 13,
      ρ.bound 14,ρ.bound 15,ρ.bound 16,ρ.bound 17,ρ.bound 18,n,h,a,
      ℓ,k,κ,u,d',q',N',m',B,U,E,g₀,g₁,g₂,g₃,b,z,s₀,s₁,s₂,s₃,s₄,s₅,s₆,j].get i,ρ.free⟩
  have head : ∀ i : Fin 19, ψ.bound (i.castAdd 28) = ρ.bound i := by
    intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))))))))))))))) i
  refine ⟨ψ,head,rfl,rfl,rfl,rfl,(td_issued_sat_l I hZF.1 ψ).mpr
    ⟨?_,hn,hj,fn,position,clock,event,⟨move,hk,hκ,arity,hd,hq,hN,hm,request.1,ee,program⟩,?_⟩⟩
  · exact (Formula.closed_env_l td_control0_m td_control0_closed_l (funext head)).mpr control
  · simp only [td_issued_aux0_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      fseq_end_sat_l I hZF.1,td_aux_sat_l hZF]
    exact ⟨t,ending,aux⟩

/-- 同一控制的首个实际策略值给出零轮完整请求。 -/
theorem td_issued_start_l (ρ : Env M 19) (control : Formula.satisfies ρ td_control0_m) :
    ∃ ψ : Env M 47,
      (∀ i : Fin 19, ψ.bound (i.castAdd 28) = ρ.bound i) ∧
      Formula.satisfies ψ td_issued0_m ∧ ψ.bound 19 = ρ.bound 1 ∧
      ψ.bound 23 = ρ.bound 1 ∧
      Rd_entry_d (ρ.bound 1) (ψ.bound 21) (ρ.bound 17) ∧
      Fseq_end_d I (ρ.bound 0) (ψ.bound 20) (ρ.bound 1) (ψ.bound 21) := by
  have data := control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at data
  have rules := (td_rules_sat_l hZF ..).mp data.2.2.1
  have strategy := (cg_control_sat_l I hZF.1 false ..).mp data.2.1
  obtain ⟨a,h,j,_,value,ending,hj,_,fn,position,clock,aux,event,ℓ,κ,u,move⟩ :=
    rules.start_l hZF strategy
  have hn := num_mem_l hZF.1 rules.omega (show Num_d 0 (ρ.bound 1) from rules.empty)
  obtain ⟨ψ,head,round,history,played,time,valid⟩ :=
    td_control_issue_l hZF ρ control hn hj fn position clock event ending aux
  have payload := (td_issued_sat_l I hZF.1 ψ).mp valid |>.payload
  have parsed : Td_move_d a (ψ.bound 22) (ψ.bound 23) (ψ.bound 24) (ψ.bound 25) :=
    played ▸ payload.1
  have reset := (parsed.unique_l move).2.1
  exact ⟨ψ,head,valid,round,reset,played.symm ▸ value,history.symm ▸ played.symm ▸ ending⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 合法回答之后的实数落子及下一完整请求

偶数轮使用给定字母，奇数轮读取原策略。随后同一策略给出辅助走法，
其载荷由原 E 行和原 P 表总性构造；域增长从实际前轮事件读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原控制把实际合法回答追加到历史；此步不涉及辅助字母的枚举。 -/
theorem td_issued_answer_history_l (ι : Env M 47) (issued : Formula.satisfies ι td_issued0_m)
    (b : M.Domain)
    (answer : Formula.satisfies
      (⟨fun k => [ι.bound 0,ι.bound 1,ι.bound 2,ι.bound 3,ι.bound 4,ι.bound 5,
        ι.bound 6,ι.bound 7,ι.bound 8,ι.bound 9,ι.bound 10,ι.bound 11,
        ι.bound 19,ι.bound 20,b].get k,ι.free⟩ : Env M 15) td_answer0_m) :
    ∃ h j, Fseq_end_d I (ι.bound 0) h (ι.bound 20) b ∧
      M.mem j (ι.bound 0) ∧ M.SuccessorOf j (ι.bound 46) ∧
      Fn0_d j (ι.bound 12) h ∧ M.mem h (ι.bound 18) ∧
      M.IsOrdinalDivision I j (ι.bound 4) (ι.bound 19) (ι.bound 3) ∧
      Tg_event_d I (ι.bound 4) (ι.bound 19) (ι.bound 2) h b := by
  have data := (td_issued_sat_l I hZF.1 ι).mp issued
  have control := data.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at control
  have advance := control.2.2.2.2.2.1
  simp only [td_answer_control_m,Formula.satisfies_forallMem_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff,fn0_sat_l hZF.1,Formula.satisfies_isOrdinalDivision_iff I hZF.1,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,fseq_end_sat_l I hZF.1,
    Formula.satisfies_mem_iff,Formula.satisfies_isSuccessor_iff,tg_event_sat_l I hZF.1,
    Definitional.Term.eval_weaken,td_answer_m,Formula.satisfies_bind] at advance
  exact advance (ι.bound 46) data.time (ι.bound 19) data.round (ι.bound 20) data.position b
    data.history data.clock ((Formula.closed_env_l td_answer0_m td_answer0_closed_l (by
      funext k
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
            (Fin.cases rfl (fun k => Fin.elim0 k))))))))))))))) k)).mp answer)

theorem td_issued_next_l (ι : Env M 47) (issued : Formula.satisfies ι td_issued0_m)
    {b h j x : M.Domain}
    (answer : Fseq_end_d I (ι.bound 0) h (ι.bound 20) b)
    (hj : M.mem j (ι.bound 0)) (fn : Fn0_d j (ι.bound 12) h) (position : M.mem h (ι.bound 18))
    (clock : M.IsOrdinalDivision I j (ι.bound 4) (ι.bound 19) (ι.bound 3))
    (input : M.mem x (ι.bound 6)) :
    ∃ y t, ∃ ψ : Env M 47,
      M.mem y (ι.bound 6) ∧
      (Gm_even_d I (ι.bound 0) (ι.bound 19) → y = x) ∧
      (¬ Gm_even_d I (ι.bound 0) (ι.bound 19) → Rd_entry_d h y (ι.bound 17)) ∧
      Fseq_end_d I (ι.bound 0) t h y ∧
      Fseq_end_d I (ι.bound 0) (ψ.bound 20) t (ψ.bound 21) ∧
      Rd_entry_d t (ψ.bound 21) (ι.bound 17) ∧
      (∀ i : Fin 19, ψ.bound (i.castAdd 28) = ι.bound (i.castAdd 28)) ∧
      M.SuccessorOf (ψ.bound 19) (ι.bound 19) ∧ Formula.satisfies ψ td_issued0_m ∧
      M.mem (ι.bound 24) (ψ.bound 24) ∧ M.MemberSubset h (ψ.bound 20) := by
  have hKP := ZF.modelsKP hZF
  have state := (td_issued_sat_l I hZF.1 ι).mp issued
  have control := state.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at control
  let p := tg_control_params_d (fun i => ι.bound (i.castAdd 28))
  have rules : Td_rules_d hZF p (ι.bound 12) (ι.bound 13) (ι.bound 14) (ι.bound 16) :=
    (td_rules_sat_l hZF ..).mp control.2.2.1
  have strategy := (cg_control_sat_l I hZF.1 false ..).mp control.2.1
  have geometry := control.2.2.2.2.2.2.2.2.2
  simp only [td_geometry_m,Formula.satisfies_conj_iff,v_sat_l I hZF.1,
    Formula.satisfies_mem_iff] at geometry
  have letters : M.MemberSubset p.A (ι.bound 12) :=
    (v_transitive_l I geometry.2.1) p.A geometry.2.2.1
  have choose : ∃ y, M.mem y p.A ∧
      (Gm_even_d I p.ω (ι.bound 19) → y = x) ∧
      (¬ Gm_even_d I p.ω (ι.bound 19) → Rd_entry_d h y (ι.bound 17)) ∧
      Tg_digit_end_d hZF p (ι.bound 12) (ι.bound 18) j (ι.bound 19) h y := by
    by_cases even : Gm_even_d I p.ω (ι.bound 19)
    · exact ⟨x,input,fun _ => rfl,fun no => (no even).elim,
        rules.digit_l hZF strategy hj state.round position fn clock even input letters⟩
    · obtain ⟨y,hy,value,ending⟩ :=
        rules.digit_strategy_l hZF strategy hj state.round position fn clock even
      exact ⟨y,hy,fun yes => (even yes).elim,fun _ => value,ending⟩
  obtain ⟨y,hy,even,odd,t,j₁,n,et,hj₁,hn,sj₁,sn,ft,ht,clock₁,digit⟩ := choose
  obtain ⟨a,h',j₂,_,value,eh,hj₂,_,fh,hh,clock₂,aux,event⟩ :=
    rules.aux_l hZF strategy hj₁ hn ht ft clock₁
  obtain ⟨ψ,head,round,history,played,_,valid⟩ := td_control_issue_l hZF
    ⟨fun i => ι.bound (i.castAdd 28),fun _ => ι.bound 0⟩ state.control
      hn hj₂ fh hh clock₂ event eh aux
  obtain ⟨ℓ,k,κ,u,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,
    move,_,_,_,_,_,_,_,_,_,_,_,growth,_⟩ := aux
  have next := (td_issued_sat_l I hZF.1 ψ).mp valid
  have parsed : Td_move_d a (ψ.bound 22) (ψ.bound 23) (ψ.bound 24) (ψ.bound 25) :=
    played ▸ next.payload.1
  have eqκ := (move.unique_l parsed).2.2.1
  have increase : M.mem (ι.bound 24) (ψ.bound 24) := by
    rw [← eqκ]
    rcases growth with ⟨zero,_⟩ | ⟨n₀,a₀,ℓ₀,k₀,κ₀,u₀,sn₀,event₀,move₀,above⟩
    · exact (rules.empty (ι.bound 19) (zero ▸ sn.predecessor_mem)).elim
    · have ordinal := rules.omega.members_areOrdinals hKP (ι.bound 19) state.round
      have eq := sn.predecessor_eq hZF.1 ordinal sn₀
      subst n₀
      obtain ⟨hc,_⟩ := tg_clock_l hZF rules.omega rules.empty rules.one rules.two rules.three state.time
      have clockOrdinal := rules.omega.members_areOrdinals hKP p.c hc
      have oldEvent := (state.event.end_l answer).end_l et
      have eq := event₀.unique_l hZF clockOrdinal (fn0_function_l hKP ft).1 oldEvent
      subst a₀
      obtain ⟨_,_,eq,_⟩ := move₀.unique_l state.payload.1
      exact (show κ₀ = ι.bound 24 from eq) ▸ above
  exact ⟨y,t,ψ,hy,even,odd,et,history.symm ▸ played.symm ▸ eh,played.symm ▸ value,
    head,round.symm ▸ sn,valid,increase,
    fun z hz => history.symm ▸ eh.subset_l I z (et.subset_l I z hz)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 实际偶数边上的尝试树秩下降

原 II 胜策的控制记录含有实际秩函数。每个完整回合将任意已选秩函数
沿同一原边运输，再由历史的严格延长得到新秩值小于旧秩值的像。
结论保留原秩函数的像，因此下一轮无需重选秩；不假定辅助域可数或节点良基。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u

/-- 起点确有秩；任意已选秩都沿同一边给出下降，供逐轮保留。 -/
structure Td_rank_step_d {N P : Structure.{u}}
    (j : N.Domain → P.Domain → Prop) (v : Fin 47 → N.Domain) (w : Fin 47 → P.Domain) : Prop where
  ranked : ∃ α F, Cg_rank_d (v 0) (v 12) (v 18) α F
  descent : ∀ α F, Cg_rank_d (v 0) (v 12) (v 18) α F →
    ∃ a : N.Domain, ∃ β G b d : P.Domain,
      Rd_entry_d (v 20) a F ∧ j α β ∧ j F G ∧ j a b ∧
      Cg_rank_d (w 0) (w 12) (w 18) β G ∧ Rd_entry_d (w 20) d G ∧ P.mem d b

variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 完整请求中的原控制直接提供尝试树的实际秩。 -/
theorem td_issued_rank_l (hKP : M.Models KP) (ι : Env M 47)
    (issued : Formula.satisfies ι td_issued0_m) :
    ∃ α F, Cg_rank_d (ι.bound 0) (ι.bound 12) (ι.bound 18) α F := by
  have data := (td_issued_sat_l (kp_pair_l hKP) hKP.1 ι).mp issued |>.control
  simp only [td_control0_m,Formula.satisfies_conj_iff] at data
  have rank := data.2.2.2.2.2.2.2.1
  simp only [cg_rank_m,Formula.satisfies_exists_iff] at rank
  obtain ⟨α,F,rank⟩ := rank
  exact ⟨α,F,(cg_rank0_sat_l hKP ..).mp rank⟩

/-- 只消费本回合已经构造的原边、回答历史及下一请求。 -/
theorem Smap_d.demand_rank_step_l
    {Ω c X R d Y S j : M.Domain} (hΩ : M.IsOmega Ω)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S) (map : Smap_d I Ω c d X Y j)
    (hN : (smdl_structure_l I (R := R) mx.2.1).Models KP)
    (hP : (smdl_structure_l I (R := S) my.2.1).Models KP)
    (ι : Env (smdl_structure_l I (R := R) mx.2.1) 47)
    (issued : Formula.satisfies ι td_issued0_m)
    (ι' ψ : Env (smdl_structure_l I (R := S) my.2.1) 47)
    (points : ∀ i, Rd_entry_d (ι.bound i).val (ι'.bound i).val j)
    (head : ∀ i : Fin 19, ψ.bound (i.castAdd 28) = ι'.bound (i.castAdd 28))
    (next : Formula.satisfies ψ td_issued0_m)
    {h b : (smdl_structure_l I (R := S) my.2.1).Domain}
    (ending : Fseq_end_d (kp_pair_l hP) (ι'.bound 0) h (ι'.bound 20) b)
    (history : (smdl_structure_l I (R := S) my.2.1).MemberSubset h (ψ.bound 20)) :
    Td_rank_step_d (N := smdl_structure_l I (R := R) mx.2.1)
      (P := smdl_structure_l I (R := S) my.2.1)
      (fun x y => Rd_entry_d x.val y.val j) ι.bound ψ.bound := by
  let N := smdl_structure_l I (R := R) mx.2.1
  let P := smdl_structure_l I (R := S) my.2.1
  have source := (td_issued_sat_l (kp_pair_l hN) hN.1 ι).mp issued
  have target := (td_issued_sat_l (kp_pair_l hP) hP.1 ψ).mp next
  -- 回答新增的末项不在旧历史中，而下一请求仍保留该项。
  have sub : P.MemberSubset (ι'.bound 20) (ψ.bound 20) :=
    fun x hx => history x (ending.subset_l (kp_pair_l hP) x hx)
  have ne : ι'.bound 20 ≠ ψ.bound 20 := by
    intro eq
    obtain ⟨n,m,last⟩ := ending
    obtain ⟨p,pair,hp⟩ := last.last_value
    have hp' : P.mem p (ι'.bound 20) := eq.symm ▸ history p hp
    have mm := (last.prefix_sequence.2.2.2 m).mpr ⟨b,p,pair,hp'⟩
    exact last.prefix_sequence.2.1.wellOrder.linear.irrefl m mm mm
  refine ⟨td_issued_rank_l hN ι issued,?_⟩
  intro α F rank
  obtain ⟨a,_,value⟩ := rank.function.2.1 (ι.bound 20) source.position
  obtain ⟨β,hβ,iα⟩ := map.1.1.2.2 α.val α.property
  obtain ⟨G,hG,iF⟩ := map.1.1.2.2 F.val F.property
  obtain ⟨b,hb,ia⟩ := map.1.1.2.2 a.val a.property
  let β' : P.Domain := ⟨β,hβ⟩
  let G' : P.Domain := ⟨G,hG⟩
  let b' : P.Domain := ⟨b,hb⟩
  let φ : Formula 1 7 := .conj
    (cg_rank0_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4))
    (rd_entry0_m (.bound 5) (.bound 6) (.bound 4))
  have closed : φ.FreeClosed := by simp -implicitDefEqProofs [φ,Definitional.Formula.FreeClosed]
  let ν : Env N 7 := ⟨fun i => [ι.bound 0,ι.bound 12,ι.bound 18,α,F,ι.bound 20,a].get i,fun _ => α⟩
  let η : Env P 7 := ⟨fun i => [ι'.bound 0,ι'.bound 12,ι'.bound 18,β',G',ι'.bound 20,b'].get i,fun _ => β'⟩
  -- 同一公式运输秩证书与旧历史的秩值，保证下降所比较的是原值的像。
  have valid : Formula.satisfies ν φ := (Formula.satisfies_conj_iff ..).mpr
    ⟨(cg_rank0_sat_l hN ..).mpr rank,(rd_entry0_sat_l hN.1 ..).mpr value⟩
  have images : ∀ i, Rd_entry_d (ν.bound i).val (η.bound i).val j :=
    Fin.cases (points 0) (Fin.cases (points 12) (Fin.cases (points 18)
      (Fin.cases iα (Fin.cases iF (Fin.cases (points 20) (Fin.cases ia (fun i => Fin.elim0 i)))))))
  have moved := (smap_source_l I hZF hΩ mx my map φ closed ν η images).mp valid
  obtain ⟨rank',value'⟩ := (Formula.satisfies_conj_iff ..).mp moved
  have rank' : Cg_rank_d (ι'.bound 0) (ι'.bound 12) (ι'.bound 18) β' G' :=
    (cg_rank0_sat_l hP ..).mp rank'
  have value' : Rd_entry_d (ι'.bound 20) b' G' := (rd_entry0_sat_l hP.1 ..).mp value'
  have h0 : ι'.bound 0 = ψ.bound 0 := (head 0).symm
  have h12 : ι'.bound 12 = ψ.bound 12 := (head 12).symm
  have h18 : ι'.bound 18 = ψ.bound 18 := (head 18).symm
  have rankNext : Cg_rank_d (ψ.bound 0) (ψ.bound 12) (ψ.bound 18) β' G' :=
    h0 ▸ h12 ▸ h18 ▸ rank'
  obtain ⟨d,_,last⟩ := rankNext.function.2.1 (ψ.bound 20) target.position
  exact ⟨a,β',G',b',d,value,iα,iF,ia,rankNext,last,
    rankNext.proper (ι'.bound 20) (ψ.bound 20) b' d value' last sub ne⟩

end YesMetaZFC.SetTheory.LargeCardinal
