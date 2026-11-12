import YesMetaZFC.SetTheory.LargeCardinal.Demand.Setup
import YesMetaZFC.SetTheory.LargeCardinal.Demand.HistoryConstruction
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RoundScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.CatalogRead
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative

/-! # 原零轮走法生产同一类型的 demanding 更新输入

重置规则直接给出原 u 的实现。零元数及开局两张表固定其语言、dcp 和
程序，完整树与已选字母给出空根，因而两张空图的节点和分组实际成立。
输入字母表 A 由本次原查询请求进入同一常量域，不另造新的重置类型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 重置输入保存原走法及两张开局表的逐字坐标；不只保存 seed 的真值。 -/
def Td_reset_seed_d (p : Tg_params_d M.Domain) (a ℓ κ u U₁ U₂ z χ : M.Domain)
    (v : Fin 43 → M.Domain) : Prop :=
  (∀ i : Fin 5, v (i.castAdd 38) = [p.ω,p.e,p.δ,p.S,p.ν].get i) ∧
  v 5 = κ ∧ v 6 = p.e ∧ v 7 = p.e ∧ v 8 = p.a ∧ v 9 = p.b ∧ v 19 = u ∧
  v 24 = χ ∧ v 25 = p.e ∧ v 26 = p.e ∧ v 27 = p.e ∧
  v 28 = U₁ ∧ v 29 = U₂ ∧ v 30 = z ∧ v 31 = p.A ∧
  Td_move_d a ℓ (v 6) (v 5) (v 19) ∧
  Tg_ee_data_d p.E (v 5) (v 8) (v 15) (v 16) (v 17) ⟨v 32,v 33,v 34,v 35⟩ ∧
  Tg_program_data_d p.P (v 8) (v 21) (v 23) (Fin.cases (v 36) (Fin.cases (v 37)
    (Fin.cases (v 38) (Fin.cases (v 39) (Fin.cases (v 40) (Fin.cases (v 41) (fun _ => v 42)))))))

theorem Td_setup_d.reset_input_l {p : Tg_params_d M.Domain} {X n h a ℓ κ u U₁ U₂ z χ : M.Domain}
    (setup : Td_setup_d hZFC p X) (woodin : Woodin_d I p.δ)
    (aux : Td_aux_d hZF p n h a) (data : Td_move_d a ℓ p.e κ u)
    (tree : Td_tree_d I p.ω p.A p.S) (alphabet : Td_alphabet_d p.S U₁ U₂)
    (chosen : M.mem z U₁) (hχ : M.mem χ p.δ) (separated : Td_separated_d p.S) :
    ∃ v : Fin 43 → M.Domain,
      Formula.satisfies (⟨v,fun _ => p.ω⟩ : Env M 43) td_seed0_m ∧
      Td_reset_seed_d p a ℓ κ u U₁ U₂ z χ v := by
  obtain ⟨ℓ₀,k,κ₀,u₀,d,q,N,m,x,s,B,U,Du,Dw,pn,pm,pp,pb,ph,C,V,E,g₀,g₁,g₂,g₃,
    parsed,_,hκ,arity,_,_,request,query,_,ee,elastic,_,_,branch⟩ := aux
  obtain ⟨el,ek,eκ,eu⟩ := parsed.unique_l data
  subst ℓ₀ k κ₀ u₀
  have zero : Td_arity_d I p.e p.e p.a p.b p.c :=
    ⟨(ZF.ordinalAddition_zero_iff hZF I setup.empty).mpr rfl,setup.one,setup.two,setup.three⟩
  obtain ⟨ed,eq,eN,em⟩ := arity.unique_l hZF zero
  subst d q N m
  obtain ⟨α,Y,c,R,r,height,rank,model,type,first,last⟩ :=
    branch.elim And.right (fun no => (no.1 rfl).elim)
  obtain ⟨_,_,_,_,_,base,constants,_⟩ := setup.queries.read_l hZFC hκ request query
  have haω := setup.omega.transitive (ZF.modelsKP hZF) p.b type.finite p.a setup.two.predecessor_mem
  have language := setup.elastic.elim fun _ table => table.read_l hZFC hκ haω request.1 ee
  have eB := ZF.v_unique_l I hZF base language.rank
  subst C
  have eU := hZF.1.eq_of_same_members V U (fun t => (language.constants t).trans (constants t).symm)
  subst V
  have letters : M.mem p.A U := by
    obtain ⟨B',U',rank',constants',_,member⟩ := request.2.2
    have eqB := ZF.v_unique_l I hZF rank' base
    subst B'
    have eqU := hZF.1.eq_of_same_members U' U (fun t => (constants' t).trans (constants t).symm)
    exact eqU ▸ member
  obtain ⟨v,drop,elastic⟩ := elastic
  obtain ⟨_,_,programs,_⟩ := setup.programs
  obtain ⟨b,z₀,σ,program,pdata,prog⟩ := programs.get_l hZFC haω
  obtain ⟨pending,cp⟩ := (I).total p.e z
  have root := (show Td_pending_d I p.ω p.A p.e p.S pending from
    ⟨tree,z,cp,(alphabet.1 z).mp chosen⟩).root_l hZF setup.omega setup.empty
  have groups : Td_groups_d I p.ω p.e p.a r p.e p.e := by
    constructor <;> intro t <;> refine iff_of_false (setup.empty t) ?_ <;>
      rintro ⟨i,hi,ne,_,_⟩ <;>
      exact ((setup.one i).mp hi).elim (setup.empty i) (fun eq => ne (hZF.1.eq_of_same_members i p.e eq))
  have node := (tg_node_empty_l I hZF.1 setup.empty).mpr root
  let v' : Fin 43 → M.Domain := fun i =>
    [p.ω,p.e,p.δ,p.S,p.ν,κ,p.e,p.e,p.a,p.b,α,Y,c,R,r,B,U,E,Du,u,v,b,program,z₀,χ,
      p.e,p.e,p.e,U₁,U₂,z,p.A,g₀,g₁,g₂,g₃,σ 0,σ 1,σ 2,σ 3,σ 4,σ 5,σ 6].get i
  have slots : (Fin.cases (σ 0) (Fin.cases (σ 1) (Fin.cases (σ 2) (Fin.cases (σ 3)
      (Fin.cases (σ 4) (Fin.cases (σ 5) (fun _ => σ 6))))))) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have valid : Formula.satisfies (⟨v',fun _ => p.ω⟩ : Env M 43) td_seed0_m := by
    simp only [td_seed0_m,td_seed_m,Formula.satisfies_conj_iff,Formula.satisfies_isOmega_iff,
      Formula.satisfies_isEmpty_iff,woodin_sat_l I hZF.1,tg_low_sat_l hZF,Formula.satisfies_mem_iff,
      Formula.satisfies_isOrdinalAddition_iff I hZF.1,Formula.satisfies_isSuccessor_iff,
      v_sat_l I hZF.1,smem_sat_l I,tt_realized_sat_l I (ZF.modelsKP hZF),ee_language_sat_l hZFC,
      td_dcp_sat_l I hZF.1,ee_elastic_sat_l,rd_entry0_sat_l hZF.1,td_groups_sat_l I hZF.1,
      tg_node_sat_l I hZF.1,td_tree_sat_l I hZF.1,td_alphabet_sat_l hZF.1,ts_program_sat_l hZF,
      td_separated_sat_l hZF.1,tt_eval_cases_l]
    exact ⟨setup.omega,setup.empty,woodin,setup.low,hκ,zero.1,setup.one,setup.two,height,
      rank,model,type,language,drop,elastic,first,last,groups,node,tree,letters,alphabet,chosen,
      slots.symm ▸ prog,hχ,separated⟩
  refine ⟨v',valid,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,data,ee,slots.symm ▸ pdata⟩
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))) i

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原零轮走法到同一 43 项输入的完整控制句

外参数依次为 ω,e,δ,S,ν,E,P、原走法、A,U₁,U₂,z,χ。全部新坐标
由同一次实际 reset_input 产生；原走法和两张固定表仍用原集合图读取。
控制句可直接进入反射记录，不依赖控制记录自身，亦不要求每轮已有字母枚举。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def td_reset_body0_m : Formula 1 56 := .conj
  (td_seed0_m.rename (fun i => ⟨i.val,by omega⟩))
  (let v : Fin 56 → Term 56 := Term.bound
   set[56] ⟪⌜v 0⌝ₛ = ⌜v 43⌝ₛ ∧ ⌜v 1⌝ₛ = ⌜v 44⌝ₛ ∧ ⌜v 2⌝ₛ = ⌜v 45⌝ₛ ∧
    ⌜v 3⌝ₛ = ⌜v 46⌝ₛ ∧ ⌜v 4⌝ₛ = ⌜v 47⌝ₛ ∧ ⌜v 6⌝ₛ = ⌜v 44⌝ₛ ∧ ⌜v 7⌝ₛ = ⌜v 44⌝ₛ ∧
    ⌜v 24⌝ₛ = ⌜v 55⌝ₛ ∧ ⌜v 25⌝ₛ = ⌜v 44⌝ₛ ∧ ⌜v 26⌝ₛ = ⌜v 44⌝ₛ ∧ ⌜v 27⌝ₛ = ⌜v 44⌝ₛ ∧
    ⌜v 28⌝ₛ = ⌜v 52⌝ₛ ∧ ⌜v 29⌝ₛ = ⌜v 53⌝ₛ ∧ ⌜v 30⌝ₛ = ⌜v 54⌝ₛ ∧ ⌜v 31⌝ₛ = ⌜v 51⌝ₛ ∧
    (∃ ℓ, ⌜td_move_m⌝ₚ(⌜v 50⌝ₛ,ℓ,⌜v 6⌝ₛ,⌜v 5⌝ₛ,⌜v 19⌝ₛ)) ∧
    ⌜tg_ee_data_m⌝ₚ(⌜v 48⌝ₛ,⌜v 5⌝ₛ,⌜v 8⌝ₛ,⌜v 15⌝ₛ,⌜v 16⌝ₛ,⌜v 17⌝ₛ,
      ⌜v 32⌝ₛ,⌜v 33⌝ₛ,⌜v 34⌝ₛ,⌜v 35⌝ₛ) ∧
    ⌜fun P q b z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_program_data_m P q b z
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜v 49⌝ₛ,⌜v 8⌝ₛ,⌜v 21⌝ₛ,⌜v 23⌝ₛ,⌜v 36⌝ₛ,⌜v 37⌝ₛ,⌜v 38⌝ₛ,⌜v 39⌝ₛ,
        ⌜v 40⌝ₛ,⌜v 41⌝ₛ,⌜v 42⌝ₛ)⟫)

theorem td_reset_body0_closed_l : td_reset_body0_m.FreeClosed := by
  refine ⟨(Definitional.Formula.freeClosed_rename _ _).mpr td_seed0_closed_l,?_⟩
  simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Fin.forall_fin_succ]

def td_reset_result0_m : Formula 1 13 := rb_exists_m (n := 43) td_reset_body0_m

theorem td_reset_result0_closed_l : td_reset_result0_m.FreeClosed :=
  (rb_exists_closed_l _).mpr td_reset_body0_closed_l

def td_reset_result_m {d} (ω e δ S ν E P a A U₁ U₂ z χ : Term d) : Formula 1 d :=
  td_reset_result0_m.bind (fun i => [ω,e,δ,S,ν,E,P,a,A,U₁,U₂,z,χ].get i)

@[simp] theorem td_reset_result_closed_l {d} (ω e δ S ν E P a A U₁ U₂ z χ : Term d)
    (hw : ω.freeSupport = []) (he : e.freeSupport = []) (hd : δ.freeSupport = [])
    (hS : S.freeSupport = []) (hn : ν.freeSupport = []) (hE : E.freeSupport = []) (hP : P.freeSupport = [])
    (ha : a.freeSupport = []) (hA : A.freeSupport = []) (hU : U₁.freeSupport = []) (hV : U₂.freeSupport = [])
    (hz : z.freeSupport = []) (hχ : χ.freeSupport = []) :
    (td_reset_result_m ω e δ S ν E P a A U₁ U₂ z χ).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr td_reset_result0_closed_l
  simp only [Fin.forall_fin_succ]
  exact ⟨hw,he,hd,hS,hn,hE,hP,ha,hA,hU,hV,hz,hχ,fun i => Fin.elim0 i⟩

theorem Td_setup_d.reset_result_l (hZFC : M.Models ZFC)
    {p : Tg_params_d M.Domain} {X n h a ℓ κ u U₁ U₂ z χ : M.Domain}
    (setup : Td_setup_d hZFC p X) (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) p.δ)
    (aux : Td_aux_d (ZFC.models_zf_l hZFC) p n h a) (data : Td_move_d a ℓ p.e κ u)
    (tree : Td_tree_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) p.ω p.A p.S)
    (alphabet : Td_alphabet_d p.S U₁ U₂) (chosen : M.mem z U₁) (hχ : M.mem χ p.δ)
    (separated : Td_separated_d p.S) :
    Formula.satisfies (⟨fun i => [p.ω,p.e,p.δ,p.S,p.ν,p.E,p.P,a,p.A,U₁,U₂,z,χ].get i,
      fun _ => p.ω⟩ : Env M 13) td_reset_result0_m := by
  let hZF := ZFC.models_zf_l hZFC
  let ρ : Env M 13 := ⟨fun i => [p.ω,p.e,p.δ,p.S,p.ν,p.E,p.P,a,p.A,U₁,U₂,z,χ].get i,fun _ => p.ω⟩
  obtain ⟨v,seed,eq,_,hk,hd,_,_,_,hχ,hs,ha,hb,hU,hV,hz,hA,move,ee,program⟩ :=
    setup.reset_input_l hZFC woodin aux data tree alphabet chosen hχ separated
  apply (rb_exists_sat_l (n := 43) ρ td_reset_body0_m).mpr
  refine ⟨v,(Formula.satisfies_conj_iff ..).mpr ⟨?_,?_⟩⟩
  · apply (Formula.satisfies_rename ..).mpr
    exact (Formula.closed_env_l td_seed0_m td_seed0_closed_l
      (ρ := ⟨fun i => Fin.addCases v ρ.bound (i.castAdd 13),ρ.free⟩)
      (η := ⟨v,fun _ => p.ω⟩) (by
        funext i
        change Fin.addCases v ρ.bound (i.castAdd 13) = v i
        simp only [Fin.addCases_left])).mpr seed
  · simp only [Formula.satisfies_conj_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_exists_iff,td_move_sat_l hZF.1,tg_ee_data_sat_l hZF.1,
      tg_program_data_sat_l hZF.1,tt_eval_cases_l,Definitional.Term.eval_weaken]
    exact ⟨eq 0,eq 1,eq 2,eq 3,eq 4,hk,hd,hχ,hs,ha,hb,hU,hV,hz,hA,⟨ℓ,move⟩,ee,program⟩

def td_reset_control_m {d} (p : Tg_params_d (Term d)) : Formula 1 d :=
  let q := p.map_l (fun t => t.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
  set[d] ⟪∀ n h a U₁ U₂ z χ, ⌜fun n h a => td_aux_m q n h a⌝ₚ(n,h,a) →
    (∃ ℓ κ u, ⌜td_move_m⌝ₚ(a,ℓ,⌜p.e⌝ₛ,κ,u)) →
    ⌜td_tree_m⌝ₚ(⌜p.ω⌝ₛ,⌜p.A⌝ₛ,⌜p.S⌝ₛ) → ⌜td_alphabet_m⌝ₚ(⌜p.S⌝ₛ,U₁,U₂) →
    z ∈ U₁ → χ ∈ ⌜p.δ⌝ₛ → ⌜td_separated_m⌝ₚ(⌜p.S⌝ₛ) →
    ⌜td_reset_result_m⌝ₚ(⌜p.ω⌝ₛ,⌜p.e⌝ₛ,⌜p.δ⌝ₛ,⌜p.S⌝ₛ,⌜p.ν⌝ₛ,⌜p.E⌝ₛ,⌜p.P⌝ₛ,
      a,⌜p.A⌝ₛ,U₁,U₂,z,χ)⟫

theorem td_reset_control_closed_l {d} (p : Tg_params_d (Term d)) (hp : p.closed_l) :
    (td_reset_control_m p).FreeClosed := by
  have hp' : (p.map_l (fun t => t.weaken.weaken.weaken.weaken.weaken.weaken.weaken)).closed_l := by
    simpa only [Tg_params_d.closed_l,Tg_params_d.map_l,Definitional.Term.freeSupport_weaken] using hp
  rcases hp with ⟨hw,he,_,_,_,hd,hA,hS,hn,hE,hP,_⟩
  simp -implicitDefEqProofs [td_reset_control_m,Definitional.Formula.FreeClosed,hw,he,hd,hA,hS,hn,hE,hP]
  exact td_aux_closed_l _ _ _ _ hp' rfl rfl rfl

theorem td_reset_control_l (hZFC : M.Models ZFC) {d} (ρ : Env M d) (p : Tg_params_d (Term d)) {X : M.Domain}
    (setup : Td_setup_d hZFC (p.map_l (fun t => t.eval ρ)) X)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (p.δ.eval ρ)) :
    Formula.satisfies ρ (td_reset_control_m p) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [td_reset_control_m,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff,td_aux_sat_l hZF,td_move_sat_l hZF.1,td_tree_sat_l I hZF.1,
    td_alphabet_sat_l hZF.1,Formula.satisfies_mem_iff,td_separated_sat_l hZF.1,
    td_reset_result_m,Formula.satisfies_bind,
    Tg_params_d.map_l,Definitional.Term.eval_weaken]
  intro n h a U₁ U₂ z χ aux reset tree alphabet chosen hχ separated
  obtain ⟨ℓ,κ,u,data⟩ := reset
  have result := setup.reset_result_l hZFC woodin aux data tree alphabet chosen hχ separated
  apply (Formula.closed_env_l td_reset_result0_m td_reset_result0_closed_l (ρ := _) (η := _) ?_).mp result
  have eval (t : Term d) : t.eval ρ = t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.eval
      (((((((ρ.push n).push h).push a).push U₁).push U₂).push z).push χ) := by
    simp only [Definitional.Term.eval_weaken]
  funext i
  exact Fin.cases (eval p.ω) (Fin.cases (eval p.e) (Fin.cases (eval p.δ) (Fin.cases (eval p.S)
    (Fin.cases (eval p.ν) (Fin.cases (eval p.E) (Fin.cases (eval p.P) (Fin.cases rfl
      (Fin.cases (eval p.A) (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun j => Fin.elim0 j))))))))))))) i

end YesMetaZFC.SetTheory.LargeCardinal
