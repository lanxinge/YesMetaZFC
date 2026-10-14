import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunMove
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRunRoot
import YesMetaZFC.Model.SetTheory.ClassResponse

/-! # 所有原实局共用的实际后继函数

原树名称与全部递归不变量一起进入反射闭包。选择只执行一次，
输入为当前状态和一个字母；以后有限前缀递归不再调用选择公理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}
section State
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Tg_run_choice_d (ω c o C γ Z A S r X D K : M.Domain) : Prop where
  initial : Tg_run_code_d hZF ω c o C γ Z A o r
  name : Tg_run_name_d S r
  member : M.mem r X
  product : M.IsCartesianProduct I D X A
  function : Fn0_d D X K
  step : ∀ n s x t p, Tg_run_code_d hZF ω c o C γ Z A n s → Tg_run_name_d S s →
    (I).Codes p s x → Rd_entry_d p t K → ∃ m, M.SuccessorOf m n ∧
      Tg_run_code_d hZF ω c o C γ Z A m t ∧ Tg_run_name_d S t ∧
      Tg_run_edge_d hZF ω c s t ∧ Tg_run_move_d hZF ω A n m s t x

end State

section Choice
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_run_code_d.choice_l {ω c o C γ Z A S r : M.Domain}
    (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o) (hγ : M.IsLimitOrdinal γ)
    (hωZ : M.mem ω Z) (hAZ : M.mem A Z)
    (initial : Tg_run_code_d hZF ω c o C γ Z A o r) (name : Tg_run_name_d S r) :
    ∃ X D K, Tg_run_choice_d hZF ω c o C γ Z A S r X D K := by
  let ρ : Env M 8 := ⟨fun i => [ω,c,o,C,γ,Z,A,S].get i,fun _ => ω⟩
  let V : UnarySchema 8 := { body := set[9] ⟪∃ n,
    ⌜tg_run_code_m⌝ₚ(⌜(.bound 1 : Term 9)⌝ₛ,⌜(.bound 2 : Term 9)⌝ₛ,⌜(.bound 3 : Term 9)⌝ₛ,
      ⌜(.bound 4 : Term 9)⌝ₛ,⌜(.bound 5 : Term 9)⌝ₛ,⌜(.bound 6 : Term 9)⌝ₛ,⌜(.bound 7 : Term 9)⌝ₛ,n,⌜(.newest : Term 9)⌝ₛ) ∧
    ⌜tg_run_name_m⌝ₚ(⌜(.bound 8 : Term 9)⌝ₛ,⌜(.newest : Term 9)⌝ₛ)⟫ }
  have valid s : V.denote ρ s ↔ ∃ n, Tg_run_code_d hZF ω c o C γ Z A n s ∧ Tg_run_name_d S s := by
    simp only [V,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      tg_run_code_sat_l hZF,tg_run_name_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl
  let φ : UnarySchema 10 := { body := set[11] ⟪∃ n m,
    ⌜tg_run_code_m⌝ₚ(⌜(.bound 3 : Term 11)⌝ₛ,⌜(.bound 4 : Term 11)⌝ₛ,⌜(.bound 5 : Term 11)⌝ₛ,
      ⌜(.bound 6 : Term 11)⌝ₛ,⌜(.bound 7 : Term 11)⌝ₛ,⌜(.bound 8 : Term 11)⌝ₛ,⌜(.bound 9 : Term 11)⌝ₛ,n,⌜(.bound 2 : Term 11)⌝ₛ) ∧
    ⌜KP.succ0_m⌝ₚ(m,n) ∧
    ⌜tg_run_code_m⌝ₚ(⌜(.bound 3 : Term 11)⌝ₛ,⌜(.bound 4 : Term 11)⌝ₛ,⌜(.bound 5 : Term 11)⌝ₛ,
      ⌜(.bound 6 : Term 11)⌝ₛ,⌜(.bound 7 : Term 11)⌝ₛ,⌜(.bound 8 : Term 11)⌝ₛ,⌜(.bound 9 : Term 11)⌝ₛ,m,⌜(.newest : Term 11)⌝ₛ) ∧
    ⌜tg_run_edge_m⌝ₚ(⌜(.bound 3 : Term 11)⌝ₛ,⌜(.bound 4 : Term 11)⌝ₛ,⌜(.bound 2 : Term 11)⌝ₛ,⌜(.newest : Term 11)⌝ₛ) ∧
    ⌜tg_run_move_m⌝ₚ(⌜(.bound 3 : Term 11)⌝ₛ,⌜(.bound 9 : Term 11)⌝ₛ,n,m,
      ⌜(.bound 2 : Term 11)⌝ₛ,⌜(.newest : Term 11)⌝ₛ,⌜(.bound 1 : Term 11)⌝ₛ)⟫ }
  have action s x t : φ.denote ((ρ.push s).push x) t ↔ ∃ n m,
      Tg_run_code_d hZF ω c o C γ Z A n s ∧ M.SuccessorOf m n ∧
      Tg_run_code_d hZF ω c o C γ Z A m t ∧ Tg_run_edge_d hZF ω c s t ∧ Tg_run_move_d hZF ω A n m s t x := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      tg_run_code_sat_l hZF,KP.succ0_sat_l hZF.1,tg_run_edge_sat_l hZF,tg_run_move_sat_l hZF,Definitional.Term.eval_weaken]; rfl
  obtain ⟨X,D,K,mem,prod,fn,steps⟩ := ZFC.class_response_l I hZFC V φ ρ (a := r) hw (by
    intro s x hs hx
    obtain ⟨n,run,name⟩ := (valid s).mp hs
    obtain ⟨m,t,succ,next,edge,move⟩ := run.advance_l hZFC ho hγ hωZ hAZ hx
    exact ⟨t,(valid t).mpr ⟨m,next,edge.name_l hZF run next name⟩,(action s x t).mpr ⟨n,m,run,succ,next,edge,move⟩⟩)
  refine ⟨X,D,K,⟨initial,name,mem,prod,fn0_of_function_l (ZF.modelsKP hZF) fn,?_⟩⟩
  intro n s x t p run name pair entry
  obtain ⟨vt,act⟩ := steps s x t p pair entry ((valid s).mpr ⟨n,run,name⟩)
  obtain ⟨k,m,old,succ,next,edge,move⟩ := (action s x t).mp act
  obtain ⟨v,code,_,eq⟩ := old
  obtain ⟨w,pack,_,eq'⟩ := run
  have kn : k = n := eq.symm.trans ((congrFun (rt_tuple_inj_l code pack) 37).trans eq')
  exact ⟨m,kn ▸ succ,next,((valid t).mp vt).choose_spec.2,edge,kn ▸ move⟩

end Choice
end YesMetaZFC.SetTheory.LargeCardinal
