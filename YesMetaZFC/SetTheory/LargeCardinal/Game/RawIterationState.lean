import YesMetaZFC.SetTheory.LargeCardinal.Game.RawRequest
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawCritical

/-! # 原树、请求与原对局的六十六项状态

二十项头部保存本次实际原树、支撑列、档案与前缀；其后四十六项
仍是原请求。根图及原字母像由完整请求保存，不重复工作复制数据。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

-- X,R,w,z,η,C,m,n,T,Q,G,E,Λ,D,χ,c,q,r,k,f。
structure Tg_raw_iteration_d (ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A : M.Domain)
    (v : Fin 20 → M.Domain) (a : Fin 46 → M.Domain) : Prop where
  finite : M.mem (v 7) ω
  successor : M.SuccessorOf (v 6) (v 7)
  tree : It_tree_d hZF ω c₀ (v 6) (v 8) (v 9) (v 10) (v 11)
  levels_function : M.IsSetFunction I (v 12)
  levels : ∀ i L, Rd_entry_d i L (v 12) ↔ ∃ p κ F, Rd_entry_d i p (v 11) ∧ It_payload_d p κ L F
  node : Rd_entry_d (v 7) (v 15) (v 9)
  model : Smdl_d I (v 15) (v 0) (v 1)
  root_node : Rd_entry_d o c₀ (v 9)
  request : Tg_raw_request_d I ω S₀ X₀ R₀ γ₀ D₀ C₀ A₀ (v 0) (v 1) (v 2) (v 4) (v 5)
    (v 14) (v 3) (v 18) (v 13) (v 17) (v 16) ⟨o,v 7,v 9,v 10,v 12⟩ a
  play : Tg_prefix_d I (v 18) A (v 0) (v 1) (v 5) (a 4) (a 3) (a 20) (v 3) (v 16) (v 19)
  critical : Tg_raw_critical_d I X₀ R₀ γ₀ D₀ C₀ o (v 9) (v 10) (v 11)

/-- 元组码只打包同一份二十项头部与四十六项请求。 -/
def Tg_raw_iteration_code_d (ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A s : M.Domain) : Prop :=
  ∃ v : Fin 66 → M.Domain, Rt_tuple_d v s ∧
    Tg_raw_iteration_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A
      (fun i => v (i.castAdd 46)) (fun i => v (Fin.natAdd 20 i))

theorem Tg_raw_iteration_d.pack_l
    {ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A : M.Domain} {v : Fin 20 → M.Domain} {a : Fin 46 → M.Domain}
    (h : Tg_raw_iteration_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A v a) :
    ∃ s, Rt_tuple_d (Fin.addCases (m := 20) (n := 46) (motive := fun _ => M.Domain) v a) s ∧
      Tg_raw_iteration_code_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A s := by
  let q : Fin 66 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) v a
  obtain ⟨s,code⟩ := rt_tuple_exists_l (ZF.modelsKP hZF) q
  exact ⟨s,code,q,code,by simpa only [q,Fin.addCases_left,Fin.addCases_right] using h⟩

/-- 同一状态码的任何完整解码都恢复这份实际状态。 -/
theorem Tg_raw_iteration_code_d.read_l
    {ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A s : M.Domain} {v : Fin 66 → M.Domain}
    (h : Tg_raw_iteration_code_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A s) (code : Rt_tuple_d v s) :
    Tg_raw_iteration_d hZF ω c₀ o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A
      (fun i => v (i.castAdd 46)) (fun i => v (Fin.natAdd 20 i)) := by
  obtain ⟨w,cw,state⟩ := h
  exact (rt_tuple_inj_l cw code) ▸ state

end YesMetaZFC.SetTheory.LargeCardinal
