import YesMetaZFC.SetTheory.LargeCardinal.TypeGameHistoryStep
import YesMetaZFC.Model.SetTheory.Internal.RelationRecord
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRootTree

/-! # 统一递归的可编码不变量

十八项保存当前模型、有限树、完整历史及原请求的记录码。所有旧轮由同一
内部函数图索引；表、反射层、根图和共同层均是已实现对象。扩展器列逐项
保留原低层高度以下无临界点的不变量，而不只保留偶数边的单步临界点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

-- X,R,μ,K,η,C,α,ξ,T,Q,G,E,L,H,b,c,π,r；u 是同一记录码 r 的四十六项。
structure Tg_run_d (ω c₀ o Cᵣ γ Z A : M.Domain) (v : Fin 18 → M.Domain) (u : Fin 46 → M.Domain) : Prop where
  source : Ic_model_d hZF ω (v 2) (v 3) (v 0) (v 1)
  context : Tg_context_d ω (v 0) (v 4) (v 5)
  finite : M.mem (v 7) ω
  successor : M.SuccessorOf (v 6) (v 7)
  tree : It_pnice_d hZF ω c₀ (v 6) (v 8) (v 9) (v 10) (v 11) (v 12)
  node : Rd_entry_d (v 7) (v 15) (v 9)
  model : Smem_d I (v 15) (v 0) (v 1)
  root : It_map_d (v 10) o (v 7) (v 16)
  image : Rd_entry_d Cᵣ (v 5) (v 16)
  anchor : Tg_anchor_d γ Z (v 0) (v 16)
  record : Rf_record_d I (v 0) (v 1) tg_issued0_m (v 5) (v 17)
  values : Rf_tuple_d I (v 0) (v 1) u (v 17)
  omega : u 0 = ω
  alphabet : u 6 = A
  lower : M.MemberSubset γ (u 24)
  past : Tg_past_d hZF ω (u 19) (v 13) (v 0) (v 14)
  links : Tg_past_links_d I (v 13) (v 9)
  roots : Tg_past_roots_d ω (v 13) (v 10) o Cᵣ γ Z
  events : Tg_past_events_d ω (v 13) (v 5) (u 4) (u 1) (u 2) (u 20)
  below : M.mem (v 14) (u 24)
  bounds : ∀ i ν, Rd_entry_d i ν (v 12) → M.mem ν (v 14) ∨ ν = v 14
  span : M.mem (u 19) (v 6)
  tree_name : Tg_common_tree_d ω (v 13) (v 10) o (v 16) (u 7)
  play : Tg_past_play_d ω (v 13) Z (v 5) (u 4) (u 3) (u 20)
  critical : It_critical_bound_d γ (v 11)

theorem Tg_run_d.read_l {ω c₀ o Cᵣ γ Z A : M.Domain} {v : Fin 18 → M.Domain} {u : Fin 46 → M.Domain}
    (h : Tg_run_d hZF ω c₀ o Cᵣ γ Z A v u) (nc : Nonempty {x // M.mem x (v 5)}) :
    ∃ ι : Env (rt_model_l (v 5) nc) 46, (∀ i, (ι.bound i).val = u i) ∧ Formula.satisfies ι tg_issued0_m := by
  have record := ((rf_record_mem_l I h.source.source.transitive h.model tg_issued0_m).mp h.record).2
  have values := ((rf_tuple_mem_l I hZF.1 h.source.source.transitive h.model u).mp h.values).2
  obtain ⟨_, w, code, valid⟩ := (rt_record_in_read_l hZF.1 tg_issued0_m tg_issued0_closed_l
    (h.context.read_l hZF h.source.source).1.transitive nc).mp record
  exact ⟨⟨w, fun _ => w 0⟩, congrFun (rt_tuple_inj_l code values), valid⟩

def Tg_run_next_d (ω c₀ : M.Domain) (v : Fin 18 → M.Domain) (u : Fin 46 → M.Domain)
    (w : Fin 18 → M.Domain) (t : Fin 46 → M.Domain) : Prop :=
  ∃ k β T Q G E L j h,
    It_pnice_d hZF ω c₀ β T Q G E L ∧
    It_extension_d (v 6) (v 7) k (v 8) (v 9) (v 10) (v 11) β T Q G E ∧
    It_extension_d β (v 6) (v 7) T Q G E (w 6) (w 8) (w 9) (w 10) (w 11) ∧
    w 7 = β ∧ M.SuccessorOf (t 19) (u 19) ∧ It_map_d (w 10) (v 7) (w 7) j ∧
    (∀ i : Fin 19, Rd_entry_d (u (i.castAdd 27)) (t (i.castAdd 27)) j) ∧
    Rd_entry_d (u 20) h j ∧ M.MemberSubset h (t 20) ∧ h ≠ t 20 ∧ M.MemberSubset (v 13) (w 13) ∧
    ∃ Y R μ K η C L V q S n s g, Tg_past_at_d (w 13) (u 19) (v 6) Y R μ K η C L V q ∧
      Tg_saved_branch_d ω V q S n s (u 23) g ∧ Tg_odd_d ω (v 13) (v 7) (v 6) k G (u 1) (u 23) (u 22) (u 7) S n s g

end YesMetaZFC.SetTheory.LargeCardinal
