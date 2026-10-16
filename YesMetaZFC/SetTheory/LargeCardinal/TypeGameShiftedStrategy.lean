import YesMetaZFC.SetTheory.LargeCardinal.TypeGameBranchProjection
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameStrategyPlay

/-! # 实际递归初值的全分支策略

从已实现的零轮状态统一选择后继表，构造一个原局策略。每个服从策略的
对局产生自己的整棵迭代树，每个活动扩展器的临界点都不低于原低层高度；
对这棵树的每条共尾良基分支，实际装配移位投影。
初值仍使用现有工作模型规格；任意地模型的相对初值不能用此规格代替。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

/-- 同一棵实际迭代树同时满足逐扩展器临界点界和全部良基共尾分支投影。 -/
def Tg_shifted_d (hZF : M.Models ZF) (ω o c γ Y F S x : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ T Q G E L, It_pnice_d hZF ω c ω T Q G E L ∧
    It_critical_bound_d γ E ∧
    ∀ b, It_wf_branch_d hZF ω ω T Q G b →
      ∃ d N W P j Y' F' S', Smem_d I d N W ∧ It_source_d hZF ω d ∧
        It_cone_d hZF ω b Q G d N W P ∧ Rd_entry_d o j P ∧
        Rd_entry_d Y Y' j ∧ Rd_entry_d F F' j ∧ Rd_entry_d S S' j ∧
        Fseq_space_d I ω Y' F' ∧ Tree_d F' S' ∧ Tg_projection_d hZF ω Y' F' S' x

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_run_code_d.shifted_strategy_l {ω c o C γ Z A r S X R Y F a : M.Domain}
    (initial : Tg_run_code_d hZF ω c o C γ Z A o r) (name : Tg_run_name_d S r)
    (hw : M.IsOmega ω) (ho : ∀ z, ¬ M.mem z o) (limit : M.IsLimitOrdinal γ)
    (hwZ : M.mem ω Z) (hAZ : M.mem A Z) (ha : M.mem a A)
    (model : Smem_d I c X R) (memS : M.mem S X) (memY : M.mem Y X)
    (space : Fseq_space_d I ω Y F) (closed : Tree_d F S) :
    ∃ K σ, Fseq_space_d I ω A K ∧ Fn0_d K A σ ∧
      ∀ x, Fn0_d ω A x → Gm_follows_d I false ω σ x → Tg_shifted_d hZF ω o c γ Y F S x := by
  obtain ⟨D, E, J, machine⟩ := initial.choice_l hZFC hw ho limit hwZ hAZ name
  obtain ⟨K, finite⟩ := ZF.fseq_space_exists_l I hZF hw A
  obtain ⟨σ, strategy, values⟩ := machine.strategy_l hZF hw ho ha finite
  refine ⟨K, σ, finite, strategy, fun x input follows => ?_⟩
  obtain ⟨H, sequence, names, played⟩ := machine.sequence_l hZF hw ho ha finite strategy values input follows
  obtain ⟨U, tree, archive, columns⟩ := sequence.union_l hZF hw
  exact ⟨U 0, U 1, U 2, U 3, U 4, tree, sequence.critical_bound_l hZF (columns 3),
    fun b wf => sequence.wf_projection_l hZF tree archive columns
    ho model memS memY names played input space closed (b := b) wf⟩

end YesMetaZFC.SetTheory.LargeCardinal
