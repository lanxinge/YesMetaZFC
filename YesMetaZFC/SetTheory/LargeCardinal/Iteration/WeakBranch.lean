import YesMetaZFC.SetTheory.LargeCardinal.Iteration.KeepTransfer
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.System

/-! # 弱迭代极限到良基树枝的严格装配

弱迭代的返回证书本身只记录直接极限和返回锥。要把它提升为
`It_wf_branch_d`，还必须显式保留指标关系与原树关系的一致性
`ls`。本文件只做这一步装配，不把该一致性从系统的单向 `forward`
字段中虚构出来。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-! 给定同一树上的分支、系统关系的双向识别、极限和实际良基证书，
严格得到完整的 `It_wf_branch_d`。 -/
theorem It_branch_d.wf_of_limit_l
    {ω α T Q G B L A p H R r c N W : M.Domain}
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G)
    (hω : M.IsOmega ω)
    (branch : It_branch_d α T B)
    (system : It_system_d B L Q G A p H R)
    (ls : ∀ i j, Rd_entry_d i j L ↔
      M.mem i B ∧ M.mem j B ∧ Rd_entry_d i j T)
    (limit : Di_limit_d A p H R r N W)
    (model : Smem_d I c N W)
    (wf : Wf_rel_d N W) :
    It_wf_branch_d hZF ω α T Q G B := by
  have elementary : Di_elementary_d I ω L A p H R :=
    system.elementary_l hZF hω diagram branch.subset ls
  exact ⟨branch, L, A, p, H, R, r, c, N, W, ls, system, elementary,
    limit, model.1, wf⟩

/-! 弱状态的规范分支是前一引理的直接实例。这里把 `ls` 作为显式的
运输证书保留在接口中，避免把 `Wi_limit_d` 中没有记录的双向关系
偷偷当作可推导字段。 -/
theorem Wi_state_d.limit_wf_branch_of_order_l
    {ω α T Q G a A S P L A0 p H R r c N W : M.Domain}
    (state : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P)
    (hω : M.IsOmega ω)
    (system : It_system_d α L Q G A0 p H R)
    (ls : ∀ i j, Rd_entry_d i j L ↔
      M.mem i α ∧ M.mem j α ∧ Rd_entry_d i j T)
    (limit : Di_limit_d A0 p H R r N W)
    (model : Smem_d I c N W)
    (wf : Wf_rel_d N W) :
    It_wf_branch_d hZF ω α T Q G α := by
  exact It_branch_d.wf_of_limit_l hZF state.diagram hω
    (state.branch_l hZF) system ls limit model wf

/-! 增强极限证书已经把 `ls` 与良基性放回同一 witness 后，
弱状态可直接产出非空的良基分支证书。 -/
theorem Wi_state_d.limit_tree_wf_branch_l
    {ω α T Q G a A S P c N W : M.Domain}
    (state : Wi_state_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G a A S P)
    (hω : M.IsOmega ω)
    (limit : Wi_limit_tree_d hZF ω α T Q G c N W P) :
    It_wf_branch_d hZF ω α T Q G α := by
  obtain ⟨L, A', p, H, R, r, system, ls, diLimit, model, _, _, wf⟩ := limit
  exact state.limit_wf_branch_of_order_l hZF hω system ls diLimit model wf
end YesMetaZFC.SetTheory.LargeCardinal
