import YesMetaZFC.SetTheory.LargeCardinal.IterationInitial
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSetPull

/-! # 可数壳的根秩段自动给出下降递归的初始行

大根秩段是真实正则 Vβ。外层嵌入在小秩段上的限制和实际可数编号，
直接满足原初始行构造的全部前提。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pn_initial_pull_l {ω B R b K U S u J π a d β V P : M.Domain}
    (source : Ep_source_d hZF ω ω K B R) (target : Ep_source_d hZF ω ω J U S)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (count : M.CardinalLessOrEqual I B ω) (had : Rd_entry_d a d π) (md : Smem_d I d V P)
    (above : M.mem ω β) (regular : M.IsRegularCardinal I β) (rank : V_d I β V) :
    ∃ X Q p ι, Smem_d I a X Q ∧ Rd_entry_d X V π ∧ M.IsRestrictionOf I p π X ∧ Pn_row_d hZF ω a X V p ι := by
  obtain ⟨L, seq⟩ := ZF.fseq_space_exists_l I hZF source.omega ω
  obtain ⟨P', child⟩ := ep_regular_source_l hZFC source.omega above regular rank above (fun _ h => h) seq
  obtain ⟨d', md'⟩ := child.code
  obtain ⟨rfl, rfl⟩ := smem_unique_l I hZF.1 md' md
  obtain ⟨X, Q, _, p, mx, sx, hXV, restriction, hp⟩ := ep_set_source_pull_l hZF source target mb mu hj had md child
  obtain ⟨η, inj⟩ := count
  obtain ⟨η', res⟩ := ZF.exists_restriction hZF I η X
  have index : M.IsSetInjectionFromTo I η' X ω :=
    ⟨res.isSetFunctionFromTo inj.1 (source.transitive X (hj.1.1.input_mem_of_pairMember hXV)),
      fun x y n hx hy => inj.2 x y n ((res.2 x n).mp hx).2 ((res.2 y n).mp hy).2⟩
  obtain ⟨ι, row⟩ := pn_initial_row_l hZFC source.omega above regular rank sx.transitive mx md hp index
  exact ⟨X, Q, p, ι, mx, hXV, restriction, row⟩

end YesMetaZFC.SetTheory.LargeCardinal
