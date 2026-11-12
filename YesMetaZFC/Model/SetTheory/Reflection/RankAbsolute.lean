import YesMetaZFC.Model.SetTheory.Relations.RankImage
import YesMetaZFC.SetTheory.CumulativeRelativeRead
import YesMetaZFC.SetTheory.CumulativeFunction

/-! # 实际极限秩模型中的累积层绝对性

向上读取使用原秩层的全部子集闭包；向下读取使用实际历史的低秩界。
小模型只需 KP，不把全层级反射另外作为输入。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smem_d.rank_iff_l {c U R θ : M.Domain} (source : Smem_d I c U R)
    (rank : V_d I θ U) (limit : M.IsLimitOrdinal θ)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models KP)
    (α V : (smdl_structure_l I (R := R) source.1.2.1).Domain) :
    V_d (kp_pair_l native) α V ↔ V_d I α.val V.val := by
  have trans := v_transitive_l I rank
  have read := (rr_rank_native_l I source.1.2.1 native α V).symm.trans
    (rr_rank_mem_l I (ZF.modelsKP hZF) source trans α.property V.property)
  apply read.trans
  constructor
  · exact fun low => low.absolute_l (ZF.modelsKP hZF) trans V.property
      (fun A B ha sub => v_subset_mem_l I rank ha sub)
  · intro low
    have below := ZF.v_ordinal_height_l hZF rank (v_ordinal_l I low) α.property
    obtain ⟨B,F,hB,hF,history,_⟩ := vr_source_l hZF rank limit below low
    exact ⟨B,F,hB,hF,fun t _ => history t⟩

end YesMetaZFC.SetTheory.Internal
