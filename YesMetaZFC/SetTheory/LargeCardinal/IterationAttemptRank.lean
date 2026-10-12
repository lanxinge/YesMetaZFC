import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptDecode
import YesMetaZFC.SetTheory.LargeCardinal.IterationEmbedding
import YesMetaZFC.SetTheory.Collapse.RelationRank

/-! # 失败的返回嵌入产生联合尝试秩

任何内部下降链都解码为实际共尾枝、传递直接极限及满足根复合式的返回嵌入。
因此反例的尝试关系内部良基，原良基递归给出实际序数值秩函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ja_counterexample_rank_l {ω T Q G E Y W z π c₀ X₀ V₀ d : M.Domain}
    (hω : M.IsOmega ω) (dc : Dc_d I ω) (h : It_diagram_d hZF ω ω T Q G)
    (en : Ja_enum_d I ω ω Q E) (hz : ∀ x, ¬ M.mem x z)
    (hc : Rd_entry_d z c₀ Q) (mx : Smdl_d I c₀ X₀ V₀) (source : It_source_d hZF ω c₀)
    (my : Smem_d I d Y W) (pi : Fn0_d X₀ Y π) (bad : ¬ It_return_d hZF ω z T Q G d Y π) :
    ∃ A R β F, Ja_space_d I ω T Q G E Y W z π A R ∧ M.IsOrdinal β ∧
      M.IsSetFunctionFromTo I F A β ∧ Wr_d I A R F := by
  obtain ⟨A, R, space⟩ := ja_space_l hZF hω h en (Y := Y) (W := W) (z := z) (π := π)
  have wf : Wf_rel_d A R := wf_of_no_desc_l hZF dc (fun g fg desc => by
    obtain ⟨B, path⟩ := ja_path_l hZF hω h.order space fg desc
    obtain ⟨P, maps, ps⟩ := ja_decode_l hZF hω h en my.1 space fg path
    have hzω := (h.model_domain z).mpr ⟨c₀, hc⟩
    obtain ⟨k, hk, _⟩ := path.branch.cofinal z hzω
    have hzB := path.branch.down z k (h.order.root_l hZF hz k (path.branch.subset k hk)) hk
    have root := ja_root_l hZF en space fg path hzB hc mx pi ps
      (fun f hf => fn0_of_function_l (ZF.modelsKP hZF) (maps.elementary z f c₀ X₀ V₀ hf hc mx).1.1)
      ((maps.domain z).mp hzB)
    exact bad (it_embedding_return_l hZF hω h path.branch hzB hc source my maps root))
  obtain ⟨β, F, hb, hf, _, rank⟩ := wr_exists_l I hZF wf
  exact ⟨A, R, β, F, space, hb, hf, rank⟩

end YesMetaZFC.SetTheory.LargeCardinal
