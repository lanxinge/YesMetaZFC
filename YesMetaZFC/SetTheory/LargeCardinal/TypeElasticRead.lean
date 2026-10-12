import YesMetaZFC.SetTheory.LargeCardinal.TypeElastic
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankSource
import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessibleRead

/-! # 从可实现弹性类型自动提取伸展数据

实现高度不预设为后继，δ 的不可达性也不外加。二者均由原查询读取；
随后实际构造 Vδ 的源实例，返回同一元组的前驱类型及全部高度的扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ee_language_d.realized_l {ω κ n B U D δ η Y c S s t : M.Domain} {q : Ee_queries_d M}
    (language : Ee_language_d hZF ω κ n B U D q) (hω : M.IsOmega ω) (hk : M.mem κ δ)
    (hY : V_d I η Y) (model : Smem_d I c Y S) (type : Tt_realized_d I ω c Y S n s δ U D t)
    (elastic : Ee_elastic_d q t) :
    M.mem ω δ ∧ M.IsRegularCardinal I δ ∧ M.IsStrongLimitCardinal I δ ∧
      ∃ ν A X K R b Q w, M.SuccessorOf η ν ∧ V_d I ν A ∧ V_d I δ X ∧ Ep_source_d hZF ω κ K X R ∧
        Smem_d I b A Q ∧ Ee_minus_d I ω D q t w ∧ Tt_realized_d I ω b A Q n s δ U D w ∧
          ∀ τ, M.mem τ δ → Ee_step_d hZF ω κ δ n s b X R w τ := by
  have inacc := (language.inaccessible c Y S s δ t model type).mp elastic.2.1
  obtain ⟨above, regular, strong⟩ := sc_v_inaccessible_read_l hZF hY inacc
  obtain ⟨ν, succ⟩ := (language.successor η Y c S s δ t hY model type).mp elastic.1.1
  obtain ⟨A, hA⟩ := ZF.v_exists_l I hZF ((v_ordinal_l I hY).mem succ.predecessor_mem)
  obtain ⟨X, hX⟩ := ZF.v_exists_l I hZF regular.1.1
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω κ
  obtain ⟨R, source⟩ := ep_regular_source_l hZFC hω above regular hX hk (hω.subset_limitOrdinal hZF language.limit) hK
  obtain ⟨_, b, Q, w, lower, minus, realized, all⟩ :=
    (language.read hZFC ν η A Y X c S δ K R s t hA hY succ hX regular.isLimitOrdinal above hk source model type).mp elastic
  exact ⟨above, regular, strong, ν, A, X, K, R, b, Q, w, succ, hA, hX, source, lower, ⟨elastic.1, minus⟩, realized, all⟩

end YesMetaZFC.SetTheory.LargeCardinal
