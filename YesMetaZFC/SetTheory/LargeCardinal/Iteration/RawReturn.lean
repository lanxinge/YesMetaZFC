import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource

/-! # 同一原共同层的严格切片与返回施加

源支撑的实际不可数共尾性生产严格极限切片，再以共同图的真实逆图
把指定扩展器施加回原前驱。输入只有同一次秩源、超幂和临界点证据，
不涉及回答类型、查询、元数组或游戏记录，也不重新选择扩展器。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.return_cut_l
    {ω c₀ X₀ R₀ c N R d P S q zp L l U V Γ g : M.Domain}
    (common : Ic_common_d I N R P S L l U V Γ g)
    (hω : M.IsOmega ω) (root : Zc_model_d I ω c₀ X₀ R₀)
    (mn : Smdl_d I c N R) (mp : Smdl_d I d P S)
    (fromRoot : Smap_d I ω c₀ c X₀ N q) :
    let Nn := smdl_structure_l I (R := R) mn.2.1
    let Pn := smdl_structure_l I (R := S) mp.2.1
    let native := ZFC.models_zf_l ((root.map_l hZF hω mn fromRoot).native_l I hZF hω)
    ∀ ground : Pn.Models ZFC,
    let hP := ZF.modelsKP (ZFC.models_zf_l ground)
    let J := kp_pair_l hP
    ∀ w τ : Nn.Domain, Nn.IsOmega w →
    (∃ ν : Nn.Domain, Nn.IsCofinality (kp_pair_l (ZF.modelsKP native)) ν ⟨L,common.left_rank.1⟩ ∧
      Nn.mem w ν) → Rr_small_d I N R U → Nn.mem τ ⟨L,common.left_rank.1⟩ →
    ∀ {wp κ δ Lp X K R' F c' d' Y T j κ' : Pn.Domain},
    Ep_source_d J wp κ K X R' → V_d J δ X → Pn.IsLimitOrdinal δ →
    It_local_d J wp X R' κ Lp F → Sc_inaccessible_d (M := Pn) wp X Lp → Ex_strength_d J wp κ Lp X F →
    Smem_d J c' X R' → Smem_d J d' Y T → It_ultra_d J wp κ Lp F c' d' j →
    Rd_entry_d (M := Pn) κ κ' j → Pn.MemberSubset Lp κ' → Rr_layer_d I ω P S wp.val zp →
    Rd_entry_d τ.val κ.val g → Rd_entry_d l Lp.val S →
    ∃ α β : Pn.Domain,
      Pn.mem α ⟨l,common.right_rank.1⟩ ∧ Pn.mem β ⟨V,common.right_rank.2.1⟩ ∧
      Pn.mem κ β ∧ Pn.IsLimitOrdinal α ∧ V_d J α β ∧
    ∃ B k, (∀ x, M.mem x B ↔ M.mem x P ∧ Rd_entry_d x V S) ∧
      M.IsSetInjectionFromTo I k B N ∧
      (∀ y, Rd_entry_d y U R ↔ ∃ x, M.mem x B ∧ Rd_entry_d x y k) ∧
      (∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y R ↔ ∃ a, Rd_entry_d a x S ∧ Rd_entry_d a v k) ∧
      (∀ x y, Rd_entry_d x y k ↔ Rd_entry_d y x g) ∧
      Er_rank_cut_d hZF ω c₀ X₀ R₀ c N R q B k P S zp d mp.2.1 hP
        ⟨V,common.right_rank.2.1⟩ wp κ Lp F β X K j := by
  intro Nn Pn native ground hP J w τ omega cofinal small below
    wp κ δ Lp X K R' F c' d' Y T j κ' source rank height loc card strong mx my ultra critical bound
    numbers point above
  have hN := ZF.modelsKP native
  let ln : Pn.Domain := ⟨l,common.right_rank.1⟩
  let Vn : Pn.Domain := ⟨V,common.right_rank.2.1⟩
  obtain ⟨ν,cf,uncountable⟩ := cofinal
  obtain ⟨α,β,hα,hβ,hκ,limitα,rankβ,_⟩ := common.limit_cut_l (ZF.modelsKP hZF)
    mn.2.1 mp.2.1 native hP w ν τ κ omega cf uncountable below point
  have rankV := (rr_rank_native_l I mp.2.1 hP ln Vn).mp common.right_rank
  have limitV := common.right_limit_native_l I hZF.1 mn mp hN hP
  obtain ⟨B,k,carrier,function,image,pred,inverse⟩ := common.reverse_native_l hZF mn hN
  have high : Pn.mem α Lp :=
    (loc.ordinals_l hP source.transitive source.code).2.transitive ln above α hα
  have result := loc.raw_rank_source_l hZFC hω mp.2.1 ground
    Vn wp κ Lp F α β ln X K R' δ c' d' Y T j κ'
    mp root mn fromRoot numbers rankV limitV carrier function image pred
    common.left_closed small hβ hκ limitα rankβ high source rank height mx my ultra
    card strong critical bound
  exact ⟨α,β,hα,hβ,hκ,limitα,rankβ,B,k,carrier,function,image,pred,inverse,result⟩

end YesMetaZFC.SetTheory.LargeCardinal
