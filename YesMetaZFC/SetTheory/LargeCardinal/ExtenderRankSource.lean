import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSource
import YesMetaZFC.SetTheory.InaccessibleHierarchy

/-! # 不可达秩层本身的源实例

源就是 Vδ，所有代表函数均属于原强嵌入的定义域；原有 Hχ 源理论直接以 χ=δ 调用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ep_inaccessible_source_l (hZFC : M.Models ZFC) {ω δ V κ K : M.Domain}
    (hω : M.IsOmega ω) (hωδ : M.mem ω δ)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hV : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ V)
    (hκ : M.mem κ δ) (hωκ : M.MemberSubset ω κ)
    (hK : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K) :
    ∃ R, Ep_source_d (ZFC.models_zf_l hZFC) ω κ K V R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hκV := ZF.v_ordinal_mem_l I hZF hV hκ
  have hKV : M.mem K V := by
    apply ZF.v_relations_mem_l I hZF hV hr.isLimitOrdinal hκV
    intro f hf p hp
    obtain ⟨n, hn, hfn⟩ := (hK f).mp hf
    obtain ⟨a, b, hab⟩ := hfn.1.1 p hp
    exact ⟨a, hωκ a (hω.transitive hZF n hn a (hfn.input_mem_of_pairMember ⟨p, hab, hp⟩)),
      b, hfn.output_mem_of_pairMember ⟨p, hab, hp⟩, hab⟩
  exact ep_source_of_h_l hZFC hω hωκ hr hωδ (ZFC.inaccessible_hereditary_l I hZFC hω hωδ hr hs hV)
    (ZF.v_ordinal_mem_l I hZF hV hωδ) hκV hKV hK

end YesMetaZFC.SetTheory.LargeCardinal
