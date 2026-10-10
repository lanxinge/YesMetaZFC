import YesMetaZFC.Model.SetTheory.Internal.CanonicalNodeSource
import YesMetaZFC.Model.SetTheory.Internal.CanonicalCode

/-! # 全部内部公式的规范自然数解码在极限秩层中绝对

程序逐行转换、自然数折叠历史及最终根编号均使用原有定义；不引入新的
编号表参数，也不要求源满足 ZF。任意非标准内部公式同样成立。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {δ Z : M.Domain}
  (hδ : M.IsLimitOrdinal δ) (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) δ Z)
  (nz : Nonempty {x // M.mem x Z})
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "T" => ZF.v_transitive_l I hZF hV
local notation "P" => sc_v_pair_l hZF hδ hV
local notation "N" => rt_model_l Z nz
local notation "J" => rt_pair_l T nz (And.left hZF) P

/-- 原规范自然数码及原程序码在源中精确对应。 -/
theorem rt_sc_num_l (ω a z : (N).Domain) (hω : M.IsOmega ω.val) :
    Sc_num_d J ω a z ↔ Sc_num_d I ω.val a.val z.val := by
  have syn := rt_sformula_l (ZF.modelsKP hZF) T nz P
  constructor
  · rintro ⟨n, F, k, G, c, hf, hg, hc, hz⟩
    have hf' := (syn ω a n F k).mp hf
    have hg' := (rt_sc_rows_l hZF hδ hV nz ω n F G hω hf'.2.1).mp hg
    exact ⟨n.val, F.val, k.val, G.val, c.val, hf', hg',
      (rt_oc_seq_l hZF hδ hV nz ω G c hω (fun _ _ h => hg'.1.output_mem_of_pairMember h)).mp hc,
      (rt_oc_pair_l hZF hδ hV nz c k z).mp hz⟩
  · rintro ⟨n, F, k, G, c, hf, hg, hc, hz⟩
    have fk := hf.1.mem_l M T a.property
    have hn := T ω.val ω.property n hf.2.1.1
    have hG := ZF.v_relation_mem_l I hZF hV hδ ω.property (fun p hp => by
      obtain ⟨i, j, code⟩ := hg.1.1.1 p hp
      have hij : M.PairMember I i j G := ⟨p, code, hp⟩
      exact ⟨i, hω.transitive hZF n hf.2.1.1 i (hg.1.input_mem_of_pairMember hij),
        j, hg.1.output_mem_of_pairMember hij, code⟩)
    have hC := T ω.val ω.property c (oc_seq_natural_l I hZF hω hg.1 hc)
    let n' : (N).Domain := ⟨n, hn⟩
    let F' : (N).Domain := ⟨F, fk.1⟩
    let k' : (N).Domain := ⟨k, fk.2⟩
    let G' : (N).Domain := ⟨G, hG⟩
    let c' : (N).Domain := ⟨c, hC⟩
    exact ⟨n', F', k', G', c', (syn ω a n' F' k').mpr hf,
      (rt_sc_rows_l hZF hδ hV nz ω n' F' G' hω hf.2.1).mpr hg,
      (rt_oc_seq_l hZF hδ hV nz ω G' c' hω (fun _ _ h => hg.1.output_mem_of_pairMember h)).mpr hc,
      (rt_oc_pair_l hZF hδ hV nz c' k' z).mpr hz⟩

end YesMetaZFC.SetTheory.Internal
