import YesMetaZFC.SetTheory.LargeCardinal.ExtenderShort
import YesMetaZFC.SetTheory.LargeCardinal.SupportConstruction

/-! # 武丁基数产生标准短扩展器

临界点随谓词固定，长度可取临界点与 δ 之间的任意序数。输出同一个实际
测度族和算子，并证明算子恰为原强嵌入的有限支撑限制；背景仅需 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem woodin_short_l (hZF : M.Models ZF) {δ : M.Domain}
    (hd : Woodin_d (kp_pair_l (ZF.modelsKP hZF)) δ) :
    let I := kp_pair_l (ZF.modelsKP hZF)
    ∃ ω V, M.IsOmega ω ∧ V_d I δ V ∧ ∀ A, M.MemberSubset A V → ∃ κ, M.mem κ δ ∧
      ∀ L, M.mem L δ → M.mem κ L → ∃ ν N B j W k S F K E,
        Wd_witness_d I ω δ V A κ ν N B j W k ∧ M.mem L ν ∧ M.mem L k ∧ Fseq_space_d I ω L S ∧ M.mem S N ∧
        Fseq_space_d I ω κ K ∧ Es_family_d I j κ L S F ∧ Ex_short_d hZF ω κ L F ∧
        Ex_operator_d K S F E ∧ Ex_derived_d j S E := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hδ : M.IsLimitOrdinal δ := by obtain ⟨_, _, _, _, hr, _⟩ := hd; exact hr.isLimitOrdinal
  obtain ⟨ω, V, hω, hV, all⟩ := woodin_components_l I hZF hd
  refine ⟨ω, V, hω, hV, fun A hA => ?_⟩
  obtain ⟨κ, hκ, hκo, hωκ, family⟩ := all A hA
  refine ⟨κ, hκ, fun L hL hκL => ?_⟩
  have hLo := hδ.1.mem hL
  have hωL : M.MemberSubset ω L := fun x hx => hLo.transitive κ hκL x (hκo.transitive ω hωκ x hx)
  obtain ⟨ν, N, B, j, W, k, S, F, hw, hLν, hLk, hS, hSN, hF, _, _, complete⟩ := family L hL hωL
  have hj := hw.2.2.2.2.2.1
  have hc := hw.2.2.2.2.2.2.1
  have hsub := hc.ordinal_image.transitive L hLk
  have hpre := es_pre_l hZF hω hV hδ hj hw.1 hc hLo hκL hsub hS (hw.1 S hSN) hF
  have short : Ex_short_d hZF ω κ L F := ⟨hpre, fun H f hH hf => (complete H f hH hf).imp fun _ hh => hh.2⟩
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω κ
  obtain ⟨E, he⟩ := ex_operator_exists_l hZF K S F
  exact ⟨ν, N, B, j, W, k, S, F, K, E, hw, hLν, hLk, hS, hSN, hK, hF, short, he,
    ex_derived_l hZF hω hV hδ hj hw.1 hc hsub hS (hw.1 S hSN) hF hK he⟩

end YesMetaZFC.SetTheory.LargeCardinal
