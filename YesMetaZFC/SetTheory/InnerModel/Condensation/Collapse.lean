import YesMetaZFC.SetTheory.InnerModel.Condensation.Queries
import YesMetaZFC.SetTheory.Collapse.Uniqueness

/-! # Σ₁ 初等子结构的内部坍塌凝聚

先构造真实 Mostowski 图，再回拉 rud 运算和微层证书的存在见证。传递坍塌
因而是 rud 闭包且由微层覆盖，最后由规范截口识别为原 J 层。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem jc_condensation_l (hM : M.Models KPi) {a U X : M.Domain} (ha : M.IsOrdinal a)
    (hU : Jh_value_d a U) (s : S1_sub_d X U) :
    ∃ b B F, J_d b B ∧ Mc_iso_d X B F ∧
      ∀ x y, Rd_entry_d x y F ↔ M.mem x X ∧ Mc_value_d X x y := by
  let hKP := (KPi.models_iff_l.mp hM).1
  have hu := jh_value_transitive_l hM hU
  have closed := jh_value_closed_l hM ha hU
  obtain ⟨B, F, hb, hf, he⟩ := mc_collapse_l hM (s.extensional_l hKP.1 hu)
  have hn := hf.nonempty_l s.nonempty
  have hB := jc_rud_closed_l hKP hb hn (fun k η => hf.total_pull_l s hn (jc_rud_s k)
    (jc_rud_total_l hKP hu closed s.target_nonempty_l k) η)
  have cover := jc_cover_sound_l hKP hb hn (fun η => hf.total_pull_l s hn jc_cover_s
    (jc_cover_total_l hM ha hU s.target_nonempty_l) η)
  obtain ⟨b, h⟩ := jc_cut_l hM hB hb cover
  exact ⟨b, B, F, h, hf, he⟩

theorem jc_condensation_unique_l (hM : M.Models KPi) {X b c B D F G : M.Domain}
    (hb : J_d b B) (hc : J_d c D) (hf : Mc_iso_d X B F) (hg : Mc_iso_d X D G) : b = c ∧ B = D ∧ F = G := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨eq, hfg⟩ := mc_iso_unique_l hM hf hg (jh_value_transitive_l hM hb.2) (jh_value_transitive_l hM hc.2)
  subst D
  refine ⟨?_, rfl, hfg⟩
  rcases Structure.IsOrdinal.trichotomy hKP.1 hb.1 hc.1 (KP.difference_exists_d hKP)
    (KP.intersection_exists_d hKP b c) with he | hbc | hcb
  · exact hKP.1.eq_of_same_members b c he
  · exact (KP.mem_irrefl_d hKP B (jh_value_mem_l hM hbc hb.2 hc.2)).elim
  · exact (KP.mem_irrefl_d hKP B (jh_value_mem_l hM hcb hc.2 hb.2)).elim

end YesMetaZFC.SetTheory.InnerModel
