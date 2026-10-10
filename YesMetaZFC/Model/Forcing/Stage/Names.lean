import YesMetaZFC.Model.Forcing.Stage.NameMap.Composition
import YesMetaZFC.Model.Forcing.Stage.NameMap.Identity
import YesMetaZFC.Model.Forcing.Stage.Composition

/-! # 阶段完全嵌入的名称搬运

实际嵌入图直接充当标签映射，自动构造目标名称及唯一性。嵌入图复合与名称
搬运复合严格一致，为阶段系统提供不依赖代表元选择的名称过渡。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u
variable {M : SetTheory.Structure.{u}} {P R z Q S w T V v F G : M.Domain}

theorem stage_nmap_l (hZF : M.Models ZF) (h : Reg_embed_d M P R z Q S w F) (x : M.Domain) :
    ∃ t, Nmap_d M F x t ∧ Name_d M Q t ∧ ∀ s, Nmap_d M F x s → s = t := by
  obtain ⟨t, ht⟩ := nmap_exists_l M hZF F x
  exact ⟨t, ht, nmap_name_l M hZF (fun b c hc => (h.domain b c hc).2.2.1) ht,
    fun s hs => nmap_unique_l M hZF.1 (check_ind_l M hZF) F x s t hs ht⟩

/-- 恒等阶段自动得到名称商所需的等号力迫，允许源条件集中含零元。 -/
theorem stage_nmap_id_l (hZF : M.Models ZF) (O : Cond_order_d M P R z) :
    ∃ F, Reg_embed_d M P R z P R z F ∧ ∀ x t, Name_d M P x → Nmap_d M F x t →
      ∀ p, M.mem p P → Eq_force_d M P R z p x t := by
  obtain ⟨F, hF, h⟩ := reg_embed_id_l hZF O
  exact ⟨F, h, fun x t hx ht p hp => nmap_id_force_l O hZF hF hx ht hp⟩

/-- 两次阶段搬运恰好等于实际复合图上的一次搬运，包含全部名称。 -/
theorem stage_nmap_comp_l (hZF : M.Models ZF) (L : Cond_order_d M T V v)
    (h : Reg_embed_d M P R z Q S w F) (k : Reg_embed_d M Q S w T V v G) :
    ∃ H, Reg_embed_d M P R z T V v H ∧
      (∀ b c, Entry_d M b c H ↔ ∃ a, Entry_d M b a F ∧ Entry_d M a c G) ∧
      ∀ x t, Nmap_d M H x t ↔ ∃ s, Nmap_d M F x s ∧ Nmap_d M G s t := by
  obtain ⟨H, hH, he⟩ := reg_embed_comp_l hZF L h k
  refine ⟨H, he, hH, fun x t => ⟨?_, ?_⟩⟩
  · intro ht
    obtain ⟨s, hs⟩ := nmap_exists_l M hZF F x
    obtain ⟨a, ha⟩ := nmap_exists_l M hZF G s
    have he := nmap_unique_l M hZF.1 (check_ind_l M hZF) H x a t (nmap_comp_l hZF hH hs ha) ht
    exact ⟨s, hs, he ▸ ha⟩
  · rintro ⟨s, hs, ht⟩
    exact nmap_comp_l hZF hH hs ht

end YesMetaZFC.Model.Forcing.Internal
