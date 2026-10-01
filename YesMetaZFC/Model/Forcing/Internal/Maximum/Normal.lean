import YesMetaZFC.Model.Forcing.Internal.Maximum.NormalSyntax

/-! # 任意内部名称的确定规范代表

同一全局力迫等号类的最早层候选集唯一。候选名称图的并仍是名称，并通过
原子力迫的双向匹配方程证明与原名称全局相等；全过程不选择候选中的元素。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem norm_name_l (hZF : M.Models ZF) {t q} (ht : Name_d M B t)
    (h : Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t q) :
    Name_d M B q ∧ All_eq_d M B R z q t := by
  obtain ⟨α, S, ⟨_, _, hn, hS, _⟩, hU⟩ := h
  have names s (hs : M.mem s S) : Name_d M B s ∧ All_eq_d M B R z s t :=
    (norm_pred_sat_l M hZF.1 (norm_env_l M B R z t) s).mp (((hS s).mp hs).2)
  have hq : Name_d M B q := (name_unfold_l M (name_ops_l M hZF) B q).mpr (by
    intro v hv
    obtain ⟨s, hs, hvs⟩ := (hU v).mp hv
    exact (name_unfold_l M (name_ops_l M hZF) B s).mp (names s hs).1 v hvs)
  refine ⟨hq, fun p hp hz => (eq_force_unfold_l M hZF hq ht).mpr ⟨hp, ?_, ?_⟩⟩
  · intro a b hab
    obtain ⟨s, hs, hab⟩ := (entry_union_l M hU a b).mp hab
    exact ((eq_force_unfold_l M hZF (names s hs).1 ht).mp ((names s hs).2 p hp hz)).2.1 a b hab
  · obtain ⟨s, hs⟩ := hn
    intro a b hab r hr hrb
    obtain ⟨v, d, c, hv, hdc, hvc, he⟩ :=
      ((eq_force_unfold_l M hZF (names s hs).1 ht).mp ((names s hs).2 p hp hz)).2.2 a b hab r hr hrb
    exact ⟨v, d, c, hv, (entry_union_l M hU d c).mpr ⟨s, hs, hdc⟩, hvc, he⟩

theorem norm_name_unique_l (hZF : M.Models ZF) {t q r}
    (hq : Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t q)
    (hr : Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t r) : q = r := by
  obtain ⟨α, S, hS, hq⟩ := hq
  obtain ⟨β, T, hT, hr⟩ := hr
  obtain ⟨_, he⟩ := ZF.v_min_unique_l _ hZF hS hT
  subst T
  exact hq.eq hZF.1 hr

/-- 全局被迫相等的输入名称具有完全相同的规范构造关系。 -/
theorem norm_name_class_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {s t}
    (hs : Name_d M B s) (ht : Name_d M B t) (hst : All_eq_d M B R z s t) (q) :
    Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z s q ↔
      Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t q := by
  have hc x : norm_pred_s.denote (norm_env_l M B R z s) x ↔ norm_pred_s.denote (norm_env_l M B R z t) x := by
    rw [norm_pred_sat_l M hZF.1, norm_pred_sat_l M hZF.1]
    change (Name_d M B x ∧ All_eq_d M B R z x s) ↔ (Name_d M B x ∧ All_eq_d M B R z x t)
    refine and_congr_right fun hx => ⟨?_, ?_⟩
    · exact fun h p hp hz => eq_force_trans_l O hZF hx hs ht (h p hp hz) (hst p hp hz)
    · exact fun h p hp hz => eq_force_trans_l O hZF hx ht hs (h p hp hz) (eq_force_symm_l hZF hs ht (hst p hp hz))
  exact exists_congr fun α => exists_congr fun S => and_congr_left fun _ => v_min_congr_l _ hc α S

/-- 一次给出规范名称、规范幂等证书和与输入的全局等号；只需原 ZF。 -/
theorem norm_name_exists_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {t} (ht : Name_d M B t) :
    ∃ q, Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t q ∧
      Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z q q ∧
      Name_d M B q ∧ All_eq_d M B R z q t := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨α, S, hS⟩ := ZF.v_min_exists_l I hZF norm_pred_s (norm_env_l M B R z t)
    ⟨t, (norm_pred_sat_l M hZF.1 _ t).mpr ⟨ht, fun p hp _ => eq_force_refl_l O hZF hp ht⟩⟩
  obtain ⟨q, hq⟩ := KP.exists_union (ZF.modelsKP hZF) S
  have hn : Norm_name_d M I B R z t q := ⟨α, S, hS, hq⟩
  obtain ⟨hqN, he⟩ := norm_name_l hZF ht hn
  exact ⟨q, hn, (norm_name_class_l O hZF hqN ht he q).mpr hn, hqN, he⟩

theorem norm_name_congr_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {s t q r}
    (hs : Name_d M B s) (ht : Name_d M B t) (hst : All_eq_d M B R z s t)
    (hq : Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z s q)
    (hr : Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t r) : q = r :=
  norm_name_unique_l hZF ((norm_name_class_l O hZF hs ht hst q).mp hq) hr

end YesMetaZFC.Model.Forcing.Internal
