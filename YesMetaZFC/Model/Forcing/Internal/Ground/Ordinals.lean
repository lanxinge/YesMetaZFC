import YesMetaZFC.Model.Forcing.Internal.Ground.NameRank

/-! # 泛型扩张不增加序数

在扩张内部对旧名称作条目归纳。支撑求值图与地模型秩图是归纳公式的集合参数，
得到序数值不超过原名称的旧秩。旧序数的成员全来自地模型，故每个扩张序数均为旧序数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

/-- 序数的包含关系只能是相等或严格隶属；供秩界与序数集合界共同使用。 -/
theorem ordinal_subset_cases_l {N : SetTheory.Structure.{u}} (hKP : N.Models KP)
    {α β} (hα : N.IsOrdinal α) (hβ : N.IsOrdinal β) (h : N.MemberSubset α β) :
    α = β ∨ N.mem α β := by
  classical
  by_cases he : N.SameMembers α β
  · exact Or.inl (hKP.1.eq_of_same_members α β he)
  · exact Or.inr (Structure.IsOrdinal.mem_of_properSubset hKP.1 hα hβ ⟨h, he⟩
      (KP.difference_exists_d hKP α β))

variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))
variable {b : M.Domain} (hb : M.mem b B) (e : M.Domain → (extension_l M hZF B R z U).Domain)
  (hv : ∀ x t, Check_d M b x t → Qval_d M B R z U t (e x))
  (he : ∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) (hi : Function.Injective e)
include O hU hb hv he hi

/-- 序数名称的值不超过其在地模型中的普通集合秩。 -/
theorem ordinal_name_bound_l {t α} {x : (E).Domain} (ht : Qval_d M B R z U t x)
    (hx : (E).IsOrdinal x) (hα : Rk_d I t α) : (E).MemberSubset x (e α) := by
  let hE := preserves_zf_l O hZF hU
  let hP := KP.exists_pair (ZF.modelsKP hZF)
  have ord {β} (hβ : M.IsOrdinal β) : (E).IsOrdinal (e β) :=
    image_ordinal_l e hi he hZF.1 (internal_foundation_l O hZF hU) hβ
  obtain ⟨S, htS, hS⟩ := qval_name_l ht
  obtain ⟨A, F, hF, hf⟩ := name_rank_graph_l hZF S
  obtain ⟨V, hV⟩ := support_values_l hZF O hU hb hS e hv
  let ρ : Env E 3 := ((⟨fun _ => e S, fun _ => V⟩ : Env E 1).push (e F)).push V
  let φ : UnarySchema 3 := {
    body := .imp (.mem .newest (.bound 3)) (.forallE (.forallE
      (.imp (entry_m (.bound 2) (.bound 1) (.bound 3))
        (.imp (entry_m (.bound 2) .newest (.bound 4))
          (.imp (Formula.isOrdinal (.bound 1)) (Formula.subset (.bound 1) .newest))))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have hφ a : φ.denote ρ a ↔ (a ∈ e S → ∀ y β,
      Entry_d E a y V → Entry_d E a β (e F) → (E).IsOrdinal y → (E).MemberSubset y β) := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, entry_sat_l E hE.1, Formula.satisfies_isOrdinal_iff,
      Formula.satisfies_subset_iff]
    rfl
  have hall := entry_ind_l (check_ind_l E hE) φ ρ (fun a ih => (hφ a).mpr (by
    intro ha y β hay haβ hy
    obtain ⟨s, hs, rfl⟩ := (he S a).mp ha
    obtain ⟨s', _, hss', hsy⟩ := (hV (e s) y).mp hay
    have hss : s' = s := hi hss'
    subst s'
    obtain ⟨s', γ, hsg, hss', hγβ⟩ := (image_entries_l e he hF.1.1 (e s) β).mp haβ
    have hss : s' = s := hi hss'
    subst s' β
    have hγ := ((hf s γ).mp hsg).2
    intro δ hδ
    obtain ⟨v, c, hvc, _, hvδ⟩ := (qval_mem_l O hZF hU hsy).mp hδ
    have hvS := (supp_entry_l M hS hs hvc).1
    obtain ⟨ε, _, hvε⟩ := hF.2.2 v hvS
    have hε := ((hf v ε).mp hvε).2
    have hv' := (image_entry_iff_l e hi he hP hE.1 v c s).mp hvc
    have bound := (hφ (e v)).mp (ih (e v) (e c) hv') ((he S (e v)).mpr ⟨v, hvS, rfl⟩)
      δ (e ε) ((hV (e v) δ).mpr ⟨v, hvS, rfl, hvδ⟩)
      ((image_entry_iff_l e hi he hP hE.1 v ε F).mp hvε) (hy.mem hδ)
    have hεγ := (image_member_l e hi he).mpr (name_rank_drop_l hZF hε hγ hvc)
    rcases ordinal_subset_cases_l (ZF.modelsKP hE) (hy.mem hδ) (ord hε.ordinal) bound with hh | hh
    · exact hh.symm ▸ hεγ
    · exact (ord hγ.ordinal).transitive (e ε) hεγ δ hh))
  obtain ⟨β, _, htβ⟩ := hF.2.2 t htS
  have hβα := rk_unique_l I hZF.1 ((hf t β).mp htβ).2 hα
  subst β
  exact (hφ (e t)).mp (hall (e t)) ((he S (e t)).mpr ⟨t, htS, rfl⟩) x (e α)
    ((hV (e t) x).mpr ⟨t, htS, rfl, ht⟩) ((image_entry_iff_l e hi he hP hE.1 t α F).mp htβ) hx

/-- 每个扩张序数都有地模型序数原像，不要求模型在外部良基。 -/
theorem no_new_ordinals_l {x : (E).Domain} (hx : (E).IsOrdinal x) :
    ∃ α, M.IsOrdinal α ∧ e α = x := by
  obtain ⟨t, _, ht⟩ := value_name_l x
  obtain ⟨β, hβ⟩ := ZF.rk_exists_l I hZF t
  have hβE := image_ordinal_l e hi he hZF.1 (internal_foundation_l O hZF hU) hβ.ordinal
  have bound := ordinal_name_bound_l O hZF hU hb e hv he hi ht hx hβ
  rcases ordinal_subset_cases_l (ZF.modelsKP (preserves_zf_l O hZF hU)) hx hβE bound with hh | hh
  · exact ⟨β, hβ.ordinal, hh.symm⟩
  · obtain ⟨α, hα, hαx⟩ := (he β x).mp hh
    exact ⟨α, hβ.ordinal.mem hα, hαx⟩

omit hb e hv he hi in
/-- 一次取得实际地嵌入及全部序数的覆盖性。 -/
theorem check_map_ordinals_l {b} (hb : U b) : ∃ e : M.Domain → (E).Domain,
    (∀ x t, Check_d M b x t → Qval_d M B R z U t (e x)) ∧
    (∀ a y, y ∈ e a ↔ ∃ x, M.mem x a ∧ e x = y) ∧ Function.Injective e ∧
    ∀ x, (E).IsOrdinal x ↔ ∃ α, M.IsOrdinal α ∧ e α = x := by
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hZF hU hb
  refine ⟨e, hv, he, hi, fun x => ⟨no_new_ordinals_l O hZF hU (hU.proper b hb).1 e hv he hi, ?_⟩⟩
  rintro ⟨α, hα, rfl⟩
  exact image_ordinal_l e hi he hZF.1 (internal_foundation_l O hZF hU) hα

end YesMetaZFC.Model.Forcing.Internal
