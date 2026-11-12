import YesMetaZFC.Model.Forcing.Ground.Collapse
import YesMetaZFC.SetTheory.Card.Cofinality.Countable
import YesMetaZFC.Model.Forcing.Names.SequenceForcing
import YesMetaZFC.Model.Forcing.Extension.Choice
import YesMetaZFC.SetTheory.Rank

/-! # 旧集合嵌入下的序数反射与共尾集保持

成员完全的单射可将目标的序数良序性回拉到所有旧子集；正向良序性使用目标基础公理。
共尾集的传输只核验极限性、包含及并集，不预设任何共尾度保持。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory
universe u v
variable {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
variable (e : M.Domain → N.Domain) (hi : Function.Injective e)
  (he : ∀ a y, N.mem y (e a) ↔ ∃ x, M.mem x a ∧ e x = y)
include hi he

theorem image_ordinal_reflect_l (hEN : Extensional N) {α} (hα : N.IsOrdinal (e α)) : M.IsOrdinal α := by
  have eq {a b} (h : N.SameMembers (e a) (e b)) : M.SameMembers a b := by
    have h := hi (hEN.eq_of_same_members (e a) (e b) h)
    exact h ▸ fun _ => Iff.rfl
  have mem {a b} := image_member_l e hi he (a := a) (b := b)
  refine ⟨fun x hx y hy => mem.mp (hα.transitive (e x) (mem.mpr hx) (e y) (mem.mpr hy)), ⟨?_, ?_⟩⟩
  · refine ⟨fun x hx hxx => hα.wellOrder.linear.irrefl (e x) (mem.mpr hx) (mem.mpr hxx),
      fun x hx y hy z hz hxy hyz => mem.mp (hα.wellOrder.linear.trans (e x) (mem.mpr hx)
        (e y) (mem.mpr hy) (e z) (mem.mpr hz) (mem.mpr hxy) (mem.mpr hyz)), ?_⟩
    intro x hx y hy
    rcases hα.wellOrder.linear.compare (e x) (mem.mpr hx) (e y) (mem.mpr hy) with h | h | h
    · exact Or.inl (eq h)
    · exact Or.inr (Or.inl (mem.mp h))
    · exact Or.inr (Or.inr (mem.mp h))
  · intro X hX hn
    obtain ⟨x, hx⟩ := hn
    obtain ⟨y, hy, hm⟩ := hα.wellOrder.least (e X) (by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := (he X y).mp hy
      exact mem.mpr (hX a ha)) ⟨e x, mem.mpr hx⟩
    obtain ⟨a, ha, rfl⟩ := (he X y).mp hy
    exact ⟨a, ha, fun b hb => (hm (e b) (mem.mpr hb)).elim (fun h => Or.inl (eq h)) (fun h => Or.inr (mem.mp h))⟩

theorem image_cofinal_subset_l (hEM : Extensional M)
    (hF : ∀ X, (∃ x, N.mem x X) → ∃ x, N.mem x X ∧ ∀ y, N.mem y X → ¬ N.mem y x)
    {A α} (hA : M.IsCofinalSubset A α) : N.IsCofinalSubset (e A) (e α) := by
  have mem {a b} := image_member_l e hi he (a := a) (b := b)
  have hα := image_ordinal_l e hi he hEM hF hA.1.1
  refine ⟨⟨hα, ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hA.1.2.1
    exact ⟨e x, mem.mpr hx⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (he α y).mp hy
    obtain ⟨z, hz, hxz⟩ := hA.1.2.2 x hx
    exact ⟨e z, mem.mpr hz, mem.mpr hxz⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (he A y).mp hy
    exact mem.mpr (hA.2.1 x hx)
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := (he α y).mp hy
      obtain ⟨z, hz, hxz⟩ := (hA.2.2 x).mp hx
      exact ⟨e z, mem.mpr hz, mem.mpr hxz⟩
    · rintro ⟨z, hz, hyz⟩
      obtain ⟨a, ha, rfl⟩ := (he A z).mp hz
      exact hα.transitive (e a) (mem.mpr (hA.2.1 a ha)) y hyz

end YesMetaZFC.Model.Forcing.Internal

/-! ## 名称支撑的内部秩图与求值图

秩图在地模型内构造，求值图由已有逐坐标名称装配得到。两者都是实际集合，
因此随后可在扩张内部对原公式归纳，而不对外部名称关系作良基归纳。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem name_rank_graph_l (S : M.Domain) : ∃ A F,
    M.IsSetFunctionFromTo I F S A ∧ ∀ s α, Entry_d M s α F ↔ M.mem s S ∧ Rk_d I s α := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => S⟩
  let φ : BinarySchema 0 := { body := rk_m (𝒞 := kpair_convention_l) (.bound 1) .newest }
  have hφ s α : φ.denote ρ s α ↔ Rk_d I s α := rk_sat_l I hZF.1 _ _ _
  have total s (_ : M.mem s S) : ∃ α, φ.denote ρ s α :=
    (ZF.rk_exists_l I hZF s).elim fun α hα => ⟨α, (hφ s α).mpr hα⟩
  have unique s (_ : M.mem s S) α β (hα : φ.denote ρ s α) (hβ : φ.denote ρ s β) : α = β :=
    rk_unique_l I hZF.1 ((hφ s α).mp hα) ((hφ s β).mp hβ)
  obtain ⟨A, hA⟩ := ZF.exists_functionalImageOn hZF φ ρ S total unique
  obtain ⟨F, hF, hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun s α hs hα => (hA α).mpr ⟨s, hs, hα⟩)
  exact ⟨A, F, hF, fun s α => (hf s α).trans (and_congr_right fun _ => hφ s α)⟩

/-- 条目左坐标沿三条成员边下降，故普通集合秩严格减小。 -/
theorem name_rank_drop_l {s b t α β} (hs : Rk_d I s α) (ht : Rk_d I t β)
    (h : Entry_d M s b t) : M.mem α β := by
  obtain ⟨p, hp, hpt⟩ := h
  obtain ⟨a, hap, hsa⟩ := (kpair_union_l M hp s).mpr (Or.inl rfl)
  obtain ⟨γ, hγ⟩ := ZF.rk_exists_l I hZF p
  obtain ⟨δ, hδ⟩ := ZF.rk_exists_l I hZF a
  exact ht.ordinal.transitive γ (ZF.rk_member_l I hZF hγ ht hpt) α
    (hγ.ordinal.transitive δ (ZF.rk_member_l I hZF hδ hγ hap) α (ZF.rk_member_l I hZF hs hδ hsa))

variable {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hU : Generic_d M B R z U)
local notation "E" => extension_l M hZF B R z U
include O hU

/-- 支撑中每个名称的求值，组成扩张内以旧支撑为定义域的实际关系图。 -/
theorem support_values_l {b S} (hb : M.mem b B) (hS : Supp_d M B S)
    (e : M.Domain → (E).Domain)
    (hv : ∀ x t, Check_d M b x t → Qval_d M B R z U t (e x)) :
    ∃ V : (E).Domain, ∀ x y, Entry_d E x y V ↔
      ∃ s, M.mem s S ∧ e s = x ∧ Qval_d M B R z U s y := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => S⟩
  let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  have hφ s t : φ.denote ρ s t ↔ t = s := Formula.satisfies_extensionalEq_iff_eq hZF.1 _ _ _
  obtain ⟨F, hF, hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := S) (target := S)
    (fun s _ => ⟨s, (hφ s s).mpr rfl⟩)
    (fun s _ t v ht hv => ((hφ s t).mp ht).trans ((hφ s v).mp hv).symm)
    (fun s t hs ht => ((hφ s t).mp ht).symm ▸ hs)
  have he s t : Entry_d M s t F ↔ M.mem s S ∧ t = s :=
    (hf s t).trans (and_congr_right fun _ => hφ s t)
  obtain ⟨t, ht⟩ := nseq_exists_l M hZF hb hF (fun s v hsv => by
    obtain ⟨hs, rfl⟩ := (he s v).mp hsv
    exact ⟨S, hs, hS⟩)
  obtain ⟨V, hV⟩ := name_value_l (R := R) (z := z) (U := U) ht.1
  have h := (nseq_value_l O hZF hU hb ht hV e hv).2
  refine ⟨V, fun x y => (h x y).trans ?_⟩
  constructor
  · rintro ⟨s, v, hsv, hsx, hvy⟩
    obtain ⟨hs, rfl⟩ := (he s v).mp hsv
    exact ⟨v, hs, hsx, hvy⟩
  · rintro ⟨s, hs, hsx, hsy⟩
    exact ⟨s, s, (he s s).mpr ⟨hs, rfl⟩, hsx, hsy⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 泛型扩张不增加序数

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
