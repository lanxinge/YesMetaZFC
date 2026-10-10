import YesMetaZFC.Model.Forcing.Internal.Names.Sequence
import YesMetaZFC.Model.Forcing.Internal.Extension.ZF
import YesMetaZFC.Model.Forcing.Internal.Ground.Cofinality
import YesMetaZFC.SetTheory.Rank

/-! # 名称支撑的内部秩图与求值图

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
