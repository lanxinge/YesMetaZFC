import YesMetaZFC.Model.Forcing.Stage.NameMap.Basic
import YesMetaZFC.Model.Forcing.Internal.Check.Model

/-! # 原 ZF 内的名称搬运存在定理

先收集全部子名称的部分递归图，再取并、分离加权像并加入当前根。内部条目
归纳的正文始终是实际原公式，故构造适用于外部非良基的任意地模型。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

/-- 任意关系对象的左坐标集合由二重并集分离得到，允许对象包含非有序对成员。 -/
theorem entry_domain_l (hZF : M.Models ZF) (x : M.Domain) :
    ∃ D, ∀ s, M.mem s D ↔ ∃ b, Entry_d M s b x := by
  obtain ⟨U, hU⟩ := KP.exists_union (ZF.modelsKP hZF) x
  obtain ⟨V, hV⟩ := KP.exists_union (ZF.modelsKP hZF) U
  let ρ : Env M 1 := ⟨fun _ => x, fun _ => x⟩
  let φ : UnarySchema 1 := { body := .existsE (entry_m (.bound 1) .newest (.bound 2)) }
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ V
  have hφ s : φ.denote ρ s ↔ ∃ b, Entry_d M s b x := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, entry_sat_l M hZF.1]
    rfl
  refine ⟨D, fun s => (hD s).trans ?_⟩
  change (M.mem s V ∧ φ.denote ρ s) ↔ _
  rw [hφ]
  refine ⟨And.right, fun ⟨b, p, hp, hpx⟩ => ?_⟩
  obtain ⟨a, hap, hsa⟩ := (kpair_union_l M hp s).mpr (Or.inl rfl)
  exact ⟨(hV s).mpr ⟨a, (hU a).mpr ⟨p, hpx, hap⟩, hsa⟩, b, p, hp, hpx⟩

private theorem nmap_image_l (hZF : M.Models ZF) (K H x : M.Domain) : ∃ t, ∀ v,
    M.mem v t ↔ ∃ s b a c, Entry_d M s b x ∧ Entry_d M s a H ∧ Entry_d M b c K ∧ KPair_d M v a c := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨A, hA⟩ := check_range_l M hZF H
  obtain ⟨C, hC⟩ := check_range_l M hZF K
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I A C
  let ρ : Env M 3 := ((⟨fun _ => K, fun _ => K⟩ : Env M 1).push H).push x
  let φ : BinarySchema 3 := {
    body := .existsE (.existsE (.conj (entry_m (.bound 1) .newest (.bound 4))
      (.conj (entry_m (.bound 1) (.bound 3) (.bound 5)) (entry_m .newest (.bound 2) (.bound 6))))) }
  have hφ a c : φ.denote ρ a c ↔ ∃ s b, Entry_d M s b x ∧ Entry_d M s a H ∧ Entry_d M b c K := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, entry_sat_l M hZF.1]
    rfl
  obtain ⟨t, ht⟩ := ZF.separation_exists_d hZF (UnarySchema.relationMember kpair_convention_l φ) ρ P
  refine ⟨t, fun v => (ht v).trans ?_⟩
  rw [hP v, Formula.satisfies_relationMember_iff I φ ρ v]
  constructor
  · rintro ⟨_, a, c, hv, h⟩
    obtain ⟨s, b, hs, ha, hc⟩ := (hφ a c).mp h
    exact ⟨s, b, a, c, hs, ha, hc, hv⟩
  · rintro ⟨s, b, a, c, hs, ha, hc, hv⟩
    exact ⟨⟨a, (hA a).mpr ⟨s, ha⟩, c, (hC c).mpr ⟨b, hc⟩, hv⟩,
      a, c, hv, (hφ a c).mpr ⟨s, b, hs, ha, hc⟩⟩

private theorem nmap_collect_l (hZF : M.Models ZF) (K x : M.Domain)
    (h : ∀ s b, Entry_d M s b x → ∃ t, Nmap_d M K s t) :
    ∃ C, (∀ H, M.mem H C → Nmap_graph_d M K H) ∧
      ∀ s b, Entry_d M s b x → ∃ H t, M.mem H C ∧ Entry_d M s t H := by
  obtain ⟨D, hD⟩ := entry_domain_l M hZF x
  let ρ : Env M 1 := ⟨fun _ => K, fun _ => K⟩
  let φ : BinarySchema 1 := {
    body := .conj (nmap_graph_m (.bound 2) .newest) (.existsE (entry_m (.bound 2) .newest (.bound 1))) }
  have hφ s H : φ.denote ρ s H ↔ Nmap_graph_d M K H ∧ ∃ t, Entry_d M s t H := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
      nmap_graph_sat_l M hZF.1, entry_sat_l M hZF.1]
    rfl
  obtain ⟨C₀, hc⟩ := ZF.collection_exists_d hZF φ ρ D (fun s hs => by
    obtain ⟨b, hs⟩ := (hD s).mp hs
    obtain ⟨t, H, hH, ht⟩ := h s b hs
    exact ⟨H, (hφ s H).mpr ⟨hH, t, ht⟩⟩)
  let ψ : UnarySchema 1 := { body := nmap_graph_m (.bound 1) .newest }
  obtain ⟨C, hC'⟩ := ZF.separation_exists_d hZF ψ ρ C₀
  have hC H : M.mem H C ↔ M.mem H C₀ ∧ Nmap_graph_d M K H :=
    (hC' H).trans (and_congr_right fun _ => nmap_graph_sat_l M hZF.1 (ρ.push H) _ _)
  refine ⟨C, fun H hH => ((hC H).mp hH).2, fun s b hs => ?_⟩
  obtain ⟨H, hH, hφH⟩ := hc s ((hD s).mpr ⟨b, hs⟩)
  obtain ⟨hH', t, ht⟩ := (hφ s H).mp hφH
  exact ⟨H, t, (hC H).mpr ⟨hH, hH'⟩, ht⟩

/-- 只消费原 ZF，一次构造任意标签关系的内部递归搬运图。 -/
theorem nmap_exists_l (hZF : M.Models ZF) (K x : M.Domain) : ∃ t, Nmap_d M K x t := by
  let ρ : Env M 1 := ⟨fun _ => K, fun _ => K⟩
  let φ : UnarySchema 1 := { body := .existsE (nmap_m (.bound 2) (.bound 1) .newest) }
  have hφ x : φ.denote ρ x ↔ ∃ t, Nmap_d M K x t := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, nmap_sat_l M hZF.1]
    rfl
  apply (hφ x).mp
  apply entry_ind_l (check_ind_l M hZF) φ ρ
  intro x ih
  apply (hφ x).mpr
  obtain ⟨C, hC, hc⟩ := nmap_collect_l M hZF K x (fun s b hs => (hφ s).mp (ih s b hs))
  obtain ⟨H, hH⟩ := KP.exists_union (ZF.modelsKP hZF) C
  have hg := nmap_union_l M hZF.1 (check_ind_l M hZF) hC hH
  obtain ⟨t, ht⟩ := nmap_image_l M hZF K H x
  refine ⟨t, nmap_adjoin_l M hZF.1 (check_ind_l M hZF) (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) hg ⟨?_, ht⟩⟩
  intro s b hs
  obtain ⟨J, a, hJ, ha⟩ := hc s b hs
  exact ⟨a, (entry_union_l M hH s a).mpr ⟨J, hJ, ha⟩⟩

/-- 递归图的值域直接给出目标名称的闭支撑。 -/
theorem nmap_name_l (hZF : M.Models ZF) {K Q x t}
    (hK : ∀ b c, Entry_d M b c K → M.mem c Q) (h : Nmap_d M K x t) : Name_d M Q t := by
  obtain ⟨H, hH, ht⟩ := h
  obtain ⟨W, hW⟩ := check_range_l M hZF H
  refine ⟨W, (hW t).mpr ⟨x, ht⟩, fun a ha v hva => ?_⟩
  obtain ⟨y, hya⟩ := (hW a).mp ha
  obtain ⟨s, b, c, d, _, hsc, hbd, hv⟩ := ((hH.2 y a hya).2 v).mp hva
  exact ⟨c, d, hv, (hW c).mpr ⟨s, hsc⟩, hK b d hbd⟩

end YesMetaZFC.Model.Forcing.Internal
