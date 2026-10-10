import YesMetaZFC.Model.Forcing.TwoStep.Flatten.Recursion

/-! # 原 ZF 内二步名称摊平的实际构造

固定深度的子名称集合收集部分递归图；其并的值域与二步条件集作笛卡尔积，
按真实关系力迫分离当前值，再添入当前根。目标名称支撑直接取递归图的值域。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

private theorem flat_image_l (hZF : M.Models ZF) (B R z C H x : M.Domain) : ∃ t, ∀ v,
    M.mem v t ↔ ∃ a c p s u, Entry_path_d M 3 x a ∧ M.mem c C ∧ KPair_d M c p s ∧
      Rel_force_d M B R z x p a s ∧ Entry_d M a u H ∧ KPair_d M v u c := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨A, hA⟩ := check_range_l M hZF H
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I A C
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push H).push x
  let φ : BinarySchema 5 := {
    body := .existsE (.existsE (.existsE (.conj (entry_path_m 3 (.bound 5) (.bound 2))
      (.conj (kpair_m (.bound 3) (.bound 1) .newest)
        (.conj (rel_force_m (.bound 9) (.bound 8) (.bound 7) (.bound 5) (.bound 1) (.bound 2) .newest)
          (entry_m (.bound 2) (.bound 4) (.bound 6))))))) }
  have hφ u c : φ.denote ρ u c ↔ ∃ a p s, Entry_path_d M 3 x a ∧ KPair_d M c p s ∧
      Rel_force_d M B R z x p a s ∧ Entry_d M a u H := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      entry_path_sat_l hZF.1, kpair_sat_l M hZF.1, rel_force_sat_l M hZF.1, entry_sat_l M hZF.1]
    rfl
  obtain ⟨t, ht⟩ := ZF.separation_exists_d hZF (UnarySchema.relationMember kpair_convention_l φ) ρ P
  refine ⟨t, fun v => (ht v).trans ?_⟩
  rw [hP v, Formula.satisfies_relationMember_iff I φ ρ v]
  constructor
  · rintro ⟨⟨u, _, c, hc, hv⟩, u', c', hv', hφ'⟩
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hv hv'
    obtain ⟨a, p, s, ha, hcp, hf, hau⟩ := (hφ u c).mp hφ'
    exact ⟨a, c, p, s, u, ha, hc, hcp, hf, hau, hv⟩
  · rintro ⟨a, c, p, s, u, ha, hc, hcp, hf, hau, hv⟩
    exact ⟨⟨u, (hA u).mpr ⟨a, hau⟩, c, hc, hv⟩, u, c, hv, (hφ u c).mpr ⟨a, p, s, ha, hcp, hf, hau⟩⟩

private theorem flat_collect_l (hZF : M.Models ZF) (B R z C x : M.Domain)
    (h : ∀ a, Entry_path_d M 3 x a → ∃ t, Flat_d M B R z C a t) :
    ∃ D, (∀ H, M.mem H D → Flat_graph_d M B R z C H) ∧
      ∀ a, Entry_path_d M 3 x a → ∃ H t, M.mem H D ∧ Entry_d M a t H := by
  obtain ⟨A, hA⟩ := entry_path_set_l M hZF 3 x
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push C
  let φ : BinarySchema 4 := {
    body := .conj (flat_graph_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest)
      (.existsE (entry_m (.bound 2) .newest (.bound 1))) }
  have hφ a H : φ.denote ρ a H ↔ Flat_graph_d M B R z C H ∧ ∃ t, Entry_d M a t H := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
      flat_graph_sat_l M hZF.1, entry_sat_l M hZF.1]
    rfl
  obtain ⟨D₀, hd⟩ := ZF.collection_exists_d hZF φ ρ A (fun a ha => by
    obtain ⟨t, H, hH, ht⟩ := h a ((hA a).mp ha)
    exact ⟨H, (hφ a H).mpr ⟨hH, t, ht⟩⟩)
  let ψ : UnarySchema 4 := { body := flat_graph_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨D, hD'⟩ := ZF.separation_exists_d hZF ψ ρ D₀
  have hD H : M.mem H D ↔ M.mem H D₀ ∧ Flat_graph_d M B R z C H :=
    (hD' H).trans (and_congr_right fun _ => flat_graph_sat_l M hZF.1 (ρ.push H) _ _ _ _ _)
  refine ⟨D, fun H hH => ((hD H).mp hH).2, fun a ha => ?_⟩
  obtain ⟨H, hH, hφH⟩ := hd a ((hA a).mpr ha)
  obtain ⟨hH', t, ht⟩ := (hφ a H).mp hφH
  exact ⟨H, t, (hD H).mpr ⟨hH, hH'⟩, ht⟩

/-- 只需原 ZF，任意输入对象都有实际内部摊平递归图。 -/
theorem flat_exists_l (hZF : M.Models ZF) (B R z C x : M.Domain) : ∃ t, Flat_d M B R z C x t := by
  let hI : Mem_ind_d M := check_ind_l M hZF
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push C
  let φ : UnarySchema 4 := {
    body := .existsE (flat_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  have hφ x : φ.denote ρ x ↔ ∃ t, Flat_d M B R z C x t := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, flat_sat_l M hZF.1]
    rfl
  apply (hφ x).mp
  apply entry_path_ind_l hZF.1 hI 3 (by decide) φ ρ
  intro x ih
  apply (hφ x).mpr
  obtain ⟨D, hD, hd⟩ := flat_collect_l M hZF B R z C x (fun a ha => (hφ a).mp (ih a ha))
  obtain ⟨H, hH⟩ := KP.exists_union (ZF.modelsKP hZF) D
  have hg := flat_union_l M hZF.1 hI hD hH
  obtain ⟨t, ht⟩ := flat_image_l M hZF B R z C H x
  refine ⟨t, flat_adjoin_l M hZF.1 hI (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) hg ⟨?_, ht⟩⟩
  intro a ha
  obtain ⟨J, u, hJ, hau⟩ := hd a ha
  exact ⟨u, (entry_union_l M hH a u).mpr ⟨J, hJ, hau⟩⟩

/-- 摊平图的值域本身是目标名称的闭支撑，不增加任何外部递归实例。 -/
theorem flat_name_l (hZF : M.Models ZF) {B R z C x t} (h : Flat_d M B R z C x t) : Name_d M C t := by
  obtain ⟨H, hH, ht⟩ := h
  obtain ⟨Z, hZ⟩ := check_range_l M hZF H
  refine ⟨Z, (hZ t).mpr ⟨x, ht⟩, fun u hu v hv => ?_⟩
  obtain ⟨a, hau⟩ := (hZ u).mp hu
  obtain ⟨d, c, p, s, w, _, hc, _, _, hdw, hv⟩ := ((hH.2 a u hau).2 v).mp hv
  exact ⟨w, c, hv, (hZ w).mpr ⟨d, hdw⟩, hc⟩

end YesMetaZFC.Model.Forcing.Internal
