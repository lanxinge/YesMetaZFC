import YesMetaZFC.SetTheory.Collapse.RelationRecursion

/-! # ZF 内任意集合良基关系的实际坍塌

收集前驱的部分图、取并并添加下一值，随后把全部规范值收集成总图。
输出值域是传递集合；不要求关系外延，重复节点可坍塌为同一集合。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {X R : M.Domain}
include hZF

theorem wc_value_exists_l (hw : Wf_rel_d X R) {a} (ha : M.mem a X) : ∃ x, Wc_value_d X R a x := by
  let ρ : Env M 2 := (⟨fun _ => X, fun _ => X⟩ : Env M 1).push R
  let φ : UnarySchema 2 := { body := .existsE (wc_value_m (.bound 3) (.bound 2) (.bound 1) .newest) }
  have hφ a : φ.denote ρ a ↔ ∃ x, Wc_value_d X R a x := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, wc_value_sat_l hZF.1]; rfl
  apply (hφ a).mp
  apply wf_rel_ind_l hZF hw φ ρ _ a ha
  intro a ha ih
  apply (hφ a).mpr
  let δ := ρ.push a
  let pred : UnarySchema 3 := { body := rd_entry_m .newest (.bound 1) (.bound 2) }
  obtain ⟨D, hd⟩ := ZF.separation_exists_d hZF pred δ X
  have hD b : M.mem b D ↔ M.mem b X ∧ Rd_entry_d b a R := by
    simpa only [pred, rd_entry_sat_l hZF.1] using! hd b
  let cover : BinarySchema 2 := {
    body := .conj (wc_graph_m (.bound 3) (.bound 2) .newest)
      (.existsE (rd_entry_m (.bound 2) .newest (.bound 1))) }
  have hc b F : cover.denote ρ b F ↔ Wc_graph_d X R F ∧ ∃ y, Rd_entry_d b y F := by
    simp only [BinarySchema.denote, cover, Formula.satisfies_conj_iff, wc_graph_sat_l hZF.1,
      Formula.satisfies_exists_iff, rd_entry_sat_l hZF.1]; rfl
  obtain ⟨C₀, hC₀⟩ := ZF.collection_exists_d hZF cover ρ D (fun b hb => by
    obtain ⟨x, F, hF, hbx⟩ := (hφ b).mp (ih b ((hD b).mp hb).1 ((hD b).mp hb).2)
    exact ⟨F, (hc b F).mpr ⟨hF, x, hbx⟩⟩)
  let valid : UnarySchema 2 := { body := wc_graph_m (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hC'⟩ := ZF.separation_exists_d hZF valid ρ C₀
  have hC F : M.mem F C ↔ M.mem F C₀ ∧ Wc_graph_d X R F :=
    (hC' F).trans (and_congr_right fun _ => wc_graph_sat_l hZF.1 (ρ.push F) _ _ _)
  obtain ⟨F, hF⟩ := KP.exists_union (ZF.modelsKP hZF) C
  have hg := wc_union_l hZF hw (fun G hG => ((hC G).mp hG).2) hF
  have total b (hb : M.mem b X) (hba : Rd_entry_d b a R) : ∃ y, Rd_entry_d b y F := by
    obtain ⟨G, hG, hh⟩ := hC₀ b ((hD b).mpr ⟨hb, hba⟩)
    obtain ⟨hg, y, hby⟩ := (hc b G).mp hh
    exact ⟨y, (wc_union_entry_l hF b y).mpr ⟨G, (hC G).mpr ⟨hG, hg⟩, hby⟩⟩
  obtain ⟨V, hV⟩ := rd_fun_exists_l (ZF.modelsKP hZF) .range F F F
  let η := (ρ.push F).push a
  let image : UnarySchema 4 := {
    body := Formula.existsMem (.bound 4) (.conj (rd_entry_m .newest (.bound 2) (.bound 4))
      (rd_entry_m .newest (.bound 1) (.bound 3))) }
  have hi y : image.denote η y ↔ ∃ b, M.mem b X ∧ Rd_entry_d b a R ∧ Rd_entry_d b y F := by
    simp only [UnarySchema.denote, image, Formula.satisfies_existsMem_iff,
      Formula.satisfies_conj_iff, rd_entry_sat_l hZF.1]; rfl
  obtain ⟨x, hx⟩ := ZF.separation_exists_d hZF image η V
  have he y : M.mem y x ↔ ∃ b, M.mem b X ∧ Rd_entry_d b a R ∧ Rd_entry_d b y F :=
    (hx y).trans ((and_congr_right fun _ => hi y).trans
      ⟨And.right, fun ⟨b, hb, hba, hby⟩ => ⟨(hV y).mpr ⟨b, hby⟩, b, hb, hba, hby⟩⟩)
  exact ⟨x, wc_adjoin_l hZF hw hg ha ⟨total, he⟩⟩

/-- 总坍塌图、精确值域与传递性一次构造，不把其中任何一项作为前提。 -/
theorem wc_collapse_l (hw : Wf_rel_d X R) : ∃ T F, Fn0_d X T F ∧ Wc_graph_d X R F ∧
    (∀ x, M.mem x T ↔ ∃ a, Rd_entry_d a x F) ∧ M.TransitiveSet T := by
  let ρ : Env M 2 := (⟨fun _ => X, fun _ => X⟩ : Env M 1).push R
  let φ : BinarySchema 2 := { body := wc_value_m (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ a x : φ.denote ρ a x ↔ Wc_value_d X R a x := wc_value_sat_l hZF.1 _ _ _ _ _
  have total a (ha : M.mem a X) := (wc_value_exists_l hZF hw ha).imp fun x hx => (hφ a x).mpr hx
  have unique a (_ : M.mem a X) x y hx hy := wc_value_unique_l hZF hw ((hφ a x).mp hx) ((hφ a y).mp hy)
  obtain ⟨T, hT⟩ := ZF.exists_functionalImageOn hZF φ ρ X total unique
  obtain ⟨F, fn, hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ ρ
    total unique (fun a x ha hx => (hT x).mpr ⟨a, ha, hx⟩)
  have entry a x : Rd_entry_d a x F ↔ M.mem a X ∧ Wc_value_d X R a x :=
    (hf a x).trans (and_congr_right fun _ => hφ a x)
  have range x : M.mem x T ↔ ∃ a, Rd_entry_d a x F := (hT x).trans
    (exists_congr fun a => ((and_congr_right fun _ => hφ a x).trans (entry a x).symm))
  refine ⟨T, F, fn0_of_function_l (ZF.modelsKP hZF) fn, ⟨fn.1.1, ?_⟩, range, ?_⟩
  · intro a x hax
    obtain ⟨ha, hx⟩ := (entry a x).mp hax
    refine ⟨ha, fun b hb _ => (fn.2.2 b hb).imp fun _ h => h.2, fun y => ?_⟩
    exact (wc_value_equation_l hZF hw hx y).trans (exists_congr fun b => and_congr_right fun hb =>
      and_congr_right fun _ => ⟨fun hy => (entry b y).mpr ⟨hb, hy⟩, fun hy => ((entry b y).mp hy).2⟩)
  · intro x hx y hy
    obtain ⟨a, hax⟩ := (range x).mp hx
    obtain ⟨b, hb, _, hby⟩ := (wc_value_equation_l hZF hw ((entry a x).mp hax).2 y).mp hy
    exact (range y).mpr ⟨b, (entry b y).mpr ⟨hb, hby⟩⟩

/-- 任意实际全域坍塌图都反映内部良基性，供编码关系与模型间回拉使用。 -/
theorem wf_of_collapse_l {T F} (fn : Fn0_d X T F) (hg : Wc_graph_d X R F) : Wf_rel_d X R := by
  intro Y hY hn
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 1 := { body := rd_entry_m (.bound 1) .newest (.bound 2) }
  have hφ a x : φ.denote ρ a x ↔ Rd_entry_d a x F := rd_entry_sat_l hZF.1 _ _ _ _
  obtain ⟨Z, hZ⟩ := ZF.exists_functionalImageOn hZF φ ρ Y
    (fun a ha => (fn.2.1 a (hY a ha)).imp fun x hx => (hφ a x).mpr hx.2)
    (fun a ha x y hx hy => fn.2.2 a (hY a ha) x (fn.bound_l ((hφ a x).mp hx)).2
      y (fn.bound_l ((hφ a y).mp hy)).2 ((hφ a x).mp hx) ((hφ a y).mp hy))
  obtain ⟨a, ha⟩ := hn
  obtain ⟨x, _, hax⟩ := fn.2.1 a (hY a ha)
  obtain ⟨x, hx, hm⟩ := KP.mem_minimal_exists_d (ZF.modelsKP hZF) ⟨x, (hZ x).mpr ⟨a, ha, (hφ a x).mpr hax⟩⟩
  obtain ⟨a, ha, hax⟩ := (hZ x).mp hx
  refine ⟨a, ha, fun b hb hba => ?_⟩
  obtain ⟨y, _, hby⟩ := fn.2.1 b (hY b hb)
  exact hm y ((hZ y).mpr ⟨b, hb, (hφ b y).mpr hby⟩)
    (((hg.2 a x ((hφ a x).mp hax)).2.2 y).mpr ⟨b, hY b hb, hba, hby⟩)

end YesMetaZFC.SetTheory
