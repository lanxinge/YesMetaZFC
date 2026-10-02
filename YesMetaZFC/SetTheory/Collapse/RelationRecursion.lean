import YesMetaZFC.SetTheory.Collapse.RelationSyntax

/-! # 内部关系坍塌的唯一性与部分图装配

对原公式作关系归纳，先证明任意两个部分解相容。其后收集图可取并，并能添加
当前节点的像；全部证书仍是模型中的集合。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {X R : M.Domain} (hw : Wf_rel_d X R)
include hZF hw

theorem wc_value_unique_l {a x y} (hx : Wc_value_d X R a x) (hy : Wc_value_d X R a y) : x = y := by
  let ρ : Env M 2 := (⟨fun _ => X, fun _ => X⟩ : Env M 1).push R
  let φ : UnarySchema 2 := {
    body := .forallE (.forallE (.imp
      (.conj (wc_value_m (.bound 4) (.bound 3) (.bound 2) (.bound 1))
        (wc_value_m (.bound 4) (.bound 3) (.bound 2) .newest))
      (Formula.extensionalEq (.bound 1) .newest))) }
  have hφ a : φ.denote ρ a ↔ ∀ x y, Wc_value_d X R a x ∧ Wc_value_d X R a y → x = y := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, wc_value_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  have hall := wf_rel_ind_l hZF hw φ ρ (fun a _ ih => (hφ a).mpr (by
    rintro x y ⟨⟨F, hF, hax⟩, ⟨G, hG, hay⟩⟩
    have sub {F G x y} (hF : Wc_graph_d X R F) (hG : Wc_graph_d X R G)
        (hax : Rd_entry_d a x F) (hay : Rd_entry_d a y G) : M.MemberSubset x y := by
      intro z hz
      obtain ⟨b, hb, hba, hbz⟩ := ((hF.2 a x hax).2.2 z).mp hz
      obtain ⟨t, hbt⟩ := (hG.2 a y hay).2.1 b hb hba
      have he := (hφ b).mp (ih b hb hba) z t ⟨⟨F, hF, hbz⟩, ⟨G, hG, hbt⟩⟩
      exact he.symm ▸ ((hG.2 a y hay).2.2 t).mpr ⟨b, hb, hba, hbt⟩
    exact hZF.1.eq_of_same_members x y (fun z => ⟨sub hF hG hax hay z, sub hG hF hay hax z⟩)))
  have ha := hx.elim fun F h => (h.1.2 a x h.2).1
  exact (hφ a).mp (hall a ha) x y ⟨hx, hy⟩

theorem wc_value_equation_l {a x} (hx : Wc_value_d X R a x) (y) :
    M.mem y x ↔ ∃ b, M.mem b X ∧ Rd_entry_d b a R ∧ Wc_value_d X R b y := by
  obtain ⟨F, hF, hax⟩ := hx
  constructor
  · intro hy
    obtain ⟨b, hb, hba, hby⟩ := ((hF.2 a x hax).2.2 y).mp hy
    exact ⟨b, hb, hba, F, hF, hby⟩
  · rintro ⟨b, hb, hba, hy⟩
    obtain ⟨z, hbz⟩ := (hF.2 a x hax).2.1 b hb hba
    exact wc_value_unique_l hZF hw ⟨F, hF, hbz⟩ hy ▸
      ((hF.2 a x hax).2.2 z).mpr ⟨b, hb, hba, hbz⟩

omit hZF hw in
theorem wc_union_entry_l {C F : M.Domain} (hF : M.IsUnionOf F C) (a x) :
    Rd_entry_d a x F ↔ ∃ G, M.mem G C ∧ Rd_entry_d a x G :=
  ⟨fun ⟨p, hp, hpF⟩ => ((hF p).mp hpF).elim fun G h => ⟨G, h.1, p, hp, h.2⟩,
    fun ⟨G, hG, p, hp, hpG⟩ => ⟨p, hp, (hF p).mpr ⟨G, hG, hpG⟩⟩⟩

theorem wc_union_l {C F} (hC : ∀ G, M.mem G C → Wc_graph_d X R G) (hF : M.IsUnionOf F C) :
    Wc_graph_d X R F := by
  refine ⟨fun p hp => ((hF p).mp hp).elim fun G h => (hC G h.1).1 p h.2, ?_⟩
  intro a x hax
  obtain ⟨G, hG, hax⟩ := (wc_union_entry_l hF a x).mp hax
  have hg := hC G hG
  have step := (hg.2 a x hax).2
  refine ⟨(hg.2 a x hax).1, ?_, fun y => ?_⟩
  · intro b hb hba
    obtain ⟨y, hby⟩ := step.1 b hb hba
    exact ⟨y, (wc_union_entry_l hF b y).mpr ⟨G, hG, hby⟩⟩
  · constructor
    · intro hy
      obtain ⟨b, hb, hba, hby⟩ := (step.2 y).mp hy
      exact ⟨b, hb, hba, (wc_union_entry_l hF b y).mpr ⟨G, hG, hby⟩⟩
    · rintro ⟨b, hb, hba, hby⟩
      obtain ⟨H, hH, hby⟩ := (wc_union_entry_l hF b y).mp hby
      obtain ⟨z, hbz⟩ := step.1 b hb hba
      exact wc_value_unique_l hZF hw ⟨G, hg, hbz⟩ ⟨H, hC H hH, hby⟩ ▸
        (step.2 z).mpr ⟨b, hb, hba, hbz⟩

theorem wc_adjoin_l {F a x} (hF : Wc_graph_d X R F) (ha : M.mem a X)
    (hx : Wc_step_d X R F a x) : Wc_value_d X R a x := by
  obtain ⟨p, hp⟩ := (kp_pair_l (ZF.modelsKP hZF)).total a x
  obtain ⟨G, hG⟩ := KP.exists_insert (ZF.modelsKP hZF) F p
  have hg b y : Rd_entry_d b y G ↔ Rd_entry_d b y F ∨ (b = a ∧ y = x) := by
    constructor
    · rintro ⟨q, hq, hqG⟩
      rcases (hG q).mp hqG with hqF | rfl
      · exact Or.inl ⟨q, hq, hqF⟩
      · exact Or.inr (kpair_injective_l M hq hp)
    · rintro (⟨q, hq, hqF⟩ | ⟨rfl, rfl⟩)
      · exact ⟨q, hq, (hG q).mpr (Or.inl hqF)⟩
      · exact ⟨p, hp, (hG p).mpr (Or.inr rfl)⟩
  have agree {b y z} (hy : Rd_entry_d b y G) (hz : Rd_entry_d b z F) : y = z := by
    rcases (hg b y).mp hy with hy | ⟨rfl, rfl⟩
    · exact wc_value_unique_l hZF hw ⟨F, hF, hy⟩ ⟨F, hF, hz⟩
    · exact hZF.1.eq_of_same_members y z (fun t => (hx.2 t).trans ((hF.2 b z hz).2.2 t).symm)
  have step {b y} (hy : Wc_step_d X R F b y) : Wc_step_d X R G b y := by
    refine ⟨fun c hc hcb => ?_, fun t => ?_⟩
    · obtain ⟨z, hcz⟩ := hy.1 c hc hcb
      exact ⟨z, (hg c z).mpr (Or.inl hcz)⟩
    · constructor
      · intro ht
        obtain ⟨c, hc, hcb, hct⟩ := (hy.2 t).mp ht
        exact ⟨c, hc, hcb, (hg c t).mpr (Or.inl hct)⟩
      · rintro ⟨c, hc, hcb, hct⟩
        obtain ⟨z, hcz⟩ := hy.1 c hc hcb
        exact (agree hct hcz).symm ▸ (hy.2 z).mpr ⟨c, hc, hcb, hcz⟩
  refine ⟨G, ⟨?_, ?_⟩, (hg a x).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro q hq
    rcases (hG q).mp hq with hq | rfl
    · exact hF.1 q hq
    · exact ⟨a, x, hp⟩
  · intro b y hby
    rcases (hg b y).mp hby with hby | ⟨rfl, rfl⟩
    · exact ⟨(hF.2 b y hby).1, step (hF.2 b y hby).2⟩
    · exact ⟨ha, step hx⟩

end YesMetaZFC.SetTheory
