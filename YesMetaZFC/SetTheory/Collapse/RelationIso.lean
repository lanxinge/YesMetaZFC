import YesMetaZFC.SetTheory.Collapse.RelationExistence

/-! # 良基外延关系的 Mostowski 同构

对内部关系归纳证明坍塌值单射，再把既有总坍塌图提升为到传递集合的双射。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Wc_ext_d (X R : M.Domain) : Prop := ∀ a, M.mem a X → ∀ b, M.mem b X →
  (∀ z, M.mem z X → (Rd_entry_d z a R ↔ Rd_entry_d z b R)) → a = b

theorem Wc_graph_d.member_l {X R F B a b x y : M.Domain} (h : Wc_graph_d X R F)
    (hf : Fn0_d X B F) (inj : ∀ a b y, Rd_entry_d a y F → Rd_entry_d b y F → a = b)
    (ha : Rd_entry_d a x F) (hb : Rd_entry_d b y F) : Rd_entry_d a b R ↔ M.mem x y := by
  refine ⟨fun hab => ((h.2 b y hb).2.2 x).mpr ⟨a, (hf.bound_l ha).1, hab, ha⟩, fun hxy => ?_⟩
  obtain ⟨z, _, hzb, hz⟩ := ((h.2 b y hb).2.2 x).mp hxy
  exact inj z a x hz ha ▸ hzb

theorem wc_value_injective_l (hZF : M.Models ZF) {X R a b y : M.Domain}
    (hw : Wf_rel_d X R) (he : Wc_ext_d X R) (ha : M.mem a X) (hb : M.mem b X)
    (h : Wc_value_d X R a y) (g : Wc_value_d X R b y) : a = b := by
  let ρ : Env M 2 := (⟨fun _ => X, fun _ => X⟩ : Env M 1).push R
  let φ : UnarySchema 2 := { body := .forallE (.forallE
    (.imp (.mem (.bound 1) (.bound 4)) (.imp (wc_value_m (.bound 4) (.bound 3) (.bound 2) .newest)
      (.imp (wc_value_m (.bound 4) (.bound 3) (.bound 1) .newest) (Formula.extensionalEq (.bound 2) (.bound 1)))))) }
  have sat a : φ.denote ρ a ↔ ∀ b y, M.mem b X → Wc_value_d X R a y → Wc_value_d X R b y → a = b := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, wc_value_sat_l hZF.1, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  apply (sat a).mp (wf_rel_ind_l hZF hw φ ρ ?_ a ha) b y hb h g
  intro a ha ih
  apply (sat a).mpr
  intro b y hb h g
  apply he a ha b hb
  intro z hz
  constructor
  · intro hza
    obtain ⟨v, hv⟩ := wc_value_exists_l hZF hw hz
    obtain ⟨w, hw, hwb, hwv⟩ := (wc_value_equation_l hZF hw g v).mp
      ((wc_value_equation_l hZF hw h v).mpr ⟨z, hz, hza, hv⟩)
    exact ((sat z).mp (ih z hz hza) w v hw hv hwv).symm ▸ hwb
  · intro hzb
    obtain ⟨v, hv⟩ := wc_value_exists_l hZF hw hz
    obtain ⟨w, hw, hwa, hwv⟩ := (wc_value_equation_l hZF hw h v).mp
      ((wc_value_equation_l hZF hw g v).mpr ⟨z, hz, hzb, hv⟩)
    exact (sat w).mp (ih w hw hwa) z v hz hwv hv ▸ hwa

theorem wc_iso_l (hZF : M.Models ZF) {X R : M.Domain} (hw : Wf_rel_d X R) (he : Wc_ext_d X R) :
    ∃ B F, M.TransitiveSet B ∧ Wc_graph_d X R F ∧
      M.IsSetBijectionFromTo (kp_pair_l (ZF.modelsKP hZF)) F X B ∧
      ∀ a b x y, Rd_entry_d a x F → Rd_entry_d b y F → (Rd_entry_d a b R ↔ M.mem x y) := by
  obtain ⟨B, F, hf, hg, range, ht⟩ := wc_collapse_l hZF hw
  have inj a b y (ha : Rd_entry_d a y F) (hb : Rd_entry_d b y F) :=
    wc_value_injective_l hZF hw he (hf.bound_l ha).1 (hf.bound_l hb).1 ⟨F, hg, ha⟩ ⟨F, hg, hb⟩
  refine ⟨B, F, ht, hg, ⟨⟨fn0_function_l (ZF.modelsKP hZF) hf, inj⟩,
    fun y hy => ((range y).mp hy).imp fun a ha => ⟨(hf.bound_l ha).1, ha⟩⟩, ?_⟩
  intro a b x y ha hb
  refine ⟨fun hab => ((hg.2 b y hb).2.2 x).mpr ⟨a, (hf.bound_l ha).1, hab, ha⟩, fun hxy => ?_⟩
  obtain ⟨z, _, hzb, hz⟩ := ((hg.2 b y hb).2.2 x).mp hxy
  exact inj z a x hz ha ▸ hzb

end YesMetaZFC.SetTheory
