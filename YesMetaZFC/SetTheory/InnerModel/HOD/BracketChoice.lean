import YesMetaZFC.SetTheory.InnerModel.HOD.Models
import YesMetaZFC.SetTheory.Ord.DefinableMinimum
import YesMetaZFC.SetTheory.Axioms.ZFC

/-! # HOD[A] 的选择公理与完整 ZFC 模型

A 固定后，定义码仍是单个序数，故逐行取最早代码。圆括号版本没有对 A 的
有限参数列作选择，这里也不向它添加选择公理。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Hb_pick_d (A X x : M.Domain) : Prop := M.mem x X ∧ ∃ q, Ob_eval_d I q A x ∧
  ∀ r, M.mem r q → ∀ y, M.mem y X → ¬ Ob_eval_d I r A y
def hb_pick_m {d} (A X x : Term d) : Formula 1 d := .conj (.mem x X) (.existsE
  (.conj (ob_eval_m .newest A.weaken x.weaken) (Formula.forallMem .newest
    (Formula.forallMem X.weaken.weaken (.neg (ob_eval_m (.bound 1) A.weaken.weaken.weaken .newest))))))
derive_free_closed hb_pick_m

theorem hb_pick_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A X x : Term d) :
    Formula.satisfies ρ (hb_pick_m A X x) ↔ Hb_pick_d I (A.eval ρ) (X.eval ρ) (x.eval ρ) := by
  simp only [hb_pick_m, Hb_pick_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, ob_eval_sat_l I hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]
  rfl

theorem hb_pick_exists_l (hZF : M.Models ZF) {A X : M.Domain} (hn : ∃ x, M.mem x X ∧ Ob_d A x) :
    ∃ x, Hb_pick_d I A X x := by
  obtain ⟨x, hx, ho⟩ := hn
  obtain ⟨q, hq⟩ := (ob_code_l I hZF).mp ho
  have hqo := hq.elim fun _ h => od_eval_ordinal_l I hZF h.1
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 1) (ob_eval_m (.bound 1) (.bound 3) .newest) }
  let ρ : Env M 2 := ⟨Fin.cases X (fun _ => A), fun _ => A⟩
  have sat r : φ.denote ρ r ↔ ∃ y, M.mem y X ∧ Ob_eval_d I r A y := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_existsMem_iff, ob_eval_sat_l I hZF.1]
    rfl
  obtain ⟨r, _, hr, hm⟩ := ZF.ordinal_min_l hZF φ ρ hqo ((sat q).mpr ⟨x, hx, hq⟩)
  obtain ⟨y, hy, he⟩ := (sat r).mp hr
  exact ⟨y, hy, r, he, fun s hs z hz hh => hm s hs ((sat s).mpr ⟨z, hz, hh⟩)⟩

theorem hb_pick_unique_l (hZF : M.Models ZF) {A X x y}
    (h : Hb_pick_d I A X x) (g : Hb_pick_d I A X y) : x = y := by
  obtain ⟨hx, q, hq, hm⟩ := h
  obtain ⟨hy, r, hr, hn⟩ := g
  have qo := hq.elim fun _ h => od_eval_ordinal_l I hZF h.1
  have ro := hr.elim fun _ h => od_eval_ordinal_l I hZF h.1
  rcases qo.trichotomy hZF.1 ro (KP.difference_exists_d (ZF.modelsKP hZF))
    (KP.intersection_exists_d (ZF.modelsKP hZF) q r) with he | hqr | hrq
  · have eq := hZF.1.eq_of_same_members q r he; subst r
    exact ob_eval_unique_l I hZF hq hr
  · exact (hn q hqr x hx hq).elim
  · exact (hm r hrq y hy hr).elim

theorem hb_choice_set_l (hZF : M.Models ZF) {A X : M.Domain} (hX : Hb_d A X)
    (hn : ∀ a, M.mem a X → ∃ x, M.mem x a)
    (hd : ∀ a, M.mem a X → ∀ b, M.mem b X → a ≠ b → ¬ ∃ x, M.mem x a ∧ M.mem x b) :
    ∃ C, Hb_d A C ∧ ∀ a, M.mem a X → ∃ x, (M.mem x C ∧ M.mem x a) ∧
      ∀ y, (M.mem y C ∧ M.mem y a) → y = x := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨U, hu, hU⟩ := ha_union_l hZF hX
  let ρ : Env M 2 := ⟨Fin.cases X (fun _ => A), fun _ => A⟩
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 1) (hb_pick_m (.bound 3) .newest (.bound 1)) }
  have sat x : φ.denote ρ x ↔ ∃ a, M.mem a X ∧ Hb_pick_d I A a x := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_existsMem_iff, hb_pick_sat_l I hZF.1]
    rfl
  obtain ⟨C, ho, hc⟩ := oa_separation_l hZF false A φ ρ
    (Fin.cases (ha_oa_l hX) (fun _ => oa_parameter_l hZF false A)) (ha_oa_l hu)
  have hC x : M.mem x C ↔ ∃ a, M.mem a X ∧ Hb_pick_d I A a x :=
    (hc x).trans ((and_congr_right fun _ => sat x).trans
      ⟨And.right, fun ⟨a, ha, hx⟩ => ⟨(hU x).mpr ⟨a, ha, hx.1⟩, a, ha, hx⟩⟩)
  have hH : Hb_d A C := ha_of_members_l hZF ho (fun x hx => ha_trans_l hu ((hc x).mp hx).1)
  refine ⟨C, hH, fun a ha => ?_⟩
  obtain ⟨x, hp⟩ := hb_pick_exists_l I hZF ((hn a ha).imp fun x hx =>
    ⟨hx, oa_bracket_l.mp (ha_oa_l (ha_trans_l (ha_trans_l hX ha) hx))⟩)
  refine ⟨x, ⟨(hC x).mpr ⟨a, ha, hp⟩, hp.1⟩, fun y hy => ?_⟩
  obtain ⟨b, hb, hpy⟩ := (hC y).mp hy.1
  have eq : a = b := Classical.byContradiction (fun he => hd a ha b hb he ⟨y, hy.2, hpy.1⟩)
  subst b
  exact hb_pick_unique_l I hZF hpy hp

theorem hb_model_choice_l (hZF : M.Models ZF) (A : M.Domain) : (hb_model_l hZF A).SatisfiesSentence Axioms.choice := by
  rw [Structure.satisfiesSentence_iff]
  intro f
  simp only [Axioms.choice, Sentence.ofFormula, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_conj_iff,
    Formula.extensionalNe, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq (ha_model_ext_l hZF false A),
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  intro X hX
  have hn a (ha : M.mem a X.val) : ∃ x, M.mem x a := by
    obtain ⟨x, hx⟩ := hX.1 ⟨a, ha_trans_l X.property ha⟩ ha
    exact ⟨x.val, hx⟩
  have hd a (ha : M.mem a X.val) b (hb : M.mem b X.val) (he : a ≠ b) : ¬ ∃ x, M.mem x a ∧ M.mem x b := by
    intro ⟨x, hx, hy⟩
    exact hX.2 ⟨a, ha_trans_l X.property ha⟩ ha ⟨b, ha_trans_l X.property hb⟩ hb
      (fun h => he (congrArg Subtype.val h)) ⟨⟨x, ha_trans_l (ha_trans_l X.property ha) hx⟩, hx, hy⟩
  obtain ⟨C, hc, hC⟩ := hb_choice_set_l hZF X.property hn hd
  refine ⟨⟨C, hc⟩, fun a ha => ?_⟩
  obtain ⟨x, hx, hm⟩ := hC a.val ha
  exact ⟨⟨x, ha_trans_l a.property hx.2⟩, hx, fun y hy => Subtype.ext (hm y.val hy)⟩

/-- 任意背景 ZF 模型与任意内部集合 A，HOD[A] 都是实际 ZFC 模型。 -/
theorem hb_model_zfc_l (hZF : M.Models ZF) (A : M.Domain) : (hb_model_l hZF A).Models ZFC := by
  refine ⟨(hb_model_zf_l hZF A).1, fun s hs => ?_⟩
  cases hs with
  | zf hs => exact (hb_model_zf_l hZF A).2 s hs
  | choice => exact hb_model_choice_l hZF A

end YesMetaZFC.SetTheory.InnerModel
