import YesMetaZFC.SetTheory.InnerModel.HOD.Definition
import YesMetaZFC.SetTheory.InnerModel.OD.Choice
import YesMetaZFC.SetTheory.Axioms.ZFC

/-! # 背景 ZF 中 HOD 的实际选择集公理

取各行最早出现的序数定义码，分离所得选择集仍从原族唯一可定义，故属于 OD；
它的元素位于原族的遗传 OD 容器中，因而整个选择集属于 HOD。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem hod_choice_set_l (hZF : M.Models ZF) {A : M.Domain} (hA : Hod_d A)
    (hn : ∀ a, M.mem a A → ∃ x, M.mem x a)
    (hd : ∀ a, M.mem a A → ∀ b, M.mem b A → a ≠ b → ¬ ∃ x, M.mem x a ∧ M.mem x b) :
    ∃ C, Hod_d C ∧ ∀ a, M.mem a A → ∃ x, (M.mem x C ∧ M.mem x a) ∧
      ∀ y, (M.mem y C ∧ M.mem y a) → y = x := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨C, hOD, hC⟩ := od_choices_exists_l hZF I (hod_od_l hA)
  have hH : Hod_d C := by
    obtain ⟨T, ht, hAT, ho⟩ := hA
    apply hod_bounded_l (ZF.modelsKP hZF) ht ho hOD
    intro x hx
    obtain ⟨a, ha, hp⟩ := (hC x).mp hx
    exact ht a (ht A hAT a ha) x hp.1
  refine ⟨C, hH, fun a ha => ?_⟩
  obtain ⟨x, hp⟩ := od_pick_exists_l I hZF ((hn a ha).imp fun x hx =>
    ⟨hx, hod_od_l (hod_transitive_l (hod_transitive_l hA ha) hx)⟩)
  refine ⟨x, ⟨(hC x).mpr ⟨a, ha, hp⟩, hp.1⟩, fun y hy => ?_⟩
  obtain ⟨b, hb, hpy⟩ := (hC y).mp hy.1
  have eq : a = b := Classical.byContradiction (fun he => hd a ha b hb he ⟨y, hy.2, hpy.1⟩)
  subst b
  exact od_pick_unique_l I hZF hpy hp

def hod_model_l (hZF : M.Models ZF) : Structure.{u} where
  Domain := {x : M.Domain // Hod_d x}
  nonempty := by
    obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
    exact ⟨⟨e, hod_ordinal_l hZF (Structure.IsOrdinal.of_no_members he)⟩⟩
  mem x y := M.mem x.val y.val

theorem hod_model_ext_l (hZF : M.Models ZF) : Extensional (hod_model_l hZF) := by
  refine ⟨fun a b h => Subtype.ext (hZF.1.eq_of_same_members a.val b.val (fun x => ?_))⟩
  exact ⟨fun hx => (h ⟨x, hod_transitive_l a.property hx⟩).mp hx,
    fun hx => (h ⟨x, hod_transitive_l b.property hx⟩).mpr hx⟩

/-- 结论是原演绎核的选择集公理在实际 HOD 隶属结构中的满足性。 -/
theorem hod_model_choice_l (hZF : M.Models ZF) : (hod_model_l hZF).SatisfiesSentence Axioms.choice := by
  rw [Structure.satisfiesSentence_iff]
  intro f
  simp only [Axioms.choice, Sentence.ofFormula, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.extensionalNe, Formula.satisfies_neg_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq (hod_model_ext_l hZF),
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  intro A hA
  have hn a (ha : M.mem a A.val) : ∃ x, M.mem x a := by
    obtain ⟨x, hx⟩ := hA.1 ⟨a, hod_transitive_l A.property ha⟩ ha
    exact ⟨x.val, hx⟩
  have hd a (ha : M.mem a A.val) b (hb : M.mem b A.val) (he : a ≠ b) :
      ¬ ∃ x, M.mem x a ∧ M.mem x b := by
    intro ⟨x, hx, hy⟩
    exact hA.2 ⟨a, hod_transitive_l A.property ha⟩ ha ⟨b, hod_transitive_l A.property hb⟩ hb
      (fun h => he (congrArg Subtype.val h)) ⟨⟨x, hod_transitive_l (hod_transitive_l A.property ha) hx⟩, hx, hy⟩
  obtain ⟨C, hc, hC⟩ := hod_choice_set_l hZF A.property hn hd
  refine ⟨⟨C, hc⟩, fun a ha => ?_⟩
  obtain ⟨x, hx, hm⟩ := hC a.val ha
  exact ⟨⟨x, hod_transitive_l a.property hx.2⟩, hx, fun y hy => Subtype.ext (hm y.val hy)⟩

end YesMetaZFC.SetTheory.InnerModel
