import YesMetaZFC.Model.Forcing.InternalSelection
import YesMetaZFC.Model.Forcing.InternalZF
import YesMetaZFC.Model.Forcing.InternalGenericInstance
import YesMetaZFC.Model.SmallGraph.ZFC

/-! # 内部名称扩张保持选择公理

在地模型中枚举源名称的闭支撑，把每个非空集合的最早隶属候选收集成加权名称。
稠密性保证每个族成员获得选值，最小指标唯一性保证选择不依赖名称呈现。
最终直接给出仓库原 ZFC 模型接口。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (h : M.Models ZFC) (hU : Generic_d M B R z U)
  (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M) (hN : ∃ t, Name_d M B t)
local notation "E" => ext_structure_l (name_domain_l M hM hL B hN) U
include O h hU

theorem internal_choice_l (A : (E).Domain)
    (hn : ∀ a : (E).Domain, a.1 ∈ A.1 → ∃ x : (E).Domain, x.1 ∈ a.1)
    (hd : ∀ a : (E).Domain, a.1 ∈ A.1 → ∀ b : (E).Domain, b.1 ∈ A.1 →
      a ≠ b → ¬ ∃ x : (E).Domain, x.1 ∈ a.1 ∧ x.1 ∈ b.1) :
    ∃ C : (E).Domain, ∀ a : (E).Domain, a.1 ∈ A.1 →
      ∃ x : (E).Domain, (x.1 ∈ C.1 ∧ x.1 ∈ a.1) ∧
        ∀ y : (E).Domain, (y.1 ∈ C.1 ∧ y.1 ∈ a.1) → y = x := by
  let hZF := ZFC.models_zf_l h
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨τ, ⟨S, hτS, hS⟩, hA⟩ := value_name_l hM hL hN A
  obtain ⟨κ, F, hκ, hf, hsur⟩ := ZFC.ordinal_enum_l h I S
  let δ : Env M 6 := (((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push F).push κ).push τ
  let φ : BinarySchema 6 := {
    body := .existsE (.conj (source_m (.bound 7) (.bound 3) .newest (.bound 1))
      (min_mem_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) (.bound 2) .newest)) }
  have hφ s p : φ.denote δ s p ↔ ∃ t, Source_d M R τ t p ∧ Min_mem_d M B R z F κ p s t := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      source_sat_l M hZF.1, min_mem_sat_l M hZF.1]
    rfl
  obtain ⟨c, hc, _, he⟩ := name_comp_l M hZF φ δ B S (fun s hs => ⟨S, hs, hS⟩)
  obtain ⟨C, hC⟩ := name_value_l hM hL hN hc
  refine ⟨C, fun a ha => ?_⟩
  obtain ⟨t, b, ht, hb, hta⟩ := (val_mem_l M hA).mp ha
  obtain ⟨y, hy⟩ := hn a ha
  obtain ⟨s, d, hs, _, hsy⟩ := (val_mem_l M hta).mp hy
  have htS := (supp_entry_l M hS hτS ht).1
  have hsS := (supp_entry_l M hS htS hs).1
  obtain ⟨i, hi, his⟩ := hsur s hsS
  obtain ⟨q, hq, hm⟩ := (val_mem_forcing_l O hZF hU hsy hta).mpr hy
  obtain ⟨p, hp, s, hm⟩ := generic_pick_l hZF hU (min_mem_defined_l M hZF.1 B R z F κ t) hq
    (min_mem_dense_l O hZF hκ hi his hm)
  have hsS : M.mem s S := hf.output_mem_of_pairMember hm.choose_spec.2.1
  obtain ⟨x, hsx⟩ := name_value_l hM hL hN (⟨S, hsS, hS⟩ : Name_d M B s)
  obtain ⟨r, hr, hrp, hrb⟩ := hU.directed p b hp hb
  have hr' := hU.proper r hr
  have hmr := min_mem_lower_l O F κ s t p r (hU.proper p hp).1 ⟨hr'.1, hr'.2, hrp⟩ hm
  have hxC := (val_mem_l M hC).mpr ⟨s, r, (he s r).mpr
    ⟨hsS, hr'.1, (hφ s r).mpr ⟨t, ⟨b, ht, hrb⟩, hmr⟩⟩, hr, hsx⟩
  have hxa := (val_mem_forcing_l O hZF hU hsx hta).mp ⟨r, hr, hmr.choose_spec.2.2.1⟩
  refine ⟨x, ⟨hxC, hxa⟩, fun y ⟨hyC, hya⟩ => ?_⟩
  obtain ⟨v, q, hv, hq, hvy⟩ := (val_mem_l M hC).mp hyC
  obtain ⟨w, hw, hmw⟩ := (hφ v q).mp ((he v q).mp hv).2.2
  have hwN : Name_d M B w := hw.elim fun d hd => (name_entry_l M ⟨S, hτS, hS⟩ hd.1).1
  obtain ⟨a', hwa⟩ := name_value_l hM hL hN hwN
  have ha'A := source_val_l M hU.upward hA hwa hw hq
  have hya' := (val_mem_forcing_l O hZF hU hvy hwa).mp ⟨q, hq, hmw.choose_spec.2.2.1⟩
  have haa : a' = a := by
    apply Classical.byContradiction
    intro hn
    exact hd a' ha'A a ha hn ⟨y, hya', hya⟩
  subst a'
  exact Subtype.ext (min_mem_unique_l O hZF hU hκ hf hq hr hvy hsx hwa hta hmw hmr)

theorem internal_choice_axiom_l : (E).SatisfiesSentence Axioms.choice := by
  rw [SetTheory.Structure.satisfiesSentence_iff]
  intro f
  simp only [Axioms.choice, Sentence.ofFormula, Formula.satisfies_forall_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.extensionalNe, Formula.satisfies_neg_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq (ext_extensional_l _ U),
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  intro A ⟨hn, hd⟩
  exact internal_choice_l O h hU hM hL hN A hn hd

/-- 一次调用获得内部泛型扩张的全部原 ZFC 公理与模式；名称域非空性自动构造。 -/
theorem preserves_zfc_l : (extension_l M (ZFC.models_zf_l h) hM hL B U).Models ZFC := by
  have hE := preserves_zf_l O (ZFC.models_zf_l h) hU hM hL
  refine ⟨hE.1, fun s hs => ?_⟩
  cases hs with
  | zf hs => exact hE.2 s hs
  | choice => exact internal_choice_axiom_l O h hU hM hL (zf_name_exists_l (B := B) (ZFC.models_zf_l h))

omit O h hU in
/-- 实际小图地模型和二元布尔主泛型滤子，直接实例化完整 ZFC 保持端点。 -/
theorem two_extension_zfc_l :
    (extension_l SmallGraph.sg_structure (ZFC.models_zf_l SmallGraph.sg_project_zfc)
      SmallGraph.SG_set.mem_wf sg_setlike_l two_conditions_l two_filter_l).Models ZFC :=
  preserves_zfc_l two_cond_order_l SmallGraph.sg_project_zfc two_generic_l
    SmallGraph.SG_set.mem_wf sg_setlike_l

end YesMetaZFC.Model.Forcing.Internal
