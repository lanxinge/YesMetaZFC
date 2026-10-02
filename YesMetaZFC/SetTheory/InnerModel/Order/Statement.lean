import YesMetaZFC.SetTheory.InnerModel.Order.Internal
import YesMetaZFC.SetTheory.Definitional.Project.GlobalOrder

/-! # 原对象语言中的 Jensen 全局良序

同一句子在 KPi + V=L、实际 Jensen 内模型和每个非空原 J 层中成立。
单层证明直接使用层内定义及初段闭包，不假定该层满足 KPi。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def js_universe_s : Sentence := gw_sentence_s js_less_s.schema

theorem js_universe_l (hM : M.Models KPi) (hVL : M.SatisfiesSentence Axioms.vl_axiom) :
    M.SatisfiesSentence js_universe_s := by
  rw [Structure.satisfiesSentence_iff]
  intro f
  have all : ∀ x : M.Domain, L_d x := (vl_sat_l (KPi.models_iff_l.mp hM).1 f).mp
    ((Structure.satisfiesSentence_iff M Axioms.vl_axiom).mp hVL f)
  apply (gw_sentence_sat_l (KPi.models_iff_l.mp hM).1.1 js_less_s.schema ⟨Fin.elim0, f⟩).mpr
  simp only [Gw_order_d, js_less_sat_l (KPi.models_iff_l.mp hM).1]
  exact ⟨js_irrefl_l hM, fun _ _ _ h g => js_trans_l hM h g,
    fun x y => js_compare_l hM (all x) (all y), fun X hn => js_min_l hM (fun x _ => all x) hn,
    fun x => (js_initial_exists_l hM (all x)).imp (fun _ h => h.2.2)⟩

theorem js_l_model_l (hM : M.Models KPi) : (l_model_l hM).SatisfiesSentence js_universe_s :=
  js_universe_l (l_model_kpi_l hM) (l_model_vl_l hM)

/-- 每个非空 J 层自身满足同一原语言的全局良序句子，包括初段集合性。 -/
theorem jh_order_model_l (hM : M.Models KPi) {a C : M.Domain} (ha : M.IsOrdinal a) (h : Jh_value_d a C)
    (hn : Nonempty {x : M.Domain // M.mem x C}) : (rt_model_l C hn).SatisfiesSentence js_universe_s := by
  rw [Structure.satisfiesSentence_iff]
  intro f
  let ρ : Env (rt_model_l C hn) 0 := ⟨Fin.elim0, f⟩
  have ht := jh_value_transitive_l hM h
  have denote x y := jh_local_sigma1_l hM ha h hn ρ x y
  have all (x : (rt_model_l C hn).Domain) : L_d x.val := ⟨a, C, ⟨ha, h⟩, x.property⟩
  apply (gw_sentence_sat_l (rt_model_ext_l (KPi.models_iff_l.mp hM).1.1 ht hn) js_less_s.schema ρ).mpr
  refine ⟨fun x hx => js_irrefl_l hM x.val ((denote x x).mp hx),
    fun x y z hxy hyz => (denote x z).mpr (js_trans_l hM ((denote x y).mp hxy) ((denote y z).mp hyz)),
    ?_, ?_, ?_⟩
  · intro x y
    exact (js_compare_l hM (all x) (all y)).elim (fun he => Or.inl (Subtype.ext he))
      (fun h => Or.inr (h.imp (denote x y).mpr (denote y x).mpr))
  · intro X hX
    obtain ⟨m, hm, hmin⟩ := js_min_l hM (X := X.val)
      (fun y hy => ⟨a, C, ⟨ha, h⟩, ht X.val X.property y hy⟩) (hX.elim fun x hx => ⟨x.val, hx⟩)
    let x : (rt_model_l C hn).Domain := ⟨m, ht X.val X.property m hm⟩
    exact ⟨x, hm, fun y hy => (hmin y.val hy).elim (fun he => Or.inl (Subtype.ext he))
      (fun hxy => Or.inr ((denote x y).mpr hxy))⟩
  · intro x
    obtain ⟨I, hIC, hi⟩ := jh_initial_in_l hM ha h x.property
    exact ⟨⟨I, hIC⟩, fun y => (hi.2 y.val).trans (denote y x).symm⟩

end YesMetaZFC.SetTheory.InnerModel
