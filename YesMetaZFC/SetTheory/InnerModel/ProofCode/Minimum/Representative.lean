import YesMetaZFC.SetTheory.InnerModel.ProofCode.Initial.EvaluationTable

/-! # 每个 J 内对象的唯一最小码名

从任一码名开始，在它的精确初段加上自身后建立完整求值表，分离同值纤维，
再取码序最小元。候选最小元之前的任何同值码都在这张表内，因此所得最小性是全局的。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Pm_min_d (v x : M.Domain) : Prop := Pn_eval_d v x ∧ ∀ u, Pn_eval_d u x → ¬ Pn_lt_d u v
theorem Pm_min_d.valid_l {v x : M.Domain} (hx : Pm_min_d v x) : Pn_valid_d v := pn_eval_domain_l hx.1

theorem pm_min_unique_l (hM : M.Models KPi) {v w x : M.Domain} (hv : Pm_min_d v x) (hw : Pm_min_d w x) : v = w := by
  rcases pn_compare_l hM hv.valid_l hw.valid_l with he | he | he
  · exact he
  · exact (hw.2 v hv.1 he).elim
  · exact (hv.2 w hw.1 he).elim

theorem pm_min_exists_l (hM : M.Models KPi) {x : M.Domain} (hx : L_d x) : ∃ v, Pm_min_d v x := by
  let hKP := (KPi.models_iff_l.mp hM).1
  obtain ⟨w, hw⟩ := (pn_cover_l hM x).mp hx
  have hwv := pn_eval_domain_l hw
  obtain ⟨I, hi⟩ := pi_initial_exists_l hM hwv
  obtain ⟨S, hs⟩ := KP.exists_insert hKP I w
  have valid v (hv : M.mem v S) : Pn_valid_d v :=
    ((hs v).mp hv).elim (fun hv => ((hi.2 v).mp hv).1) (fun he => he.symm ▸ hwv)
  let ρ := jh_env_l x
  obtain ⟨F, hf⟩ := pn_eval_table_exists_l hM valid ρ
  let η := (ρ.push F).push x
  let φ : Delta0UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2), delta0 := rd_entry0_delta_l .. }
  obtain ⟨U, hu⟩ := KP.separation_exists_d hKP φ η S
  have hU v : M.mem v U ↔ M.mem v S ∧ Pn_eval_d v x := by
    have sat : Formula.satisfies (η.push v) φ.body ↔ Rd_entry_d v x F := rd_entry0_sat_l hKP.1 _ _ _ _
    rw [hu v, sat, hf.entry_l hKP, pn_eval_sat_l hKP]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h.1, h⟩⟩
  have hwU := (hU w).mpr ⟨(hs w).mpr (Or.inr rfl), hw⟩
  -- U 是初段加端点中所有解释为 x 的码名；取其最小元，再证明没有界外的更小同值码。
  obtain ⟨v, hvU, hmin⟩ := pn_min_l hM (fun v hv => valid v ((hU v).mp hv).1) ⟨w, hwU⟩
  obtain ⟨hvS, hvx⟩ := (hU v).mp hvU
  refine ⟨v, hvx, fun u hux huv => ?_⟩
  have hvv := valid v hvS
  have huv' := pn_eval_domain_l hux
  have huw : Pn_lt_d u w := ((hs v).mp hvS).elim
    (fun hv => pn_trans_l hM huv' hvv hwv huv ((hi.2 v).mp hv).2) (fun he => he ▸ huv)
  have huS := (hs u).mpr (Or.inl ((hi.2 u).mpr ⟨huv', huw⟩))
  rcases hmin u ((hU u).mpr ⟨huS, hux⟩) with he | he
  · subst u; exact pn_irrefl_l hM hvv huv
  · exact pn_irrefl_l hM hvv (pn_trans_l hM hvv huv' hvv he huv)

theorem pm_min_iff_l (hM : M.Models KPi) (x : M.Domain) : L_d x ↔ ∃ v, Pm_min_d v x :=
  ⟨pm_min_exists_l hM, fun ⟨v, hv⟩ => (pn_cover_l hM x).mpr ⟨v, hv.1⟩⟩

end YesMetaZFC.SetTheory.InnerModel
