import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype

/-! # 原控制记录中的武丁界在实际工作源内不可达 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.control_card_l {ω X R μ K η C : M.Domain}
    (context : Tg_context_d I ω X R η C) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K X R)
    (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 19)
    (valid : Formula.satisfies ρ tg_control0_m) (hw : (ρ.bound 0).val = ω) :
    Sc_inaccessible_d ω X (ρ.bound 5).val := by
  have fs := (context.read_l hZF source).1
  let J := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  simp only [tg_control0_m, Formula.satisfies_conj_iff] at valid
  have rules := valid.2.2.1
  simp only [tg_rules_m, Formula.satisfies_conj_iff] at rules
  have omega := (Formula.satisfies_isOmega_iff ..).mp rules.1
  obtain ⟨w, _, omega', below, regular, strong, _⟩ := (woodin_sat_l J ext ..).mp rules.2.2.2.2.2.1
  have ew := ext.eq_of_same_members w (ρ.bound 0)
    (fun x => ⟨omega'.2 (ρ.bound 0) omega.1 x, omega.2 w omega'.1 x⟩)
  have card : Formula.satisfies ρ (sc_inaccessible_m (.bound 0) (.bound 5)) := by
    simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_isRegularCardinal_iff J ext, Formula.satisfies_isStrongLimitCardinal_iff J ext]
    exact ⟨Eq.mp (congrArg (fun x => (rt_model_l C nc).mem x (ρ.bound 5)) ew) below, regular, strong⟩
  have card : Sc_inaccessible_d ω C (ρ.bound 5).val :=
    hw ▸ (sc_inaccessible_sat_l hZF.1 fs.transitive fs.pair nc ρ (.bound 0) (.bound 5)).mp card
  exact card.of_rank_l hZF source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair context.member (context.rank_l (ZF.modelsKP hZF) source.transitive source.code) (context.limit_l (ZF.modelsKP hZF) source.transitive source.code)

end YesMetaZFC.SetTheory.LargeCardinal
