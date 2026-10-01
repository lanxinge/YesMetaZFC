import YesMetaZFC.Model.Forcing.Internal.Maximum.Mixing
import YesMetaZFC.Model.Forcing.Internal.Maximum.Selection

/-! # 内部名称的统一成员见证

在目标名称的内部支撑上作序数枚举，以最小可能指标选择成员，再混合这些选择。
得到的一个名称同时服务于所有条件，不将 Prop 存在性导出为不可计算选择实例。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
include O hZFC

/-- 每个内部名称都有统一成员名称：任何条件能迫使它有成员时，该名称即为成员。 -/
theorem member_maximum_l {A} (hA : Name_d M B A) : ∃ t, Name_d M B t ∧
    ∀ p s, Mem_force_d M B R z p s A → Mem_force_d M B R z p t A := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨W, hAW, hW⟩ := hA
  obtain ⟨κ, F, hκ, hf, hsur⟩ := ZFC.ordinal_enum_l hZFC I W
  let ρ : Env M 6 := (((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push F).push κ).push A
  let φ : BinarySchema 6 := {
    body := min_mem_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) .newest (.bound 1) (.bound 2) }
  have hφ s p : φ.denote ρ s p ↔ Min_mem_d M B R z F κ p s A :=
    min_mem_sat_l M hZF.1 ((ρ.push s).push p) _ _ _ _ _ _ _ _
  obtain ⟨t, ht, _, hm⟩ := mixing_l O hZF φ ρ hW (by
    intro p q s t r _ _ hs _ hp hq hrp hrq
    have he := min_mem_compat_l O hZF.1 hκ hf.1.2 hrp hrq ((hφ s p).mp hp) ((hφ t q).mp hq)
    exact he ▸ eq_force_refl_l O hZF hrp.1 ⟨W, hs, hW⟩)
  refine ⟨t, ht, fun p s hp => mem_force_dense_l O hp.1 ?_⟩
  intro q hq
  obtain ⟨r, a, c, hr, hac, hrc, _⟩ := hp.2 q hq
  have haW := (supp_entry_l M hW hAW hac).1
  have ha : Name_d M B a := ⟨W, haW, hW⟩
  obtain ⟨i, hi, hia⟩ := hsur a haW
  have har := mem_force_entry_l O hZF hr.1 ha (supp_entry_l M hW hAW hac).2 hac hrc
  obtain ⟨v, hv, a, hmin⟩ := min_mem_dense_l O hZF hκ hi hia har r (below_refl_l O hr.1 hr.2.1)
  have haW : M.mem a W := hf.output_mem_of_pairMember hmin.choose_spec.2.1
  have ha : Name_d M B a := ⟨W, haW, hW⟩
  have he := hm v a hv.1 haW ((hφ a v).mpr hmin)
  exact ⟨v, below_trans_l O hq.1 hv hr, mem_force_left_l O hZF ha ht ⟨W, hAW, hW⟩
    (eq_force_symm_l hZF ht ha he) hmin.choose_spec.2.2.1⟩

end YesMetaZFC.Model.Forcing.Internal
