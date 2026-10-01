import YesMetaZFC.Model.Forcing.Proper.Hereditary.NameReduction
import YesMetaZFC.Model.Forcing.Proper.Hereditary.Value
import YesMetaZFC.Model.Forcing.Proper.Hereditary.Cardinal

/-! # H(χ) 的泛型对应

正向由传递闭包的求值大小界给出；反向在泛型中取得小传递容器及单射，回到一个
共同条件后消费内部小名称定理。故地 H(χ) 的全部名称值恰好组成扩张的 H(χ)。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} {U : M.Domain → Prop}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC) (hU : Generic_d M B R z U)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
local notation "E" => extension_l M hZF B R z U
local notation "J" => kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)

/-- 扩张中每个遗传小集合都有地 H(χ) 中的名称，不要求地模型外部良基。 -/
theorem hmem_name_l {ω χ H b} (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ)
    (hωχ : M.mem ω χ) (hH : H_d I χ H) (hB : M.mem B H) (hb : U b)
    (e : M.Domain → (E).Domain) (he : ∀ a y, y ∈ e a ↔ ∃ s, M.mem s a ∧ e s = y)
    (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    {x : (E).Domain} (hx : Hmem_d J (e χ) x) : Ng_mem_d M B R z U H x := by
  obtain ⟨Y, α, hY, hα, F, hF⟩ := hx
  obtain ⟨μ, hμ, rfl⟩ := (he χ α).mp hα
  obtain ⟨T, hTN, hTY⟩ := value_name_l Y
  obtain ⟨t, htN, htx⟩ := value_name_l x
  obtain ⟨f, hfN, hfF⟩ := value_name_l F
  obtain ⟨w, hw, hwN, _⟩ := zf_check_l M hZF (hU.proper b hb).1 μ
  let ρ : Env M 1 := ⟨fun _ => T, fun _ => T⟩
  let η : Env E 1 := ⟨fun _ => Y, fun _ => Y⟩
  have hρ : Env_val_d hZF ρ η := by intro a; cases a <;> exact hTY
  have hclosed : (Formula.isTransitive (.bound 0) : Formula 1 1).FreeClosed := by
    simp [Formula.isTransitive, Definitional.Formula.FreeClosed]
  obtain ⟨a, ha, hat⟩ := (forcing_truth_l O hZF hU _ hclosed ρ η hρ).mpr
    ((Formula.satisfies_isTransitive_iff _ _).mpr hY.1)
  have hι : Env_val_d hZF (fn_env_l T w f) (fn_env_l Y (e μ) F) := by
    intro v
    cases v with
    | free _ => exact hv μ w hw
    | bound i => exact Fin.cases hfF (Fin.cases hTY (fun _ => hv μ w hw)) i
  obtain ⟨c, hc, hcf⟩ := (forcing_truth_l O hZF hU inj_body_m inj_body_closed_l _ _ hι).mpr
    ((Formula.satisfies_isInjectionFromTo_iff J (extension_ext_l O hZF hU) _ _ _ _).mpr hF)
  obtain ⟨d, hd, hdt⟩ := (qval_mem_forcing_l O hZF hU htx hTY).mpr hY.2.1
  obtain ⟨r, hr, hra, hrc⟩ := hU.directed a c ha hc
  obtain ⟨s, hs, hsr, hsd⟩ := hU.directed r d hr hd
  obtain ⟨q, hq, hqs, hqb⟩ := hU.directed s b hs hb
  have hqr : Below_d M B R z q r := ⟨(hU.proper q hq).1, (hU.proper q hq).2,
    O.trans q s r (hU.proper q hq).1 (hU.proper s hs).1 (hU.proper r hr).1 hqs hsr⟩
  have hqa := below_trans_l O (hU.proper a ha).1 hqr ⟨(hU.proper r hr).1, (hU.proper r hr).2, hra⟩
  have hqc := below_trans_l O (hU.proper c hc).1 hqr ⟨(hU.proper r hr).1, (hU.proper r hr).2, hrc⟩
  have hqd : Below_d M B R z q d := ⟨(hU.proper q hq).1, (hU.proper q hq).2,
    O.trans q s d (hU.proper q hq).1 (hU.proper s hs).1 (hU.proper d hd).1 hqs hsd⟩
  have hρN : ∀ v : Term 1, Name_d M B (v.eval ρ) := by intro v; cases v <;> exact hTN
  have hιN : ∀ v : Term 3, Name_d M B (v.eval (fn_env_l T w f)) := by
    intro v
    cases v with
    | free _ => exact hwN
    | bound i => exact Fin.cases hfN (Fin.cases hTN (fun _ => hwN)) i
  have hqt := (forces_regular_l O hZF _ ρ hρN).1 a q (hU.proper a ha).1 hqa hat
  have hqf := (forces_regular_l O hZF inj_body_m _ hιN).1 c q (hU.proper c hc).1 hqc hcf
  obtain ⟨v, hvq, hqfv⟩ := inj_name_check_l O hZF ⟨hTN, hwN, hfN, hqf⟩
    hqr.1 hqr.2.1 (hU.proper b hb).1 hqb hw
  obtain ⟨t', ht'H, ht'N, heq⟩ := h_name_reduce_l O hZFC hω hχ hωχ hH hB hμ hqr.1 hqfv hvq hqt htN
    (below_refl_l O hqr.1 hqr.2.1) ⟨hqr.1, fun p hp => hdt.2 p (below_trans_l O (hU.proper d hd).1 hp hqd)⟩
  obtain ⟨y, hy⟩ := name_value_l (R := R) (z := z) (U := U) ht'N
  exact ⟨t', ht'H, (qval_eq_l O hZF hU hy htx).mp ⟨q, hq, heq⟩ ▸ hy⟩

/-- 地 H(χ) 的泛型值域就是扩张中实际的 H(eχ)，且 eχ 仍为正则基数。 -/
theorem h_generic_l {ω χ H b Y} (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ)
    (hωχ : M.mem ω χ) (hH : H_d I χ H) (hB : M.mem B H) (hb : U b)
    (e : M.Domain → (E).Domain) (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ s, M.mem s a ∧ e s = y)
    (hv : ∀ a s, Check_d M b a s → Qval_d M B R z U s (e a))
    (hY : ∀ x, x ∈ Y ↔ Ng_mem_d M B R z U H x) : (E).IsRegularCardinal J (e χ) ∧ H_d J (e χ) Y := by
  obtain ⟨μ, hμ, hBμ⟩ := ZF.hmem_size_l I hZF ((hH B).mp hB)
  refine ⟨small_regular_l O hZFC hU hω hωχ hμ hBμ hb e hi he hv hχ, fun x => (hY x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht, hx⟩
    exact hmem_value_l O hZF hU hb hχ.isCardinal.1 ((hH t).mp ht) hx e hi he hv
  · exact hmem_name_l O hZFC hU hω hχ hωχ hH hB hb e he hv

end YesMetaZFC.Model.Forcing.Internal
