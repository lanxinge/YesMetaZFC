import YesMetaZFC.Model.SetTheory.Internal.TypeSource
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure
import YesMetaZFC.SetTheory.FlatPairing.CumulativeSource
import YesMetaZFC.SetTheory.Rank

/-! # 规则 (7) 的末位严格秩界

以 S∈Vα 表达 rank(S)<α，并同时检查 δ<α。实际累积层级在源中
双向读取，不预设源模型满足 ZF，也不把源内秩判断当成背景假设。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tg_bound_d (I : kpair_convention_l.Interpretation M) (δ S α : M.Domain) : Prop :=
  M.IsOrdinal α ∧ M.mem δ α ∧ ∃ B, V_d I α B ∧ M.mem S B

def tg_bound_m {d} (δ S α : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isOrdinal⌝ₚ(⌜α⌝ₛ) ∧ ⌜δ⌝ₛ ∈ ⌜α⌝ₛ ∧ (∃ B, ⌜v_m FlatPairing.convention⌝ₚ(⌜α⌝ₛ, B) ∧ ⌜S⌝ₛ ∈ B)⟫
derive_free_closed tg_bound_m

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_bound_rank_l {δ S α : M.Domain} : Tg_bound_d I δ S α ↔
    M.IsOrdinal α ∧ M.mem δ α ∧ ∃ ρ, Rk_d I S ρ ∧ M.mem ρ α := by
  refine and_congr_right fun hα => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨B, hB, hS⟩
    obtain ⟨ρ, rank⟩ := ZF.rk_exists_l I hZF S
    exact ⟨ρ, rank, (ZF.rk_mem_l I hZF rank hB).mp hS⟩
  · rintro ⟨ρ, rank, lt⟩
    obtain ⟨B, hB⟩ := ZF.v_exists_l I hZF hα
    exact ⟨B, hB, (ZF.rk_mem_l I hZF rank hB).mpr lt⟩

theorem tg_bound_source_l {ω η X : M.Domain} (hω : M.IsOmega ω) (hX : V_d I η X) (hw : M.mem ω X)
    {d} (ρ : Env (rt_model_l X ⟨⟨ω, hw⟩⟩) d) (δ S α : Term d) :
    Formula.satisfies ρ (tg_bound_m δ S α) ↔ Tg_bound_d I (δ.eval ρ).val (S.eval ρ).val (α.eval ρ).val := by
  let J := fp_rank_interpretation_l I hZF hω hX hw
  have trans := ZF.v_transitive_l I hZF hX
  simp only [tg_bound_m, Tg_bound_d, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    rt_ordinal_iff_l trans ⟨⟨ω, hw⟩⟩ (ZF.modelsKP hZF), Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, v_sat_l J (rt_model_ext_l hZF.1 trans ⟨⟨ω, hw⟩⟩),
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨?_, ?_⟩)
  · rintro ⟨B, hv, hS⟩
    exact ⟨B.val, (rt_fp_v_l I hZF hω hX hw (α.eval ρ) B).mp hv, hS⟩
  · rintro ⟨B, hv, hS⟩
    have hb := ZF.v_mem_l I hZF hv hX (ZF.v_ordinal_height_l hZF hX (v_ordinal_l I hv) (α.eval ρ).property)
    exact ⟨⟨B, hb⟩, (rt_fp_v_l I hZF hω hX hw (α.eval ρ) ⟨B, hb⟩).mpr hv, hS⟩

def Tg_bound_query_d (J : kpair_convention_l.Interpretation M) (ω e l n U D q : M.Domain) : Prop :=
  M.mem q D ∧ ∀ η X c R r δ T S α, V_d J η X → Smem_d J c X R →
    Tt_realized_d J ω c X R n r δ U D T → Rd_entry_d e S r → Rd_entry_d l α r →
      (M.mem q T ↔ Tg_bound_d J δ S α)

theorem tt_bound_query_l {ω e l n U D : M.Domain} (hω : M.IsOmega ω)
    (he : M.mem e n) (hl : M.mem l n) (hw : M.mem ω U) (pool : Tt_pool_d I ω n U D) :
    ∃ q, Tg_bound_query_d I ω e l n U D q := by
  let φ : Formula 1 3 := tg_bound_m (.bound 2) (.bound 1) .newest
  obtain ⟨q, hq, read⟩ := tt_fixed_query_l hZF hω pool φ (tg_bound_m_freeClosed _ _ _ rfl rfl rfl)
    (Fin.cases l (Fin.cases e (fun _ => n)))
    (Fin.cases (Or.inl hl) (Fin.cases (Or.inl he) (fun _ => Or.inr (Or.inl rfl))))
  refine ⟨q, hq, fun η X c R r δ T S α hX model type rS rα => ?_⟩
  have hwX := type.constants ω hw
  let ρ : Env (rt_model_l X ⟨⟨ω, hwX⟩⟩) 3 :=
    ⟨Fin.cases ⟨α, (type.tuple.bound_l rα).2⟩ (Fin.cases ⟨S, (type.tuple.bound_l rS).2⟩ (fun _ => ⟨δ, type.point⟩)),
      fun _ => ⟨δ, type.point⟩⟩
  let ξ : Env (smdl_structure_l I (R := R) type.model.2.1) 3 := ⟨ρ.bound, ρ.free⟩
  exact (read c X R r δ T type ξ (Fin.cases (Or.inl rα) (Fin.cases (Or.inl rS)
    (fun _ => Or.inr (Or.inl ⟨rfl, rfl⟩))))).trans
    ((smem_formula_l I model ⟨⟨ω, hwX⟩⟩ φ ρ).symm.trans (tg_bound_source_l hZF hω hX hwX ρ _ _ _))

end YesMetaZFC.SetTheory.Internal
