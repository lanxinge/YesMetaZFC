import YesMetaZFC.SetTheory.LargeCardinal.WoodinTypes
import YesMetaZFC.SetTheory.LargeCardinal.TypeOneStep

/-! # 武丁基数下的一步伸展实例

对任意 Vη 中的内部有限元组，在 V(η+3) 与 V(η+1) 先后选择弹性类型。
低处类型的域严格大于高处类型的域，故实际超过高处类型；一步引理因此
生成同一原类型的真实扩展器伸展。所有实现高度及元组均显式保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 在任意给定 α<δ 之上构造两个弹性类型及其一步伸展，保持原元组。 -/
theorem woodin_elastic_step_l {δ η : M.Domain} (hd : Woodin_d I δ)
    (hη : M.IsOrdinal η) (hδη : M.mem δ η) :
    ∃ ω Z η₁ η₂ η₃ Y₁ Y₃ c₁ R₁ c₃ R₃,
      M.IsOmega ω ∧ V_d I η Z ∧ M.SuccessorOf η₁ η ∧ M.SuccessorOf η₂ η₁ ∧ M.SuccessorOf η₃ η₂ ∧
      V_d I η₁ Y₁ ∧ V_d I η₃ Y₃ ∧ Smem_d I c₁ Y₁ R₁ ∧ Smem_d I c₃ Y₃ R₃ ∧
      ∀ n s, M.mem n ω → Fn0_d n Z s →
        ∃ b σ a z, Ts_program_d hZF ω n b σ a z ∧ ∀ α, M.mem α δ →
        ∃ κ τ B U D u C V W w, ∃ q p : Ee_queries_d M,
          M.mem α κ ∧ M.mem κ τ ∧ M.mem τ δ ∧
          Ee_language_d hZF ω κ n B U D q ∧ Ee_language_d hZF ω τ n C V W p ∧
          Tt_realized_d I ω c₃ Y₃ R₃ n s δ U D u ∧ Tt_realized_d I ω c₁ Y₁ R₁ n s δ V W w ∧
          Ee_elastic_d q u ∧ Ee_elastic_d p w ∧ Tx_exceeds_d hZF ω δ κ n U D u τ n V W w ∧
          Ee_one_step_d hZF ω κ δ n u τ n w b σ z := by
  obtain ⟨ω, _, Z, η₁, Y₁, _, _, c₁, R₁, hω, _, hZ, h₁, hY₁, _, lower, low⟩ :=
    woodin_elastic_l hZFC hd hη hδη
  obtain ⟨η₂, hη₂, h₂⟩ := KP.ordinal_successor_l (ZF.modelsKP hZF)
    (KP.successor_isOrdinal (ZF.modelsKP hZF) hη h₁)
  have hηη₂ := hη₂.transitive η₁ h₂.predecessor_mem η h₁.predecessor_mem
  obtain ⟨ω', _, Z₂, η₃, Y₃, _, _, c₃, R₃, hω', _, hZ₂, h₃, hY₃, _, upper, high⟩ :=
    woodin_elastic_l hZFC hd hη₂ (hη₂.transitive η hηη₂ δ hδη)
  have eqω := hZF.1.eq_of_same_members ω' ω (fun x => ⟨hω'.2 ω hω.1 x, hω.2 ω' hω'.1 x⟩)
  subst ω'
  have sub := ZF.v_mono_l I hZF hZ hZ₂ (hη₂.transitive η hηη₂)
  refine ⟨ω, Z, η₁, η₂, η₃, Y₁, Y₃, c₁, R₁, c₃, R₃, hω, hZ, h₁, h₂, h₃, hY₁, hY₃,
    lower, upper, fun n s hn hs => ?_⟩
  -- 子类型程序先固定；随后全部临界点、类型和扩展器共用这份代码。
  obtain ⟨b, σ, a, z, prog⟩ := ts_program_l hZF hω hn
  refine ⟨b, σ, a, z, prog, fun α hα => ?_⟩
  have lifted := hs.mono_target_l sub
  obtain ⟨κ, _, _, B, U, D, q, _, u, hακ, hκδ, _, _, language, _, hu, _, elastic⟩ :=
    high n s hn lifted α hα
  obtain ⟨τ, _, _, C, V, W, p, _, w, hκτ, hτδ, hτ, _, language', _, hw, _, elastic'⟩ :=
    low n s hn hs κ hκδ
  have exceeds := tx_exceeds_same_l hZF hω hκτ hY₃ upper hu hY₁ lower hw h₂ h₃.predecessor_mem
  exact ⟨κ, τ, B, U, D, u, C, V, W, w, q, p, hακ, hκτ, hτδ, language, language', hu, hw,
    elastic, elastic', exceeds, ee_one_step_l hZFC hω prog language hτ hτδ language'.rank language'.constants elastic exceeds⟩

end YesMetaZFC.SetTheory.LargeCardinal
