import YesMetaZFC.Model.SetTheory.Internal.TypeTruth

/-! # 类型查询域的实际秩界

变量名来自内部有限序数，常量名只加固定次数的配对。有限列空间整体属于
任意包含参数域和 ω 的极限秩层；类型再由分离取得，亦属于同一秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tn_names_d.rank_mem_l {ω θ X n U N : M.Domain} (hω : M.IsOmega ω)
    (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X) (hn : M.mem n ω)
    (hU : M.mem U X) (hN : Tn_names_d n U N) : M.mem N X := by
  obtain ⟨m, hm⟩ := KP.exists_successor (ZF.modelsKP hZF) n
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I U U
  obtain ⟨m', hm', hm'ω⟩ := hω.1.2 n hn
  have hmω := (Structure.SuccessorOf.eq hZF.1 hm' hm) ▸ hm'ω
  have hmX := ZF.v_transitive_l I hZF hX ω hωX m hmω
  have hPX := ZF.v_product_mem_l I hZF hX hθ hU hU hP
  obtain ⟨B, hBX, hmB, hPB⟩ := ZF.v_joint_bound_l I hZF hX hmX hPX
  apply ZF.v_subset_mem_l I hZF hX hBX
  intro a ha
  rcases (hN a).mp ha with ha | ha | ⟨x, hx, code⟩
  · exact hmB a ((hm a).mpr (Or.inl ha))
  · exact hmB a ((hm a).mpr (Or.inr (ha ▸ fun _ => Iff.rfl)))
  · exact hPB a ((hP a).mpr ⟨x, hx, x, hx, code⟩)

theorem Tt_pool_d.rank_mem_l {ω θ X n U D : M.Domain} (hω : M.IsOmega ω)
    (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ) (hωX : M.mem ω X) (hn : M.mem n ω)
    (hU : M.mem U X) (pool : Tt_pool_d I ω n U D) : M.mem D X := by
  obtain ⟨N, E, names, seq, prod⟩ := pool
  have hN := names.rank_mem_l hZF hω hX hθ hωX hn hU
  have hE := ZF.v_fseq_mem_l I hZF hX hθ hω hωX hN seq
  exact ZF.v_product_mem_l I hZF hX hθ hωX hE prod

/-- κ 型的常量域恰为 Vκ∪{κ}，并实际属于任意更高的极限秩层。 -/
theorem tt_constants_exists_l {θ X κ : M.Domain} (hX : V_d I θ X) (hθ : M.IsLimitOrdinal θ)
    (hκ : M.mem κ θ) : ∃ B U, V_d I κ B ∧ M.mem U X ∧ ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ := by
  obtain ⟨B, hB⟩ := ZF.v_exists_l I hZF (hθ.1.mem hκ)
  obtain ⟨a, ha⟩ := KP.exists_pair (ZF.modelsKP hZF) κ κ
  obtain ⟨U, hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) B a
  have spec x : M.mem x U ↔ M.mem x B ∨ x = κ := (hU x).trans
    (or_congr Iff.rfl ((ha x).trans ⟨fun hh => hh.elim id id, Or.inl⟩))
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  have hPX := ZF.v_power_mem_l I hZF hX hθ (ZF.v_mem_l I hZF hB hX hκ) hP
  refine ⟨B, U, hB, ZF.v_subset_mem_l I hZF hX hPX (fun x hx => (hP x).mpr ?_), spec⟩
  rcases (spec x).mp hx with hx | rfl
  · exact ZF.v_transitive_l I hZF hB x hx
  · exact ZF.v_ordinal_subset_l I hZF hB

end YesMetaZFC.SetTheory.Internal
