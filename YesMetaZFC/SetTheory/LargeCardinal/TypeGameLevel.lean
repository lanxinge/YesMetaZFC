import YesMetaZFC.SetTheory.LargeCardinal.TypeGameGenericTarget

/-! # 地模型中的请求实现高度关系

只收集旧请求、旧有限标签图及有界高度；完整类型的实现仍在地模型中求值。
扩张以后读取这个实际集合的像，不能把旧 Vα 当成扩张模型的 Vα。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_level_d (ω e δ S l κ u α g : M.Domain) : Prop := ∃ μ A d H n C V P r,
  M.SuccessorOf μ α ∧ V_d I μ A ∧ Smem_d I d A H ∧ M.SuccessorOf n l ∧ V_d I κ C ∧
  (∀ x, M.mem x V ↔ M.mem x C ∨ x = κ) ∧ Tt_realized_d I ω d A H n r δ V P u ∧
  Rd_entry_d e S r ∧ Rd_entry_d l α r ∧ Sg_set_d I e l r g

def tg_level_m {d} (ω e δ S l κ u α g : Term d) : Formula 1 d := set[d] ⟪∃ μ A d H n C V P r,
  ⌜Formula.isSuccessor⌝ₚ(μ, ⌜α⌝ₛ) ∧ ⌜v_m kpair_convention_l⌝ₚ(μ, A) ∧
  ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(d, A, H) ∧ ⌜Formula.isSuccessor⌝ₚ(n, ⌜l⌝ₛ) ∧
  ⌜v_m kpair_convention_l⌝ₚ(⌜κ⌝ₛ, C) ∧ ⌜tt_constants0_m⌝ₚ(⌜κ⌝ₛ, C, V) ∧
  ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ, d, A, H, n, r, ⌜δ⌝ₛ, V, P, ⌜u⌝ₛ) ∧
  ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ, ⌜S⌝ₛ, r) ∧ ⌜rd_entry0_m⌝ₚ(⌜l⌝ₛ, ⌜α⌝ₛ, r) ∧
  ⌜sg_set_m (𝒞 := kpair_convention_l)⌝ₚ(⌜e⌝ₛ, ⌜l⌝ₛ, r, ⌜g⌝ₛ)⟫
derive_free_closed tg_level_m

theorem tg_level_sat_l {d} (ρ : Env M d) (ω e δ S l κ u α g : Term d) :
    Formula.satisfies ρ (tg_level_m ω e δ S l κ u α g) ↔ Tg_level_d hZF
      (ω.eval ρ) (e.eval ρ) (δ.eval ρ) (S.eval ρ) (l.eval ρ) (κ.eval ρ) (u.eval ρ) (α.eval ρ) (g.eval ρ) := by
  simp only [tg_level_m, Tg_level_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSuccessor_iff, v_sat_l I hZF.1, smem_sat_l I, tt_constants0_sat_l hZF.1,
    tt_realized_sat_l I (ZF.modelsKP hZF), rd_entry0_sat_l hZF.1, sg_set_sat_l I hZF.1, Definitional.Term.eval_weaken]; rfl

def Tg_level_key_d (p : Tg_params_d M.Domain) (X Z a k t g α : M.Domain) : Prop :=
  M.mem a X ∧ M.mem k p.ω ∧ M.mem t X ∧ M.MemberSubset g Z ∧ (M.mem α p.ν ∨ α = p.ν) ∧
  ∃ ℓ κ u l, Tg_aux_data_d a ℓ t κ u ∧ M.mem κ p.δ ∧ Fn0_d k p.ω t ∧ M.SuccessorOf l k ∧
    Tg_level_d hZF p.ω p.e p.δ p.S l κ u α g

def tg_level_key_m {d} (ω e δ S ν X Z a k t g α : Term d) : Formula 1 d := set[d] ⟪
  ⌜a⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜k⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜t⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜g⌝ₛ ⊆ ⌜Z⌝ₛ ∧ (⌜α⌝ₛ ∈ ⌜ν⌝ₛ ∨ ⌜α⌝ₛ = ⌜ν⌝ₛ) ∧
  (∃ ℓ κ u l, ⌜tg_aux_data_m⌝ₚ(⌜a⌝ₛ, ℓ, ⌜t⌝ₛ, κ, u) ∧ κ ∈ ⌜δ⌝ₛ ∧ ⌜fn0_m⌝ₚ(⌜k⌝ₛ, ⌜ω⌝ₛ, ⌜t⌝ₛ) ∧
    ⌜Formula.isSuccessor⌝ₚ(l, ⌜k⌝ₛ) ∧ ⌜tg_level_m⌝ₚ(⌜ω⌝ₛ, ⌜e⌝ₛ, ⌜δ⌝ₛ, ⌜S⌝ₛ, l, κ, u, ⌜α⌝ₛ, ⌜g⌝ₛ))⟫
derive_free_closed tg_level_key_m

theorem tg_level_key_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X Z a k t g α : Term d) :
    Formula.satisfies ρ (tg_level_key_m p.ω p.e p.δ p.S p.ν X Z a k t g α) ↔
      Tg_level_key_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (Z.eval ρ) (a.eval ρ) (k.eval ρ) (t.eval ρ) (g.eval ρ) (α.eval ρ) := by
  simp only [tg_level_key_m, Tg_level_key_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_exists_iff, tg_aux_data_sat_l hZF.1, fn0_sat_l hZF.1, Formula.satisfies_isSuccessor_iff,
    tg_level_sat_l hZF, Definitional.Term.eval_weaken, Tg_params_d.map_l]; rfl

def Tg_level_table_d (p : Tg_params_d M.Domain) (X Z R : M.Domain) : Prop := M.IsSetRelation I R ∧
  ∀ q α, Rd_entry_d q α R ↔ ∃ a k t g, Rd_quad_d q a k t g ∧ Tg_level_key_d hZF p X Z a k t g α

theorem tg_level_table_l (p : Tg_params_d M.Domain) (X Z : M.Domain) : ∃ R, Tg_level_table_d hZF p X Z R := by
  obtain ⟨P, power⟩ := ZF.exists_powerSet hZF Z
  obtain ⟨D₁, prod₁⟩ := ZF.exists_cartesianProduct hZF I X P
  obtain ⟨D₂, prod₂⟩ := ZF.exists_cartesianProduct hZF I p.ω D₁
  obtain ⟨D₃, prod₃⟩ := ZF.exists_cartesianProduct hZF I X D₂
  obtain ⟨ν, succ⟩ := KP.exists_successor (ZF.modelsKP hZF) p.ν
  obtain ⟨C, union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) D₃ ν
  let ρ : Env M 7 := ⟨fun i => [p.ω, p.e, p.δ, p.S, p.ν, X, Z].get i, fun _ => p.ω⟩
  let φ : BinarySchema 7 := { body := set[9] ⟪∃ a k t g,
    ⌜rd_quad_m⌝ₚ(⌜(.bound 1 : Term 9)⌝ₛ, a, k, t, g) ∧
    ⌜tg_level_key_m⌝ₚ(⌜(.bound 2 : Term 9)⌝ₛ, ⌜(.bound 3 : Term 9)⌝ₛ, ⌜(.bound 4 : Term 9)⌝ₛ,
      ⌜(.bound 5 : Term 9)⌝ₛ, ⌜(.bound 6 : Term 9)⌝ₛ, ⌜(.bound 7 : Term 9)⌝ₛ, ⌜(.bound 8 : Term 9)⌝ₛ,
      a, k, t, g, ⌜(.newest : Term 9)⌝ₛ)⟫ }
  have sat q α : φ.denote ρ q α ↔ ∃ a k t g, Rd_quad_d q a k t g ∧ Tg_level_key_d hZF p X Z a k t g α := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_quad_sat_l hZF.1, tg_level_key_m, Tg_level_key_d, Formula.satisfies_mem_iff,
      Formula.satisfies_subset_iff, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
      tg_aux_data_sat_l hZF.1, fn0_sat_l hZF.1, Formula.satisfies_isSuccessor_iff,
      tg_level_sat_l hZF, Definitional.Term.eval_weaken]; rfl
  obtain ⟨R, rel, read⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ C
  refine ⟨R, rel.1, fun q α => (read q α).trans ⟨fun h => (sat q α).mp h.2.2, fun h => ?_⟩⟩
  obtain ⟨a, k, t, g, code, key⟩ := h
  obtain ⟨v, vg, w, kw, aw⟩ := code
  have hq := (prod₃ q).mpr ⟨a, key.1, w, (prod₂ w).mpr ⟨k, key.2.1, v,
    (prod₁ v).mpr ⟨t, key.2.2.1, g, (power g).mpr key.2.2.2.1, vg⟩, kw⟩, aw⟩
  have hα := key.2.2.2.2.1.elim (fun h => (succ α).mpr (Or.inl h)) (fun eq => eq.symm ▸ succ.predecessor_mem)
  exact ⟨(union q).mpr (Or.inl hq), (union α).mpr (Or.inr hα),
    (sat q α).mpr ⟨a, k, t, g, ⟨v, vg, w, kw, aw⟩, key⟩⟩

/-- 稠密工厂的真实实现直接进入旧高度关系。 -/
theorem Tg_generic_target_d.level_l {p : Tg_params_d M.Domain} {ℓ s t k n β g a₀ b₀ κ C a u : M.Domain}
    (h : Tg_generic_target_d hZF p ℓ s t k n β g a₀ b₀ κ C a u) : Tg_level_d hZF p.ω p.e p.δ p.S n κ u β g := by
  obtain ⟨μ, A, d, H, m, V, P, r, hμ, hA, model, hm, constants, full, first, last, labels⟩ := h.2.2.2.1
  exact ⟨μ, A, d, H, m, C, V, P, r, hμ, hA, model, hm, h.2.1, constants, full, first, last, labels⟩

end YesMetaZFC.SetTheory.LargeCardinal
