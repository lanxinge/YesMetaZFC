import YesMetaZFC.SetTheory.LargeCardinal.TypeGameHistory
import YesMetaZFC.SetTheory.LargeCardinal.LocalIndiscerniblesLeast

/-! # 原游戏固定参数的自动构造

重置高度取相对于 max(δ,rank(S)) 的原最小局部不可分辨对的第一坐标。
三张代码表和内部 0、1、2、3 同时构造；输入不包含任何查询或编译谕示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_low_d (hZF : M.Models ZF) (ω e δ S ν : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ ρ θ γ U D μ, Rk_d I S ρ ∧ M.IsOrdinal θ ∧ M.IsUnionOfTwo θ δ ρ ∧
    M.IsOrdinalAddition I γ θ ω ∧ V_d I γ U ∧ Tt_pool_d I ω e U D ∧ Li_least_d I ω e U D θ ν μ

theorem tg_low_l (hZF : M.Models ZF) {ω δ : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsOrdinal δ) (S : M.Domain) :
    ∃ e ν, (∀ x, ¬ M.mem x e) ∧ M.mem e ω ∧ Tg_low_d hZF ω e δ S ν := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ρ, rank⟩ := ZF.rk_exists_l I hZF S
  obtain ⟨P, pair⟩ := KP.exists_pair (ZF.modelsKP hZF) δ ρ
  obtain ⟨θ, union⟩ := KP.exists_union (ZF.modelsKP hZF) P
  have ordinal : M.IsOrdinal θ := .of_union (ZF.modelsKP hZF) union (fun x hx =>
    ((pair x).mp hx).elim (fun eq => eq.symm ▸ hδ) (fun eq => eq.symm ▸ rank.ordinal I))
  have max : M.IsUnionOfTwo θ δ ρ := by
    intro x
    refine (union x).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy, hx⟩
      exact ((pair y).mp hy).elim (fun eq => Or.inl (eq ▸ hx)) (fun eq => Or.inr (eq ▸ hx))
    · intro hx
      exact hx.elim (fun h => ⟨δ, (pair δ).mpr (Or.inl rfl), h⟩) (fun h => ⟨ρ, (pair ρ).mpr (Or.inr rfl), h⟩)
  obtain ⟨e, γ, U, D, ν, μ, he, heω, sum, hU, pool, least⟩ := li_canonical_l I hZF hω ordinal
  exact ⟨e, ν, he, heω, ρ, θ, γ, U, D, μ, rank, ordinal, max, sum, hU, pool, least⟩

theorem Tg_low_d.read_l (hZF : M.Models ZF) {ω e δ S ν : M.Domain} (hδ : M.IsOrdinal δ)
    (low : Tg_low_d hZF ω e δ S ν) : M.mem δ ν ∧ ∃ Y, V_d (kp_pair_l (ZF.modelsKP hZF)) ν Y ∧ M.mem S Y := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨ρ, θ, _, _, _, _, rank, _, max, _, _, _, least⟩ := low
  have oν := least.2.1.1
  have below (α : M.Domain) (hα : M.IsOrdinal α) (sub : M.MemberSubset α θ) : M.mem α ν :=
    ordinal_down_l (ZF.modelsKP hZF) hα oν sub least.1
  obtain ⟨Y, hY⟩ := ZF.v_exists_l I hZF oν
  exact ⟨below δ hδ (fun x hx => (max x).mpr (Or.inl hx)), Y, hY,
    (ZF.rk_mem_l I hZF rank hY).mpr (below ρ (rank.ordinal I) (fun x hx => (max x).mpr (Or.inr hx)))⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Tg_setup_d (p : Tg_params_d M.Domain) (X : M.Domain) : Prop where
  omega : M.IsOmega p.ω
  empty : ∀ x, ¬ M.mem x p.e
  one : M.SuccessorOf p.a p.e
  two : M.SuccessorOf p.b p.a
  three : M.SuccessorOf p.c p.b
  limit : M.IsLimitOrdinal p.δ
  above : M.mem p.ω p.δ
  rank : V_d I p.δ X
  letters : M.mem p.A X
  elastic : ∃ D, Ee_catalog_d hZFC p.ω p.δ X D p.E
  programs : ∃ H, V_d I p.ω H ∧ Tg_program_catalog_d hZFC p.ω H p.P ∧ M.MemberSubset p.P H
  queries : Tg_query_catalog_d hZFC p.ω p.e p.δ X p.Q
  elastic_bound : M.MemberSubset p.E X
  query_bound : M.MemberSubset p.Q X
  low : Tg_low_d hZF p.ω p.e p.δ p.S p.ν

/-- 从原数学输入一次构造全部参数；代码表的选择只发生于开局之前。 -/
theorem tg_setup_l {ω δ A S X : M.Domain} (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (hwδ : M.mem ω δ) (hX : V_d I δ X) (hA : M.mem A X) :
    ∃ p : Tg_params_d M.Domain, p.ω = ω ∧ p.δ = δ ∧ p.A = A ∧ p.S = S ∧ Tg_setup_d hZFC p X := by
  obtain ⟨e, ν, he, heω, low⟩ := tg_low_l hZF hω hδ.1 S
  obtain ⟨a, ha, haω⟩ := hω.1.2 e heω
  obtain ⟨b, hb, hbω⟩ := hω.1.2 a haω
  obtain ⟨c, hc, _⟩ := hω.1.2 b hbω
  obtain ⟨D, E, elastic, eBound⟩ := ee_catalog_l hZFC hω hδ hwδ hX
  obtain ⟨H, P, hH, programs, pBound⟩ := tg_program_catalog_l hZFC hω
  obtain ⟨Q, queries, qBound⟩ := tg_query_catalog_l hZFC hω he hδ hwδ hX
  exact ⟨⟨ω, e, a, b, c, δ, A, S, ν, E, P, Q⟩, rfl, rfl, rfl, rfl,
    hω, he, ha, hb, hc, hδ, hwδ, hX, hA, ⟨D, elastic⟩, ⟨H, hH, programs, pBound⟩, queries, eBound, qBound, low⟩

end YesMetaZFC.SetTheory.LargeCardinal
