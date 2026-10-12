import YesMetaZFC.SetTheory.LargeCardinal.TypeGameStepImage
import YesMetaZFC.SetTheory.LargeCardinal.TypeImageSyntax

/-! # 一轮回答的实际超幂证书公式

证书包含原秩段、所属扩展器、同一超幂及完整规则 (7)。将它单独编码，
使反射句子只绑定游戏输入，而后继读取能直接消费这一份存在证书。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_image_m {d} (ω κ δ l n U D u τ Q w b z r q h : Term d) (σ : Fin 7 → Term d) : Formula 1 d := set[d] ⟪
  ∃ X K R L F c d Y T j κ' U' D' u',
    ⌜ti_image_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜δ⌝ₛ, ⌜τ⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ, X, K, R, L, F, c, d, Y, T, j, κ', U', D', u') ∧
    (∃ W, ⌜v_sigma_m⌝ₚ(L, W) ∧ ⌜Q⌝ₛ ∈ W) ∧
    ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜l⌝ₛ, U', D') ∧
    ⌜fun ω l n κ τ U D Q u w b z r q h s₀ s₁ s₂ s₃ s₄ s₅ s₆ => tg_reply_m ω l n κ τ U D Q u w b z r q h
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜ω⌝ₛ, ⌜l⌝ₛ, ⌜n⌝ₛ, κ', ⌜τ⌝ₛ, U', D', ⌜Q⌝ₛ, u', ⌜w⌝ₛ, ⌜b⌝ₛ, ⌜z⌝ₛ, ⌜r⌝ₛ, ⌜q⌝ₛ, ⌜h⌝ₛ,
        ⌜σ 0⌝ₛ, ⌜σ 1⌝ₛ, ⌜σ 2⌝ₛ, ⌜σ 3⌝ₛ, ⌜σ 4⌝ₛ, ⌜σ 5⌝ₛ, ⌜σ 6⌝ₛ)⟫

@[simp] theorem tg_image_closed_l {d} (ω κ δ l n U D u τ Q w b z r q h : Term d) (σ : Fin 7 → Term d)
    (hω : ω.freeSupport = []) (hκ : κ.freeSupport = []) (hδ : δ.freeSupport = [])
    (hl : l.freeSupport = []) (hn : n.freeSupport = []) (hU : U.freeSupport = []) (hD : D.freeSupport = [])
    (hu : u.freeSupport = []) (hτ : τ.freeSupport = []) (hQ : Q.freeSupport = []) (hw : w.freeSupport = [])
    (hb : b.freeSupport = []) (hz : z.freeSupport = []) (hr : r.freeSupport = []) (hq : q.freeSupport = [])
    (hh : h.freeSupport = []) (hσ : ∀ i, (σ i).freeSupport = []) :
    (tg_image_m ω κ δ l n U D u τ Q w b z r q h σ).FreeClosed := by
  simp -implicitDefEqProofs [tg_image_m, Definitional.Formula.FreeClosed, hω, hκ, hδ, hl, hn, hU, hD, hu,
    hτ, hQ, hw, hb, hz, hr, hq, hh, hσ, Fin.forall_fin_succ]

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_image_sat_l {d} (ρ : Env M d) (ω κ δ l n U D u τ Q w b z r q h : Term d) (σ : Fin 7 → Term d) :
    Formula.satisfies ρ (tg_image_m ω κ δ l n U D u τ Q w b z r q h σ) ↔
    ∃ X K R L F c d Y T j κ' U' D' u',
      V_d I (δ.eval ρ) X ∧ Ep_source_d hZF (ω.eval ρ) (κ.eval ρ) K X R ∧
      M.mem L (δ.eval ρ) ∧ M.mem (κ.eval ρ) L ∧ M.mem (τ.eval ρ) L ∧
      (∃ W, V_d I L W ∧ M.mem (Q.eval ρ) W) ∧
      It_local_d (ω.eval ρ) X (κ.eval ρ) L F ∧ Sc_inaccessible_d (ω.eval ρ) X L ∧
      Ex_strength_d hZF (ω.eval ρ) (κ.eval ρ) L X F ∧ Smem_d I c X R ∧ Smem_d I d Y T ∧
      It_ultra_d hZF (ω.eval ρ) (κ.eval ρ) L F c d j ∧ Wd_crit_d I X j (κ.eval ρ) κ' ∧
      M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧ Rd_entry_d (U.eval ρ) U' j ∧
      Rd_entry_d (D.eval ρ) D' j ∧ Rd_entry_d (u.eval ρ) u' j ∧ Tt_pool_d I (ω.eval ρ) (l.eval ρ) U' D' ∧
      Tg_reply_d I (ω.eval ρ) (l.eval ρ) (n.eval ρ) κ' (τ.eval ρ) U' D' (Q.eval ρ) u' (w.eval ρ)
        (b.eval ρ) (fun i => (σ i).eval ρ) (z.eval ρ) ⟨r.eval ρ, q.eval ρ, h.eval ρ⟩ := by
  have eta (f : Fin 7 → M.Domain) :
      (Fin.cases (f 0) (Fin.cases (f 1) (Fin.cases (f 2) (Fin.cases (f 3)
        (Fin.cases (f 4) (Fin.cases (f 5) (fun _ => f 6))))))) = f := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  simp only [tg_image_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    ti_image_sat_l hZF, v_sigma_sat_l (ZF.modelsKP hZF), Formula.satisfies_mem_iff,
    tt_pool_sat_l I (ZF.modelsKP hZF), tg_reply_sat_l hZF,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, tt_eval_cases_l, eta (fun i => (σ i).eval ρ)]
  constructor
  · rintro ⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u', core, queryRank, pool, reply⟩
    obtain ⟨rank, source, hL, hk, ht, loc, card, strong, mx, my, ultra, critical, bound, limit, hU, hD, hu⟩ := core
    exact ⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u', rank, source, hL, hk, ht, queryRank,
      loc, card, strong, mx, my, ultra, critical, bound, limit, hU, hD, hu, pool, reply⟩
  · rintro ⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u', rank, source, hL, hk, ht, queryRank,
      loc, card, strong, mx, my, ultra, critical, bound, limit, hU, hD, hu, pool, reply⟩
    exact ⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u',
      ⟨rank, source, hL, hk, ht, loc, card, strong, mx, my, ultra, critical, bound, limit, hU, hD, hu⟩,
      queryRank, pool, reply⟩

end YesMetaZFC.SetTheory.LargeCardinal
