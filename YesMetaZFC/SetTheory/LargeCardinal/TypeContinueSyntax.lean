import YesMetaZFC.SetTheory.LargeCardinal.TypeOneStepImage
import YesMetaZFC.SetTheory.LargeCardinal.TypeImageSyntax
import YesMetaZFC.Model.SetTheory.Internal.SubtypeProgramSyntax
import YesMetaZFC.Model.SetTheory.Internal.SubtypeSyntax
import YesMetaZFC.Model.SetTheory.Internal.TypeExceedsSyntax
import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticLanguageSyntax

/-! # 继续分支的一步伸展反射句子

原超过关系与旧类型弹性产生引理 3.23 的同一扩展器。句子保留原程序，
结论是实际像上的子类型；它不要求新类型预先在旧工作模型中实现。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tc_image_m {s} (ω κ δ n U D u τ m w b z : Term s) (σ : Fin 7 → Term s) : Formula 1 s := set[s] ⟪
  ∃ X K R L F c d Y T j κ' U' D' u',
    ⌜ti_image_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜δ⌝ₛ, ⌜τ⌝ₛ, ⌜U⌝ₛ, ⌜D⌝ₛ, ⌜u⌝ₛ, X, K, R, L, F, c, d, Y, T, j, κ', U', D', u') ∧
    ⌜tt_pool_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, U', D') ∧
    ⌜fun ω n κ τ m U w b z u s₀ s₁ s₂ s₃ s₄ s₅ s₆ => ts_subtype_m ω n κ τ m U w b z u
      (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
      (⌜ω⌝ₛ, ⌜n⌝ₛ, κ', ⌜τ⌝ₛ, ⌜m⌝ₛ, U', ⌜w⌝ₛ, ⌜b⌝ₛ, ⌜z⌝ₛ, u',
        ⌜σ 0⌝ₛ, ⌜σ 1⌝ₛ, ⌜σ 2⌝ₛ, ⌜σ 3⌝ₛ, ⌜σ 4⌝ₛ, ⌜σ 5⌝ₛ, ⌜σ 6⌝ₛ)⟫

-- 二十八个原输入：ω,κ,δ,n,B,U,D,u,τ,m,C,V,W,w,b,a,z；四个弹性查询；七个程序槽位。
def tc_seed0_m : Formula 1 28 :=
  let p : Fin 28 → Term 28 := Term.bound
  set[28] ⟪
  ⌜Formula.isOmega⌝ₚ(⌜p 0⌝ₛ) ∧
  ⌜fun ω n b a z s₀ s₁ s₂ s₃ s₄ s₅ s₆ => ts_program_m ω n b a z
    (Fin.cases s₀ (Fin.cases s₁ (Fin.cases s₂ (Fin.cases s₃ (Fin.cases s₄ (Fin.cases s₅ (fun _ => s₆)))))))⌝ₚ
    (⌜p 0⌝ₛ, ⌜p 3⌝ₛ, ⌜p 14⌝ₛ, ⌜p 15⌝ₛ, ⌜p 16⌝ₛ, ⌜p 21⌝ₛ, ⌜p 22⌝ₛ, ⌜p 23⌝ₛ, ⌜p 24⌝ₛ, ⌜p 25⌝ₛ, ⌜p 26⌝ₛ, ⌜p 27⌝ₛ) ∧
  ⌜ee_language_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜p 4⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ, ⌜p 17⌝ₛ, ⌜p 18⌝ₛ, ⌜p 19⌝ₛ, ⌜p 20⌝ₛ) ∧
  ⌜Formula.isLimitOrdinal⌝ₚ(⌜p 8⌝ₛ) ∧ ⌜p 8⌝ₛ ∈ ⌜p 2⌝ₛ ∧ ⌜v_sigma_m⌝ₚ(⌜p 8⌝ₛ, ⌜p 10⌝ₛ) ∧
  ⌜tt_constants0_m⌝ₚ(⌜p 8⌝ₛ, ⌜p 10⌝ₛ, ⌜p 11⌝ₛ) ∧ ⌜ee_elastic_m⌝ₚ(⌜p 17⌝ₛ, ⌜p 18⌝ₛ, ⌜p 19⌝ₛ, ⌜p 20⌝ₛ, ⌜p 7⌝ₛ) ∧
  ⌜tx_exceeds_m⌝ₚ(⌜p 0⌝ₛ, ⌜p 2⌝ₛ, ⌜p 1⌝ₛ, ⌜p 3⌝ₛ, ⌜p 5⌝ₛ, ⌜p 6⌝ₛ, ⌜p 7⌝ₛ, ⌜p 8⌝ₛ, ⌜p 9⌝ₛ, ⌜p 11⌝ₛ, ⌜p 12⌝ₛ, ⌜p 13⌝ₛ)⟫

def tc_result0_m : Formula 1 28 := .conj (tc_image_m
  (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9)
  (.bound 13) (.bound 14) (.bound 16)
  (Fin.cases (.bound 21) (Fin.cases (.bound 22) (Fin.cases (.bound 23) (Fin.cases (.bound 24)
    (Fin.cases (.bound 25) (Fin.cases (.bound 26) (fun _ => .bound 27))))))))
  (.conj (.mem (.bound 9) (.bound 0)) (tt_pool_m (.bound 0) (.bound 9) (.bound 11) (.bound 12)))

@[simp] theorem tc_seed0_closed_l : tc_seed0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_seed0_m, Definitional.Formula.FreeClosed, Fin.forall_fin_succ]
@[simp] theorem tc_result0_closed_l : tc_result0_m.FreeClosed := by
  simp -implicitDefEqProofs [tc_result0_m, tc_image_m, Definitional.Formula.FreeClosed]
  apply ts_subtype_closed_l <;> try rfl
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i

def tc_transfer_m : Formula 1 0 := Formula.forallClosure 28 (.imp tc_seed0_m tc_result0_m)

theorem tc_transfer_closed_l : tc_transfer_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨tc_seed0_closed_l, tc_result0_closed_l⟩

/-- 超过关系中的真实上层实现调用已证的一步伸展，不另设实现参数。 -/
theorem tc_transfer_true_l (hZFC : M.Models ZFC) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) tc_transfer_m := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  simp only [tc_seed0_m, tc_result0_m, tc_image_m, Formula.satisfies_imp_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, ts_program_sat_l hZF, ee_language_sat_l hZFC,
    Formula.satisfies_isLimitOrdinal_iff, Formula.satisfies_mem_iff, v_sigma_sat_l (ZF.modelsKP hZF),
    tt_constants0_sat_l hZF.1, ee_elastic_sat_l, tx_exceeds_sat_l hZF, Formula.satisfies_exists_iff,
    ti_image_sat_l hZF, tt_pool_sat_l I (ZF.modelsKP hZF), ts_subtype_sat_l (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken, tt_eval_cases_l]
  rintro ⟨hω, prog, language, hτ, hτδ, rank, constants, elastic, exceeds⟩
  have step := ee_one_step_l hZFC hω prog language hτ hτδ rank constants elastic exceeds
  obtain ⟨_, _, η, A, c₀, R₀, r, hA, model, type, _, _, _, _, witness⟩ := exceeds
  obtain ⟨_, regular, _⟩ := sc_v_inaccessible_read_l hZF hA
    ((language.inaccessible c₀ A R₀ r (p 2) (p 7) model type).mp elastic.2.1)
  obtain ⟨_, _, _, _, _, _, _, _, _, realized, _⟩ := witness
  obtain ⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u', hX, source, hL, hk, ht,
    loc, card, strong, mx, my, ultra, critical, bound, limit, hU, hD, hu, pool, subtype⟩ :=
    step.image_l hZF hω regular.isLimitOrdinal prog language hA model type hτ realized.finite
  exact ⟨⟨X, K, R, L, F, c, d, Y, T, j, κ', U', D', u',
    ⟨hX, source, hL, hk, ht, loc, card, strong, mx, my, ultra, critical, bound, limit, hU, hD, hu⟩, pool, subtype⟩,
    realized.finite, realized.pool⟩

end YesMetaZFC.SetTheory.LargeCardinal
