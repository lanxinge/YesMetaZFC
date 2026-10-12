import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRenewalSyntax

/-! # 同一完整回答对原查询表的所有合法代码为真

查询表允许选取不同但语义相同的代码。完整类型的同一个实现把三条查询
还原为同一个根、秩界及末位条件，故无需假定两张查询表逐字相等。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_reply_compare0_m : Formula 1 54 :=
  let p : Fin 54 → Term 54 := Term.bound
  set[54] ⟪∀ r b h,
    ⌜tg_reply_base_m⌝ₚ(⌜p 16⌝ₛ, ⌜p 17⌝ₛ, ⌜p 23⌝ₛ, ⌜p 24⌝ₛ, r, b, h) →
    r ∈ ⌜p 11⌝ₛ ∧ b ∈ ⌜p 11⌝ₛ ∧ h ∈ ⌜p 11⌝ₛ⟫

@[simp] theorem tg_reply_compare0_closed_l : tg_reply_compare0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_reply_compare0_m, Definitional.Formula.FreeClosed]

def tg_reply_compare_m : Formula 1 0 := Formula.forallClosure 54 (.imp tg_round0_m tg_reply_compare0_m)

theorem tg_reply_compare_closed_l : tg_reply_compare_m.FreeClosed :=
  (Definitional.Formula.freeClosed_forallClosure _).mpr ⟨tg_round0_closed_l, tg_reply_compare0_closed_l⟩

theorem tg_reply_compare_true_l (hZF : M.Models ZF) (ε : FreeVarId → M.Domain) :
    Formula.satisfies (⟨Fin.elim0, ε⟩ : Env M 0) tg_reply_compare_m := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  apply (Formula.satisfies_forallClosure_iff ε _).mpr
  intro p
  apply (Formula.satisfies_imp_iff ..).mpr
  intro round
  obtain ⟨seed, data⟩ := (Formula.satisfies_conj_iff ..).mp round
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at seed
  have hω := (Formula.satisfies_isOmega_iff ..).mp seed.1
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, v_sigma_sat_l (ZF.modelsKP hZF), smem_sat_l I,
    tt_realized_sat_l I (ZF.modelsKP hZF), tg_reply_language_sat_l hZF] at data
  obtain ⟨_, _, _, _, rank, model, _, real, _, language, hr, hb, hh, _⟩ := data
  simp only [tg_reply_compare0_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, tg_reply_base_sat_l I (ZF.modelsKP hZF),
    Definitional.Term.eval_weaken]
  intro r b h base
  have hw := (tt_constants_finite_l hZF hω language.finite language.limit language.rank language.constants).1
  obtain ⟨root, bound, height⟩ := base.scope_l I (ZF.modelsKP hZF) real.pool hw
  obtain ⟨S, _, rS⟩ := real.tuple.2.1 (p 17) language.root_slot
  obtain ⟨α, _, rα⟩ := real.tuple.2.1 (p 23) language.last_slot
  have trans := ZF.v_transitive_l I hZF rank
  exact ⟨(root.2 _ _ _ _ _ _ S model trans real rS).mpr
      ((language.root.2 _ _ _ _ _ _ S model trans real rS).mp hr),
    (bound.2 _ _ _ _ _ _ _ S α rank model real rS rα).mpr
      ((language.bound.2 _ _ _ _ _ _ _ S α rank model real rS rα).mp hb),
    (height.2 _ _ _ _ _ _ _ α rank model real rα).mpr
      ((language.height.2 _ _ _ _ _ _ _ α rank model real rα).mp hh)⟩

end YesMetaZFC.SetTheory.LargeCardinal
