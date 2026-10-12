import YesMetaZFC.SetTheory.Descriptive.GameGlue

/-! # 玩家 II 获胜局面的闭包性质

所有后继均可获胜时，模型内选择给出各后继的策略，再按首项拼接。
轮到 II 时，一个可获胜后继已经足够。两种闭包均用于同一实际局面集合。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

section Choice
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_ii_all_l {ω X F J B W Z Q s n a : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (runs : M.IsFunctionSpace I B ω X)
    (strategies : M.IsFunctionSpace I Z F X) (positions : Cg_ii_d I ω X F J B W Q)
    (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n X) (ha : M.mem a X)
    (all : ∀ x, M.mem x X → ∀ t, Fseq_end_d I ω t s x → M.mem t Q) : M.mem s Q := by
  let ρ : Env M 7 := ((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push X).push F).push J).push B).push W).push s
  let φ : BinarySchema 7 := { body := .existsE (.conj
      (fseq_end_m (𝒞 := kpair_convention_l) (.bound 9) .newest (.bound 3) (.bound 2))
      (cg_tail_win_m false (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1))) }
  have sat x τ : φ.denote ρ x τ ↔ ∃ t, Fseq_end_d I ω t s x ∧ Cg_tail_win_d I false ω X F J B W t τ := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      fseq_end_sat_l I hZF.1, cg_tail_win_sat_l I hZF.1]
    rfl
  obtain ⟨K, table, read⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := X) (Y := Z) (by
    intro x hx
    obtain ⟨_, t, _, _, endt⟩ := ZF.fseq_end_exists_l I hZF hω hn hs hx
    obtain ⟨_, τ, win⟩ := (positions t).mp (all x hx t endt)
    exact ⟨τ, (strategies τ).mpr (fn0_function_l (ZF.modelsKP hZF) win.1), (sat x τ).mpr ⟨t, endt, win⟩⟩)
  refine (positions s).mpr ⟨(space s).mpr ⟨n, hn, hs⟩, ?_⟩
  apply cg_glue_l hZF hω space runs strategies hn hs ha table
  intro x _ _ τ hτ t endt
  obtain ⟨u, endu, win⟩ := (sat x τ).mp (read x τ hτ)
  exact fseq_end_rebuild_l I hZF.1 endu endt ▸ win

end Choice

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_ii_some_l {ω X F J B W Z Q s n a t : M.Domain} (hω : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (runs : M.IsFunctionSpace I B ω X)
    (strategies : M.IsFunctionSpace I Z F X) (positions : Cg_ii_d I ω X F J B W Q)
    (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n X) (ha : M.mem a X)
    (turn : ¬ M.mem n J) (endt : Fseq_end_d I ω t s a) (ht : M.mem t Q) : M.mem s Q := by
  obtain ⟨_, τ, win⟩ := (positions t).mp ht
  obtain ⟨K, table, read⟩ := ZF.exists_constantFunction hZF I (source := X)
    ((strategies τ).mpr (fn0_function_l (ZF.modelsKP hZF) win.1))
  refine (positions s).mpr ⟨(space s).mpr ⟨n, hn, hs⟩, ?_⟩
  apply cg_glue_l hZF hω space runs strategies hn hs ha table
  intro x _ head υ hυ u endu
  have eq := head turn
  subst x
  have eq := table.1.2 a τ υ ((read a τ).mpr ⟨ha, rfl⟩) hυ
  subst υ
  exact fseq_end_rebuild_l I hZF.1 endt endu ▸ win

/-- 不在收益树中的有限证据使 II 立即获胜；常值图就是所需的真实策略。 -/
theorem cg_ii_bad_l {ω X F J B W Q T s a : M.Domain} (positions : Cg_ii_d I ω X F J B W Q)
    (body : Body_d F B T W) (hs : M.mem s F) (bad : ¬ M.mem s T) (ha : M.mem a X) : M.mem s Q := by
  obtain ⟨σ, fn, _⟩ := ZF.exists_constantFunction hZF I (source := F) ha
  exact (positions s).mpr ⟨hs, σ, fn0_of_function_l (ZF.modelsKP hZF) fn,
    fun f _ sf _ win => bad (((body f).mp win).2 s hs sf)⟩

end YesMetaZFC.SetTheory.Descriptive
