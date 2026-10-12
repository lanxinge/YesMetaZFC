import YesMetaZFC.Model.SetTheory.Internal.TuplePackCode
import YesMetaZFC.Model.SetTheory.Internal.RankLargest
import YesMetaZFC.SetTheory.FlatPairing.RecursionSource
import YesMetaZFC.SetTheory.FlatPairing.SequenceSource

/-! # 从平坦前缀恢复原变量列的图

固定公式在后继秩层中自行找到前一层，量化完整平坦赋值及其前缀轨道，
再取前 n 项的图。所有见证的所属秩均由实际函数图自动给出。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

def st_unpack_s : UnarySchema 3 := { body := .existsE (.existsE
  (.conj (sv_last_m (.bound 1)) (.conj
    (Formula.isFunctionFromTo FlatPairing.convention .newest (.bound 5) (.bound 1)) (.conj
    (Formula.isFunctionFromTo FlatPairing.convention (.bound 3) (.bound 4) (.bound 1)) (.conj
    (fs_code_m (𝒞 := FlatPairing.convention) (.bound 5) (.bound 1) .newest (.bound 4) (.bound 2))
    (Formula.isRestriction FlatPairing.convention (.bound 3) .newest (.bound 4))))))) }

variable {ω ν μ X Y : M.Domain} (hω : M.IsOmega ω)
  (hV : V_d (kp_pair_l (ZF.modelsKP hZF)) ν X)
  (hW : V_d (kp_pair_l (ZF.modelsKP hZF)) μ Y) (hs : M.SuccessorOf μ ν) (hωY : M.mem ω Y)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l Q hZF hω hW hωY

include hω hV hW hs in
theorem st_unpack_source_l (n h p : (N).Domain) :
    Formula.satisfies (⟨Fin.cases p (Fin.cases h (Fin.cases n (fun _ => ⟨ω, hωY⟩))),
      fun _ => h⟩ : Env N 4) st_unpack_s.body ↔
    M.IsSetFunctionFromTo K h.val n.val X ∧ ∃ g, M.IsSetFunctionFromTo K g ω X ∧
      Fs_code_d K ω X g n.val p.val ∧ M.IsRestrictionOf K h.val g n.val := by
  let ρ : Env N 4 := ⟨Fin.cases p (Fin.cases h (Fin.cases n (fun _ => ⟨ω, hωY⟩))), fun _ => h⟩
  have hων : M.MemberSubset ω ν := by
    have hωμ := ZF.v_ordinal_height_l hZF hW (hω.isOrdinal hZF) hωY
    rcases (hs ω).mp hωμ with h | h
    · exact (v_ordinal_l Q hV).transitive ω h
    · exact fun i hi => (h i).mp hi
  have last (A g : (N).Domain) := sv_last_rank_l Q hZF hω hV hW hs hωY ((ρ.push A).push g) (.bound 1)
  have fn := rt_fp_function_from_l Q hZF hω hW hωY
  have code := rt_fs_code_l Q hZF hω hW hωY
  have cut := rt_fp_restriction_l Q hZF hω hW hωY
  have read : Formula.satisfies ρ st_unpack_s.body ↔ ∃ A g : (N).Domain,
      A.val = X ∧ (N).IsSetFunctionFromTo J g ⟨ω, hωY⟩ A ∧ (N).IsSetFunctionFromTo J h n A ∧
        Fs_code_d J ⟨ω, hωY⟩ A g n p ∧ (N).IsRestrictionOf J h g n := by
    simp only [st_unpack_s, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, last,
      Formula.satisfies_isFunctionFromTo_iff J (rt_model_ext_l hZF.1 (ZF.v_transitive_l Q hZF hW) _),
      fs_code_sat_l J (rt_model_ext_l hZF.1 (ZF.v_transitive_l Q hZF hW) _),
      Formula.satisfies_isRestriction_iff J]
    rfl
  refine read.trans ⟨?_, ?_⟩
  · rintro ⟨A, g, eq, hg, hh, cp, restrict⟩
    exact ⟨eq ▸ (fn h n A).mp hh, g.val, eq ▸ (fn g ⟨ω, hωY⟩ A).mp hg,
      eq ▸ (code A g n p (eq.symm ▸ hV) hων).mp cp, (cut h g n).mp restrict⟩
  · rintro ⟨hh, g, hg, cp, restrict⟩
    let A : (N).Domain := ⟨X, (ZF.v_successor_l Q hZF hV hW hs X).mpr (fun _ h => h)⟩
    let g' : (N).Domain := ⟨g, (ZF.v_successor_l Q hZF hV hW hs g).mpr
      (fp_function_rank_l Q hZF hω hV hων (fun i hi => ZF.v_ordinal_mem_l Q hZF hV (hων i hi)) hg)⟩
    exact ⟨A, g', rfl, (fn g' ⟨ω, hωY⟩ A).mpr hg, (fn h n A).mpr hh,
      (code A g' n p hV hων).mpr cp, (cut h g' n).mpr restrict⟩

end YesMetaZFC.SetTheory.Internal
