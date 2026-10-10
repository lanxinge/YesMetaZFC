import YesMetaZFC.Model.Forcing.Closed.Master
import YesMetaZFC.Model.Forcing.Proper.Basic
import YesMetaZFC.SetTheory.BinaryWitnessClub

/-! # 内部可数闭偏序的 properness

在任意含条件域的 X 上，实际构造对稠密加强见证闭合的可数子集 club。
其成员内的每个正条件均可沿内部 ω 下降链取得主加强。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z ω : M.Domain}
variable (O : Preord_d M B R) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))
include O

/-- 任意内部可数闭偏序具有实际 club 主条件 properness。 -/
theorem closed_proper_l (hω : M.IsOmega ω) (hc : Closed_d I B R z ω) : Proper_d I ω B R z := by
  intro X hBX
  obtain ⟨C₀, hC₀, _⟩ := ZFC.cc_all_l I hZFC hω X
  let ρ : Env M 3 := ((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z
  let φ : UnarySchema 5 := {
    body := .conj (below_m (.bound 5) (.bound 4) (.bound 3) .newest (.bound 1)) (.mem .newest (.bound 2)) }
  have hφ D p q : φ.denote ((ρ.push D).push p) q ↔ Below_d M B R z q p ∧ M.mem q D := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_conj_iff, below_sat_l M hZFC.1,
      Formula.satisfies_mem_iff]
    rfl
  obtain ⟨C, hC, hcl⟩ := ZFC.bw_club_l I hZFC hω hC₀ φ ρ
  refine ⟨C, hC, fun N hN p hpN hp hz => closed_mstr_l O hZFC hω hc (hC.members N hN).2 hpN hp hz ?_⟩
  intro D r hDN hrN hd hr hrz
  obtain ⟨q, hqr, hqD⟩ := hd.2 r hr hrz
  obtain ⟨s, hsN, hs⟩ := (hcl N hN).2 D r hDN hrN ⟨q, hBX q hqr.1, (hφ D r q).mpr ⟨hqr, hqD⟩⟩
  exact ⟨s, hsN, ((hφ D r s).mp hs).2, ((hφ D r s).mp hs).1⟩

end YesMetaZFC.Model.Forcing.Internal
