import YesMetaZFC.Model.Forcing.Applications.Collapse.Rule
import YesMetaZFC.Model.Forcing.Closed.ProperName
import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Rule

/-! # 参数化塌缩的实际 proper 后继规则

同一原公式后继已经带有预序、内部 ω 和可数闭性名称；直接把这些真实证书
转为 properness。它可以与一般 proper 规则共用全部后继及完整区间设施。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem collapse_rule_pr_l (ρ : Env M 3) (hω : M.IsOmega (ρ.bound 2)) : Row_pr_rule_d I coll_rule_s ρ := by
  intro δ F G b D V h _ hd
  obtain ⟨α, B, R, hδ, hB, hR, w, x, y, A, T, t, hw, _, _, hn, hNext⟩ :=
    (coll_rule_denote_l I hZFC.1 ρ δ F G b D V).mp hd
  have hs := h.stages α B R hB hR
  have hb : b ≠ B := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hs.base)
  have hp := below_refl_l hs.order hs.base hb
  obtain ⟨hP, _, hc⟩ := collapse_names_closed_l hs.order hZFC hω hs.base hw hp hn
  exact ⟨α, B, R, hδ, hB, hR, A, T, t, hn.1.2.1,
    closed_name_proper_l hs.order hZFC hω hs.base hw hp hn.1.1 hn.1.2.1 hP hc, hNext⟩

end YesMetaZFC.Model.Forcing.Internal
