import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Syntax

/-! # 指定稠密集的变动前缀递归步

从真实主条件与商名称出发，先在原前缀选择稠密加强名称，再投影到下一阶段。
已证明区间的迭代引理给出新主前缀；商换段和逐阶段比较同时得到实际证明。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_move_l {ω χ H c J d N S α B R b β C T D V E x}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ) (hH : H_d I χ H)
    (hJ : ∀ u v, M.PairMember I u v J ↔ M.mem u H ∧ M.mem v H ∧ M.mem u v)
    (hSub : Ssub_d I c d H J N S) (hElem : Selem_d I ω c d)
    (hβN : M.mem β N) (hαβ : M.MemberSubset α β)
    (hB : M.mem B N) (hR : M.mem R N) (hD : M.mem D N) (hV : M.mem V N) (hE : M.mem E N)
    (h : Row_stage_d M α B R b) (L : Cond_order_d M C T C) (O : Cond_order_d M D V D)
    (k : Row_link_d I α B R C T) (l : Row_link_d I β C T D V)
    (hP : Row_pil_d I α B R b C T N) (hd : Dense_set_d M D V D E)
    (hx : Row_pr_state_d I α B R b D N x) :
    ∃ y, Row_pr_state_d I β C T b D N y ∧ Row_pr_move_d I α B R b D V N β T E x y := by
  obtain ⟨p, τ, K, hx, hm, hτ, hK, hτK⟩ := hx
  have kl := row_link_comp_l hZF O hαβ k l
  obtain ⟨σ, ν, η, hσ, hν, hη, hσK, hση, hστ⟩ :=
    row_dense_name_l hZFC hω hχ hH hJ hSub hElem hB hR hD hV hE h O kl hd hm hK hτ hτK
  obtain ⟨ρ, K', f, F, hρ, hK', hf, hF, happ, hρK, hσρ⟩ :=
    row_project_name_l hZF hω hχ hH hJ hSub hElem hβN hαβ h l hK hσ hσK
  obtain ⟨q, hq, hpq, hqm, hl⟩ := hP ρ p K' hK' hρ hρK hm
  obtain ⟨γ, hγ⟩ := gname_exists_l hZF (k.mem b h.base)
  have hργ := row_quot_accept_l hZF h.order L k hρ hq hpq hK' hρK hγ hl
  obtain ⟨K'', hK'', hσ', hσK'⟩ := row_quot_transfer_l hZF h L k hq hpq hf hF hK hσ hρ hσK hσρ hγ hργ
  obtain ⟨y, hy⟩ := (I).total q σ
  exact ⟨y, ⟨q, σ, K'', hy, hqm, hσ', hK'', hσK'⟩,
    p, τ, q, σ, K, ν, η, hx, hy, hpq, hσ, hK, hν, hη, hσK, hση, hστ,
    row_cut_project_l hZF hω hχ hH hJ hSub hElem hβN hαβ h hf happ hl⟩

end YesMetaZFC.Model.Forcing.Internal
