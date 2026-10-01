import YesMetaZFC.Model.Forcing.Iteration.Proper.Lemma

/-! # 已证明迭代区间的稠密主加强

先在原主前缀上选择进入指定 N 稠密集的商名称，再消费实际区间迭代引理。
尾部比较的单调性保证输出仍加强原名称，且在后段接受被选中的稠密见证。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 固定原前缀，同时满足旧名称的实际尾部比较和任意指定的 N 稠密集。 -/
theorem row_pil_dense_l {ω χ H c J d N S α B R b D V E p τ K}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ) (hH : H_d I χ H)
    (hJ : ∀ x y, M.PairMember I x y J ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H J N S) (hElem : Selem_d I ω c d)
    (hB : M.mem B N) (hR : M.mem R N) (hD : M.mem D N) (hV : M.mem V N) (hE : M.mem E N)
    (h : Row_stage_d M α B R b) (L : Cond_order_d M D V D) (k : Row_link_d I α B R D V)
    (hP : Row_pil_d I α B R b D V N) (hd : Dense_set_d M D V D E)
    (hK : Row_quot_d I α B b D N K) (hτ : Name_d M B τ)
    (hτK : Mem_force_d M B R B p τ K) (hm : Mstr_d M B R B N p) :
    ∃ q σ γ η, M.mem q D ∧ M.IsRestrictionOf I p q α ∧ Mstr_d M D V D N q ∧
      Row_quot_lower_d I α B R b D V N τ p q ∧ Name_d M B σ ∧ Gname_d (M := M) D b γ ∧
      Check_d M b E η ∧ Mem_force_d M D V D q σ γ ∧ Mem_force_d M D V D q σ η := by
  obtain ⟨σ, ν, η, hσ, hν, hη, hσK, hση, hστ⟩ :=
    row_dense_name_l hZFC hω hχ hH hJ hSub hElem hB hR hD hV hE h L k hd hm hK hτ hτK
  obtain ⟨q, hq, hpq, hqm, hl⟩ := hP σ p K hK hσ hσK hm
  obtain ⟨γ, hγ⟩ := gname_exists_l hZF (k.mem b h.base)
  have hηn := check_name_l M (check_range_l M hZF) h.base hη
  have hqE := (regular_mem_l L σ η).1 p q (k.mem p hm.1) ⟨hq, hqm.2.1, k.below q p hq hpq⟩
    ((row_mem_force_l hZF h.order L k hm.1 hσ hηn).mp hση)
  exact ⟨q, σ, γ, η, hq, hpq, hqm, row_quot_lower_mono_l hZF h L k hq hpq hK hσ hτ hν hσK hστ hl,
    hσ, hγ, hη, row_quot_accept_l hZF h.order L k hσ hq hpq hK hσK hγ hl, hqE⟩

end YesMetaZFC.Model.Forcing.Internal
