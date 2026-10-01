import YesMetaZFC.Model.Forcing.Iteration.Names.QuotientEntry
import YesMetaZFC.Model.Forcing.Iteration.Names.QuotientOrder
import YesMetaZFC.Model.Forcing.Iteration.Names.Bounded

/-! # 变动前缀时的商成员与实际尾部比较

前缀名称被下一阶段接受后，原名称自动进入新的商条件集。两段实际尾部加强
通过规范拼接的结合律复合，保留适用于非分离预序的字面序比较。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 前段名称原样搬到新阶段；投影被接受即自动得到新的商成员力迫。 -/
theorem row_quot_transfer_l (hZF : M.Models ZF) {α B R b β E T D N τ σ p q K γ f F}
    (h : Row_stage_d M α B R b) (L : Cond_order_d M E T E)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R E T)
    (hq : M.mem q E)
    (hpq : M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) p q α)
    (hf : Row_proj_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β D E f)
    (hF : Check_d M b f F)
    (hK : Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B b D N K)
    (hτ : Name_d M B τ) (hσ : Name_d M B σ) (hτK : Mem_force_d M B R B p τ K)
    (hτσ : Rel_force_d M B R B F p τ σ) (hγ : Gname_d (M := M) E b γ) (hσγ : Mem_force_d M E T E q σ γ) :
    ∃ K', Row_quot_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β E b D N K' ∧
      Name_d M E τ ∧ Mem_force_d M E T E q τ K' := by
  have hp := hτK.1
  have hb := k.mem b h.base
  have hqp : Below_d M E T E q p := ⟨hq, (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) E (he ▸ hq)), k.below q p hq hpq⟩
  have hqb : Below_d M E T E q b := ⟨hq, hqp.2.1,
    L.trans q p b hq (k.mem p hp) hb hqp.2.2 ((k.order p b hp h.base).mpr (h.top p hp))⟩
  obtain ⟨c, hc, hcn, _⟩ := zf_check_l M hZF h.base D
  obtain ⟨ν, hν, hνn, _⟩ := zf_check_l M hZF h.base N
  have mem {X v} (hv : Check_d M b X v) (hvn : Name_d M B v)
      (hX : ∀ r, M.mem r D → M.mem r N → M.mem r X) : Mem_force_d M E T E q τ v :=
    (regular_mem_l L τ v).1 p q (k.mem p hp) hqp ((row_mem_force_l hZF h.order L k hp hτ hvn).mp
      (row_quot_subset_l hZF h.order h.base hK hX hv (h.top p hp) hτK))
  have hFn := check_name_l M (check_range_l M hZF) h.base hF
  have hrel := (rel_force_regular_l L hZF (row_name_l k hFn) (row_name_l k hτ) (row_name_l k hσ)).1 p q (k.mem p hp) hqp
    ((row_rel_force_l hZF h.order L k hp hFn hτ hσ).mp hτσ)
  obtain ⟨K', hK'⟩ := row_quot_exists_l hZF hb β D N
  exact ⟨K', hK', row_name_l k hτ, row_quot_enter_l hZF L hb hqb hf hF hc hν hγ hK'
    (row_name_l k hτ) (row_name_l k hσ) (mem hc hcn (fun _ hr _ => hr))
      (mem hν hνn (fun _ _ hrN => hrN)) hrel hσγ⟩

/-- 两段真实尾部加强复合；证明使用前缀投影的决定分支和拼接结合律。 -/
theorem row_quot_lower_comp_l (hZF : M.Models ZF) {ω χ H c J d N S α B R b β E T D V τ σ p q r f}
    (hω : M.IsOmega ω) (hχ : M.IsLimitOrdinal χ)
    (hH : H_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) χ H)
    (hJ : ∀ x y, M.PairMember (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) x y J ↔
      M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) c d H J N S)
    (hElem : Selem_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) ω c d)
    (hβN : M.mem β N) (hαβ : M.MemberSubset α β) (h : Row_stage_d M α B R b)
    (L : Cond_order_d M E T E)
    (k : Row_link_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R E T)
    (hf : Row_proj_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β D E f)
    (hApp : Check_app_d M B R B b f τ σ) (hτ : Name_d M B τ) (hq : M.mem q E)
    (hpq : M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) p q α)
    (hqr : M.IsRestrictionOf (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) q r β)
    (h₀ : Row_quot_lower_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b E T N σ p q)
    (h₁ : Row_quot_lower_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) β E T b D V N τ q r) :
    Row_quot_lower_d (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) α B R b D V N τ p r := by
  intro u a v c hc hcp w hw
  obtain ⟨hu, huN, ha, hau, huv, hca, heq⟩ := hc
  obtain ⟨x, hx, hux⟩ := hf.1.2.2 u hu
  have hxu := ((hf.2 u x).mp hux).2
  have hxN := selem_restriction_l hZF hω hχ hH hJ hSub hElem hβN huN hxu
  obtain ⟨t, ht, _, _⟩ := zf_check_l M hZF h.base x
  have hσt := hApp c u x v t ⟨hcp.1, hcp.2.1, h.top c hcp.1⟩ hux huv ht heq
  obtain ⟨q', hq'⟩ := row_splice_exists_l M hZF α c q
  obtain ⟨hq'E, hq'q, hq'c⟩ := k.splice q p c q' hq hpq hcp.1 hcp.2.2 hq'
  have hq'x := h₀ x a t c ⟨hx, hxN, ha, hxu.trans hau hαβ, ht, hca, hσt⟩ hcp q' hq'
  have hvn := check_name_l M (check_range_l M hZF) h.base huv
  have heq' := (row_eq_force_l hZF h.order L k hcp.1 hτ hvn).mp heq
  have hn : q' ≠ E := fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) E (he ▸ hq'E)
  have heq'' := eq_force_lower_l L hZF (row_name_l k hτ) (row_name_l k hvn) c q' (k.mem c hcp.1)
    ⟨hq'E, hn, hq'c⟩ heq'
  exact h₁ u x v q' ⟨hu, huN, hx, hxu, huv, ⟨hq'E, hn, hq'x⟩, heq''⟩
    ⟨hq'E, hn, hq'q⟩ w (row_splice_nested_l hZF.1 hαβ hqr.2 hq' hw)

end YesMetaZFC.Model.Forcing.Internal
