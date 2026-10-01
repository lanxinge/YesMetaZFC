import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Comparison

/-! # 全部稠密选择名称的统一后期比较

每个相邻转移已经给出所选名称的第一条限制比较。将它作为一般不变量定理的
起点，统一得到该名称对任意后期前缀的比较，供融合主性使用。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def Row_pr_bounds_d (I : kpair_convention_l.Interpretation M) (F G b D N A Q : M.Domain) : Prop :=
  ∀ i j x y α B R p τ q σ, M.SuccessorOf j i → Entry_d M i x Q → Entry_d M j y Q →
    Entry_d M i α A → Entry_d M α B F → Entry_d M α R G → KPair_d M x p τ → KPair_d M y q σ →
    Name_d M B σ ∧ ∀ k z γ C T r η, (M.mem j k ∨ j = k) → Entry_d M k z Q → Entry_d M k γ A →
      Entry_d M γ C F → Entry_d M γ T G → KPair_d M z r η → Row_cut_lower_d I α B R b D N σ p γ T r

variable (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_bounds_l {ω δ F G b β D V N A Z E X Q}
    (hω : M.IsOmega ω) (h : Row_system_d I δ F G b)
    (hD : Entry_d M β D F) (hV : Entry_d M β V G)
    (hA : M.IsSetFunctionFromTo I A ω Z) (hm : Cc_increasing_d I A)
    (hi : ∀ i α, Entry_d M i α A → M.MemberSubset α β)
    (hQ : M.IsSetFunctionFromTo I Q ω X)
    (hv : ∀ i y, Entry_d M i y Q → Row_pr_thread_d I F G b D N A i y)
    (hs : ∀ i j y z, M.SuccessorOf j i → Entry_d M i y Q → Entry_d M j z Q →
      Row_pr_advance_d I F G b D V N A E i y z) : Row_pr_bounds_d I F G b D N A Q := by
  intro i j x y α B R p τ q σ hj hx hy hiα hB hR hxp hyq
  obtain ⟨j', α', B', R', γ, C, T, U, hj', hiα', hjγ, hB', hR', hC, hT, _, hmove⟩ := hs i j x y hj hx hy
  have he := hZF.1.eq_of_same_members j' j (fun z => (hj' z).trans (hj z).symm)
  subst j'
  have heα := hA.1.2 i α' α hiα' hiα
  subst α'
  have heB := h.conditions.2.1.2 α B' B hB' hB
  have heR := h.relations.2.1.2 α R' R hR' hR
  subst B'; subst R'
  obtain ⟨p', τ', q', σ', _, _, _, hxp', hyq', hpq, hσ, _, _, _, _, _, _, hLow⟩ := hmove
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hxp hxp'
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hyq hyq'
  exact ⟨hσ, row_pr_bound_l hZF hω h hD hV hA hm hi hQ hv hs hB hR hσ hy hjγ hT hyq
    (hm i j α γ hj.predecessor_mem hiα hjγ) hpq hLow⟩

end YesMetaZFC.Model.Forcing.Internal
