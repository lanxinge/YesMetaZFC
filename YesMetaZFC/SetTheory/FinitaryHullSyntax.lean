import YesMetaZFC.SetTheory.CountableChain

/-! # 内部有限元运算族的闭包公式

运算族是实际图 K，输入为 (规则编号,有限参数列)。闭包条件量化地模型的全部
有限参数列；不把运算族或闭包解释为宿主函数。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fc_value_d (ω T K A x : M.Domain) : Prop := ∃ n s t p,
  M.mem n ω ∧ M.IsSetFunctionFromTo I s n A ∧ M.mem t T ∧ I.Codes p t s ∧ M.PairMember I p x K

def fc_value_m {d} (ω T K A x : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 3) ω.weaken.weaken.weaken.weaken) (.conj
    (Formula.isFunctionFromTo 𝒞 (.bound 2) (.bound 3) A.weaken.weaken.weaken.weaken) (.conj
    (.mem (.bound 1) T.weaken.weaken.weaken.weaken) (.conj (𝒞.code .newest (.bound 1) (.bound 2))
    (Formula.orderedPairMem 𝒞 .newest x.weaken.weaken.weaken.weaken K.weaken.weaken.weaken.weaken))))))))
derive_free_closed fc_value_m

theorem fc_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω T K A x : Term d) :
    Formula.satisfies ρ (fc_value_m (𝒞 := 𝒞) ω T K A x) ↔
      Fc_value_d I (ω.eval ρ) (T.eval ρ) (K.eval ρ) (A.eval ρ) (x.eval ρ) := by
  simp only [fc_value_m, Fc_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isFunctionFromTo_iff I hE, I.satisfies_code_iff,
    Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

def Fc_closed_d (ω T K N : M.Domain) : Prop := ∀ x, Fc_value_d I ω T K N x → M.mem x N

def fc_closed_m {d} (ω T K N : Term d) : Formula 1 d :=
  .forallE (.imp (fc_value_m (𝒞 := 𝒞) ω.weaken T.weaken K.weaken N.weaken .newest) (.mem .newest N.weaken))
derive_free_closed fc_closed_m

theorem fc_closed_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω T K N : Term d) :
    Formula.satisfies ρ (fc_closed_m (𝒞 := 𝒞) ω T K N) ↔
      Fc_closed_d I (ω.eval ρ) (T.eval ρ) (K.eval ρ) (N.eval ρ) := by
  simp only [fc_closed_m, Fc_closed_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    fc_value_sat_l I hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Fc_step_d (ω T K A B : M.Domain) : Prop := ∀ x, M.mem x B ↔ M.mem x A ∨ Fc_value_d I ω T K A x

def fc_step_m {d} (ω T K A B : Term d) : Formula 1 d :=
  .forallE (.iff (.mem .newest B.weaken) (.disj (.mem .newest A.weaken)
    (fc_value_m (𝒞 := 𝒞) ω.weaken T.weaken K.weaken A.weaken .newest)))
derive_free_closed fc_step_m

theorem fc_step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω T K A B : Term d) :
    Formula.satisfies ρ (fc_step_m (𝒞 := 𝒞) ω T K A B) ↔
      Fc_step_d I (ω.eval ρ) (T.eval ρ) (K.eval ρ) (A.eval ρ) (B.eval ρ) := by
  simp only [fc_step_m, Fc_step_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_mem_iff, fc_value_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Fc_hull_d (ω X T K A N : M.Domain) : Prop :=
  M.MemberSubset A N ∧ M.MemberSubset N X ∧ Fc_closed_d I ω T K N ∧
    ∀ B, M.MemberSubset A B → Fc_closed_d I ω T K B → M.MemberSubset N B

def fc_hull_m {d} (ω X T K A N : Term d) : Formula 1 d :=
  .conj (Formula.subset A N) (.conj (Formula.subset N X) (.conj (fc_closed_m (𝒞 := 𝒞) ω T K N)
    (.forallE (.imp (Formula.subset A.weaken .newest)
      (.imp (fc_closed_m (𝒞 := 𝒞) ω.weaken T.weaken K.weaken .newest) (Formula.subset N.weaken .newest))))))
derive_free_closed fc_hull_m

theorem fc_hull_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X T K A N : Term d) :
    Formula.satisfies ρ (fc_hull_m (𝒞 := 𝒞) ω X T K A N) ↔
      Fc_hull_d I (ω.eval ρ) (X.eval ρ) (T.eval ρ) (K.eval ρ) (A.eval ρ) (N.eval ρ) := by
  simp only [fc_hull_m, Fc_hull_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    fc_closed_sat_l I hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem fc_value_mono_l {ω T K A B x} (h : M.MemberSubset A B) (hx : Fc_value_d I ω T K A x) :
    Fc_value_d I ω T K B x := by
  obtain ⟨n, s, t, p, hn, hs, ht, hp, hx⟩ := hx
  exact ⟨n, s, t, p, hn, hs.mono_target_l I h, ht, hp, hx⟩

theorem fc_hull_unique_l (hE : Extensional M) {ω X T K A N L}
    (hN : Fc_hull_d I ω X T K A N) (hL : Fc_hull_d I ω X T K A L) : N = L :=
  hE.eq_of_same_members N L (fun x => ⟨hN.2.2.2 L hL.1 hL.2.2.1 x, hL.2.2.2 N hN.1 hN.2.2.1 x⟩)

end YesMetaZFC.SetTheory
