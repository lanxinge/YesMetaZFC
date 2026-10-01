import YesMetaZFC.Model.SetTheory.Internal.Assignment

/-! # 模型内部的有限公式指令码

四个构造符为二元关系、等号、或非、存在量词。指令 (标签,i,j) 中，前两种读取
变量；或非读取较早两行；存在量词在变量 i 上量化较早的第 j 行。长度和全部
编号来自模型自身 ω，合法性是实际原公式，允许内部非标准的有限指令序列。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sop_d (k : Nat) (c i j : M.Domain) : Prop :=
  ∃ a o, Num_d k o ∧ I.Codes a i j ∧ I.Codes c o a

def sop_m (k : Nat) {n} (c i j : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (num_m k .newest)
    (.conj (𝒞.code (.bound 1) i.weaken.weaken j.weaken.weaken) (𝒞.code c.weaken.weaken .newest (.bound 1)))))
derive_free_closed sop_m

theorem sop_sat_l (k : Nat) {n} (ρ : Env M n) (c i j : Term n) :
    Formula.satisfies ρ (sop_m (𝒞 := 𝒞) k c i j) ↔ Sop_d I k (c.eval ρ) (i.eval ρ) (j.eval ρ) := by
  simp only [sop_m, Sop_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    num_sat_l, I.satisfies_code_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem sop_exists_l (hKP : M.Models KP) (k : Nat) (i j : M.Domain) : ∃ c, Sop_d I k c i j := by
  obtain ⟨o, ho⟩ := num_exists_l hKP k
  obtain ⟨a, ha⟩ := I.total i j
  obtain ⟨c, hc⟩ := I.total o a
  exact ⟨c, a, o, ho, ha, hc⟩

theorem sop_injective_l (hKP : M.Models KP) {k l c i j a b}
    (h : Sop_d I k c i j) (g : Sop_d I l c a b) : k = l ∧ i = a ∧ j = b := by
  obtain ⟨s, o, ho, hs, hc⟩ := h
  obtain ⟨t, p, hp, ht, hd⟩ := g
  obtain ⟨he, hf⟩ := I.injective hc hd
  subst p
  subst t
  exact ⟨num_injective_l hKP ho hp, I.injective hs ht⟩

def Sfm_node_d (ω r c : M.Domain) : Prop :=
  (∃ i j, Sop_d I 0 c i j ∧ M.mem i ω ∧ M.mem j ω) ∨
  (∃ i j, Sop_d I 1 c i j ∧ M.mem i ω ∧ M.mem j ω) ∨
  (∃ i j, Sop_d I 2 c i j ∧ M.mem i r ∧ M.mem j r) ∨
  (∃ i j, Sop_d I 3 c i j ∧ M.mem i ω ∧ M.mem j r)

private def node_case_m (k : Nat) {n} (c A B : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (sop_m (𝒞 := 𝒞) k c.weaken.weaken (.bound 1) .newest)
    (.conj (.mem (.bound 1) A.weaken.weaken) (.mem .newest B.weaken.weaken))))
derive_free_closed node_case_m

def sfm_node_m {n} (ω r c : Term n) : Formula 1 n :=
  .disj (node_case_m (𝒞 := 𝒞) 0 c ω ω) (.disj (node_case_m (𝒞 := 𝒞) 1 c ω ω)
    (.disj (node_case_m (𝒞 := 𝒞) 2 c r r) (node_case_m (𝒞 := 𝒞) 3 c ω r)))
derive_free_closed sfm_node_m

theorem sfm_node_sat_l {n} (ρ : Env M n) (ω r c : Term n) :
    Formula.satisfies ρ (sfm_node_m (𝒞 := 𝒞) ω r c) ↔ Sfm_node_d I (ω.eval ρ) (r.eval ρ) (c.eval ρ) := by
  simp only [sfm_node_m, Sfm_node_d, node_case_m, Formula.satisfies_disj_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, sop_sat_l I,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Sfm_d (ω n F : M.Domain) : Prop :=
  M.mem n ω ∧ M.IsSequenceOfLength I F n ∧ ∀ r c, M.PairMember I r c F → Sfm_node_d I ω r c

def sfm_m {n} (ω l F : Term n) : Formula 1 n :=
  .conj (.mem l ω) (.conj (Formula.isSequenceOfLength 𝒞 F l) (.forallE (.forallE
    (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
      (sfm_node_m (𝒞 := 𝒞) ω.weaken.weaken (.bound 1) .newest)))))
derive_free_closed sfm_m

theorem sfm_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω l F : Term n) :
    Formula.satisfies ρ (sfm_m (𝒞 := 𝒞) ω l F) ↔ Sfm_d I (ω.eval ρ) (l.eval ρ) (F.eval ρ) := by
  simp only [sfm_m, Sfm_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isSequenceOfLength_iff I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I, sfm_node_sat_l I,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 将一个合法指令追加到内部有限程序；无需把旧程序解码成宿主 List。 -/
theorem sfm_append_l (hZF : M.Models ZF) {ω n F c} (hω : M.IsOmega ω)
    (hF : Sfm_d I ω n F) (hc : Sfm_node_d I ω n c) : ∃ l G,
    M.SuccessorOf l n ∧ Sfm_d I ω l G ∧ ∀ i a, M.PairMember I i a G ↔
      M.PairMember I i a F ∨ (i = n ∧ a = c) := by
  obtain ⟨l, hl, hlω⟩ := hω.1.2 n hF.1
  obtain ⟨G, hG, he⟩ := hF.2.1.exists_append (ZF.modelsKP hZF) I (hω.members_areOrdinals hZF l hlω) hl (value := c)
  refine ⟨l, G, hl, ⟨hlω, hG, fun i a ha => ?_⟩, he⟩
  rcases (he i a).mp ha with ha | ⟨rfl, rfl⟩
  · exact hF.2.2 i a ha
  · exact hc

end YesMetaZFC.SetTheory.Internal
