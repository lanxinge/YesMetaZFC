import YesMetaZFC.SetTheory.Card.CountablePair
import YesMetaZFC.SetTheory.FunctionSpaceConstruction
import YesMetaZFC.SetTheory.Ord.FiniteSequenceParsing

/-! # 内部有限序列的统一编号公式

固定字母表单射 Q 和自然数对单射 J。第 n 层给 X^n 编号；后继层把前缀编号
与末项编号经 J 合并。各层同时在模型的 ω 上递归，故包含非标准有限长度。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fseq_space_d (ω X S : M.Domain) : Prop :=
  ∀ F, M.mem F S ↔ ∃ n, M.mem n ω ∧ M.IsSetFunctionFromTo I F n X

def fseq_space_m {d} (ω X S : Term d) : Formula 1 d :=
  .forallE (.iff (.mem .newest S.weaken) (.existsE (.conj (.mem .newest ω.weaken.weaken)
    (Formula.isFunctionFromTo 𝒞 (.bound 1) .newest X.weaken.weaken))))
derive_free_closed fseq_space_m

theorem fseq_space_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X S : Term d) :
    Formula.satisfies ρ (fseq_space_m (𝒞 := 𝒞) ω X S) ↔
      Fseq_space_d I (ω.eval ρ) (X.eval ρ) (S.eval ρ) := by
  simp only [fseq_space_m, Fseq_space_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Fseq_pair_d (Q J L P x z : M.Domain) : Prop :=
  ∃ a b p, M.PairMember I P a L ∧ M.PairMember I x b Q ∧ I.Codes p a b ∧ M.PairMember I p z J

def fseq_pair_m {d} (Q J L P x z : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.conj
    (Formula.orderedPairMem 𝒞 P.weaken.weaken.weaken (.bound 2) L.weaken.weaken.weaken) (.conj
    (Formula.orderedPairMem 𝒞 x.weaken.weaken.weaken (.bound 1) Q.weaken.weaken.weaken) (.conj
    (𝒞.code .newest (.bound 2) (.bound 1))
    (Formula.orderedPairMem 𝒞 .newest z.weaken.weaken.weaken J.weaken.weaken.weaken))))))
derive_free_closed fseq_pair_m

theorem fseq_pair_sat_l {d} (ρ : Env M d) (Q J L P x z : Term d) :
    Formula.satisfies ρ (fseq_pair_m (𝒞 := 𝒞) Q J L P x z) ↔
      Fseq_pair_d I (Q.eval ρ) (J.eval ρ) (L.eval ρ) (P.eval ρ) (x.eval ρ) (z.eval ρ) := by
  simp only [fseq_pair_m, Fseq_pair_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff, Definitional.Term.eval_weaken]
  rfl

def Fseq_snoc_d (Q J L m F z : M.Domain) : Prop :=
  ∃ P x, M.IsRestrictionOf I P F m ∧ M.PairMember I m x F ∧ Fseq_pair_d I Q J L P x z

def fseq_snoc_m {d} (Q J L m F z : Term d) : Formula 1 d :=
  .existsE (.existsE (.conj (Formula.isRestriction 𝒞 (.bound 1) F.weaken.weaken m.weaken.weaken)
    (.conj (Formula.orderedPairMem 𝒞 m.weaken.weaken .newest F.weaken.weaken)
      (fseq_pair_m (𝒞 := 𝒞) Q.weaken.weaken J.weaken.weaken L.weaken.weaken
        (.bound 1) .newest z.weaken.weaken))))
derive_free_closed fseq_snoc_m

theorem fseq_snoc_sat_l {d} (ρ : Env M d) (Q J L m F z : Term d) :
    Formula.satisfies ρ (fseq_snoc_m (𝒞 := 𝒞) Q J L m F z) ↔
      Fseq_snoc_d I (Q.eval ρ) (J.eval ρ) (L.eval ρ) (m.eval ρ) (F.eval ρ) (z.eval ρ) := by
  simp only [fseq_snoc_m, Fseq_snoc_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isRestriction_iff I, Formula.satisfies_orderedPairMem_iff I,
    fseq_pair_sat_l I, Definitional.Term.eval_weaken]
  rfl

def Fseq_at_d (X Q J H F z : M.Domain) : Prop :=
  ∃ n, M.IsDomainOf I n H ∧ M.IsSetFunctionFromTo I F n X ∧
    (((∀ i, ¬ M.mem i n) ∧ ∀ i, ¬ M.mem i z) ∨ ∃ m L,
      M.SuccessorOf n m ∧ M.PairMember I m L H ∧ Fseq_snoc_d I Q J L m F z)

def fseq_at_m {d} (X Q J H F z : Term d) : Formula 1 d :=
  .existsE (.conj (Formula.isDomain 𝒞 .newest H.weaken) (.conj
    (Formula.isFunctionFromTo 𝒞 F.weaken .newest X.weaken) (.disj
    (.conj (Formula.isEmpty .newest) (Formula.isEmpty z.weaken))
    (.existsE (.existsE (.conj (Formula.isSuccessor (.bound 2) (.bound 1)) (.conj
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken.weaken)
      (fseq_snoc_m (𝒞 := 𝒞) Q.weaken.weaken.weaken J.weaken.weaken.weaken .newest
        (.bound 1) F.weaken.weaken.weaken z.weaken.weaken.weaken))))))))
derive_free_closed fseq_at_m

theorem fseq_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X Q J H F z : Term d) :
    Formula.satisfies ρ (fseq_at_m (𝒞 := 𝒞) X Q J H F z) ↔
      Fseq_at_d I (X.eval ρ) (Q.eval ρ) (J.eval ρ) (H.eval ρ) (F.eval ρ) (z.eval ρ) := by
  simp only [fseq_at_m, Fseq_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_isDomain_iff I, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_isSuccessor_iff, Formula.satisfies_orderedPairMem_iff I,
    fseq_snoc_sat_l I, Definitional.Term.eval_weaken]
  rfl

def Fseq_step_d (ω X S Q J H K : M.Domain) : Prop :=
  M.IsSetRelation I K ∧ ∀ F z, M.PairMember I F z K ↔
    M.mem F S ∧ M.mem z ω ∧ Fseq_at_d I X Q J H F z

def fseq_step_m {d} (ω X S Q J H K : Term d) : Formula 1 d :=
  .conj (Formula.isRelation 𝒞 K) (.forallE (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest K.weaken.weaken) (.conj
    (.mem (.bound 1) S.weaken.weaken) (.conj (.mem .newest ω.weaken.weaken)
    (fseq_at_m (𝒞 := 𝒞) X.weaken.weaken Q.weaken.weaken J.weaken.weaken H.weaken.weaken (.bound 1) .newest))))))
derive_free_closed fseq_step_m

theorem fseq_step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X S Q J H K : Term d) :
    Formula.satisfies ρ (fseq_step_m (𝒞 := 𝒞) ω X S Q J H K) ↔
      Fseq_step_d I (ω.eval ρ) (X.eval ρ) (S.eval ρ) (Q.eval ρ) (J.eval ρ) (H.eval ρ) (K.eval ρ) := by
  simp only [fseq_step_m, Fseq_step_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, fseq_at_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

def fseq_env_l (ω X S Q J : M.Domain) : Env M 5 :=
  ⟨Fin.cases J (Fin.cases Q (Fin.cases S (Fin.cases X (fun _ => ω)))), fun _ => ω⟩

def fseq_step_s : BinarySchema 5 where
  body := fseq_step_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest

theorem fseq_op_l (hE : Extensional M) (ω X S Q J : M.Domain) :
    (fseq_step_s (𝒞 := 𝒞)).denote (fseq_env_l ω X S Q J) = Fseq_step_d I ω X S Q J := by
  funext H K
  apply propext
  exact fseq_step_sat_l I hE _ _ _ _ _ _ _ _

end YesMetaZFC.SetTheory
