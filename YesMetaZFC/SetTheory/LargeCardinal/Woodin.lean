import YesMetaZFC.Model.SetTheory.Internal.PredicateEmbedding
import YesMetaZFC.SetTheory.Card.Properties.Basic
import YesMetaZFC.SetTheory.Cumulative
import YesMetaZFC.SetTheory.Kuratowski

/-! # 武丁基数与真类个武丁基数

采用标准的 Vδ 内 A-strong 刻画：δ 不可达，任意 A⊆Vδ 都有同一个 κ<δ，
使每个 ν<δ 存在 (Vδ,∈,A) 到传递内模型 (N,∈,B) 的初等嵌入，
临界点 κ，j(κ)>ν，Vν⊆N，且 A、B 在 Vν 上相同。
见 Welch《Large Cardinals, Inner Models and Determinacy》定义 4.5、定理 4.6。
这里所有量词均为集合量词，初等性消费已构造的内部满足关系。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

structure Wd_crit_d (X j κ k : M.Domain) : Prop where
  ordinal : M.IsOrdinal κ
  source : M.mem κ X
  ordinal_image : M.IsOrdinal k
  image : M.PairMember I κ k j
  moved : κ ≠ k
  fixed : ∀ a, M.mem a κ → M.PairMember I a a j

def wd_crit_m {d} (X j κ k : Term d) : Formula 1 d :=
  .conj (Formula.isOrdinal κ) (.conj (.mem κ X) (.conj (Formula.isOrdinal k)
    (.conj (Formula.orderedPairMem 𝒞 κ k j) (.conj (.neg (Formula.extensionalEq κ k))
      (Formula.forallMem κ (Formula.orderedPairMem 𝒞 .newest .newest j.weaken))))))
derive_free_closed wd_crit_m

theorem wd_crit_sat_l (hE : Extensional M) {d} (ρ : Env M d) (X j κ k : Term d) :
    Formula.satisfies ρ (wd_crit_m (𝒞 := 𝒞) X j κ k) ↔
      Wd_crit_d I (X.eval ρ) (j.eval ρ) (κ.eval ρ) (k.eval ρ) := by
  simp only [wd_crit_m, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_forallMem_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩,
    fun h => ⟨h.ordinal, h.source, h.ordinal_image, h.image, h.moved, h.fixed⟩⟩

/-- 一个 ν-A-strong 见证；N 是 Vδ 中的内模型载体，B 是其谓词解释。 -/
def Wd_witness_d (ω δ X A κ ν N B j W k : M.Domain) : Prop :=
  M.TransitiveSet N ∧ M.MemberSubset N X ∧ M.MemberSubset δ N ∧
  V_d I ν W ∧ M.MemberSubset W N ∧ Spred_emb_d I ω X A N B j ∧
  Wd_crit_d I X j κ k ∧ M.mem ν k ∧ ∀ x, M.mem x W → (M.mem x A ↔ M.mem x B)

def wd_witness_m {d} (ω δ X A κ ν N B j W k : Term d) : Formula 1 d :=
  .conj (Formula.isTransitive N) (.conj (Formula.subset N X) (.conj (Formula.subset δ N)
    (.conj (v_m 𝒞 ν W) (.conj (Formula.subset W N)
      (.conj (spred_emb_m (𝒞 := 𝒞) ω X A N B j) (.conj (wd_crit_m (𝒞 := 𝒞) X j κ k)
        (.conj (.mem ν k) (Formula.forallMem W (.iff (.mem .newest A.weaken) (.mem .newest B.weaken))))))))))
derive_free_closed wd_witness_m

theorem wd_witness_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω δ X A κ ν N B j W k : Term d) :
    Formula.satisfies ρ (wd_witness_m (𝒞 := 𝒞) ω δ X A κ ν N B j W k) ↔
      Wd_witness_d I (ω.eval ρ) (δ.eval ρ) (X.eval ρ) (A.eval ρ) (κ.eval ρ) (ν.eval ρ)
        (N.eval ρ) (B.eval ρ) (j.eval ρ) (W.eval ρ) (k.eval ρ) := by
  simp only [wd_witness_m, Wd_witness_d, Formula.satisfies_conj_iff, Formula.satisfies_isTransitive_iff,
    Formula.satisfies_subset_iff, v_sat_l I hE, spred_emb_sat_l I hE, wd_crit_sat_l I hE,
    Formula.satisfies_mem_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Wd_strong_d (ω δ X A κ : M.Domain) : Prop := ∀ ν, M.mem ν δ →
  ∃ N B j W k, Wd_witness_d I ω δ X A κ ν N B j W k

def wd_strong_m {d} (ω δ X A κ : Term d) : Formula 1 d :=
  Formula.forallMem δ (.existsE (.existsE (.existsE (.existsE (.existsE
    (wd_witness_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken.weaken
      δ.weaken.weaken.weaken.weaken.weaken.weaken X.weaken.weaken.weaken.weaken.weaken.weaken
      A.weaken.weaken.weaken.weaken.weaken.weaken κ.weaken.weaken.weaken.weaken.weaken.weaken
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))))
derive_free_closed wd_strong_m

theorem wd_strong_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω δ X A κ : Term d) :
    Formula.satisfies ρ (wd_strong_m (𝒞 := 𝒞) ω δ X A κ) ↔
      Wd_strong_d I (ω.eval ρ) (δ.eval ρ) (X.eval ρ) (A.eval ρ) (κ.eval ρ) := by
  simp only [wd_strong_m, Wd_strong_d, Formula.satisfies_forallMem_iff,
    Formula.satisfies_exists_iff, wd_witness_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

def Woodin_d (δ : M.Domain) : Prop := ∃ ω X, M.IsOmega ω ∧ M.mem ω δ ∧
  M.IsRegularCardinal I δ ∧ M.IsStrongLimitCardinal I δ ∧ V_d I δ X ∧
    ∀ A, M.MemberSubset A X → ∃ κ, M.mem κ δ ∧ Wd_strong_d I ω δ X A κ

def woodin0_m (𝒞 : OrderedPairConvention) : Formula 1 1 :=
  let δ : Term 1 := .bound 0
  .existsE (.existsE (.conj (Formula.isOmega (.bound 1)) (.conj (.mem (.bound 1) δ.weaken.weaken)
    (.conj (Formula.isRegularCardinal 𝒞 δ.weaken.weaken) (.conj (Formula.isStrongLimitCardinal 𝒞 δ.weaken.weaken)
      (.conj (v_m 𝒞 δ.weaken.weaken .newest) (.forallE (.imp (Formula.subset .newest (.bound 1))
        (Formula.existsMem δ.weaken.weaken.weaken
          (wd_strong_m (𝒞 := 𝒞) (.bound 3) δ.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) .newest))))))))))

@[simp] theorem woodin0_closed_l : (woodin0_m 𝒞).FreeClosed := by
  simp -implicitDefEqProofs [woodin0_m, Formula.isStrongLimitCardinal,
    Formula.cardinalLess, Definitional.Formula.FreeClosed]

def woodin_m {d} (δ : Term d) : Formula 1 d :=
  (woodin0_m 𝒞).bind (fun _ => δ)

@[simp] theorem woodin_closed_l {d} (δ : Term d) (hδ : δ.freeSupport = []) :
    (woodin_m (𝒞 := 𝒞) δ).FreeClosed :=
  (Definitional.Formula.freeClosed_bind_iff_of_closed _ (fun _ => hδ) _).mpr woodin0_closed_l

theorem woodin_sat_l (hE : Extensional M) {d} (ρ : Env M d) (δ : Term d) :
    Formula.satisfies ρ (woodin_m (𝒞 := 𝒞) δ) ↔ Woodin_d I (δ.eval ρ) := by
  simp only [woodin_m, Formula.satisfies_bind, woodin0_m, Woodin_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isOmega_iff, Formula.satisfies_mem_iff, Formula.satisfies_isRegularCardinal_iff I hE,
    Formula.satisfies_isStrongLimitCardinal_iff I hE, v_sat_l I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Formula.satisfies_existsMem_iff,
    wd_strong_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

/-- 真类个表示在全部内部序数中无界，不使用宿主 Type 的基数或外部序数。 -/
def Wd_proper_d : Prop := ∀ α, M.IsOrdinal α → ∃ δ, M.mem α δ ∧ Woodin_d I δ

def wd_proper_m (𝒞 : OrderedPairConvention) : Formula 1 0 :=
  .forallE (.imp (Formula.isOrdinal .newest) (.existsE
    (.conj (.mem (.bound 1) .newest) (woodin_m (𝒞 := 𝒞) .newest))))

theorem wd_proper_closed_l : (wd_proper_m 𝒞).FreeClosed := by
  simp -implicitDefEqProofs [wd_proper_m, Definitional.Formula.FreeClosed]

theorem wd_proper_sat_l (hE : Extensional M) (ρ : Env M 0) :
    Formula.satisfies ρ (wd_proper_m 𝒞) ↔ Wd_proper_d I := by
  simp only [wd_proper_m, Wd_proper_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isOrdinal_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, woodin_sat_l I hE]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u

def Axioms.woodin_proper : Sentence := Sentence.ofFormula
  (LargeCardinal.wd_proper_m kpair_convention_l) LargeCardinal.wd_proper_closed_l

theorem wd_proper_axiom_sat_l {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)
    (hE : Extensional M) : M.SatisfiesSentence Axioms.woodin_proper ↔ LargeCardinal.Wd_proper_d I := by
  rw [Structure.satisfiesSentence_iff]
  constructor
  · intro h
    obtain ⟨x⟩ := M.nonempty
    exact (LargeCardinal.wd_proper_sat_l I hE ⟨Fin.elim0, fun _ => x⟩).mp (h (fun _ => x))
  · exact fun h f => (LargeCardinal.wd_proper_sat_l I hE ⟨Fin.elim0, f⟩).mpr h

end YesMetaZFC.SetTheory
