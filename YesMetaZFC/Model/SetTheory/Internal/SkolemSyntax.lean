import YesMetaZFC.Model.SetTheory.Internal.FiniteAssignment
import YesMetaZFC.Model.SetTheory.Internal.Countable

/-! # 内部司寇伦选择的实际公式

规则编号为 (公式码,被量化变量)，参数为任意内部有限序列。参数列外取基点 u；
存在见证时选择真见证，无见证时精确返回 u。所有量化对象均在地模型内。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ssk_wit_d (ω c X u a i s x : M.Domain) : Prop := ∃ n f g,
  M.mem n ω ∧ M.IsSetFunctionFromTo I s n X ∧ Senv_fill_d I ω u n s f ∧
    Senv_update_d I f i x g ∧ Satisfies_d I ω c a g

def ssk_wit_m {d} (ω c X u a i s x : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.conj (.mem (.bound 2) ω.weaken.weaken.weaken) (.conj
    (Formula.isFunctionFromTo 𝒞 s.weaken.weaken.weaken (.bound 2) X.weaken.weaken.weaken) (.conj
    (senv_fill_m (𝒞 := 𝒞) ω.weaken.weaken.weaken u.weaken.weaken.weaken (.bound 2) s.weaken.weaken.weaken (.bound 1)) (.conj
    (senv_update_m (𝒞 := 𝒞) (.bound 1) i.weaken.weaken.weaken x.weaken.weaken.weaken .newest)
    (satisfies_m (𝒞 := 𝒞) ω.weaken.weaken.weaken c.weaken.weaken.weaken a.weaken.weaken.weaken .newest)))))))
derive_free_closed ssk_wit_m

theorem ssk_wit_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c X u a i s x : Term d) :
    Formula.satisfies ρ (ssk_wit_m (𝒞 := 𝒞) ω c X u a i s x) ↔
      Ssk_wit_d I (ω.eval ρ) (c.eval ρ) (X.eval ρ) (u.eval ρ) (a.eval ρ) (i.eval ρ) (s.eval ρ) (x.eval ρ) := by
  simp only [ssk_wit_m, Ssk_wit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_isFunctionFromTo_iff I hE, senv_fill_sat_l I hE,
    senv_update_sat_l I hE, satisfies_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

/-- 在实际参数延拓和更新图上，见证公式精确还原为原内部满足关系。 -/
theorem ssk_wit_decode_l (hE : Extensional M) {ω c X u a i n s f g x}
    (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n X) (hf : Senv_fill_d I ω u n s f)
    (hg : Senv_update_d I f i x g) : Ssk_wit_d I ω c X u a i s x ↔ Satisfies_d I ω c a g := by
  constructor
  · rintro ⟨m, h, k, _, hm, hh, hk, ht⟩
    have he := hm.2.1.eq hE hs.2.1
    subst m
    have he := senv_fill_unique_l I hE hh hf
    subst h
    have he := senv_update_unique_l I hE hk hg
    exact he ▸ ht
  · exact fun ht => ⟨n, f, g, hn, hs, hf, hg, ht⟩

def Ssk_choice_d (ω c X u p x : M.Domain) : Prop := ∃ a i t s,
  I.Codes t a i ∧ I.Codes p t s ∧ (Ssk_wit_d I ω c X u a i s x ∨
    ((¬ ∃ y, M.mem y X ∧ Ssk_wit_d I ω c X u a i s y) ∧ x = u))

def ssk_choice_m {d} (ω c X u p x : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE (.conj (𝒞.code (.bound 1) (.bound 3) (.bound 2)) (.conj
    (𝒞.code p.weaken.weaken.weaken.weaken (.bound 1) .newest) (.disj
    (ssk_wit_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken
      X.weaken.weaken.weaken.weaken u.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) .newest x.weaken.weaken.weaken.weaken)
    (.conj (.neg (.existsE (.conj (.mem .newest X.weaken.weaken.weaken.weaken.weaken)
      (ssk_wit_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken.weaken
        X.weaken.weaken.weaken.weaken.weaken u.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 1) .newest))))
      (Formula.extensionalEq x.weaken.weaken.weaken.weaken u.weaken.weaken.weaken.weaken))))))))
derive_free_closed ssk_choice_m

theorem ssk_choice_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c X u p x : Term d) :
    Formula.satisfies ρ (ssk_choice_m (𝒞 := 𝒞) ω c X u p x) ↔
      Ssk_choice_d I (ω.eval ρ) (c.eval ρ) (X.eval ρ) (u.eval ρ) (p.eval ρ) (x.eval ρ) := by
  simp only [ssk_choice_m, Ssk_choice_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, ssk_wit_sat_l I hE, I.satisfies_code_iff, Definitional.Term.eval_weaken]
  rfl

structure Ssk_d (ω c X u C S T D K : M.Domain) : Prop where
  point : M.mem u X
  codes : Scode_d I ω C
  params : Fseq_space_d I ω X S
  labels : M.IsCartesianProduct I T C ω
  domain : M.IsCartesianProduct I D T S
  graph : M.IsSetFunctionFromTo I K D X
  select : ∀ p x, M.PairMember I p x K → Ssk_choice_d I ω c X u p x

def ssk_m {d} (ω c X u C S T D K : Term d) : Formula 1 d :=
  .conj (.mem u X) (.conj (scode_m (𝒞 := 𝒞) ω C) (.conj (fseq_space_m (𝒞 := 𝒞) ω X S) (.conj
    (Formula.isCartesianProduct 𝒞 T C ω) (.conj (Formula.isCartesianProduct 𝒞 D T S) (.conj
    (Formula.isFunctionFromTo 𝒞 K D X) (.forallE (.forallE (.imp
      (Formula.orderedPairMem 𝒞 (.bound 1) .newest K.weaken.weaken)
      (ssk_choice_m (𝒞 := 𝒞) ω.weaken.weaken c.weaken.weaken X.weaken.weaken u.weaken.weaken (.bound 1) .newest)))))))))

@[simp] theorem ssk_closed_l {d} (ω c X u C S T D K : Term d)
    (hω : ω.freeSupport = []) (hc : c.freeSupport = []) (hX : X.freeSupport = []) (hu : u.freeSupport = [])
    (hC : C.freeSupport = []) (hS : S.freeSupport = []) (hT : T.freeSupport = []) (hD : D.freeSupport = []) (hK : K.freeSupport = []) :
    (ssk_m (𝒞 := 𝒞) ω c X u C S T D K).FreeClosed := by
  simp -implicitDefEqProofs [ssk_m, Definitional.Formula.FreeClosed, Formula.isCartesianProduct, hω, hc, hX, hu, hC, hS, hT, hD, hK]

theorem ssk_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c X u C S T D K : Term d) :
    Formula.satisfies ρ (ssk_m (𝒞 := 𝒞) ω c X u C S T D K) ↔
      Ssk_d I (ω.eval ρ) (c.eval ρ) (X.eval ρ) (u.eval ρ) (C.eval ρ) (S.eval ρ) (T.eval ρ) (D.eval ρ) (K.eval ρ) := by
  simp only [ssk_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, scode_sat_l I hE,
    fseq_space_sat_l I hE, Formula.satisfies_isCartesianProduct_iff I, Formula.satisfies_isFunctionFromTo_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    ssk_choice_sat_l I hE, Definitional.Term.eval_weaken]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩,
    fun h => ⟨h.point, h.codes, h.params, h.labels, h.domain, h.graph, h.select⟩⟩

/-- 对全部内部公式及有限参数列的存在见证封闭；列外参数按既定基点解释。 -/
def Ssk_closed_d (ω c X u C N : M.Domain) : Prop :=
  ∀ a i n s, M.mem a C → M.mem i ω → M.mem n ω → M.IsSetFunctionFromTo I s n N →
    (∃ x, M.mem x X ∧ Ssk_wit_d I ω c X u a i s x) → ∃ x, M.mem x N ∧ Ssk_wit_d I ω c X u a i s x

def ssk_closed_m {d} (ω c X u C N : Term d) : Formula 1 d :=
  Formula.forallMem C (Formula.forallMem ω.weaken (Formula.forallMem ω.weaken.weaken (.forallE (.imp
    (Formula.isFunctionFromTo 𝒞 .newest (.bound 1) N.weaken.weaken.weaken.weaken) (.imp
    (.existsE (.conj (.mem .newest X.weaken.weaken.weaken.weaken.weaken)
      (ssk_wit_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken.weaken
        X.weaken.weaken.weaken.weaken.weaken u.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 1) .newest)))
    (.existsE (.conj (.mem .newest N.weaken.weaken.weaken.weaken.weaken)
      (ssk_wit_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken c.weaken.weaken.weaken.weaken.weaken
        X.weaken.weaken.weaken.weaken.weaken u.weaken.weaken.weaken.weaken.weaken (.bound 4) (.bound 3) (.bound 1) .newest))))))))
derive_free_closed ssk_closed_m

theorem ssk_closed_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c X u C N : Term d) :
    Formula.satisfies ρ (ssk_closed_m (𝒞 := 𝒞) ω c X u C N) ↔
      Ssk_closed_d I (ω.eval ρ) (c.eval ρ) (X.eval ρ) (u.eval ρ) (C.eval ρ) (N.eval ρ) := by
  simp only [ssk_closed_m, Ssk_closed_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, ssk_wit_sat_l I hE, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]
  exact ⟨fun h a i n s ha hi hn hs => h a ha i hi n hn s hs,
    fun h a ha i hi n hn s hs => h a i n s ha hi hn hs⟩

end YesMetaZFC.SetTheory.Internal
