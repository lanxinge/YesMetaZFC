import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.SetTheory.Card.Properties.Basic
import YesMetaZFC.SetTheory.Cumulative
import YesMetaZFC.SetTheory.Kuratowski
import YesMetaZFC.Model.SetTheory.ClassChoice
import YesMetaZFC.Model.SetTheory.ProjectEmbedding
import YesMetaZFC.SetTheory.RelationChain
import YesMetaZFC.SetTheory.CumulativeClosure
import YesMetaZFC.SetTheory.CumulativeFunction
import YesMetaZFC.Model.Forcing.Collapse.ProductRealCollapse
import YesMetaZFC.Model.SetTheory.Embedding.Reflect
import YesMetaZFC.Model.SetTheory.Reflection.RankAbsolute
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial
import YesMetaZFC.Model.SetTheory.Internal.RealTrace
import YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer
import YesMetaZFC.Model.SetTheory.Reflection.ReflectedSeed
import YesMetaZFC.Model.Forcing.Order.GenericTreeGround
import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.Model.Forcing.Collapse.ProductTopTruth
import YesMetaZFC.SetTheory.Descriptive.Coding.RelationCode

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

/-! ## 内部递增 Woodin 序列及每轮吸收参数

真类 Woodin 假设通过内部类依赖选择产生实际 ω 序列。
首项可选在任意指定序数上方，并保留原零指标及其实际函数图条目。
相邻两项给出小坍缩基数、下一 Woodin、实数字母表的秩界和全部已冻结坐标的统一界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel
universe u v
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Wd_sequence_d (ω A : M.Domain) : Prop where
  function : M.IsSetFunction I A
  domain : M.IsDomainOf I ω A
  woodin : ∀ i δ, M.PairMember I i δ A → Woodin_d I δ
  increasing : ∀ i j δ ε, M.mem i j → M.PairMember I i δ A → M.PairMember I j ε A → M.mem δ ε

def wd_sequence_m {d} (ω A : Term d) : Formula 1 d := set[d] ⟪
  ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜A⌝ₛ) ∧ ⌜Formula.isDomain kpair_convention_l⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ) ∧
  (∀ i δ, ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i,δ,⌜A⌝ₛ) → ⌜woodin_m (𝒞 := kpair_convention_l)⌝ₚ(δ)) ∧
  (∀ i j δ ε, i ∈ j → ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i,δ,⌜A⌝ₛ) →
    ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(j,ε,⌜A⌝ₛ) → δ ∈ ε)⟫
derive_free_closed wd_sequence_m

theorem wd_sequence_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A : Term d) :
    Formula.satisfies ρ (wd_sequence_m ω A) ↔ Wd_sequence_d I (ω.eval ρ) (A.eval ρ) := by
  simp only [wd_sequence_m,Formula.satisfies_conj_iff,Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_isDomain_iff I,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_orderedPairMem_iff I,woodin_sat_l I hE,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a,b,c,d⟩ => ⟨a,b,c,d⟩,fun h => ⟨h.function,h.domain,h.woodin,h.increasing⟩⟩

theorem wd_sequence_exists_l (hZFC : M.Models ZFC) {ω α : M.Domain} (hw : M.IsOmega ω)
    (proper : Wd_proper_d I) (hα : M.IsOrdinal α) :
    ∃ A o κ, Wd_sequence_d I ω A ∧ (∀ x, ¬ M.mem x o) ∧ M.PairMember I o κ A ∧ M.mem α κ := by
  have hZF := ZFC.models_zf_l hZFC
  obtain ⟨δ,above,wd⟩ := proper α hα
  obtain ⟨o,empty,_⟩ := hw.1.1
  let ρ : Env M 0 := ⟨Fin.elim0,fun _ => ω⟩
  let V : BinarySchema 0 := { body := woodin_m (𝒞 := kpair_convention_l) .newest }
  let φ : UnarySchema 2 := { body := .mem (.bound 1) .newest }
  have valid i x : V.denote ρ i x ↔ Woodin_d I x := woodin_sat_l I hZF.1 ..
  obtain ⟨U,A,fn,first,all,chain⟩ := ZFC.class_indexed_choice_l I hZFC V φ ρ hw empty
    ((valid o δ).mpr wd) (by
      intro i j x _ _ hx
      have wx := (valid i x).mp hx
      obtain ⟨ω₀,Z,hw₀,above,regular,strong,rank,_⟩ := wx
      obtain ⟨y,xy,wy⟩ := proper x strong.1.1
      exact ⟨y,(valid j y).mpr wy,xy⟩)
  have values i δ (edge : M.PairMember I i δ A) := (valid i δ).mp (all i δ edge)
  obtain ⟨W,range⟩ := ZF.exists_range_of_setFunction hZF I fn.1 fn.2.1
  have bounded : M.IsSetFunctionFromTo I A ω W := ⟨fn.1,fn.2.1,fun i hi => by
    obtain ⟨δ,_,edge⟩ := fn.2.2 i hi
    exact ⟨δ,(range δ).mpr ⟨i,edge⟩,edge⟩⟩
  have ordinal δ (hδ : M.mem δ W) : M.IsOrdinal δ := by
    obtain ⟨i,edge⟩ := (range δ).mp hδ
    obtain ⟨_,_,_,_,_,strong,_,_⟩ := values i δ edge
    exact strong.1.1
  let relation : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  have transitive := ZF.rel_chain_l I hZF relation ρ hw bounded
    (fun x y z _ _ hz xy yz => (ordinal z hz).transitive y yz x xy)
    (fun i j x y succ ix jy => chain i j x y succ ix jy)
  exact ⟨A,o,δ,⟨fn.1,fn.2.1,values,transitive⟩,empty,first,above⟩

theorem Wd_sequence_d.image_l {N : Structure.{v}} (J : kpair_convention_l.Interpretation N)
    (hM : Extensional M) (hN : Extensional N) (e : M.Domain → N.Domain) (elem : Pe_d e)
    {ω A : M.Domain} (h : Wd_sequence_d I ω A) : Wd_sequence_d J (e ω) (e A) := by
  let ρ : Env M 2 := ⟨Fin.cases ω (fun _ => A),fun _ => A⟩
  let φ := wd_sequence_m (.bound 0 : Term 2) (.bound 1)
  exact (wd_sequence_sat_l J hN (image_env_l e ρ) _ _).mp
    ((elem φ (by simp -implicitDefEqProofs [φ]) ρ).mp ((wd_sequence_sat_l I hM ρ _ _).mpr h))

theorem Wd_sequence_d.successor_l (hZF : M.Models ZF) {ω A i n : M.Domain} (h : Wd_sequence_d I ω A)
    (hw : M.IsOmega ω) (hi : M.mem i ω) (succ : M.SuccessorOf n i) :
    ∃ κ δ Z, M.PairMember I i κ A ∧ M.PairMember I n δ A ∧ M.IsUncountableCardinal I ω κ ∧
      M.mem κ δ ∧ Woodin_d I δ ∧ V_d I δ Z ∧ M.mem ω Z ∧
      ∀ j α, M.mem j n → M.PairMember I j α A → M.MemberSubset α κ := by
  obtain ⟨n₀,succ₀,hn₀⟩ := hw.1.2 i hi
  have hn : M.mem n ω := succ₀.eq hZF.1 succ ▸ hn₀
  obtain ⟨κ,ik⟩ := (h.domain i).mp hi
  obtain ⟨δ,nd⟩ := (h.domain n).mp hn
  obtain ⟨ω₀,_,hw₀,aboveκ,_,strongκ,_,_⟩ := h.woodin i κ ik
  have eq₀ := hZF.1.eq_of_same_members ω₀ ω (fun j => ⟨hw₀.2 ω hw.1 j,hw.2 ω₀ hw₀.1 j⟩)
  have wd := h.woodin n δ nd
  obtain ⟨ω₁,Z,hw₁,aboveδ,_,_,rank,_⟩ := wd
  have eq₁ := hZF.1.eq_of_same_members ω₁ ω (fun j => ⟨hw₁.2 ω hw.1 j,hw.2 ω₁ hw₁.1 j⟩)
  refine ⟨κ,δ,Z,ik,nd,⟨strongκ.1,eq₀ ▸ aboveκ⟩,h.increasing i n κ δ succ.predecessor_mem ik nd,
    h.woodin n δ nd,rank,ZF.v_ordinal_mem_l I hZF rank (eq₁ ▸ aboveδ),?_⟩
  intro j α hj ja
  rcases (succ j).mp hj with ji | eq
  · exact strongκ.1.1.transitive α (h.increasing j i α κ ji ja ik)
  · have eq := hZF.1.eq_of_same_members j i eq
    subst j
    have eq := h.function.2 i α κ ja ik
    exact eq.symm ▸ (show M.MemberSubset κ κ from fun _ hx => hx)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 真类 Woodin 假设生产原乘积和备用 Woodin

先选查询树使用的较小 Woodin，再从其上方构造严格递增序列。
整个原序列图的一个实际秩界同时严格界定全部坐标；再在该界上方
选择备用 Woodin。全乘积和规范实数并名字由已有构造实际产生。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem wd_product_l {ω : M.Domain} (hw : M.IsOmega ω) (proper : Wd_proper_d I) :
    ∃ α Vα A o κ μ δ Z P R σ, Woodin_d I α ∧ V_d I α Vα ∧ M.mem ω Vα ∧
      (∀ x, ¬ M.mem x o) ∧ Entry_d M o κ A ∧ M.IsUncountableCardinal I ω κ ∧ M.mem α κ ∧
      Wd_sequence_d I ω A ∧ M.IsSetFunctionFromTo I A ω μ ∧ M.mem μ δ ∧
      Woodin_d I δ ∧ V_d I δ Z ∧ Fp_product_d hZF ω A P R ∧ Rp_name_d hZF ω A P σ := by
  obtain ⟨α,ωα,wa⟩ := proper ω (hw.isOrdinal (ZF.modelsKP hZF))
  have ha := wa
  obtain ⟨_,Vα,_,_,_,strongα,rankα,_⟩ := ha
  obtain ⟨A,o,κ,sequence,empty,first,lower⟩ := wd_sequence_exists_l I hZFC hw proper strongα.1.1
  obtain ⟨_,_,_,_,_,strongκ,_,_⟩ := sequence.woodin o κ first
  have hκ : M.IsUncountableCardinal I ω κ :=
    ⟨strongκ.1,strongκ.1.1.transitive α lower ω ωα⟩
  obtain ⟨μ,V,rankA,hA⟩ := ZF.v_cover_l I hZF A
  have bounded i ε (edge : M.PairMember I i ε A) : M.mem ε μ := by
    obtain ⟨_,_,_,_,_,strong,_,_⟩ := sequence.woodin i ε edge
    exact ZF.v_ordinal_height_l hZF rankA strong.1.1 (rd_entry_transitive_l (v_transitive_l I rankA) hA edge).2
  have fa : M.IsSetFunctionFromTo I A ω μ := ⟨sequence.function,sequence.domain,fun i hi => by
    obtain ⟨ε,edge⟩ := (sequence.domain i).mp hi
    exact ⟨ε,bounded i ε edge,edge⟩⟩
  obtain ⟨δ,small,wd⟩ := proper μ (v_ordinal_l I rankA)
  have hd := wd
  obtain ⟨_,Z,_,_,_,_,rank,_⟩ := hd
  obtain ⟨P,R,product⟩ := fp_product_l hZF hw fa
  obtain ⟨σ,name⟩ := rp_name_exists_l hZF hw fa product
  exact ⟨α,Vα,A,o,κ,μ,δ,Z,P,R,σ,wa,rankα,ZF.v_ordinal_mem_l I hZF rankα ωα,
    empty,first,hκ,lower,sequence,fa,small,wd,rank,product,name⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 真实 Woodin 在包含它的实际 ZF 极限秩层中仍是 Woodin

每个见证载体、谓词、嵌入图及较低秩层都由 Vδ 的统一秩界回收。
完整内部初等性由成员满包含反射，故源内部也能检验全部自己的程序。
结论直接使用原 Woodin 定义，不附加见证选择或绝对性合同。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Woodin_d.rank_l {c U R θ : M.Domain} (source : Smem_d I c U R)
    (upper : V_d I θ U) (limit : M.IsLimitOrdinal θ)
    (native : (smdl_structure_l I (R := R) source.1.2.1).Models ZF)
    (δ : (smdl_structure_l I (R := R) source.1.2.1).Domain) (wd : Woodin_d I δ.val) :
    Woodin_d (kp_pair_l (ZF.modelsKP native)) δ := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  let J := kp_pair_l (ZF.modelsKP native)
  have trans := v_transitive_l I upper
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have member {a b : N.Domain} : N.mem a b ↔ M.mem a.val b.val := smem_member_l I source.1 source.2 a b
  have subset {a b : N.Domain} : N.MemberSubset a b ↔ M.MemberSubset a.val b.val :=
    (image_subset_iff_l (M := N) (N := M) Subtype.val inj full).symm
  have edge := image_entry_iff_l (M := N) (N := M) Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hZF.1
  have ordinal (a : N.Domain) : N.IsOrdinal a ↔ M.IsOrdinal a.val := by
    let ρ : Env N 1 := ⟨fun _ => a,fun _ => a⟩
    exact (KP.ord0_sat_l (ZF.modelsKP native) ρ .newest).symm.trans
      ((delta0_image_l (M := N) (N := M) Subtype.val inj full (KP.ord0_delta_l .newest) ρ).trans
        (KP.ord0_sat_l (ZF.modelsKP hZF) (image_env_l Subtype.val ρ) .newest))
  obtain ⟨ω,X,hw,above,regular,strong,rank,all⟩ := wd
  have hω := trans δ.val δ.property ω above
  have below := ZF.v_ordinal_height_l hZF upper strong.1.1 δ.property
  have hX := ZF.v_mem_l I hZF rank upper below
  let w : N.Domain := ⟨ω,hω⟩
  let V : N.Domain := ⟨X,hX⟩
  let nu : Nonempty {x // M.mem x U} := ⟨w⟩
  let ρ : Env (rt_model_l U nu) 1 := ⟨fun _ => w,fun _ => w⟩
  have hwN : N.IsOmega w := (Formula.satisfies_isOmega_iff _ .newest).mp
    ((smem_formula_l I source nu (Formula.isOmega .newest) ρ).mp
      ((Formula.satisfies_isOmega_iff ρ .newest).mpr (rt_omega_l trans nu hZF.1 w hw)))
  obtain ⟨_,_,card⟩ := sc_v_inaccessible_l hZF upper δ.property above regular strong
  let η : Env (rt_model_l U nu) 2 := ⟨Fin.cases δ (fun _ => w),fun _ => w⟩
  have card' := (smem_formula_l I source nu (sc_inaccessible_m (.bound 1) .newest) η).mp card
  have nativeCard : N.mem w δ ∧ N.IsRegularCardinal J δ ∧ N.IsStrongLimitCardinal J δ := by
    simp only [sc_inaccessible_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
      Formula.satisfies_isRegularCardinal_iff J native.1,Formula.satisfies_isStrongLimitCardinal_iff J native.1] at card'
    exact card'
  refine ⟨w,V,hwN,nativeCard.1,nativeCard.2.1,nativeCard.2.2,
    (source.rank_iff_l hZF upper limit (ZF.modelsKP native) δ V).mpr rank,?_⟩
  intro A subA
  obtain ⟨κ,hκ,large⟩ := all A.val (subset.mp subA)
  let k₀ : N.Domain := ⟨κ,trans δ.val δ.property κ hκ⟩
  refine ⟨k₀,member.mpr hκ,fun ν hν => ?_⟩
  obtain ⟨Y,B,j,W,k,ty,yx,dy,rW,wy,pred,crit,νk,agree⟩ := large ν.val (member.mp hν)
  have pred₀ := pred
  obtain ⟨a,S,b,T,left,right,map⟩ := pred₀
  have hY := v_subset_mem_l I upper hX yx
  have hB := v_subset_mem_l I upper hY right.2.1
  have hW := v_subset_mem_l I upper hY wy
  have hj : M.mem j U := v_relation_mem_l I upper limit hX (fun p hp => by
    obtain ⟨x,y,pair⟩ := map.1.1.1.1 p hp
    exact ⟨x,map.1.1.input_mem_of_pairMember ⟨p,pair,hp⟩,
      y,yx y (map.1.1.output_mem_of_pairMember ⟨p,pair,hp⟩),pair⟩)
  have hk := trans Y hY k (map.1.1.output_mem_of_pairMember crit.image)
  let Y₀ : N.Domain := ⟨Y,hY⟩
  let B₀ : N.Domain := ⟨B,hB⟩
  let j₀ : N.Domain := ⟨j,hj⟩
  let W₀ : N.Domain := ⟨W,hW⟩
  let k₁ : N.Domain := ⟨k,hk⟩
  refine ⟨Y₀,B₀,j₀,W₀,k₁,?_,subset.mpr yx,subset.mpr dy,
    (source.rank_iff_l hZF upper limit (ZF.modelsKP native) ν W₀).mpr rW,subset.mpr wy,
    reflect_spred_emb_l Subtype.val inj full native hZF hwN hw pred,?_,member.mpr νk,?_⟩
  · intro a ha b hb
    exact member.mpr (ty a.val (member.mp ha) b.val (member.mp hb))
  · exact ⟨(ordinal k₀).mpr crit.ordinal,member.mpr crit.source,(ordinal k₁).mpr crit.ordinal_image,
      (edge k₀ k₁ j₀).mpr crit.image,fun eq => crit.moved (congrArg Subtype.val eq),
      fun a ha => (edge a a j₀).mpr (crit.fixed a.val (member.mp ha))⟩
  · intro x hx
    exact (member (a := x) (b := A)).trans
      ((agree x.val (member.mp hx)).trans (member (a := x) (b := B₀)).symm)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从真类 Woodin 构造固定原实数的初始可数源

真实不可达秩层包含整列 Woodin 及备用 Woodin。其可数初等壳保留完整
内部 ZFC；反坍塌固定自然数和给定实数。全部内部大基数资料从实际
秩层读取，最后在同一源内构造全乘积、规范名字及背景泛型集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem wd_initial_l {Ω a : M.Domain} (hw : M.IsOmega Ω) (proper : Wd_proper_d I)
    (binary : Bc_binary_d Ω a) :
    ∃ θ Y d S, Smem_d I d Y S ∧ V_d I θ Y ∧ Zc_model_d I Ω d Y S ∧
      ∃ c X R π, ∃ source : Smem_d I c X R, ∃ certificate : Zc_model_d I Ω c X R,
      M.TransitiveSet X ∧ M.CardinalLessOrEqual I X Ω ∧ Smap_d I Ω c d X Y π ∧
      let N := smdl_structure_l I (R := R) source.1.2.1
      let native := ZFC.models_zf_l (certificate.native_l I hZF hw)
      let J := kp_pair_l (ZF.modelsKP native)
      ∃ w A μ δ Z o κ b P V σ : N.Domain, w.val = Ω ∧ b.val = a ∧ Rd_entry_d a a π ∧
        N.IsOmega w ∧ Bc_binary_d w b ∧
        Wd_sequence_d J w A ∧ N.IsSetFunctionFromTo J A w μ ∧ N.mem μ δ ∧ Woodin_d J δ ∧ V_d J δ Z ∧
        (∀ x, ¬ N.mem x o) ∧ Entry_d N o κ A ∧
        ∃ K α Vα, Rd_entry_d κ.val K π ∧ M.IsUncountableCardinal I Ω K ∧
          Woodin_d I α ∧ V_d I α Vα ∧ M.mem Ω Vα ∧ M.MemberSubset α K ∧
          Fp_product_d native w A P V ∧ Rp_name_d native w A P σ ∧ ∃ H, Gset_d P.val V.val P.val X H := by
  obtain ⟨α,Vα,A,o,K,μ,δ,Z,_,_,_,wa,rankα,insideα,empty,first,hK,αK,sequence,fa,small,wd,rankδ,_,_⟩ :=
    wd_product_l hZFC hw proper
  let v : Fin 8 → M.Domain := fun i => [Ω,A,o,K,μ,δ,Z,a].get i
  obtain ⟨B,finite,params⟩ := ZF.finite_params_l I hZF hw v
  obtain ⟨γ,U,rankU,hB⟩ := ZF.v_cover_l I hZF B
  obtain ⟨θ,γθ,large⟩ := proper γ (v_ordinal_l I rankU)
  obtain ⟨wθ,Y,hwθ,above,regular,strong,rank,_⟩ := large
  have eqw := hZF.1.eq_of_same_members wθ Ω (fun n => ⟨hwθ.2 Ω hw.1 n,hw.2 wθ hwθ.1 n⟩)
  have transY := v_transitive_l I rank
  have byY := transY U (ZF.v_mem_l I hZF rankU rank γθ) B hB
  have owned i : M.mem (v i) Y := transY B byY (v i) ((params (v i)).mpr ⟨i,rfl⟩)
  obtain ⟨d,S,target,theory⟩ := zc_inaccessible_l hZFC hw (eqw ▸ above) regular strong rank
  have hY := ZFC.models_zf_l (theory.native_l I hZF hw)
  -- 种子含全部内部自然数及八个实际参数；可数性在背景内部证明。
  obtain ⟨B₀,union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) Ω B
  obtain ⟨id,identity⟩ := ZF.exists_identityBijection hZF I Ω
  have countSeed := ZF.countable_union_two_l I hZF hw ⟨id,identity.1⟩
    (ZF.finite_countable_l I hZF hw finite) union
  have seed x (hx : M.mem x B₀) : M.mem x Y := ((union x).mp hx).elim
    (transY Ω (owned 0) x) (transY B byY x)
  obtain ⟨X₀,c₀,R₀,X,F,π,c,R,_,cover,_,_,trans,collapse,count,inverse,source,map⟩ :=
    selem_hull_collapse_l hZFC hw transY target seed countSeed
  have certificate := theory.pull_l hZF hw source.1 map
  let N := smdl_structure_l I (R := R) source.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hw)
  let J := kp_pair_l (ZF.modelsKP native)
  have preimage x (hx : M.mem x B₀) : ∃ y, Rd_entry_d y x π := by
    obtain ⟨y,_,xy⟩ := collapse.function.2.1 x (cover x hx)
    exact ⟨y,(inverse x y).mpr xy⟩
  have parameter i : ∃ y, Rd_entry_d y (v i) π :=
    preimage (v i) ((union (v i)).mpr (Or.inr ((params (v i)).mpr ⟨i,rfl⟩)))
  have rel x y z t (xz : Rd_entry_d x z π) (yt : Rd_entry_d y t π) :=
    map.member_l I hZF hw source target xz yt
  obtain ⟨_,naturals⟩ := mem_embedding_fixed_l hZF trans map.1 rel
    (hw.transitive (ZF.modelsKP hZF)) (fun n hn => preimage n ((union n).mpr (Or.inl hn)))
  obtain ⟨w₀,wΩ⟩ := parameter 0
  have sameω : w₀ = Ω := map.fixed_preimage_l hZF hw trans source target wΩ naturals
  subst w₀
  have hΩ : M.mem Ω X := map.1.1.input_mem_of_pairMember wΩ
  have ΩΩ : Rd_entry_d Ω Ω π := wΩ
  let w : N.Domain := ⟨Ω,hΩ⟩
  let nx : Nonempty {x // M.mem x X} := ⟨w⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => w,fun _ => w⟩
  have hwN : N.IsOmega w := (Formula.satisfies_isOmega_iff _ .newest).mp
    ((smem_formula_l I source nx (Formula.isOmega .newest) ρ).mp
      ((Formula.satisfies_isOmega_iff ρ .newest).mpr (rt_omega_l trans nx hZF.1 w hw)))
  -- 反坍塌固定原实数整张图，而不仅保留其一个同构副本。
  obtain ⟨a₀,aa⟩ := parameter 7
  have real : Fn0_d Ω Ω a₀ := (map.function_l hZF hw trans transY source target ΩΩ ΩΩ aa).mpr binary.1
  have fixed := map.fixed_function_l hZF hw trans transY source target ΩΩ naturals hΩ
    (map.1.1.input_mem_of_pairMember aa) real (fun _ y edge => naturals y (real.bound_l edge).2)
  have eqa : a₀ = a := map.1.1.1.2 _ _ _ fixed aa
  let b : N.Domain := ⟨a,eqa ▸ map.1.1.input_mem_of_pairMember aa⟩
  have binaryN : Bc_binary_d w b := by
    let ρ : Env N 2 := ⟨fun i => [w,b].get i,fun _ => w⟩
    exact (bc_binary_sat_l native.1 ρ (.bound 0) (.bound 1)).mp
      ((smem_delta_image_l I source trans (bc_binary_delta_l ..) ρ).mpr
        ((bc_binary_sat_l hZF.1 (image_env_l (M := N) (N := M) Subtype.val ρ) (.bound 0) (.bound 1)).mpr binary))
  obtain ⟨A₁,aA⟩ := parameter 1
  obtain ⟨o₁,oo⟩ := parameter 2
  obtain ⟨κ₁,kK⟩ := parameter 3
  obtain ⟨μ₁,mm⟩ := parameter 4
  obtain ⟨δ₁,dd⟩ := parameter 5
  obtain ⟨Z₁,zz⟩ := parameter 6
  let A' : N.Domain := ⟨A₁,map.1.1.input_mem_of_pairMember aA⟩
  let o' : N.Domain := ⟨o₁,map.1.1.input_mem_of_pairMember oo⟩
  let κ' : N.Domain := ⟨κ₁,map.1.1.input_mem_of_pairMember kK⟩
  let μ' : N.Domain := ⟨μ₁,map.1.1.input_mem_of_pairMember mm⟩
  let δ' : N.Domain := ⟨δ₁,map.1.1.input_mem_of_pairMember dd⟩
  let Z' : N.Domain := ⟨Z₁,map.1.1.input_mem_of_pairMember zz⟩
  have member {x y : N.Domain} : N.mem x y ↔ M.mem x.val y.val := smem_member_l I source.1 source.2 x y
  have full := smem_full_l I source trans
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have edge := image_entry_iff_l (M := N) (N := M) Subtype.val inj full (KP.exists_pair (ZF.modelsKP native)) hZF.1
  have fa' : N.IsSetFunctionFromTo J A' w μ' := fn0_function_l (ZF.modelsKP native)
    ((smem_fn0_l I hZF.1 source trans w μ' A').mpr
      ((map.function_l hZF hw trans transY source target ΩΩ mm aA).mpr (fn0_of_function_l (ZF.modelsKP hZF) fa)))
  obtain ⟨e,elem,values⟩ := map.project_l I hZF hw source.1 target.1
  -- 全部原生 Woodin 判断先在真实秩层验证，再沿原壳映射回拉。
  have reflectWd (ε : N.Domain) (hε : Woodin_d I (e ε).val) : Woodin_d J ε := by
    let ρ : Env N 1 := ⟨fun _ => ε,fun _ => ε⟩
    have wd' := hε.rank_l hZF target rank regular.isLimitOrdinal hY (e ε)
    exact (woodin_sat_l J native.1 ρ .newest).mp
      ((elem (woodin_m (𝒞 := kpair_convention_l) .newest) (by simp -implicitDefEqProofs) ρ).mpr
        ((woodin_sat_l (kp_pair_l (ZF.modelsKP hY)) hY.1 (image_env_l e ρ) .newest).mpr wd'))
  have read i ε (iε : Entry_d N i ε A') : Rd_entry_d (e i).val (e ε).val A :=
    (map.entry_l hZF hw trans transY source target (values i) (values ε) aA).mp ((edge i ε A').mp iε)
  have sequence' : Wd_sequence_d J w A' := ⟨fa'.1,fa'.2.1,
    fun i ε iε => reflectWd ε (sequence.woodin (e i).val (e ε).val (read i ε iε)),
    fun i j ε ζ ij iε jζ => member.mpr ((rel _ _ _ _ (values ε) (values ζ)).mpr
      (sequence.increasing _ _ _ _ ((rel _ _ _ _ (values i) (values j)).mp (member.mp ij))
        (read i ε iε) (read j ζ jζ)))⟩
  have eδ : (e δ').val = δ := map.1.1.1.2 _ _ _ (values δ') dd
  have eZ : (e Z').val = Z := map.1.1.1.2 _ _ _ (values Z') zz
  have wd' := reflectWd δ' (eδ.symm ▸ wd)
  have rank' : V_d J δ' Z' := by
    let ρ : Env N 2 := ⟨Fin.cases δ' (fun _ => Z'),fun _ => δ'⟩
    have actual : V_d I (e δ').val (e Z').val := eδ.symm ▸ eZ.symm ▸ rankδ
    have nativeRank := (target.rank_iff_l hZF rank regular.isLimitOrdinal (ZF.modelsKP hY) (e δ') (e Z')).mpr actual
    exact (v_sat_l J native.1 ρ (.bound 0) (.bound 1)).mp
      ((elem (v_m kpair_convention_l (.bound 0) (.bound 1)) (by simp -implicitDefEqProofs) ρ).mpr
        ((v_sat_l (kp_pair_l (ZF.modelsKP hY)) hY.1 (image_env_l e ρ) (.bound 0) (.bound 1)).mpr nativeRank))
  have empty' : ∀ x, ¬ N.mem x o' := by
    intro x hx
    exact empty (e x).val ((rel _ _ _ _ (values x) oo).mp (member.mp hx))
  have first' : Entry_d N o' κ' A' := (edge o' κ' A').mpr
    ((map.entry_l hZF hw trans transY source target oo kK aA).mpr first)
  have small' : N.mem μ' δ' := member.mpr ((rel _ _ _ _ mm dd).mpr small)
  -- 原全乘积、规范名字及其真正泛型集合一并生成。
  obtain ⟨P,V,product⟩ := fp_product_l native hwN fa'
  obtain ⟨σ,name⟩ := rp_name_exists_l native hwN fa' product
  have base := (product.empty_top_l native hwN empty').1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,H,_,_,_,_,_,_,_,sub,_,generic⟩ :=
    gn_source_branch_l hZF hw (ZFC.dc_l I hZFC hw) source trans native count P V o' (product.order_l native) base
  have coded := (source.generic_code_l I hZF.1 trans (ZF.modelsKP native) P V P H).mpr ⟨sub,generic⟩
  exact ⟨θ,Y,d,S,target,rank,theory,c,X,R,π,source,certificate,trans,count,map,w,A',μ',δ',Z',o',κ',b,P,V,σ,
    rfl,rfl,eqa ▸ fixed,hwN,binaryN,sequence',fa',small',wd',rank',empty',first',K,α,Vα,kK,hK,wa,rankα,insideα,
    hK.1.1.transitive α αK,product,name,H,coded⟩

end YesMetaZFC.SetTheory.LargeCardinal
