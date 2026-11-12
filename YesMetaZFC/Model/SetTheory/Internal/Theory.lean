import YesMetaZFC.Model.SetTheory.Internal.Quotient
import YesMetaZFC.SetTheory.FunctionSpaceConstruction

/-! # 集合编码赋值及单变量更新

变量域 V 和对象域 X 都是内部集合。赋值空间是 X^V 的实际内部函数集；
量词使用覆盖一个坐标的函数图，不在宿主层选择点值或更新函数。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Senv_update_d (f i x g : M.Domain) : Prop :=
  M.IsSetRelation I g ∧ ∀ j y, M.PairMember I j y g ↔
    (j = i ∧ y = x) ∨ (j ≠ i ∧ M.PairMember I j y f)

def senv_update_m {n} (f i x g : Term n) : Formula 1 n :=
  .conj (Formula.isRelation 𝒞 g) (.forallE (.forallE
    (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest g.weaken.weaken)
      (.disj (.conj (Formula.extensionalEq (.bound 1) i.weaken.weaken)
        (Formula.extensionalEq .newest x.weaken.weaken))
        (.conj (.neg (Formula.extensionalEq (.bound 1) i.weaken.weaken))
          (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken))))))
derive_free_closed senv_update_m

theorem senv_update_sat_l (hE : Extensional M) {n} (ρ : Env M n) (f i x g : Term n) :
    Formula.satisfies ρ (senv_update_m (𝒞 := 𝒞) f i x g) ↔
      Senv_update_d I (f.eval ρ) (i.eval ρ) (x.eval ρ) (g.eval ρ) := by
  simp only [senv_update_m, Senv_update_d, Formula.satisfies_conj_iff,
    Formula.satisfies_isRelation_iff I, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_neg_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  rfl

theorem senv_update_unique_l (hE : Extensional M) {f i x g h}
    (hg : Senv_update_d I f i x g) (hh : Senv_update_d I f i x h) : g = h :=
  hg.1.eq_of_pairMember_iff hE hh.1 (fun j y => (hg.2 j y).trans (hh.2 j y).symm)

/-- 任意满足更新方程的图仍是同一变量域上的赋值；不需要选择或额外集合公理。 -/
theorem Senv_update_d.function_l {V X f i x g} (h : Senv_update_d I f i x g)
    (hf : M.IsSetFunctionFromTo I f V X) (hi : M.mem i V) (hx : M.mem x X) :
    M.IsSetFunctionFromTo I g V X := by
  classical
  have range j y (hy : M.PairMember I j y g) : M.mem j V ∧ M.mem y X := by
    rcases (h.2 j y).mp hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · exact ⟨hi, hx⟩
    · exact ⟨hf.input_mem_of_pairMember hy, hf.output_mem_of_pairMember hy⟩
  have total j (hj : M.mem j V) : ∃ y, M.mem y X ∧ M.PairMember I j y g := by
    by_cases he : j = i
    · exact ⟨x, hx, (h.2 j x).mpr (Or.inl ⟨he, rfl⟩)⟩
    · obtain ⟨y, hy, hjy⟩ := hf.2.2 j hj
      exact ⟨y, hy, (h.2 j y).mpr (Or.inr ⟨he, hjy⟩)⟩
  refine ⟨⟨h.1, ?_⟩, fun j => ⟨fun hj => (total j hj).elim fun y h => ⟨y, h.2⟩,
    fun ⟨y, hy⟩ => (range j y hy).1⟩, total⟩
  intro j a b ha hb
  rcases (h.2 j a).mp ha with ⟨he, rfl⟩ | ⟨he, ha⟩ <;>
    rcases (h.2 j b).mp hb with ⟨he', rfl⟩ | ⟨he', hb⟩
  · rfl
  · exact (he' he).elim
  · exact (he he').elim
  · exact hf.1.2 j a b ha hb

/-- 更新模型内赋值并核验函数域和值域；变量域不必是外部可数集。 -/
theorem senv_update_exists_l (hZF : M.Models ZF) {V X f i x}
    (hf : M.IsSetFunctionFromTo I f V X) (hi : M.mem i V) (hx : M.mem x X) :
    ∃ g, Senv_update_d I f i x g ∧ M.IsSetFunctionFromTo I g V X := by
  classical
  let ρ : Env M 3 := ((⟨fun _ => f, fun _ => f⟩ : Env M 1).push i).push x
  let φ : BinarySchema 3 := {
    body := .disj (.conj (Formula.extensionalEq (.bound 1) (.bound 3))
      (Formula.extensionalEq .newest (.bound 2)))
      (.conj (.neg (Formula.extensionalEq (.bound 1) (.bound 3)))
        (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4))) }
  have hφ j y : φ.denote ρ j y ↔ (j = i ∧ y = x) ∨ (j ≠ i ∧ M.PairMember I j y f) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  obtain ⟨g, hg, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := V) (target := X)
    (fun j hj => by
      by_cases hji : j = i
      · exact ⟨x, (hφ j x).mpr (Or.inl ⟨hji, rfl⟩)⟩
      · obtain ⟨y, _, hy⟩ := hf.2.2 j hj
        exact ⟨y, (hφ j y).mpr (Or.inr ⟨hji, hy⟩)⟩)
    (by
      intro j _ y z hy hz
      rcases (hφ j y).mp hy with ⟨hji, rfl⟩ | ⟨hji, hy⟩ <;>
        rcases (hφ j z).mp hz with ⟨hji', rfl⟩ | ⟨hji', hz⟩
      · rfl
      · exact (hji' hji).elim
      · exact (hji hji').elim
      · exact hf.1.2 j y z hy hz)
    (fun j y _ hy => ((hφ j y).mp hy).elim (fun h => h.2.symm ▸ hx) (fun h => hf.output_mem_of_pairMember h.2))
  refine ⟨g, ⟨hg.1.1, fun j y => (he j y).trans ?_⟩, hg⟩
  rw [hφ j y]
  exact ⟨And.right, fun h => ⟨h.elim (fun h => h.1.symm ▸ hi) (fun h => hf.input_mem_of_pairMember h.2), h⟩⟩

/-- 非空集合结构的完整赋值空间实际存在且非空。 -/
theorem senv_space_l (hZF : M.Models ZF) (V : M.Domain) {X} (hX : ∃ x, M.mem x X) :
    ∃ E, M.IsFunctionSpace I E V X ∧ ∃ f, M.mem f E := by
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I V X
  obtain ⟨x, hx⟩ := hX
  obtain ⟨f, hf, _⟩ := ZF.exists_constantFunction hZF I (source := V) hx
  exact ⟨E, hE, f, (hE f).mpr hf⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 模型内部的有限公式指令码

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
  obtain ⟨G, hG, he⟩ := hF.2.1.exists_append (ZF.modelsKP hZF) I (hω.members_areOrdinals (ZF.modelsKP hZF) l hlω) hl (value := c)
  refine ⟨l, G, hl, ⟨hlω, hG, fun i a ha => ?_⟩, he⟩
  rcases (he i a).mp ha with ha | ⟨rfl, rfl⟩
  · exact hF.2.2 i a ha
  · exact hc

end YesMetaZFC.SetTheory.Internal

/-! ## 内部满足关系的递归原公式

每行真值是一个赋值集合。关系与等号逐点读取赋值；或非取两真值集之并的补；
存在量词沿单变量更新作投影。递归算子只生成原公式，解的存在性由后续模块证明。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sarg_d (k : Nat) (X R H f i j : M.Domain) : Prop :=
  match k with
  | 0 => ∃ x y, M.PairMember I i x f ∧ M.PairMember I j y f ∧ M.PairMember I x y R
  | 1 => ∃ x, M.PairMember I i x f ∧ M.PairMember I j x f
  | 2 => ∃ A B, M.PairMember I i A H ∧ M.PairMember I j B H ∧ ¬ (M.mem f A ∨ M.mem f B)
  | _ => ∃ A, M.PairMember I j A H ∧ ∃ x g, M.mem x X ∧ Senv_update_d I f i x g ∧ M.mem g A

def sarg_m (k : Nat) {n} (X R H f i j : Term n) : Formula 1 n :=
  match k with
  | 0 => .existsE (.existsE
      (.conj (Formula.orderedPairMem 𝒞 i.weaken.weaken (.bound 1) f.weaken.weaken)
        (.conj (Formula.orderedPairMem 𝒞 j.weaken.weaken .newest f.weaken.weaken)
          (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken))))
  | 1 => .existsE (.conj (Formula.orderedPairMem 𝒞 i.weaken .newest f.weaken)
      (Formula.orderedPairMem 𝒞 j.weaken .newest f.weaken))
  | 2 => .existsE (.existsE
      (.conj (Formula.orderedPairMem 𝒞 i.weaken.weaken (.bound 1) H.weaken.weaken)
        (.conj (Formula.orderedPairMem 𝒞 j.weaken.weaken .newest H.weaken.weaken)
          (.neg (.disj (.mem f.weaken.weaken (.bound 1)) (.mem f.weaken.weaken .newest))))))
  | _ => .existsE (.conj (Formula.orderedPairMem 𝒞 j.weaken .newest H.weaken)
      (.existsE (.existsE (.conj (.mem (.bound 1) X.weaken.weaken.weaken)
        (.conj (senv_update_m (𝒞 := 𝒞) f.weaken.weaken.weaken i.weaken.weaken.weaken (.bound 1) .newest)
          (.mem .newest (.bound 2)))))))
@[simp] theorem sarg_closed_l (k : Nat) {n} (X R H f i j : Term n)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hH : H.freeSupport = [])
    (hf : f.freeSupport = []) (hi : i.freeSupport = []) (hj : j.freeSupport = []) :
    (sarg_m (𝒞 := 𝒞) k X R H f i j).FreeClosed := by
  rcases k with _ | (_ | (_ | k)) <;>
    simp -implicitDefEqProofs [sarg_m, Definitional.Formula.FreeClosed, hX, hR, hH, hf, hi, hj]

theorem sarg_sat_l (hE : Extensional M) (k : Nat) {n} (ρ : Env M n) (X R H f i j : Term n) :
    Formula.satisfies ρ (sarg_m (𝒞 := 𝒞) k X R H f i j) ↔
      Sarg_d I k (X.eval ρ) (R.eval ρ) (H.eval ρ) (f.eval ρ) (i.eval ρ) (j.eval ρ) := by
  rcases k with _ | (_ | (_ | k)) <;>
    simp only [sarg_m, Sarg_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_mem_iff, senv_update_sat_l I hE,
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest] <;> rfl

def Snode_d (X R H c f : M.Domain) : Prop :=
  ∃ k : Fin 4, ∃ i j, Sop_d I k.val c i j ∧ Sarg_d I k.val X R H f i j

private def eval_case_m (k : Nat) {n} (X R H c f : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (sop_m (𝒞 := 𝒞) k c.weaken.weaken (.bound 1) .newest)
    (sarg_m (𝒞 := 𝒞) k X.weaken.weaken R.weaken.weaken H.weaken.weaken f.weaken.weaken (.bound 1) .newest)))
derive_free_closed eval_case_m

def snode_m {n} (X R H c f : Term n) : Formula 1 n :=
  .disj (eval_case_m (𝒞 := 𝒞) 0 X R H c f) (.disj (eval_case_m (𝒞 := 𝒞) 1 X R H c f)
    (.disj (eval_case_m (𝒞 := 𝒞) 2 X R H c f) (eval_case_m (𝒞 := 𝒞) 3 X R H c f)))
derive_free_closed snode_m

theorem snode_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R H c f : Term n) :
    Formula.satisfies ρ (snode_m (𝒞 := 𝒞) X R H c f) ↔
      Snode_d I (X.eval ρ) (R.eval ρ) (H.eval ρ) (c.eval ρ) (f.eval ρ) := by
  simp only [snode_m, Snode_d, Fin.exists_fin_succ, Fin.exists_fin_zero, or_false,
    eval_case_m, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, sop_sat_l I, sarg_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 合法构造符唯一决定其语义分支，不能用另一种指令伪造真值。 -/
theorem snode_decode_l (hKP : M.Models KP) {X R H c f i j} (k : Fin 4) (hc : Sop_d I k.val c i j) :
    Snode_d I X R H c f ↔ Sarg_d I k.val X R H f i j := by
  constructor
  · rintro ⟨l, a, b, hd, harg⟩
    obtain ⟨hk, rfl, rfl⟩ := sop_injective_l I hKP hc hd
    have he : k = l := Fin.ext hk
    subst l
    exact harg
  · exact fun h => ⟨k, i, j, hc, h⟩

def Seval_at_d (X R F H f : M.Domain) : Prop :=
  ∃ k c, M.IsDomainOf I k H ∧ M.PairMember I k c F ∧ Snode_d I X R H c f

def seval_at_m {n} (X R F H f : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (Formula.isDomain 𝒞 (.bound 1) H.weaken.weaken)
    (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
      (snode_m (𝒞 := 𝒞) X.weaken.weaken R.weaken.weaken H.weaken.weaken .newest f.weaken.weaken))))
derive_free_closed seval_at_m

theorem seval_at_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R F H f : Term n) :
    Formula.satisfies ρ (seval_at_m (𝒞 := 𝒞) X R F H f) ↔
      Seval_at_d I (X.eval ρ) (R.eval ρ) (F.eval ρ) (H.eval ρ) (f.eval ρ) := by
  simp only [seval_at_m, Seval_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isDomain_iff I, Formula.satisfies_orderedPairMem_iff I, snode_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Seval_step_d (X R E F H Y : M.Domain) : Prop :=
  ∀ f, M.mem f Y ↔ M.mem f E ∧ Seval_at_d I X R F H f

def seval_step_m {n} (X R E F H Y : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest Y.weaken) (.conj (.mem .newest E.weaken)
    (seval_at_m (𝒞 := 𝒞) X.weaken R.weaken F.weaken H.weaken .newest)))
derive_free_closed seval_step_m

theorem seval_step_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R E F H Y : Term n) :
    Formula.satisfies ρ (seval_step_m (𝒞 := 𝒞) X R E F H Y) ↔
      Seval_step_d I (X.eval ρ) (R.eval ρ) (E.eval ρ) (F.eval ρ) (H.eval ρ) (Y.eval ρ) := by
  simp only [seval_step_m, Seval_step_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, seval_at_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def seval_s : BinarySchema 4 := {
  body := seval_step_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }

def seval_env_l (X R E F : M.Domain) : Env M 4 :=
  (((⟨fun _ => X, fun _ => X⟩ : Env M 1).push R).push E).push F

theorem seval_op_l (hE : Extensional M) (ρ : Env M 4) :
    (seval_s (𝒞 := 𝒞)).denote ρ = Seval_step_d I (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) := by
  funext H Y
  exact propext (seval_step_sat_l I hE ((ρ.push H).push Y) _ _ _ _ _ _)

def Seval_d (X R E F n H : M.Domain) : Prop :=
  M.IsRecursiveSequence I (Seval_step_d I X R E F) H n

def seval_m {n} (X R E F l H : Term n) : Formula 1 n :=
  Formula.isRecursiveSequence 𝒞 (seval_s (𝒞 := 𝒞))
    (Definitional.TermVector.ofFn (Fin.cases F (Fin.cases E (Fin.cases R (fun _ => X))))) H l
@[simp] theorem seval_closed_l {n} (X R E F l H : Term n)
    (hX : X.freeSupport = []) (hR : R.freeSupport = []) (hE : E.freeSupport = [])
    (hF : F.freeSupport = []) (hl : l.freeSupport = []) (hH : H.freeSupport = []) :
    (seval_m (𝒞 := 𝒞) X R E F l H).FreeClosed := by
  apply Formula.isRecursiveSequence_freeClosed
  · intro i
    simp only [Definitional.TermVector.get_ofFn]
    exact Fin.cases hF (Fin.cases hE (Fin.cases hR (fun _ => hX))) i
  · exact hH
  · exact hl

theorem seval_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R E F l H : Term n) :
    Formula.satisfies ρ (seval_m (𝒞 := 𝒞) X R E F l H) ↔
      Seval_d I (X.eval ρ) (R.eval ρ) (E.eval ρ) (F.eval ρ) (l.eval ρ) (H.eval ρ) := by
  rw [seval_m, Formula.satisfies_isRecursiveSequence_iff I hE, seval_op_l I hE]
  rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 内部真值递归的存在、唯一性与原公式

一步算子在赋值空间上作实际分离，原序数递归给出整张真值表。递归先对任意
内部序数长度成立，有限公式码只需取长度属于 ω；没有外部良基性或真值表假设。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem seval_step_exists_l (hZF : M.Models ZF) (X R E F H : M.Domain) :
    ∃ Y, Seval_step_d I X R E F H Y := by
  let ρ := (seval_env_l X R E F).push H
  let φ : UnarySchema 5 := {
    body := seval_at_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 2) (.bound 1) .newest }
  obtain ⟨Y, hY⟩ := ZF.separation_exists_d hZF φ ρ E
  exact ⟨Y, fun f => (hY f).trans (and_congr_right fun _ => seval_at_sat_l I hZF.1 (ρ.push f) _ _ _ _ _)⟩

theorem seval_step_unique_l (hE : Extensional M) {X R E F H Y Z}
    (h : Seval_step_d I X R E F H Y) (k : Seval_step_d I X R E F H Z) : Y = Z :=
  hE.eq_of_same_members Y Z (fun f => (h f).trans (k f).symm)

theorem seval_class_l (hZF : M.Models ZF) (X R E F : M.Domain) :
    M.IsClassFunctionOnTransfiniteSequences I (Seval_step_d I X R E F) := by
  intro H _
  obtain ⟨Y, hY⟩ := seval_step_exists_l I hZF X R E F H
  exact ⟨Y, hY, fun Z hZ => seval_step_unique_l I hZF.1 hZ hY⟩

/-- 每个内部序数长度的真值表实际存在；算子的全定义性已由分离证明。 -/
theorem seval_exists_l (hZF : M.Models ZF) (X R E F : M.Domain) {n} (hn : M.IsOrdinal n) :
    ∃ H, Seval_d I X R E F n H := by
  have ho : (seval_s (𝒞 := 𝒞)).denote (seval_env_l X R E F) = Seval_step_d I X R E F :=
    seval_op_l I hZF.1 (seval_env_l X R E F)
  have hc : M.IsClassFunctionOnTransfiniteSequences I
      ((seval_s (𝒞 := 𝒞)).denote (seval_env_l X R E F)) := by
    rw [ho]
    exact seval_class_l I hZF X R E F
  obtain ⟨H, hH⟩ := ZF.recursiveSequence_exists hZF I (seval_env_l X R E F) (seval_s (𝒞 := 𝒞)) hc hn
  exact ⟨H, by simpa only [ho, Seval_d] using hH⟩

theorem seval_unique_l (hZF : M.Models ZF) {X R E F n H J}
    (hH : Seval_d I X R E F n H) (hJ : Seval_d I X R E F n J) : H = J := by
  have ho : (seval_s (𝒞 := 𝒞)).denote (seval_env_l X R E F) = Seval_step_d I X R E F :=
    seval_op_l I hZF.1 (seval_env_l X R E F)
  have hc : M.IsClassFunctionOnTransfiniteSequences I
      ((seval_s (𝒞 := 𝒞)).denote (seval_env_l X R E F)) := by
    rw [ho]
    exact seval_class_l I hZF X R E F
  exact ZF.recursiveSequence_unique hZF I (seval_env_l X R E F) (seval_s (𝒞 := 𝒞)) hc
    (by simpa only [ho, Seval_d] using hH) (by simpa only [ho, Seval_d] using hJ)

def Ssat_d (X R E F n k f : M.Domain) : Prop :=
  ∃ H Y, Seval_d I X R E F n H ∧ M.PairMember I k Y H ∧ M.mem f Y

def ssat_m {n} (X R E F l k f : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (seval_m (𝒞 := 𝒞) X.weaken.weaken R.weaken.weaken E.weaken.weaken
    F.weaken.weaken l.weaken.weaken (.bound 1))
    (.conj (Formula.orderedPairMem 𝒞 k.weaken.weaken .newest (.bound 1)) (.mem f.weaken.weaken .newest))))
derive_free_closed ssat_m

theorem ssat_sat_l (hE : Extensional M) {n} (ρ : Env M n) (X R E F l k f : Term n) :
    Formula.satisfies ρ (ssat_m (𝒞 := 𝒞) X R E F l k f) ↔
      Ssat_d I (X.eval ρ) (R.eval ρ) (E.eval ρ) (F.eval ρ) (l.eval ρ) (k.eval ρ) (f.eval ρ) := by
  simp only [ssat_m, Ssat_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    seval_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 存在量化的满足关系精确等于唯一真值表中的实际成员性。 -/
theorem ssat_value_l (hZF : M.Models ZF) {X R E F n H k Y}
    (hH : Seval_d I X R E F n H) (hY : M.PairMember I k Y H) (f : M.Domain) :
    Ssat_d I X R E F n k f ↔ M.mem f Y := by
  constructor
  · rintro ⟨J, Z, hJ, hZ, hf⟩
    have he := seval_unique_l I hZF hJ hH
    subst J
    exact (hH.1.2.1.2 k Z Y hZ hY) ▸ hf
  · exact fun hf => ⟨H, Y, hH, hY, hf⟩

/-- 直接解码任意一行，所得递归语义使用精确的先前真值表。 -/
theorem seval_unfold_l (hE : Extensional M) {X R E F n H k c Y}
    (hF : M.IsSetFunction I F) (hH : Seval_d I X R E F n H)
    (hc : M.PairMember I k c F) (hY : M.PairMember I k Y H) : ∃ P,
    M.IsRestrictionOf I P H k ∧ M.IsDomainOf I k P ∧
      ∀ f, M.mem f Y ↔ M.mem f E ∧ Snode_d I X R P c f := by
  have hk := (hH.1.2.2 k).mpr ⟨Y, hY⟩
  obtain ⟨P, hP, hStep⟩ := hH.2 k hk Y hY
  have hd := (hH.restriction hk hP).1.2.2
  refine ⟨P, hP, hd, fun f => (hStep f).trans (and_congr_right fun _ => ?_)⟩
  constructor
  · rintro ⟨l, d, hl, hld, h⟩
    have he := hl.eq hE hd
    subst l
    have he := hF.2 k d c hld hc
    subst d
    exact h
  · exact fun h => ⟨k, c, hd, hc, h⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 编码满足关系的完整逻辑方程

合法指令的子公式编号严格小于当前行，所以先前真值表和完整真值表在这些
编号处一致。由此直接得到关系、等号、或非与存在量词的 Tarski 方程。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sref_d (k : Nat) (ω r i j : M.Domain) : Prop :=
  match k with
  | 0 | 1 => M.mem i ω ∧ M.mem j ω
  | 2 => M.mem i r ∧ M.mem j r
  | _ => M.mem i ω ∧ M.mem j r

theorem Sfm_node_d.refs_l (hKP : M.Models KP) {ω r c k i j}
    (hc : Sfm_node_d I ω r c) (hs : Sop_d I k c i j) : Sref_d k ω r i j := by
  rcases hc with ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ | ⟨a, b, ht, ha, hb⟩ <;>
    obtain ⟨rfl, rfl, rfl⟩ := sop_injective_l I hKP hs ht <;> exact ⟨ha, hb⟩

private theorem arg_restrict_l {k X R H P ω r f i j} (hP : M.IsRestrictionOf I P H r)
    (hr : Sref_d k ω r i j) : Sarg_d I k X R P f i j ↔ Sarg_d I k X R H f i j := by
  have hp a A (ha : M.mem a r) : M.PairMember I a A P ↔ M.PairMember I a A H :=
    (hP.2 a A).trans ⟨And.right, fun h => ⟨ha, h⟩⟩
  rcases k with _ | (_ | (_ | k))
  · rfl
  · rfl
  · exact exists_congr fun A => exists_congr fun B =>
      and_congr (hp i A hr.1) (and_congr (hp j B hr.2) Iff.rfl)
  · exact exists_congr fun A => and_congr (hp j A hr.2) Iff.rfl

/-- 原指令只读取严格较早行，故全表与当前行以前的限制给出同一节点真值。 -/
theorem snode_restrict_l (hKP : M.Models KP) {ω X R H P r c : M.Domain}
    (hc : Sfm_node_d I ω r c) (hP : M.IsRestrictionOf I P H r) (f : M.Domain) :
    Snode_d I X R P c f ↔ Snode_d I X R H c f :=
  exists_congr fun _ => exists_congr fun _ => exists_congr fun _ => and_congr_right fun hs =>
    arg_restrict_l I hP (hc.refs_l I hKP hs)

theorem seval_row_l (hZF : M.Models ZF) {ω X R E F n H r c Y}
    (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H)
    (hc : M.PairMember I r c F) (hY : M.PairMember I r Y H) (f : M.Domain) :
    M.mem f Y ↔ M.mem f E ∧ Snode_d I X R H c f := by
  obtain ⟨P, hP, _, he⟩ := seval_unfold_l I hZF.1 hF.2.1.2.1 hH hc hY
  refine (he f).trans (and_congr_right fun _ => ?_)
  exact snode_restrict_l I (ZF.modelsKP hZF) (hF.2.2 r c hc) hP f

/-- 满足关系直接展开为该构造符在唯一真值表中的语义。 -/
theorem ssat_op_l (hZF : M.Models ZF) {ω X R E F n H r c i j}
    (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H) (hc : M.PairMember I r c F)
    (k : Fin 4) (hs : Sop_d I k.val c i j) (f : M.Domain) :
    Ssat_d I X R E F n r f ↔ M.mem f E ∧ Sarg_d I k.val X R H f i j := by
  have hr := (hF.2.1.2.2 r).mpr ⟨c, hc⟩
  obtain ⟨Y, hY⟩ := (hH.1.2.2 r).mp hr
  exact (ssat_value_l I hZF hH hY f).trans ((seval_row_l I hZF hF hH hc hY f).trans
    (and_congr Iff.rfl (snode_decode_l I (ZF.modelsKP hZF) k hs)))

/-- 二元关系的编码真值就是解码关系在赋值对象上的真值。 -/
theorem ssat_rel_l (hZF : M.Models ZF) {ω V X R E F n H r c i j f x y}
    (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H) (hc : M.PairMember I r c F)
    (hs : Sop_d I 0 c i j) (hE : M.IsFunctionSpace I E V X) (hf : M.mem f E)
    (hi : M.PairMember I i x f) (hj : M.PairMember I j y f) :
    Ssat_d I X R E F n r f ↔ M.PairMember I x y R := by
  rw [ssat_op_l I hZF hF hH hc 0 hs f]
  have hh := (hE f).mp hf
  constructor
  · rintro ⟨_, a, b, ha, hb, hr⟩
    have hx := hh.1.2 i a x ha hi
    have hy := hh.1.2 j b y hb hj
    exact hx ▸ hy ▸ hr
  · exact fun hr => ⟨hf, x, y, hi, hj, hr⟩

theorem ssat_eq_l (hZF : M.Models ZF) {ω V X R E F n H r c i j f x y}
    (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H) (hc : M.PairMember I r c F)
    (hs : Sop_d I 1 c i j) (hE : M.IsFunctionSpace I E V X) (hf : M.mem f E)
    (hi : M.PairMember I i x f) (hj : M.PairMember I j y f) :
    Ssat_d I X R E F n r f ↔ x = y := by
  rw [ssat_op_l I hZF hF hH hc 1 hs f]
  have hh := (hE f).mp hf
  exact ⟨fun ⟨_, a, ha, hb⟩ => (hh.1.2 i a x ha hi).symm.trans (hh.1.2 j a y hb hj),
    fun he => ⟨hf, x, hi, he ▸ hj⟩⟩

theorem ssat_nor_l (hZF : M.Models ZF) {ω X R E F n H r c i j f}
    (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H) (hc : M.PairMember I r c F)
    (hs : Sop_d I 2 c i j) (hf : M.mem f E) :
    Ssat_d I X R E F n r f ↔ ¬ (Ssat_d I X R E F n i f ∨ Ssat_d I X R E F n j f) := by
  have hr := (hF.2.1.2.2 r).mpr ⟨c, hc⟩
  obtain ⟨hi, hj⟩ := (hF.2.2 r c hc).refs_l I (ZF.modelsKP hZF) hs
  obtain ⟨A, hA⟩ := (hH.1.2.2 i).mp (hH.1.1.transitive r hr i hi)
  obtain ⟨B, hB⟩ := (hH.1.2.2 j).mp (hH.1.1.transitive r hr j hj)
  rw [ssat_op_l I hZF hF hH hc 2 hs f, ssat_value_l I hZF hH hA, ssat_value_l I hZF hH hB]
  constructor
  · rintro ⟨_, A', B', hA', hB', hh⟩
    have he := hH.1.2.1.2 i A' A hA' hA
    have he' := hH.1.2.1.2 j B' B hB' hB
    exact he ▸ he' ▸ hh
  · exact fun h => ⟨hf, A, B, hA, hB, h⟩

/-- 内部存在量词沿实际单坐标更新取投影，包含全部模型对象见证。 -/
theorem ssat_exists_l (hZF : M.Models ZF) {ω X R E F n H r c i j f}
    (hF : Sfm_d I ω n F) (hH : Seval_d I X R E F n H) (hc : M.PairMember I r c F)
    (hs : Sop_d I 3 c i j) (hf : M.mem f E) :
    Ssat_d I X R E F n r f ↔ ∃ x g, M.mem x X ∧ Senv_update_d I f i x g ∧ Ssat_d I X R E F n j g := by
  have hr := (hF.2.1.2.2 r).mpr ⟨c, hc⟩
  have hj := ((hF.2.2 r c hc).refs_l I (ZF.modelsKP hZF) hs).2
  obtain ⟨A, hA⟩ := (hH.1.2.2 j).mp (hH.1.1.transitive r hr j hj)
  rw [ssat_op_l I hZF hF hH hc 3 hs f]
  constructor
  · rintro ⟨_, A', hA', x, g, hx, hg, hh⟩
    have he := hH.1.2.1.2 j A' A hA' hA
    exact ⟨x, g, hx, hg, (ssat_value_l I hZF hH hA g).mpr (he ▸ hh)⟩
  · rintro ⟨x, g, hx, hg, hh⟩
    exact ⟨hf, A, hA, x, g, hx, hg, (ssat_value_l I hZF hH hA g).mp hh⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 内部公式码的实际全集

完整公式码为 (程序,根行号)。程序是 ω×(ω×(ω×ω)) 的内部子集，根编号属于 ω；
在这一幂集乘积界上按合法性分离，得到包含全部内部有限公式的实际集合。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Sformula_d (ω a n F k : M.Domain) : Prop :=
  I.Codes a F k ∧ Sfm_d I ω n F ∧ M.mem k n

def sformula_m {n} (ω a l F k : Term n) : Formula 1 n :=
  .conj (𝒞.code a F k) (.conj (sfm_m (𝒞 := 𝒞) ω l F) (.mem k l))
derive_free_closed sformula_m

theorem sformula_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω a l F k : Term n) :
    Formula.satisfies ρ (sformula_m (𝒞 := 𝒞) ω a l F k) ↔
      Sformula_d I (ω.eval ρ) (a.eval ρ) (l.eval ρ) (F.eval ρ) (k.eval ρ) := by
  simp only [sformula_m, Sformula_d, Formula.satisfies_conj_iff, I.satisfies_code_iff,
    sfm_sat_l I hE, Formula.satisfies_mem_iff]

theorem sformula_unique_l (hE : Extensional M) {ω a n F k m G j}
    (h : Sformula_d I ω a n F k) (g : Sformula_d I ω a m G j) : n = m ∧ F = G ∧ k = j := by
  obtain ⟨he, hk⟩ := I.injective h.1 g.1
  subst G
  exact ⟨h.2.1.2.1.length_eq hE g.2.1.2.1, rfl, hk⟩

def Scode_d (ω C : M.Domain) : Prop := ∀ a, M.mem a C ↔ ∃ n F k, Sformula_d I ω a n F k

def scode_m {n} (ω C : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest C.weaken) (.existsE (.existsE (.existsE
    (sformula_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)))))
derive_free_closed scode_m

theorem scode_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω C : Term n) :
    Formula.satisfies ρ (scode_m (𝒞 := 𝒞) ω C) ↔ Scode_d I (ω.eval ρ) (C.eval ρ) := by
  simp only [scode_m, Scode_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, sformula_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 合法指令全部落在同一个可数的三重自然数积中。 -/
theorem sfm_node_mem_l (hZF : M.Models ZF) {ω P Q r c} (hω : M.IsOmega ω)
    (hP : M.IsCartesianProduct I P ω ω) (hQ : M.IsCartesianProduct I Q ω P)
    (hr : M.mem r ω) (hc : Sfm_node_d I ω r c) : M.mem c Q := by
  have op {k i j} (h : Sop_d I k c i j) (hi : M.mem i ω) (hj : M.mem j ω) : M.mem c Q := by
    obtain ⟨a, o, ho, ha, hc⟩ := h
    exact (hQ c).mpr ⟨o, num_mem_l hZF.1 hω ho, a, (hP a).mpr ⟨i, hi, j, hj, ha⟩, hc⟩
  rcases hc with ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩ | ⟨i, j, hs, hi, hj⟩
  · exact op hs hi hj
  · exact op hs hi hj
  · exact op hs (hω.transitive (ZF.modelsKP hZF) r hr i hi) (hω.transitive (ZF.modelsKP hZF) r hr j hj)
  · exact op hs hi (hω.transitive (ZF.modelsKP hZF) r hr j hj)

/-- 全部内部有限公式码组成一个模型内集合，而非仅有外部标准公式的枚举。 -/
theorem scode_exists_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω) : ∃ C, Scode_d I ω C := by
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I ω ω
  obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hZF I ω P
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I ω Q
  obtain ⟨U, hU⟩ := ZF.exists_powerSet hZF D
  obtain ⟨A, hA⟩ := ZF.exists_cartesianProduct hZF I U ω
  have bound {a n F k} (ha : Sformula_d I ω a n F k) : M.mem a A := by
    obtain ⟨hc, hF, hk⟩ := ha
    have row r (hr : M.mem r n) := hω.transitive (ZF.modelsKP hZF) n hF.1 r hr
    refine (hA a).mpr ⟨F, (hU F).mpr ?_, k, row k hk, hc⟩
    intro p hp
    obtain ⟨r, c, hpc⟩ := hF.2.1.2.1.1 p hp
    have hrc : M.PairMember I r c F := ⟨p, hpc, hp⟩
    exact (hD p).mpr ⟨r, row r ((hF.2.1.2.2 r).mpr ⟨c, hrc⟩), c,
      sfm_node_mem_l I hZF hω hP hQ (row r ((hF.2.1.2.2 r).mpr ⟨c, hrc⟩)) (hF.2.2 r c hrc), hpc⟩
  let ρ : Env M 1 := ⟨fun _ => ω, fun _ => ω⟩
  let φ : UnarySchema 1 := { body := .existsE (.existsE (.existsE
    (sformula_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))) }
  have hφ a : φ.denote ρ a ↔ ∃ n F k, Sformula_d I ω a n F k := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, sformula_sat_l I hZF.1]
    rfl
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ A
  refine ⟨C, fun a => (hC a).trans ?_⟩
  rw [show Formula.satisfies (ρ.push a) φ.body ↔ _ from hφ a]
  exact ⟨And.right, fun h => ⟨h.elim fun n h => h.elim fun F h => h.elim fun k h => bound h, h⟩⟩

theorem scode_unique_l (hE : Extensional M) {ω C D} (hC : Scode_d I ω C) (hD : Scode_d I ω D) : C = D :=
  hE.eq_of_same_members C D (fun a => (hC a).trans (hD a).symm)

/-- 任意变量对的关系原子有实际公式码，作为编码语言的直接构造实例。 -/
theorem sformula_rel_l (hZF : M.Models ZF) {ω i j} (hω : M.IsOmega ω)
    (hi : M.mem i ω) (hj : M.mem j ω) : ∃ a n F k c,
    Sformula_d I ω a n F k ∧ M.PairMember I k c F ∧ Sop_d I 0 c i j := by
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hF : Sfm_d I ω e e := ⟨num_mem_l hZF.1 hω (show Num_d 0 e from he),
    Structure.IsSequenceOfLength.empty I he, fun _ _ h => h.elim fun p hp => (he p hp.2).elim⟩
  obtain ⟨c, hc⟩ := sop_exists_l I (ZF.modelsKP hZF) 0 i j
  obtain ⟨n, F, hn, hf, hd⟩ := sfm_append_l I hZF hω hF (Or.inl ⟨i, j, hc, hi, hj⟩)
  obtain ⟨a, ha⟩ := I.total F e
  exact ⟨a, n, F, e, c, ⟨ha, hf, hn.predecessor_mem⟩, (hd e c).mpr (Or.inr ⟨rfl, rfl⟩), hc⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 内部程序行上的原公式强归纳

归纳性质必须给出实际一元 schema。反例集由原分离取得，再使用模型内序数归纳；
不要求程序在外部良基，也不允许把任意宿主谓词当作可分离性质。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sfm_induction_l (hZF : M.Models ZF) {ω n F} (hF : Sfm_d I ω n F)
    {d} (φ : UnarySchema d) (ρ : Env M d)
    (hp : ∀ r, M.mem r n → (∀ i, M.mem i r → φ.denote ρ i) → φ.denote ρ r)
    {r} (hr : M.mem r n) : φ.denote ρ r := by
  apply (hF.2.1.1.mem hr).inductionWithin (fun i => φ.denote ρ i)
  · obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ.neg ρ r
    exact ⟨D, fun i => by simpa only [UnarySchema.neg, UnarySchema.denote, Formula.satisfies_neg_iff] using hD i⟩
  · intro i _ hi ih
    apply hp i ?_ ih
    rcases hi with rfl | hi
    · exact hr
    · exact hF.2.1.1.transitive r hr i hi

end YesMetaZFC.SetTheory.Internal

/-! ## 结构码与公式码上的统一内部满足关系

调用只提供模型内的结构码、公式码和赋值。解码、赋值空间与真值递归均由
已实现的原公式刻画，所选中间集合不改变结果；全部满足对还能收集成一个内部集合。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Satisfies_d (ω c a f : M.Domain) : Prop := ∃ X R E n F k,
  Smdl_d I c X R ∧ Sformula_d I ω a n F k ∧ M.IsFunctionSpace I E ω X ∧ Ssat_d I X R E F n k f

def satisfies_m {n} (ω c a f : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (smdl_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5) (.bound 4))
      (.conj (sformula_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken.weaken
        a.weaken.weaken.weaken.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
        (.conj (Formula.isFunctionSpace 𝒞 (.bound 3) ω.weaken.weaken.weaken.weaken.weaken.weaken (.bound 5))
          (ssat_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 2) .newest
            f.weaken.weaken.weaken.weaken.weaken.weaken)))))))))
@[simp] theorem satisfies_closed_l {n} (ω c a f : Term n)
    (hω : ω.freeSupport = []) (hc : c.freeSupport = []) (ha : a.freeSupport = []) (hf : f.freeSupport = []) :
    (satisfies_m (𝒞 := 𝒞) ω c a f).FreeClosed := by
  simp -implicitDefEqProofs [satisfies_m, Definitional.Formula.FreeClosed, Formula.isFunctionSpace, hω, hc, ha, hf]

theorem satisfies_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω c a f : Term n) :
    Formula.satisfies ρ (satisfies_m (𝒞 := 𝒞) ω c a f) ↔
      Satisfies_d I (ω.eval ρ) (c.eval ρ) (a.eval ρ) (f.eval ρ) := by
  simp only [satisfies_m, Satisfies_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    smdl_sat_l I, sformula_sat_l I hE, Formula.satisfies_isFunctionSpace_iff I hE, ssat_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 统一满足关系精确还原为已指定解码上的真值，不依赖任何任选的中间见证。 -/
theorem satisfies_decode_l (hE : Extensional M) {ω c a X R E n F k f}
    (hM : Smdl_d I c X R) (hF : Sformula_d I ω a n F k) (hA : M.IsFunctionSpace I E ω X) :
    Satisfies_d I ω c a f ↔ Ssat_d I X R E F n k f := by
  constructor
  · rintro ⟨Y, S, D, m, G, j, hN, hG, hD, h⟩
    obtain ⟨hx, hr⟩ := smdl_unique_l I hM hN
    obtain ⟨hn, hf, hk⟩ := sformula_unique_l I hE hF hG
    subst Y
    subst S
    subst m
    subst G
    subst j
    have hd := hE.eq_of_same_members D E (fun g => (hD g).trans (hA g).symm)
    exact hd ▸ h
  · exact fun h => ⟨X, R, E, n, F, k, hM, hF, hA, h⟩

/-- 一次构造完整赋值空间、唯一真值表及指定公式的真值集。 -/
theorem smdl_table_l (hZF : M.Models ZF) {ω c a X R n F k}
    (hM : Smdl_d I c X R) (hF : Sformula_d I ω a n F k) : ∃ E H Y,
    M.IsFunctionSpace I E ω X ∧ Seval_d I X R E F n H ∧ M.PairMember I k Y H ∧
      M.MemberSubset Y E ∧ (∀ f, Satisfies_d I ω c a f ↔ M.mem f Y) ∧
      ∀ D J, M.IsFunctionSpace I D ω X → Seval_d I X R D F n J → D = E ∧ J = H := by
  obtain ⟨E, hE, _⟩ := senv_space_l I hZF ω hM.2.1
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E F hF.2.1.2.1.1
  obtain ⟨Y, hY⟩ := (hH.1.2.2 k).mp hF.2.2
  obtain ⟨P, _, hStep⟩ := hH.2 k hF.2.2 Y hY
  refine ⟨E, H, Y, hE, hH, hY, fun f hf => ((hStep f).mp hf).1, fun f => ?_, ?_⟩
  · exact (satisfies_decode_l I hZF.1 hM hF hE).trans (ssat_value_l I hZF hH hY f)
  · intro D J hD hJ
    have he := hZF.1.eq_of_same_members D E (fun f => (hD f).trans (hE f).symm)
    subst D
    exact ⟨rfl, seval_unique_l I hZF hJ hH⟩

/-- 一个实际内部集合同时记录给定结构对全部内部有限公式及赋值的满足关系。 -/
theorem smdl_satisfaction_l (hZF : M.Models ZF) {ω c X R} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) : ∃ C E S,
    Scode_d I ω C ∧ M.IsFunctionSpace I E ω X ∧ M.IsSetRelation I S ∧
      ∀ a f, M.PairMember I a f S ↔ M.mem a C ∧ M.mem f E ∧ Satisfies_d I ω c a f := by
  obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE, _⟩ := senv_space_l I hZF ω hM.2.1
  obtain ⟨U, hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) C E
  let ρ : Env M 4 := (((⟨fun _ => c, fun _ => c⟩ : Env M 1).push ω).push C).push E
  let φ : BinarySchema 4 := {
    body := .conj (.mem (.bound 1) (.bound 3)) (.conj (.mem .newest (.bound 2))
      (satisfies_m (𝒞 := 𝒞) (.bound 4) (.bound 5) (.bound 1) .newest)) }
  have hφ a f : φ.denote ρ a f ↔ M.mem a C ∧ M.mem f E ∧ Satisfies_d I ω c a f := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, satisfies_sat_l I hZF.1]
    rfl
  obtain ⟨S, hS, hs⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ U
  refine ⟨C, E, S, hC, hE, hS.1, fun a f => (hs a f).trans ?_⟩
  rw [hφ a f]
  exact ⟨fun h => h.2.2, fun h => ⟨(hU a).mpr (Or.inl h.1), (hU f).mpr (Or.inr h.2.1), h⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 有限参数列的完整赋值

把定义域为内部自然数 n 的参数列延拓到 ω，域外统一取指定基点 u。延拓图
由原公式构造且字面唯一；随后可在任意变量位置施行已有的单坐标更新。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Senv_fill_d (ω u n s f : M.Domain) : Prop :=
  M.IsSetRelation I f ∧ ∀ i x, M.PairMember I i x f ↔ M.mem i ω ∧
    ((M.mem i n ∧ M.PairMember I i x s) ∨ (¬ M.mem i n ∧ x = u))

def senv_fill_m {d} (ω u n s f : Term d) : Formula 1 d :=
  .conj (Formula.isRelation 𝒞 f) (.forallE (.forallE (.iff
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken) (.conj (.mem (.bound 1) ω.weaken.weaken)
      (.disj (.conj (.mem (.bound 1) n.weaken.weaken) (Formula.orderedPairMem 𝒞 (.bound 1) .newest s.weaken.weaken))
        (.conj (.neg (.mem (.bound 1) n.weaken.weaken)) (Formula.extensionalEq .newest u.weaken.weaken)))))))
derive_free_closed senv_fill_m

theorem senv_fill_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω u n s f : Term d) :
    Formula.satisfies ρ (senv_fill_m (𝒞 := 𝒞) ω u n s f) ↔
      Senv_fill_d I (ω.eval ρ) (u.eval ρ) (n.eval ρ) (s.eval ρ) (f.eval ρ) := by
  simp only [senv_fill_m, Senv_fill_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_disj_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken]
  rfl

theorem senv_fill_unique_l (hE : Extensional M) {ω u n s f g}
    (hf : Senv_fill_d I ω u n s f) (hg : Senv_fill_d I ω u n s g) : f = g :=
  hf.1.eq_of_pairMember_iff hE hg.1 (fun i x => (hf.2 i x).trans (hg.2 i x).symm)

theorem Senv_fill_d.function_l {ω X u n s f} (hf : Senv_fill_d I ω u n s f)
    (hs : M.IsSetFunctionFromTo I s n X) (hu : M.mem u X) : M.IsSetFunctionFromTo I f ω X := by
  classical
  have total i (hi : M.mem i ω) : ∃ x, M.mem x X ∧ M.PairMember I i x f := by
    by_cases hn : M.mem i n
    · obtain ⟨x, hx, hix⟩ := hs.2.2 i hn
      exact ⟨x, hx, (hf.2 i x).mpr ⟨hi, Or.inl ⟨hn, hix⟩⟩⟩
    · exact ⟨u, hu, (hf.2 i u).mpr ⟨hi, Or.inr ⟨hn, rfl⟩⟩⟩
  refine ⟨⟨hf.1, ?_⟩, fun i => ⟨fun hi => (total i hi).elim fun x hx => ⟨x, hx.2⟩,
    fun ⟨x, hx⟩ => ((hf.2 i x).mp hx).1⟩, total⟩
  intro i x y hx hy
  rcases ((hf.2 i x).mp hx).2 with ⟨hn, hx⟩ | ⟨hn, rfl⟩ <;>
    rcases ((hf.2 i y).mp hy).2 with ⟨hn', hy⟩ | ⟨hn', rfl⟩
  · exact hs.1.2 i x y hx hy
  · exact (hn' hn).elim
  · exact (hn hn').elim
  · rfl

theorem senv_fill_exists_l (hZF : M.Models ZF) {ω X u n s}
    (hs : M.IsSetFunctionFromTo I s n X) (hu : M.mem u X) :
    ∃ f, Senv_fill_d I ω u n s f ∧ M.IsSetFunctionFromTo I f ω X := by
  classical
  let ρ : Env M 3 := ((⟨fun _ => s, fun _ => s⟩ : Env M 1).push n).push u
  let φ : BinarySchema 3 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 3)) (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4)))
      (.conj (.neg (.mem (.bound 1) (.bound 3))) (Formula.extensionalEq .newest (.bound 2))) }
  have hφ i x : φ.denote ρ i x ↔ (M.mem i n ∧ M.PairMember I i x s) ∨ (¬ M.mem i n ∧ x = u) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  obtain ⟨f, hf, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := X) (by
    intro i _
    by_cases hi : M.mem i n
    · obtain ⟨x, _, hx⟩ := hs.2.2 i hi
      exact ⟨x, (hφ i x).mpr (Or.inl ⟨hi, hx⟩)⟩
    · exact ⟨u, (hφ i u).mpr (Or.inr ⟨hi, rfl⟩)⟩) (by
    intro i _ x y hx hy
    rcases (hφ i x).mp hx with ⟨hi, hx⟩ | ⟨hi, rfl⟩ <;>
      rcases (hφ i y).mp hy with ⟨hi', hy⟩ | ⟨hi', rfl⟩
    · exact hs.1.2 i x y hx hy
    · exact (hi' hi).elim
    · exact (hi hi').elim
    · rfl) (by
    intro i x _ hx
    exact ((hφ i x).mp hx).elim (fun hx => hs.output_mem_of_pairMember hx.2) (fun hx => hx.2.symm ▸ hu))
  exact ⟨f, ⟨hf.1.1, fun i x => (he i x).trans (and_congr_right fun _ => hφ i x)⟩, hf⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 公式程序扩张与真值前缀

追加指令不改变旧行的真值。证明直接限制实际递归表，并用每步只读取当前
指令的性质搬运递归方程；不对外部可解码的程序另设一套求值。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sfm_prefix_subset_l {ω n F m G} (hF : Sfm_d I ω n F) (hG : Sfm_d I ω m G)
    (h : M.IsRestrictionOf I F G n) : M.MemberSubset n m := by
  intro i hi
  obtain ⟨c, hc⟩ := (hF.2.1.2.2 i).mp hi
  exact (hG.2.1.2.2 i).mpr ⟨c, ((h.2 i c).mp hc).2⟩

theorem sfm_append_prefix_l (hZF : M.Models ZF) {ω n F c G} (hF : Sfm_d I ω n F)
    (h : ∀ i a, M.PairMember I i a G ↔ M.PairMember I i a F ∨ (i = n ∧ a = c)) :
    M.IsRestrictionOf I F G n := by
  refine ⟨hF.2.1.2.1.1, fun i a => ?_⟩
  constructor
  · exact fun hi => ⟨(hF.2.1.2.2 i).mpr ⟨a, hi⟩, (h i a).mpr (Or.inl hi)⟩
  · rintro ⟨hi, ha⟩
    rcases (h i a).mp ha with ha | ⟨rfl, _⟩
    · exact ha
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) _ hi).elim

theorem seval_prefix_l (hE : Extensional M) {ω X R E n F m G H P}
    (hF : Sfm_d I ω n F) (hG : Sfm_d I ω m G) (hFG : M.IsRestrictionOf I F G n)
    (hH : Seval_d I X R E G m H) (hP : M.IsRestrictionOf I P H n) : Seval_d I X R E F n P := by
  have hnm := sfm_prefix_subset_l I hF hG hFG
  refine ⟨⟨hF.2.1.1, hP.isSetFunction hH.1.2.1, hP.isDomainOf hH.1.2.2 hnm⟩, ?_⟩
  intro i hi Y hY
  obtain ⟨Q, hQ, hStep⟩ := hH.2 i (hnm i hi) Y (((hP.2 i Y).mp hY).2)
  have hd := (hH.restriction (hnm i hi) hQ).1.2.2
  refine ⟨Q, hP.trans hQ (hF.2.1.1.transitive i hi), fun f => (hStep f).trans ?_⟩
  apply and_congr_right
  intro _
  have he : ∀ j c, M.IsDomainOf I j Q → (M.PairMember I j c G ↔ M.PairMember I j c F) := by
    intro j c hj
    have hj := hj.eq hE hd
    subst j
    exact ⟨fun hc => (hFG.2 i c).mpr ⟨hi, hc⟩, fun hc => ((hFG.2 i c).mp hc).2⟩
  exact exists_congr fun j => exists_congr fun c => and_congr_right fun hj =>
    and_congr (he j c hj) Iff.rfl

/-- 旧公式在任意合法程序扩张中的满足关系逐赋值不变。 -/
theorem ssat_prefix_l (hZF : M.Models ZF) {ω X R E n F m G k}
    (hF : Sfm_d I ω n F) (hG : Sfm_d I ω m G) (hFG : M.IsRestrictionOf I F G n)
    (hk : M.mem k n) (f : M.Domain) : Ssat_d I X R E F n k f ↔ Ssat_d I X R E G m k f := by
  obtain ⟨H, hH⟩ := seval_exists_l I hZF X R E G hG.2.1.1
  obtain ⟨P, hP⟩ := ZF.exists_restriction hZF I H n
  have hp := seval_prefix_l I hZF.1 hF hG hFG hH hP
  obtain ⟨Y, hY⟩ := (hp.1.2.2 k).mp hk
  exact (ssat_value_l I hZF hp hY f).trans
    (ssat_value_l I hZF hH (((hP.2 k Y).mp hY).2) f).symm

end YesMetaZFC.SetTheory.Internal

/-! ## 内部公式的坐标界与赋值一致性

程序只读取各条指令中出现的两个坐标。用一个内部自然数同时界住它们，得到
后续真值比较所需的有限参数支撑；坐标界和赋值一致性均由实际原公式表达。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Scoord_d (F r i j : M.Domain) : Prop := ∃ c o a,
  M.PairMember I r c F ∧ I.Codes c o a ∧ I.Codes a i j

def scoord_m {d} (F r i j : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 r.weaken.weaken.weaken (.bound 2) F.weaken.weaken.weaken)
    (.conj (𝒞.code (.bound 2) (.bound 1) .newest) (𝒞.code .newest i.weaken.weaken.weaken j.weaken.weaken.weaken)))))
derive_free_closed scoord_m

theorem scoord_sat_l {d} (ρ : Env M d) (F r i j : Term d) :
    Formula.satisfies ρ (scoord_m (𝒞 := 𝒞) F r i j) ↔ Scoord_d I (F.eval ρ) (r.eval ρ) (i.eval ρ) (j.eval ρ) := by
  simp only [scoord_m, Scoord_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff, Definitional.Term.eval_weaken]
  rfl

def Sbound_d (F b : M.Domain) : Prop := ∀ r i j, Scoord_d I F r i j → M.mem i b ∧ M.mem j b

def sbound_m {d} (F b : Term d) : Formula 1 d :=
  .forallE (.forallE (.forallE (.imp (scoord_m (𝒞 := 𝒞) F.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
    (.conj (.mem (.bound 1) b.weaken.weaken.weaken) (.mem .newest b.weaken.weaken.weaken)))))
derive_free_closed sbound_m

theorem sbound_sat_l {d} (ρ : Env M d) (F b : Term d) :
    Formula.satisfies ρ (sbound_m (𝒞 := 𝒞) F b) ↔ Sbound_d I (F.eval ρ) (b.eval ρ) := by
  simp only [sbound_m, Sbound_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    scoord_sat_l I, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  rfl

theorem Sbound_d.operands_l {F b r c k i j} (h : Sbound_d I F b) (hc : M.PairMember I r c F)
    (hs : Sop_d I k c i j) : M.mem i b ∧ M.mem j b := by
  obtain ⟨a, o, _, ha, ho⟩ := hs
  exact h r i j ⟨c, o, a, hc, ho, ha⟩

def Senv_agree_d (b f g : M.Domain) : Prop := ∀ i x, M.mem i b → (M.PairMember I i x f ↔ M.PairMember I i x g)

def senv_agree_m {d} (b f g : Term d) : Formula 1 d :=
  Formula.forallMem b (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken)
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest g.weaken.weaken)))
derive_free_closed senv_agree_m

theorem senv_agree_sat_l {d} (ρ : Env M d) (b f g : Term d) :
    Formula.satisfies ρ (senv_agree_m (𝒞 := 𝒞) b f g) ↔ Senv_agree_d I (b.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [senv_agree_m, Senv_agree_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  exact ⟨fun h i x hi => h i hi x, fun h i hi x => h i x hi⟩

theorem Senv_agree_d.symm_l {b f g} (h : Senv_agree_d I b f g) : Senv_agree_d I b g f :=
  fun i x hi => (h i x hi).symm

/-- 更新支撑外的坐标保留支撑上的整张赋值图。 -/
theorem Senv_update_d.agree_l {b f i x g} (h : Senv_update_d I f i x g) (hi : ¬ M.mem i b) :
    Senv_agree_d I b f g := by
  intro j y hj
  have hji : j ≠ i := fun he => hi (he ▸ hj)
  exact ⟨fun hy => (h.2 j y).mpr (Or.inr ⟨hji, hy⟩),
    fun hy => ((h.2 j y).mp hy).elim (fun h => (hji h.1).elim) And.right⟩

theorem Senv_agree_d.update_l {b f g i x h k} (ha : Senv_agree_d I b f g)
    (hh : Senv_update_d I f i x h) (hk : Senv_update_d I g i x k) : Senv_agree_d I b h k := by
  intro j y hj
  exact (hh.2 j y).trans ((or_congr Iff.rfl (and_congr Iff.rfl (ha j y hj))).trans (hk.2 j y).symm)

theorem senv_fill_agree_l {ω u b s f g} (hb : M.MemberSubset b ω) (hs : M.IsRestrictionOf I s f b)
    (hg : Senv_fill_d I ω u b s g) : Senv_agree_d I b f g := by
  intro i x hi
  exact ⟨fun hx => (hg.2 i x).mpr ⟨hb i hi, Or.inl ⟨hi, (hs.2 i x).mpr ⟨hi, hx⟩⟩⟩,
    fun hx => (((hg.2 i x).mp hx).2.elim (fun h => ((hs.2 i x).mp h.2).2) (fun h => (h.1 hi).elim))⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 编码理论的内部模型性

理论是公式码的内部集合；开放公式按全部内部赋值解释，即取其全称闭包。
统一模型性也是实际原公式。给定结构的全部有效公式由分离构造为模型内理论，
从而模型性接口具有实际实例，不要求地模型证明另一个 ZFC 模型存在。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Smodels_d (ω c T : M.Domain) : Prop := ∃ X R E C,
  Smdl_d I c X R ∧ M.IsFunctionSpace I E ω X ∧ Scode_d I ω C ∧ M.MemberSubset T C ∧
    ∀ a, M.mem a T → ∀ f, M.mem f E → Satisfies_d I ω c a f

def smodels_m {n} (ω c T : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (smdl_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken (.bound 3) (.bound 2))
      (.conj (Formula.isFunctionSpace 𝒞 (.bound 1) ω.weaken.weaken.weaken.weaken (.bound 3))
        (.conj (scode_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken .newest)
          (.conj (Formula.subset T.weaken.weaken.weaken.weaken .newest)
            (Formula.forallMem T.weaken.weaken.weaken.weaken (Formula.forallMem (.bound 2)
              (satisfies_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken.weaken.weaken
                c.weaken.weaken.weaken.weaken.weaken.weaken (.bound 1) .newest))))))))))

@[simp] theorem smodels_closed_l {n} (ω c T : Term n)
    (hω : ω.freeSupport = []) (hc : c.freeSupport = []) (hT : T.freeSupport = []) :
    (smodels_m (𝒞 := 𝒞) ω c T).FreeClosed := by
  simp -implicitDefEqProofs [smodels_m, Definitional.Formula.FreeClosed, Formula.isFunctionSpace, hω, hc, hT]

theorem smodels_sat_l (hE : Extensional M) {n} (ρ : Env M n) (ω c T : Term n) :
    Formula.satisfies ρ (smodels_m (𝒞 := 𝒞) ω c T) ↔ Smodels_d I (ω.eval ρ) (c.eval ρ) (T.eval ρ) := by
  simp only [smodels_m, Smodels_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    smdl_sat_l I, Formula.satisfies_isFunctionSpace_iff I hE, scode_sat_l I hE,
    Formula.satisfies_subset_iff, Formula.satisfies_forallMem_iff, satisfies_sat_l I hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

/-- 给定结构的全部内部有效公式组成实际理论，结构码确实满足这套理论。 -/
theorem smodels_theory_l (hZF : M.Models ZF) {ω c X R} (hω : M.IsOmega ω)
    (hM : Smdl_d I c X R) : ∃ T, Smodels_d I ω c T ∧ ∀ a, M.mem a T ↔
      (∃ n F k, Sformula_d I ω a n F k) ∧
        ∀ E, M.IsFunctionSpace I E ω X → ∀ f, M.mem f E → Satisfies_d I ω c a f := by
  obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE, _⟩ := senv_space_l I hZF ω hM.2.1
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push c).push E
  let φ : UnarySchema 3 := {
    body := Formula.forallMem (.bound 1)
      (satisfies_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 1) .newest) }
  have hφ a : φ.denote ρ a ↔ ∀ f, M.mem f E → Satisfies_d I ω c a f := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forallMem_iff, satisfies_sat_l I hZF.1]
    rfl
  obtain ⟨T, hT⟩ := ZF.separation_exists_d hZF φ ρ C
  have ht a : M.mem a T ↔ M.mem a C ∧ ∀ f, M.mem f E → Satisfies_d I ω c a f :=
    (hT a).trans (and_congr_right fun _ => hφ a)
  refine ⟨T, ⟨X, R, E, C, hM, hE, hC, fun a ha => ((ht a).mp ha).1,
    fun a ha => ((ht a).mp ha).2⟩, fun a => ?_⟩
  refine (ht a).trans (and_congr (hC a) ?_)
  constructor
  · intro h D hD f hf
    have he := hZF.1.eq_of_same_members D E (fun g => (hD g).trans (hE g).symm)
    exact h f (he ▸ hf)
  · exact fun h => h E hE

end YesMetaZFC.SetTheory.Internal
