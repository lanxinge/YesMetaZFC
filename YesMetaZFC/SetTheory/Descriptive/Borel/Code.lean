import YesMetaZFC.SetTheory.Descriptive.Tree
import YesMetaZFC.SetTheory.Descriptive.Borel.Boolean

/-! # 内部 Borel 码的树语法

单个码按 (T,(R,(N,F))) 打包：T 是自然数有限列上的前缀树，R 是反向子边，
N 标记一元补节点，F 给叶节点标注空间的基本前缀；其余节点取全部子值的并。
合法性要求内部良基，补节点恰有一个子节点，叶节点没有子节点。
地址字母表与空间字母表分开，故同一编码支持 Baire 与 Cantor 空间。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bpack_d (c T R N F : M.Domain) : Prop := ∃ p q,
  I.Codes c T p ∧ I.Codes p R q ∧ I.Codes q N F
def bpack_m {d} (c T R N F : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (𝒞.code c.weaken.weaken T.weaken.weaken (.bound 1)) (.conj
    (𝒞.code (.bound 1) R.weaken.weaken .newest) (𝒞.code .newest N.weaken.weaken F.weaken.weaken))))
derive_free_closed bpack_m
theorem bpack_sat_l {d} (ρ : Env M d) (c T R N F : Term d) :
    Formula.satisfies ρ (bpack_m (𝒞 := 𝒞) c T R N F) ↔
      Bpack_d I (c.eval ρ) (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) := by
  simp only [bpack_m, Bpack_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Definitional.Term.eval_weaken]; rfl

theorem bpack_exists_l (T R N F : M.Domain) : ∃ c, Bpack_d I c T R N F := by
  obtain ⟨q, hq⟩ := I.total N F
  obtain ⟨p, hp⟩ := I.total R q
  obtain ⟨c, hc⟩ := I.total T p
  exact ⟨c, p, q, hc, hp, hq⟩

theorem bpack_unique_l {c T R N F T' R' N' F'} (h : Bpack_d I c T R N F)
    (k : Bpack_d I c T' R' N' F') : T = T' ∧ R = R' ∧ N = N' ∧ F = F' := by
  obtain ⟨p, q, hc, hp, hq⟩ := h
  obtain ⟨p', q', hc', hp', hq'⟩ := k
  obtain ⟨rfl, rfl⟩ := I.injective hc hc'
  obtain ⟨rfl, rfl⟩ := I.injective hp hp'
  obtain ⟨rfl, rfl⟩ := I.injective hq hq'
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem bpack_ext_l {c d T R N F} (h : Bpack_d I c T R N F) (k : Bpack_d I d T R N F) : c = d := by
  obtain ⟨p, q, hc, hp, hq⟩ := h
  obtain ⟨p', q', hd, hp', hq'⟩ := k
  have e := I.unique hq hq'
  subst q'
  have e := I.unique hp hp'
  subst p'
  exact I.unique hc hd

structure Btree_d (ω A S T R N F : M.Domain) : Prop where
  tree : Tree_d A T
  edges : Edge_d I ω T R
  wf : Wf_rel_d T R
  root : ∃ e, (∀ x, ¬ M.mem x e) ∧ M.mem e T
  neg_sub : M.MemberSubset N T
  leaf_fn : M.IsSetFunction I F
  leaf : ∀ a s, M.PairMember I a s F → M.mem a T ∧ M.mem s S ∧ ¬ M.mem a N ∧
    ∀ b, M.mem b T → ¬ Rd_entry_d b a R
  neg : ∀ a, M.mem a N → ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧
    ∀ c, M.mem c T → Rd_entry_d c a R → c = b

def btree_m {d} (ω A S T R N F : Term d) : Formula 1 d := .conj (tree_m A T)
  (.conj (edge_m (𝒞 := 𝒞) ω T R) (.conj (wf_rel_m T R) (.conj
    (.existsE (.conj (Formula.isEmpty .newest) (.mem .newest T.weaken)))
    (.conj (Formula.subset N T) (.conj (Formula.isFunction 𝒞 F) (.conj
      (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
        (.conj (.mem (.bound 1) T.weaken.weaken) (.conj (.mem .newest S.weaken.weaken)
          (.conj (.neg (.mem (.bound 1) N.weaken.weaken))
            (Formula.forallMem T.weaken.weaken (.neg (rd_entry_m .newest (.bound 2) R.weaken.weaken.weaken)))))))))
      (Formula.forallMem N (Formula.existsMem T.weaken (.conj (rd_entry_m .newest (.bound 1) R.weaken.weaken)
        (Formula.forallMem T.weaken.weaken (.imp (rd_entry_m .newest (.bound 2) R.weaken.weaken.weaken)
          (Formula.extensionalEq .newest (.bound 1)))))))))))))
derive_free_closed btree_m
@[prove_auto_norm semantic]
theorem btree_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S T R N F : Term d) :
    Formula.satisfies ρ (btree_m (𝒞 := 𝒞) ω A S T R N F) ↔
      Btree_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) := by
  simp only [btree_m, Formula.satisfies_conj_iff, tree_sat_l, edge_sat_l I hE,
    wf_rel_sat_l hE, Formula.satisfies_exists_iff, Formula.satisfies_isEmpty_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_subset_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_neg_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    rd_entry_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest, Term.eval_bound_one_push, Term.eval_bound_zero_push]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩,
    fun h => ⟨h.tree, h.edges, h.wf, h.root, h.neg_sub, h.leaf_fn, h.leaf, h.neg⟩⟩

def Bcode_d (ω A S c : M.Domain) : Prop := ∃ T R N F,
  Bpack_d I c T R N F ∧ Btree_d I ω A S T R N F
def bcode_m {d} (ω A S c : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (bpack_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)
  (btree_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
    S.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)))))
derive_free_closed bcode_m
@[prove_auto_norm semantic]
theorem bcode_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S c : Term d) :
    Formula.satisfies ρ (bcode_m (𝒞 := 𝒞) ω A S c) ↔ Bcode_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (c.eval ρ) := by
  simp only [bcode_m, Bcode_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bpack_sat_l I, btree_sat_l I hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Descriptive
