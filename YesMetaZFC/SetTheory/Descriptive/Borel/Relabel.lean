import YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail
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

theorem bcode_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S c : Term d) :
    Formula.satisfies ρ (bcode_m (𝒞 := 𝒞) ω A S c) ↔ Bcode_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (c.eval ρ) := by
  simp only [bcode_m, Bcode_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bpack_sat_l I, btree_sat_l I hE, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Descriptive

/-! ## Borel 码的内部求值与集合解释

固定空间点后，叶值与并节点由原公式分离得到，随后调用内部良基布尔递归。
每个合法码在每个内部点上有唯一的整树求值；根真值再分离出该码表示的实际集合。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Blit_d (F x a : M.Domain) : Prop := ∃ s, M.PairMember I a s F ∧ M.MemberSubset s x
def blit_m {d} (F x a : Term d) : Formula 1 d := .existsE
  (.conj (Formula.orderedPairMem 𝒞 a.weaken .newest F.weaken) (Formula.subset .newest x.weaken))
derive_free_closed blit_m
theorem blit_sat_l {d} (ρ : Env M d) (F x a : Term d) :
    Formula.satisfies ρ (blit_m (𝒞 := 𝒞) F x a) ↔ Blit_d I (F.eval ρ) (x.eval ρ) (a.eval ρ) := by
  simp only [blit_m, Blit_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

def Buni_d (N F a : M.Domain) : Prop := ¬ M.mem a N ∧ ¬ ∃ s, M.PairMember I a s F
def buni_m {d} (N F a : Term d) : Formula 1 d := .conj (.neg (.mem a N))
  (.neg (.existsE (Formula.orderedPairMem 𝒞 a.weaken .newest F.weaken)))
derive_free_closed buni_m
theorem buni_sat_l {d} (ρ : Env M d) (N F a : Term d) :
    Formula.satisfies ρ (buni_m (𝒞 := 𝒞) N F a) ↔ Buni_d I (N.eval ρ) (F.eval ρ) (a.eval ρ) := by
  simp only [buni_m, Buni_d, Formula.satisfies_conj_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I,
    Definitional.Term.eval_weaken]; rfl

def Bsem_d (T R N F x V : M.Domain) : Prop := ∃ L U,
  (∀ a, M.mem a L ↔ M.mem a T ∧ Blit_d I F x a) ∧
  (∀ a, M.mem a U ↔ M.mem a T ∧ Buni_d I N F a) ∧ Br_eval_d T R L N U V
def bsem_m {d} (T R N F x V : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (.forallE (.iff (.mem .newest (.bound 2)) (.conj (.mem .newest T.weaken.weaken.weaken)
    (blit_m (𝒞 := 𝒞) F.weaken.weaken.weaken x.weaken.weaken.weaken .newest)))) (.conj
  (.forallE (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest T.weaken.weaken.weaken)
    (buni_m (𝒞 := 𝒞) N.weaken.weaken.weaken F.weaken.weaken.weaken .newest))))
  (br_eval_m T.weaken.weaken R.weaken.weaken (.bound 1) N.weaken.weaken .newest V.weaken.weaken))))
derive_free_closed bsem_m
theorem bsem_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R N F x V : Term d) :
    Formula.satisfies ρ (bsem_m (𝒞 := 𝒞) T R N F x V) ↔
      Bsem_d I (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) (x.eval ρ) (V.eval ρ) := by
  simp only [bsem_m, Bsem_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    blit_sat_l I, buni_sat_l I, br_eval_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem bsem_exists_unique_l (hZF : M.Models ZF) {T R : M.Domain} (hw : Wf_rel_d T R) (N F x : M.Domain) :
    ∃ V, Bsem_d I T R N F x V ∧ ∀ W, Bsem_d I T R N F x W → W = V := by
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push x
  let φ : UnarySchema 2 := { body := blit_m (𝒞 := 𝒞) (.bound 2) (.bound 1) .newest }
  let η : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push N
  let ψ : UnarySchema 2 := { body := buni_m (𝒞 := 𝒞) (.bound 1) (.bound 2) .newest }
  obtain ⟨L, hL'⟩ := ZF.separation_exists_d hZF φ ρ T
  obtain ⟨U, hU'⟩ := ZF.separation_exists_d hZF ψ η T
  have hL a : M.mem a L ↔ M.mem a T ∧ Blit_d I F x a :=
    (hL' a).trans (and_congr_right fun _ => blit_sat_l I _ _ _ _)
  have hU a : M.mem a U ↔ M.mem a T ∧ Buni_d I N F a :=
    (hU' a).trans (and_congr_right fun _ => buni_sat_l I _ _ _ _)
  obtain ⟨V, hv, hu⟩ := br_eval_exists_unique_l hZF hw L N U
  refine ⟨V, ⟨L, U, hL, hU, hv⟩, fun W ⟨L', U', hl', hu', hw'⟩ => ?_⟩
  have e := hZF.1.eq_of_same_members L' L (fun a => (hl' a).trans (hL a).symm)
  subst L'
  have e := hZF.1.eq_of_same_members U' U (fun a => (hu' a).trans (hU a).symm)
  subst U'
  exact hu W hw'

def Bvalue_d (T R N F x : M.Domain) : Prop := ∃ V e,
  Bsem_d I T R N F x V ∧ (∀ a, ¬ M.mem a e) ∧ M.mem e V
def bvalue_m {d} (T R N F x : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (bsem_m (𝒞 := 𝒞) T.weaken.weaken R.weaken.weaken N.weaken.weaken F.weaken.weaken x.weaken.weaken (.bound 1))
  (.conj (Formula.isEmpty .newest) (.mem .newest (.bound 1)))))
derive_free_closed bvalue_m
theorem bvalue_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T R N F x : Term d) :
    Formula.satisfies ρ (bvalue_m (𝒞 := 𝒞) T R N F x) ↔
      Bvalue_d I (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) (x.eval ρ) := by
  simp only [bvalue_m, Bvalue_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bsem_sat_l I hE, Formula.satisfies_isEmpty_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

def Bsat_d (ω A S c x : M.Domain) : Prop := ∃ T R N F,
  Bpack_d I c T R N F ∧ Btree_d I ω A S T R N F ∧ Bvalue_d I T R N F x
def bsat_m {d} (ω A S c x : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (bpack_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest) (.conj
  (btree_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken
    S.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)
  (bvalue_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest x.weaken.weaken.weaken.weaken))))))
derive_free_closed bsat_m

theorem bsat_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S c x : Term d) :
    Formula.satisfies ρ (bsat_m (𝒞 := 𝒞) ω A S c x) ↔
      Bsat_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (c.eval ρ) (x.eval ρ) := by
  simp only [bsat_m, Bsat_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bpack_sat_l I, btree_sat_l I hE, bvalue_sat_l I hE, Definitional.Term.eval_weaken]; rfl

/-- 已求出的整树真值精确决定该单一码在当前点的根真值。 -/
theorem bsat_root_l (hZF : M.Models ZF) {ω A S c T R N F x V e}
    (hp : Bpack_d I c T R N F) (hc : Btree_d I ω A S T R N F)
    (hv : Bsem_d I T R N F x V) (he : ∀ a, ¬ M.mem a e) : Bsat_d I ω A S c x ↔ M.mem e V := by
  obtain ⟨Z, hz, hu⟩ := bsem_exists_unique_l I hZF hc.wf N F x
  have ev := hu V hv
  constructor
  · rintro ⟨T', R', N', F', hp', _, W, e', hw, he', hm⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := bpack_unique_l I hp hp'
    have ew := (hu W hw).trans ev.symm
    have ee := hZF.1.eq_of_same_members e' e (fun a => iff_of_false (he' a) (he a))
    exact ew ▸ ee ▸ hm
  · exact fun h => ⟨T, R, N, F, hp, hc, V, e, hv, he, h⟩

def Bden_d (ω A S B c K : M.Domain) : Prop :=
  ∀ x, M.mem x K ↔ M.mem x B ∧ Bsat_d I ω A S c x
def bden_m {d} (ω A S B c K : Term d) : Formula 1 d := .forallE (.iff (.mem .newest K.weaken)
  (.conj (.mem .newest B.weaken) (bsat_m (𝒞 := 𝒞) ω.weaken A.weaken S.weaken c.weaken .newest)))
derive_free_closed bden_m
theorem bden_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S B c K : Term d) :
    Formula.satisfies ρ (bden_m (𝒞 := 𝒞) ω A S B c K) ↔
      Bden_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (B.eval ρ) (c.eval ρ) (K.eval ρ) := by
  simp only [bden_m, Bden_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, bsat_sat_l I hE, Definitional.Term.eval_weaken]; rfl

/-- 从码和空间直接分离其解释集合，输出唯一。 -/
theorem bden_exists_unique_l (hZF : M.Models ZF) (ω A S B c : M.Domain) :
    ∃ K, Bden_d I ω A S B c K ∧ ∀ L, Bden_d I ω A S B c L → L = K := by
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push S).push c
  let φ : UnarySchema 4 := { body := bsat_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨K, hK'⟩ := ZF.separation_exists_d hZF φ ρ B
  have hK : Bden_d I ω A S B c K := fun x => (hK' x).trans (and_congr_right fun _ => bsat_sat_l I hZF.1 _ _ _ _ _ _)
  exact ⟨K, hK, fun L hL => hZF.1.eq_of_same_members L K (fun x => (hL x).trans (hK x).symm)⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## Borel 码的节点方程与三条求值规则 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 节点方程：叶真值、子值并的否定、子值并。 -/
theorem bsem_node_l {T R N F x V a : M.Domain} (hv : Bsem_d I T R N F x V) (ha : M.mem a T) :
    M.mem a V ↔ Blit_d I F x a ∨
      (M.mem a N ∧ ¬ ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.mem b V) ∨
      (Buni_d I N F a ∧ ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.mem b V) := by
  obtain ⟨L, U, hL, hU, hV⟩ := hv
  refine (hV.2 a ha).trans ?_
  simp only [Br_step_d, hL a, hU a, ha, true_and]
  exact or_congr Iff.rfl (or_congr (and_congr_right fun _ =>
    ⟨fun h ⟨b, hb, hr, hv⟩ => h b hb hr hv, fun h b hb hr hv => h ⟨b, hb, hr, hv⟩⟩) Iff.rfl)

theorem bsem_leaf_l {T R N F x V a s : M.Domain} (hv : Bsem_d I T R N F x V)
    (hf : M.IsSetFunction I F) (ha : M.mem a T) (hn : ¬ M.mem a N) (hs : M.PairMember I a s F) :
    M.mem a V ↔ M.MemberSubset s x := by
  obtain ⟨L, U, hL, hU, hV⟩ := hv
  have hu : ¬ M.mem a U := fun h => ((hU a).mp h).2.2 ⟨s, hs⟩
  have hl : M.mem a L ↔ M.MemberSubset s x := (hL a).trans
    ⟨fun ⟨_, t, ht, htx⟩ => (hf.2 a t s ht hs) ▸ htx, fun h => ⟨ha, s, hs, h⟩⟩
  exact (hV.2 a ha).trans (by simp only [Br_step_d, hn, hu, false_and, or_false]; exact hl)

theorem bsem_neg_l {T R N F x V a b : M.Domain} (hv : Bsem_d I T R N F x V)
    (ha : M.mem a T) (hn : M.mem a N) (hf : ¬ ∃ s, M.PairMember I a s F)
    (hb : M.mem b T) (hr : Rd_entry_d b a R)
    (hu : ∀ c, M.mem c T → Rd_entry_d c a R → c = b) : M.mem a V ↔ ¬ M.mem b V := by
  obtain ⟨L, U, hL, hU, hV⟩ := hv
  have hl : ¬ M.mem a L := fun h => ((hL a).mp h).2.elim fun s hs => hf ⟨s, hs.1⟩
  have hnU : ¬ M.mem a U := fun h => ((hU a).mp h).2.1 hn
  refine (hV.2 a ha).trans ?_
  simp only [Br_step_d, hl, hn, hnU, false_or, true_and, false_and, or_false]
  exact ⟨fun h => h b hb hr, fun h c hc hca hv => h (hu c hc hca ▸ hv)⟩

theorem bsem_union_l {T R N F x V a : M.Domain} (hv : Bsem_d I T R N F x V)
    (ha : M.mem a T) (hn : ¬ M.mem a N) (hf : ¬ ∃ s, M.PairMember I a s F) :
    M.mem a V ↔ ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.mem b V := by
  obtain ⟨L, U, hL, hU, hV⟩ := hv
  have hl : ¬ M.mem a L := fun h => ((hL a).mp h).2.elim fun s hs => hf ⟨s, hs.1⟩
  have hu := (hU a).mpr ⟨ha, hn, hf⟩
  simpa only [Br_step_d, hl, hn, hu, false_or, false_and, true_and] using hV.2 a ha

end YesMetaZFC.SetTheory.Descriptive

/-! ## 可数码族的内部子树拼接

码族由以内部自然数为指标的部分函数图给出。每棵子树的地址加上指标作首项，
新根单独加入；节点、补标记和叶标签均由原公式分离形成实际集合。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bfam_d (ω A S H : M.Domain) : Prop := M.IsSetFunction I H ∧
  ∀ i c, M.PairMember I i c H → M.mem i ω ∧ Bcode_d I ω A S c
def bfam_m {d} (ω A S H : Term d) : Formula 1 d := .conj (Formula.isFunction 𝒞 H)
  (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken)
    (.conj (.mem (.bound 1) ω.weaken.weaken) (bcode_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken S.weaken.weaken .newest)))))
derive_free_closed bfam_m
theorem bfam_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S H : Term d) :
    Formula.satisfies ρ (bfam_m (𝒞 := 𝒞) ω A S H) ↔ Bfam_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (H.eval ρ) := by
  simp only [bfam_m, Bfam_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, bcode_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def Bsub_d (H i T R N F : M.Domain) : Prop := ∃ c, M.PairMember I i c H ∧ Bpack_d I c T R N F
def bsub_m {d} (H i T R N F : Term d) : Formula 1 d := .existsE (.conj
  (Formula.orderedPairMem 𝒞 i.weaken .newest H.weaken) (bpack_m (𝒞 := 𝒞) .newest T.weaken R.weaken N.weaken F.weaken))
derive_free_closed bsub_m
theorem bsub_sat_l {d} (ρ : Env M d) (H i T R N F : Term d) :
    Formula.satisfies ρ (bsub_m (𝒞 := 𝒞) H i T R N F) ↔
      Bsub_d I (H.eval ρ) (i.eval ρ) (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) := by
  simp only [bsub_m, Bsub_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, bpack_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem bsub_valid_l {ω A S H i T R N F} (hH : Bfam_d I ω A S H) (h : Bsub_d I H i T R N F) :
    M.mem i ω ∧ Btree_d I ω A S T R N F := by
  obtain ⟨c, hi, hp⟩ := h
  obtain ⟨hiω, T', R', N', F', hp', hc⟩ := hH.2 i c hi
  obtain ⟨rfl, rfl, rfl, rfl⟩ := bpack_unique_l I hp hp'
  exact ⟨hiω, hc⟩

theorem bsub_unique_l {H i T R N F T' R' N' F'} (hH : M.IsSetFunction I H)
    (h : Bsub_d I H i T R N F) (k : Bsub_d I H i T' R' N' F') :
    T = T' ∧ R = R' ∧ N = N' ∧ F = F' := by
  obtain ⟨c, hi, hp⟩ := h
  obtain ⟨c', hi', hp'⟩ := k
  exact bpack_unique_l I hp (hH.2 i c' c hi' hi ▸ hp')

def Bshift_d (z H t s N F : M.Domain) : Prop := ∃ i T R,
  Bsub_d I H i T R N F ∧ M.mem s T ∧ Cons_d I z i s t
def bshift_m {d} (z H t s N F : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (bsub_m (𝒞 := 𝒞) H.weaken.weaken.weaken (.bound 2) (.bound 1) .newest N.weaken.weaken.weaken F.weaken.weaken.weaken)
  (.conj (.mem s.weaken.weaken.weaken (.bound 1))
    (cons_m (𝒞 := 𝒞) z.weaken.weaken.weaken (.bound 2) s.weaken.weaken.weaken t.weaken.weaken.weaken)))))
derive_free_closed bshift_m
theorem bshift_sat_l (hE : Extensional M) {d} (ρ : Env M d) (z H t s N F : Term d) :
    Formula.satisfies ρ (bshift_m (𝒞 := 𝒞) z H t s N F) ↔
      Bshift_d I (z.eval ρ) (H.eval ρ) (t.eval ρ) (s.eval ρ) (N.eval ρ) (F.eval ρ) := by
  simp only [bshift_m, Bshift_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bsub_sat_l I, Formula.satisfies_mem_iff, cons_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem bshift_type_l (hZF : M.Models ZF) {ω A S z H t s N F} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hH : Bfam_d I ω A S H)
    (h : Bshift_d I z H t s N F) : M.mem t A ∧ t ≠ z := by
  obtain ⟨i, T, R, hc, hs, ht⟩ := h
  obtain ⟨hi, hc⟩ := bsub_valid_l I hH hc
  obtain ⟨n, hn, hs⟩ := (hA s).mp (hc.tree.1 s hs)
  obtain ⟨k, hk, _, ht'⟩ := cons_type_l I hZF hω hz hi hn hs ht
  exact ⟨(hA t).mpr ⟨k, hk, ht'⟩, cons_ne_empty_l I hz ht⟩

theorem bshift_unique_l (hZF : M.Models ZF) {ω A S z H t s N F s' N' F'} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hH : Bfam_d I ω A S H)
    (h : Bshift_d I z H t s N F) (k : Bshift_d I z H t s' N' F') : s = s' ∧ N = N' ∧ F = F' := by
  obtain ⟨i, T, R, hc, hs, ht⟩ := h
  obtain ⟨j, T', R', hc', hs', ht'⟩ := k
  obtain ⟨n, hn, hsf⟩ := (hA s).mp ((bsub_valid_l I hH hc).2.tree.1 s hs)
  obtain ⟨m, hm, hsf'⟩ := (hA s').mp ((bsub_valid_l I hH hc').2.tree.1 s' hs')
  obtain ⟨rfl, es⟩ := cons_injective_l I hZF hω hz hn hm hsf hsf' ht ht'
  have e := bsub_unique_l I hH.1 hc hc'
  exact ⟨es, e.2.2.1, e.2.2.2⟩

def Gnode_d (z H t : M.Domain) : Prop := t = z ∨ ∃ s N F, Bshift_d I z H t s N F
def Gneg_d (z H E t : M.Domain) : Prop := (t = z ∧ M.mem z E) ∨
  ∃ s N F, Bshift_d I z H t s N F ∧ M.mem s N
def Glab_d (z H t v : M.Domain) : Prop := ∃ s N F, Bshift_d I z H t s N F ∧ M.PairMember I s v F
def gnode_m {d} (z H t : Term d) : Formula 1 d := .disj (Formula.extensionalEq t z)
  (.existsE (.existsE (.existsE (bshift_m (𝒞 := 𝒞) z.weaken.weaken.weaken H.weaken.weaken.weaken
    t.weaken.weaken.weaken (.bound 2) (.bound 1) .newest))))
def gneg_m {d} (z H E t : Term d) : Formula 1 d := .disj (.conj (Formula.extensionalEq t z) (.mem z E))
  (.existsE (.existsE (.existsE (.conj (bshift_m (𝒞 := 𝒞) z.weaken.weaken.weaken H.weaken.weaken.weaken
    t.weaken.weaken.weaken (.bound 2) (.bound 1) .newest) (.mem (.bound 2) (.bound 1))))))
def glab_m {d} (z H t v : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (bshift_m (𝒞 := 𝒞) z.weaken.weaken.weaken H.weaken.weaken.weaken t.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
  (Formula.orderedPairMem 𝒞 (.bound 2) v.weaken.weaken.weaken .newest))))
derive_free_closed gnode_m
derive_free_closed gneg_m
derive_free_closed glab_m
theorem gnode_sat_l (hE : Extensional M) {d} (ρ : Env M d) (z H t : Term d) :
    Formula.satisfies ρ (gnode_m (𝒞 := 𝒞) z H t) ↔ Gnode_d I (z.eval ρ) (H.eval ρ) (t.eval ρ) := by
  simp only [gnode_m, Gnode_d, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    Formula.satisfies_exists_iff, bshift_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem gneg_sat_l (hE : Extensional M) {d} (ρ : Env M d) (z H E t : Term d) :
    Formula.satisfies ρ (gneg_m (𝒞 := 𝒞) z H E t) ↔ Gneg_d I (z.eval ρ) (H.eval ρ) (E.eval ρ) (t.eval ρ) := by
  simp only [gneg_m, Gneg_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, bshift_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem glab_sat_l (hE : Extensional M) {d} (ρ : Env M d) (z H t v : Term d) :
    Formula.satisfies ρ (glab_m (𝒞 := 𝒞) z H t v) ↔ Glab_d I (z.eval ρ) (H.eval ρ) (t.eval ρ) (v.eval ρ) := by
  simp only [glab_m, Glab_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bshift_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl

structure Bgraft_d (ω z H E T R N F : M.Domain) : Prop where
  nodes : ∀ t, M.mem t T ↔ Gnode_d I z H t
  edges : Edge_d I ω T R
  negs : ∀ t, M.mem t N ↔ Gneg_d I z H E t
  relation : M.IsSetRelation I F
  labels : ∀ t v, M.PairMember I t v F ↔ Glab_d I z H t v

/-- 拼接集合的实际存在性，尚不预先假设新树良基。 -/
theorem bgraft_exists_l (hZF : M.Models ZF) {ω A S z H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hH : Bfam_d I ω A S H) (E : M.Domain) : ∃ T R N F, Bgraft_d I ω z H E T R N F := by
  let ρ : Env M 3 := ((⟨fun _ => z, fun _ => z⟩ : Env M 1).push H).push E
  let φ : UnarySchema 3 := { body := gnode_m (𝒞 := 𝒞) (.bound 3) (.bound 2) .newest }
  let ψ : UnarySchema 3 := { body := gneg_m (𝒞 := 𝒞) (.bound 3) (.bound 2) (.bound 1) .newest }
  let θ : BinarySchema 3 := { body := glab_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 1) .newest }
  have typed t : Gnode_d I z H t → M.mem t A := fun h => h.elim
    (fun e => e.symm ▸ (hA z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩)
    (fun ⟨_, _, _, h⟩ => (bshift_type_l I hZF hω hA hz hH h).1)
  obtain ⟨T, hT'⟩ := ZF.separation_exists_d hZF φ ρ A
  have hT t : M.mem t T ↔ Gnode_d I z H t := ((hT' t).trans
    (and_congr_right fun _ => gnode_sat_l I hZF.1 _ _ _ _)).trans ⟨And.right, fun h => ⟨typed t h, h⟩⟩
  obtain ⟨N, hN'⟩ := ZF.separation_exists_d hZF ψ ρ A
  have hN t : M.mem t N ↔ Gneg_d I z H E t := ((hN' t).trans
    (and_congr_right fun _ => gneg_sat_l I hZF.1 _ _ _ _ _)).trans
      ⟨And.right, fun h => ⟨typed t (h.elim (fun h => Or.inl h.1) (fun ⟨s, N, F, h, _⟩ => Or.inr ⟨s, N, F, h⟩)), h⟩⟩
  obtain ⟨W, hW⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) A S
  obtain ⟨F, hf, hF⟩ := ZF.exists_setRelationOn_of_denote hZF I θ ρ W
  obtain ⟨R, hR⟩ := tree_edges_l I hZF ω T
  refine ⟨T, R, N, F, hT, hR, hN, hf.1, fun t v => ?_⟩
  have hh : θ.denote ρ t v ↔ Glab_d I z H t v := glab_sat_l I hZF.1 _ _ _ _ _
  refine ((hF t v).trans (and_congr_right fun _ => and_congr_right fun _ => hh)).trans ⟨fun h => h.2.2, fun h => ?_⟩
  obtain ⟨s, N, G, hs, hv⟩ := h
  obtain ⟨i, U, Q, hc, hst, hcons⟩ := hs
  have hvS := (bsub_valid_l I hH hc).2.leaf s v hv |>.2.1
  have hs : Bshift_d I z H t s N G := ⟨i, U, Q, hc, hst, hcons⟩
  exact ⟨(hW t).mpr (Or.inl (typed t (Or.inr ⟨s, N, G, hs⟩))), (hW v).mpr (Or.inr hvS), s, N, G, hs, hv⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 拼接树的前缀封闭性与子边

不同首项的子树互不相交。根的子节点恰为各旧根；非根节点的子边与旧树精确对应。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bgraft_tree_l (hZF : M.Models ZF) {ω A S z H E T R N F} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F) : Tree_d A T := by
  have hzA := (hA z).mpr ⟨z, hzω, ds_empty_fun_l I hz⟩
  constructor
  · intro t ht
    exact ((hG.nodes t).mp ht).elim (fun e => e.symm ▸ hzA)
      (fun ⟨_, _, _, h⟩ => (bshift_type_l I hZF hω hA hz hH h).1)
  · intro t ht u hu hut
    apply (hG.nodes u).mpr
    rcases (hG.nodes t).mp ht with e | ⟨s, Q, G, i, U, V, hc, hs, ht⟩
    · exact Or.inl (hZF.1.eq_of_same_members u z (fun p => iff_of_false (fun hp => hz p (e ▸ hut p hp)) (hz p)))
    · rcases cons_cases_l I hZF hω hA hz hu with e | ⟨j, r, _, hr, hu⟩
      · exact Or.inl e
      · obtain ⟨n, hn, hrf⟩ := (hA r).mp hr
        obtain ⟨e, hrs⟩ := (cons_subset_l I hZF hω hz hn hrf hu ht).mp hut
        subst j
        have hrU := (bsub_valid_l I hH hc).2.tree.2 s hs r hr hrs
        exact Or.inr ⟨r, Q, G, i, U, V, hc, hrU, hu⟩

theorem bsub_root_l (hE : Extensional M) {ω A S z H i T R N F}
    (hz : ∀ p, ¬ M.mem p z) (hH : Bfam_d I ω A S H) (hc : Bsub_d I H i T R N F) : M.mem z T := by
  obtain ⟨e, he, het⟩ := (bsub_valid_l I hH hc).2.root
  exact hE.eq_of_same_members e z (fun p => iff_of_false (he p) (hz p)) ▸ het

theorem bgraft_child_l (hZF : M.Models ZF) {ω A S z H E T R N F i U V Q G s t}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F)
    (hc : Bsub_d I H i U V Q G) (hs : M.mem s U) (ht : Cons_d I z i s t) (v : M.Domain) :
    Rd_entry_d v t R ↔ ∃ r, M.mem r U ∧ Cons_d I z i r v ∧ Rd_entry_d r s V := by
  obtain ⟨hi, hU⟩ := bsub_valid_l I hH hc
  obtain ⟨n, hn, hsf⟩ := (hA s).mp (hU.tree.1 s hs)
  have htT := (hG.nodes t).mpr (Or.inr ⟨s, Q, G, i, U, V, hc, hs, ht⟩)
  constructor
  · intro hv
    obtain ⟨_, hvT, htv⟩ := (hG.edges.2 t v).mp hv
    rcases (hG.nodes v).mp hvT with e | ⟨r, Q', G', j, U', V', hc', hr, hv⟩
    · exact (tree_step_not_empty_l I hz (e ▸ htv)).elim
    · obtain ⟨hj, hU'⟩ := bsub_valid_l I hH hc'
      obtain ⟨m, hm, hrf⟩ := (hA r).mp (hU'.tree.1 r hr)
      obtain ⟨e, hsr⟩ := (cons_step_l I hZF hω hz hi hj hn hm hsf hrf ht hv).mp htv
      subst j
      obtain ⟨rfl, rfl, rfl, rfl⟩ := bsub_unique_l I hH.1 hc hc'
      exact ⟨r, hr, hv, (hU.edges.2 s r).mpr ⟨hs, hr, hsr⟩⟩
  · rintro ⟨r, hr, hv, hsr⟩
    obtain ⟨m, hm, hrf⟩ := (hA r).mp (hU.tree.1 r hr)
    have hvT := (hG.nodes v).mpr (Or.inr ⟨r, Q, G, i, U, V, hc, hr, hv⟩)
    exact (hG.edges.2 t v).mpr ⟨htT, hvT, (cons_step_l I hZF hω hz hi hi hn hm hsf hrf ht hv).mpr
      ⟨rfl, ((hU.edges.2 s r).mp hsr).2.2⟩⟩

theorem bgraft_root_child_l (hZF : M.Models ZF) {ω A S z H E T R N F}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F) (v : M.Domain) :
    Rd_entry_d v z R ↔ ∃ i U V Q G, Bsub_d I H i U V Q G ∧ Cons_d I z i z v := by
  have hzT := (hG.nodes z).mpr (Or.inl rfl)
  constructor
  · intro hv
    obtain ⟨_, hvT, hv⟩ := (hG.edges.2 z v).mp hv
    rcases (hG.nodes v).mp hvT with e | ⟨s, Q, G, i, U, V, hc, hs, ht⟩
    · exact (tree_step_not_empty_l I hz (e ▸ hv)).elim
    · obtain ⟨hi, hU⟩ := bsub_valid_l I hH hc
      have e := (cons_root_l I hZF hω hA hz hzω hi (hU.tree.1 s hs) ht).mp hv
      exact ⟨i, U, V, Q, G, hc, e ▸ ht⟩
  · rintro ⟨i, U, V, Q, G, hc, ht⟩
    obtain ⟨hi, hU⟩ := bsub_valid_l I hH hc
    have hzU := bsub_root_l I hZF.1 hz hH hc
    have hvT := (hG.nodes v).mpr (Or.inr ⟨z, Q, G, i, U, V, hc, hzU, ht⟩)
    exact (hG.edges.2 z v).mpr ⟨hzT, hvT,
      (cons_root_l I hZF hω hA hz hzω hi (hU.tree.1 z hzU) ht).mpr rfl⟩

theorem bgraft_negs_l (hZF : M.Models ZF) {ω A S z H E T R N F t s Q G}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F)
    (h : Bshift_d I z H t s Q G) : M.mem t N ↔ M.mem s Q := by
  refine (hG.negs t).trans ⟨?_, fun hs => Or.inr ⟨s, Q, G, h, hs⟩⟩
  rintro (⟨e, _⟩ | ⟨s', Q', G', h', hs'⟩)
  · exact ((bshift_type_l I hZF hω hA hz hH h).2 e).elim
  · obtain ⟨rfl, rfl, rfl⟩ := bshift_unique_l I hZF hω hA hz hH h h'
    exact hs'

theorem bgraft_labels_l (hZF : M.Models ZF) {ω A S z H E T R N F t s Q G}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F)
    (h : Bshift_d I z H t s Q G) (v : M.Domain) : M.PairMember I t v F ↔ M.PairMember I s v G := by
  refine (hG.labels t v).trans ⟨?_, fun hs => ⟨s, Q, G, h, hs⟩⟩
  rintro ⟨s', Q', G', h', hs'⟩
  obtain ⟨rfl, rfl, rfl⟩ := bshift_unique_l I hZF hω hA hz hH h h'
  exact hs'

theorem bgraft_root_l (hZF : M.Models ZF) {ω A S z H E T R N F}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F) :
    (M.mem z N ↔ M.mem z E) ∧ ¬ ∃ v, M.PairMember I z v F := by
  constructor
  · refine (hG.negs z).trans ⟨?_, fun h => Or.inl ⟨rfl, h⟩⟩
    rintro (⟨_, h⟩ | ⟨_, _, _, h, _⟩)
    · exact h
    · exact ((bshift_type_l I hZF hω hA hz hH h).2 rfl).elim
  · rintro ⟨v, hv⟩
    obtain ⟨_, _, _, h, _⟩ := (hG.labels z v).mp hv
    exact (bshift_type_l I hZF hω hA hz hH h).2 rfl

end YesMetaZFC.SetTheory.Descriptive

/-! ## 拼接树的内部良基性与码合法性

在任意非空内部节点集中，若出现非根节点，就在对应旧树的内部截面取极小元。
因此无需把内部良基性升级成外部良基性，也无需选择一个码族的求值。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bgraft_wf_l (hZF : M.Models ZF) {ω A S z H E T R N F}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F) : Wf_rel_d T R := by
  classical
  intro Y hY hn
  by_cases h : ∃ t, M.mem t Y ∧ t ≠ z
  · obtain ⟨t, htY, htz⟩ := h
    obtain ⟨s, Q, G, i, U, V, hc, hs, ht⟩ := ((hG.nodes t).mp (hY t htY)).resolve_left htz
    let ρ : Env M 3 := ((⟨fun _ => z, fun _ => z⟩ : Env M 1).push i).push Y
    let φ : UnarySchema 3 := {
      body := Formula.existsMem (.bound 1) (cons_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 1) .newest) }
    obtain ⟨D, hD'⟩ := ZF.separation_exists_d hZF φ ρ U
    have hD a : M.mem a D ↔ M.mem a U ∧ ∃ b, M.mem b Y ∧ Cons_d I z i a b := by
      simp only [φ, Formula.satisfies_existsMem_iff, cons_sat_l I hZF.1] at hD'
      exact hD' a
    obtain ⟨a, ha, hmin⟩ := (bsub_valid_l I hH hc).2.wf D (fun a ha => ((hD a).mp ha).1)
      ⟨s, (hD s).mpr ⟨hs, t, htY, ht⟩⟩
    obtain ⟨haU, b, hbY, hb⟩ := (hD a).mp ha
    refine ⟨b, hbY, fun v hv hr => ?_⟩
    obtain ⟨r, hrU, hrv, hra⟩ := (bgraft_child_l I hZF hω hA hz hH hG hc haU hb v).mp hr
    exact hmin r ((hD r).mpr ⟨hrU, v, hv, hrv⟩) hra
  · obtain ⟨a, ha⟩ := hn
    refine ⟨a, ha, fun b hb hr => ?_⟩
    have eb : b = z := Classical.byContradiction (fun e => h ⟨b, hb, e⟩)
    exact tree_step_not_empty_l I hz (eb ▸ ((hG.edges.2 a b).mp hr).2.2)

/-- 根取补时只需码族非空且指标唯一；并根允许空族和任意内部可数族。 -/
theorem bgraft_valid_l (hZF : M.Models ZF) {ω A S z H E T R N F}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F)
    (hE : M.mem z E → ∃ i c, M.PairMember I i c H ∧ ∀ j d, M.PairMember I j d H → j = i) :
    Btree_d I ω A S T R N F := by
  have tree := bgraft_tree_l I hZF hω hA hz hzω hH hG
  have root := (hG.nodes z).mpr (Or.inl rfl)
  have funF : M.IsSetFunction I F := by
    refine ⟨hG.relation, fun t v w hv hw => ?_⟩
    obtain ⟨s, Q, G, hs, hv⟩ := (hG.labels t v).mp hv
    have hw := (bgraft_labels_l I hZF hω hA hz hH hG hs w).mp hw
    obtain ⟨i, U, V, hc, _, _⟩ := hs
    exact (bsub_valid_l I hH hc).2.leaf_fn.2 s v w hv hw
  refine ⟨tree, hG.edges, bgraft_wf_l I hZF hω hA hz hH hG, ⟨z, hz, root⟩, ?_, funF, ?_, ?_⟩
  · intro t ht
    exact (hG.nodes t).mpr (((hG.negs t).mp ht).elim (fun h => Or.inl h.1)
      (fun ⟨s, Q, G, h, _⟩ => Or.inr ⟨s, Q, G, h⟩))
  · intro t v hv
    obtain ⟨s, Q, G, hs, hv⟩ := (hG.labels t v).mp hv
    have htT := (hG.nodes t).mpr (Or.inr ⟨s, Q, G, hs⟩)
    have hneg := bgraft_negs_l I hZF hω hA hz hH hG hs
    obtain ⟨i, U, V, hc, hs, ht⟩ := hs
    obtain ⟨_, hvS, hn, he⟩ := (bsub_valid_l I hH hc).2.leaf s v hv
    refine ⟨htT, hvS, fun h => hn (hneg.mp h), fun b _ hb => ?_⟩
    obtain ⟨r, hr, _, hrs⟩ := (bgraft_child_l I hZF hω hA hz hH hG hc hs ht b).mp hb
    exact he r hr hrs
  · intro t htN
    rcases (hG.negs t).mp htN with ⟨e, he⟩ | ⟨s, Q, G, hs, hsQ⟩
    · subst t
      obtain ⟨i, c, hic, hi⟩ := hE he
      obtain ⟨hiω, U, V, Q, G, hp, _⟩ := hH.2 i c hic
      have hc : Bsub_d I H i U V Q G := ⟨c, hic, hp⟩
      obtain ⟨_, b, _, _, _, hb⟩ := cons_exists_l I hZF hω hz hiω hzω (ds_empty_fun_l I hz)
      have hbR := (bgraft_root_child_l I hZF hω hA hz hzω hH hG b).mpr ⟨i, U, V, Q, G, hc, hb⟩
      refine ⟨b, ((hG.edges.2 z b).mp hbR).2.1, hbR, fun v _ hv => ?_⟩
      obtain ⟨j, U', V', Q', G', ⟨d, hj, _⟩, hv⟩ :=
        (bgraft_root_child_l I hZF hω hA hz hzω hH hG v).mp hv
      exact cons_unique_l I hZF.1 (hi j d hj ▸ hv) hb
    · obtain ⟨i, U, V, hc, hsU, ht⟩ := hs
      obtain ⟨hi, hU⟩ := bsub_valid_l I hH hc
      obtain ⟨r, hr, hrs, huniq⟩ := hU.neg s hsQ
      obtain ⟨n, hn, hrf⟩ := (hA r).mp (hU.tree.1 r hr)
      obtain ⟨_, b, _, _, _, hb⟩ := cons_exists_l I hZF hω hz hi hn hrf
      have hbR := (bgraft_child_l I hZF hω hA hz hH hG hc hsU ht b).mpr ⟨r, hr, hb, hrs⟩
      refine ⟨b, ((hG.edges.2 t b).mp hbR).2.1, hbR, fun v _ hv => ?_⟩
      obtain ⟨r', hr', hv, hr's⟩ := (bgraft_child_l I hZF hω hA hz hH hG hc hsU ht v).mp hv
      exact cons_unique_l I hZF.1 (huniq r' hr' hr's ▸ hv) hb

end YesMetaZFC.SetTheory.Descriptive

/-! ## 子树拼接保持求值

比较新旧两棵树的实际求值集。比较性质是原公式，对旧树使用内部良基归纳，
因而即使外部看来有非标准长路径，也不影响本层结论。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bgraft_eval_l (hZF : M.Models ZF) {ω A S z H E T R N F i U V Q G x D W}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F)
    (hc : Bsub_d I H i U V Q G) (hD : Bsem_d I T R N F x D) (hW : Bsem_d I U V Q G x W) :
    ∀ s, M.mem s U → ∀ t, Cons_d I z i s t → (M.mem t D ↔ M.mem s W) := by
  obtain ⟨hi, hU⟩ := bsub_valid_l I hH hc
  let ρ : Env M 4 := (((⟨fun _ => z, fun _ => z⟩ : Env M 1).push i).push D).push W
  let φ : UnarySchema 4 := {
    body := .forallE (.imp (cons_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 1) .newest)
      (.iff (.mem .newest (.bound 3)) (.mem (.bound 1) (.bound 2)))) }
  have hp s : φ.denote ρ s ↔ ∀ t, Cons_d I z i s t → (M.mem t D ↔ M.mem s W) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      cons_sat_l I hZF.1, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff]; rfl
  have hall := wf_rel_ind_l hZF hU.wf φ ρ (fun s hs ih => (hp s).mpr (by
    intro t ht
    have shift : Bshift_d I z H t s Q G := ⟨i, U, V, hc, hs, ht⟩
    have htT := (hG.nodes t).mpr (Or.inr ⟨s, Q, G, shift⟩)
    have neg := bgraft_negs_l I hZF hω hA hz hH hG shift
    have lab := bgraft_labels_l I hZF hω hA hz hH hG shift
    have lit : Blit_d I F x t ↔ Blit_d I G x s := exists_congr fun v => and_congr_left fun _ => lab v
    have uni : Buni_d I N F t ↔ Buni_d I Q G s :=
      and_congr (not_congr neg) (not_congr (exists_congr lab))
    have child : (∃ b, M.mem b T ∧ Rd_entry_d b t R ∧ M.mem b D) ↔
        ∃ r, M.mem r U ∧ Rd_entry_d r s V ∧ M.mem r W := by
      constructor
      · rintro ⟨b, _, hb, hbD⟩
        obtain ⟨r, hr, hrb, hrs⟩ := (bgraft_child_l I hZF hω hA hz hH hG hc hs ht b).mp hb
        exact ⟨r, hr, hrs, ((hp r).mp (ih r hr hrs) b hrb).mp hbD⟩
      · rintro ⟨r, hr, hrs, hrW⟩
        obtain ⟨n, hn, hrf⟩ := (hA r).mp (hU.tree.1 r hr)
        obtain ⟨_, b, _, _, _, hb⟩ := cons_exists_l I hZF hω hz hi hn hrf
        have hbR := (bgraft_child_l I hZF hω hA hz hH hG hc hs ht b).mpr ⟨r, hr, hb, hrs⟩
        exact ⟨b, ((hG.edges.2 t b).mp hbR).2.1, hbR, ((hp r).mp (ih r hr hrs) b hb).mpr hrW⟩
    exact (bsem_node_l I hD htT).trans ((or_congr lit
      (or_congr (and_congr neg (not_congr child)) (and_congr uni child))).trans (bsem_node_l I hW hs).symm)))
  exact fun s hs => (hp s).mp (hall s hs)

theorem bgraft_value_l (hZF : M.Models ZF) {ω A S z H E T R N F x D}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hH : Bfam_d I ω A S H) (hG : Bgraft_d I ω z H E T R N F) (hD : Bsem_d I T R N F x D) :
    M.mem z D ↔
      (M.mem z E ∧ ¬ ∃ i c, M.PairMember I i c H ∧ Bsat_d I ω A S c x) ∨
      (¬ M.mem z E ∧ ∃ i c, M.PairMember I i c H ∧ Bsat_d I ω A S c x) := by
  have child : (∃ b, M.mem b T ∧ Rd_entry_d b z R ∧ M.mem b D) ↔
      ∃ i c, M.PairMember I i c H ∧ Bsat_d I ω A S c x := by
    constructor
    · rintro ⟨b, _, hbR, hbD⟩
      obtain ⟨i, U, V, Q, G, hc, hb⟩ := (bgraft_root_child_l I hZF hω hA hz hzω hH hG b).mp hbR
      obtain ⟨_, hU⟩ := bsub_valid_l I hH hc
      obtain ⟨W, hW, _⟩ := bsem_exists_unique_l I hZF hU.wf Q G x
      have hzW := (bgraft_eval_l I hZF hω hA hz hH hG hc hD hW z (bsub_root_l I hZF.1 hz hH hc) b hb).mp hbD
      obtain ⟨c, hic, hp⟩ := hc
      exact ⟨i, c, hic, (bsat_root_l I hZF hp hU hW hz).mpr hzW⟩
    · rintro ⟨i, c, hic, hx⟩
      obtain ⟨hi, U, V, Q, G, hp, hU⟩ := hH.2 i c hic
      have hc : Bsub_d I H i U V Q G := ⟨c, hic, hp⟩
      obtain ⟨W, hW, _⟩ := bsem_exists_unique_l I hZF hU.wf Q G x
      obtain ⟨_, b, _, _, _, hb⟩ := cons_exists_l I hZF hω hz hi hzω (ds_empty_fun_l I hz)
      have hbR := (bgraft_root_child_l I hZF hω hA hz hzω hH hG b).mpr ⟨i, U, V, Q, G, hc, hb⟩
      have hzW := (bsat_root_l I hZF hp hU hW hz).mp hx
      exact ⟨b, ((hG.edges.2 z b).mp hbR).2.1, hbR,
        (bgraft_eval_l I hZF hω hA hz hH hG hc hD hW z (bsub_root_l I hZF.1 hz hH hc) b hb).mpr hzW⟩
  obtain ⟨neg, lab⟩ := bgraft_root_l I hZF hω hA hz hH hG
  have lit : ¬ Blit_d I F x z := fun ⟨s, hs, _⟩ => lab ⟨s, hs⟩
  have uni : Buni_d I N F z ↔ ¬ M.mem z E := ⟨fun h => fun he => h.1 (neg.mpr he),
    fun h => ⟨fun hn => h (neg.mp hn), lab⟩⟩
  have h := (bsem_node_l I hD ((hG.nodes z).mpr (Or.inl rfl))).trans
    (or_congr Iff.rfl (or_congr (and_congr neg (not_congr child)) (and_congr uni child)))
  simpa only [lit, false_or] using h

end YesMetaZFC.SetTheory.Descriptive

/-! ## Borel 码的补与内部可数并

拼接关系有实际原公式且输出唯一，可直接用于替代、函数图构造与相对化。
补通过一棵子树及一个补根构造；可数并接受任意内部自然数部分指标族，允许空族。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def bgraft_m {d} (ω z H E T R N F : Term d) : Formula 1 d := .conj
  (.forallE (.iff (.mem .newest T.weaken) (gnode_m (𝒞 := 𝒞) z.weaken H.weaken .newest))) (.conj
  (edge_m (𝒞 := 𝒞) ω T R) (.conj
  (.forallE (.iff (.mem .newest N.weaken) (gneg_m (𝒞 := 𝒞) z.weaken H.weaken E.weaken .newest))) (.conj
  (Formula.isRelation 𝒞 F) (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)
    (glab_m (𝒞 := 𝒞) z.weaken.weaken H.weaken.weaken (.bound 1) .newest)))))))
derive_free_closed bgraft_m
theorem bgraft_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω z H E T R N F : Term d) :
    Formula.satisfies ρ (bgraft_m (𝒞 := 𝒞) ω z H E T R N F) ↔
      Bgraft_d I (ω.eval ρ) (z.eval ρ) (H.eval ρ) (E.eval ρ) (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) := by
  simp only [bgraft_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, gnode_sat_l I hE, edge_sat_l I hE,
    gneg_sat_l I hE, Formula.satisfies_isRelation_iff I, Formula.satisfies_orderedPairMem_iff I,
    glab_sat_l I hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
    Term.eval_bound_one_push, Term.eval_bound_zero_push]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩,
    fun h => ⟨h.nodes, h.edges, h.negs, h.relation, h.labels⟩⟩

def Bjoin_d (ω z H E c : M.Domain) : Prop := ∃ T R N F,
  Bgraft_d I ω z H E T R N F ∧ Bpack_d I c T R N F
def bjoin_m {d} (ω z H E c : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (bgraft_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken z.weaken.weaken.weaken.weaken
    H.weaken.weaken.weaken.weaken E.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)
  (bpack_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)))))
derive_free_closed bjoin_m

theorem bjoin_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω z H E c : Term d) :
    Formula.satisfies ρ (bjoin_m (𝒞 := 𝒞) ω z H E c) ↔
      Bjoin_d I (ω.eval ρ) (z.eval ρ) (H.eval ρ) (E.eval ρ) (c.eval ρ) := by
  simp only [bjoin_m, Bjoin_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bgraft_sat_l I hE, bpack_sat_l I, Definitional.Term.eval_weaken]; rfl

theorem bjoin_unique_l (hE : Extensional M) {ω z H E c d}
    (h : Bjoin_d I ω z H E c) (k : Bjoin_d I ω z H E d) : c = d := by
  obtain ⟨T, R, N, F, h, hp⟩ := h
  obtain ⟨U, Q, L, G, k, kp⟩ := k
  have e := hE.eq_of_same_members T U (fun t => (h.nodes t).trans (k.nodes t).symm)
  subst U
  have e := hE.eq_of_same_members N L (fun t => (h.negs t).trans (k.negs t).symm)
  subst L
  have e := h.relation.eq_of_pairMember_iff hE k.relation (fun t v => (h.labels t v).trans (k.labels t v).symm)
  subst G
  have e := tree_edges_unique_l I hE h.edges k.edges
  subst Q
  exact bpack_ext_l I hp kp

theorem bjoin_exists_l (hZF : M.Models ZF) {ω A S z H E}
    (hω : M.IsOmega ω) (hA : Fseq_space_d I ω ω A) (hz : ∀ p, ¬ M.mem p z) (hzω : M.mem z ω)
    (hH : Bfam_d I ω A S H)
    (hE : M.mem z E → ∃ i c, M.PairMember I i c H ∧ ∀ j d, M.PairMember I j d H → j = i) :
    ∃ c, Bjoin_d I ω z H E c ∧ Bcode_d I ω A S c ∧ ∀ x,
      Bsat_d I ω A S c x ↔
        (M.mem z E ∧ ¬ ∃ i d, M.PairMember I i d H ∧ Bsat_d I ω A S d x) ∨
        (¬ M.mem z E ∧ ∃ i d, M.PairMember I i d H ∧ Bsat_d I ω A S d x) := by
  obtain ⟨T, R, N, F, hG⟩ := bgraft_exists_l I hZF hω hA hz hzω hH E
  have hc := bgraft_valid_l I hZF hω hA hz hzω hH hG hE
  obtain ⟨c, hp⟩ := bpack_exists_l I T R N F
  refine ⟨c, ⟨T, R, N, F, hG, hp⟩, ⟨T, R, N, F, hp, hc⟩, fun x => ?_⟩
  obtain ⟨D, hD, _⟩ := bsem_exists_unique_l I hZF hc.wf N F x
  exact (bsat_root_l I hZF hp hc hD hz).trans (bgraft_value_l I hZF hω hA hz hzω hH hG hD)

/-- 内部部分可数码族的并；码族为空时得到空集码。 -/
theorem bcode_union_l (hZF : M.Models ZF) {ω A S H} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hH : Bfam_d I ω A S H) :
    ∃ c, Bcode_d I ω A S c ∧ ∀ x,
      Bsat_d I ω A S c x ↔ ∃ i d, M.PairMember I i d H ∧ Bsat_d I ω A S d x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨c, _, hc, hv⟩ := bjoin_exists_l I hZF hω hA hz hzω hH (E := z) (fun h => (hz z h).elim)
  exact ⟨c, hc, fun x => by simpa only [hz z, false_and, not_false_eq_true, true_and, false_or] using hv x⟩

theorem bcode_empty_l (hZF : M.Models ZF) {ω A S} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) : ∃ c, Bcode_d I ω A S c ∧ ∀ x, ¬ Bsat_d I ω A S c x := by
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have hf : Bfam_d I ω A S z := ⟨(ds_empty_fun_l I (X := ω) hz).1,
    fun _ _ ⟨p, _, hp⟩ => (hz p hp).elim⟩
  obtain ⟨c, hc, hv⟩ := bcode_union_l I hZF hω hA hf
  exact ⟨c, hc, fun x hx => ((hv x).mp hx).elim fun _ h => h.elim fun _ h =>
    h.1.elim fun p hp => hz p hp.2⟩

/-- 一元补码；集合解释时自动成为所选空间中的相对补。 -/
theorem bcode_compl_l (hZF : M.Models ZF) {ω A S c} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Bcode_d I ω A S c) :
    ∃ d, Bcode_d I ω A S d ∧ ∀ x, Bsat_d I ω A S d x ↔ ¬ Bsat_d I ω A S c x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨J, hJ⟩ := KP.exists_singleton (ZF.modelsKP hZF) z
  obtain ⟨C, hC⟩ := KP.exists_singleton (ZF.modelsKP hZF) c
  obtain ⟨H, hH, he⟩ := ZF.exists_constantFunction hZF I (source := J) ((hC c).mpr rfl)
  have hH' : Bfam_d I ω A S H := ⟨hH.1, fun i d hd => by
    obtain ⟨hi, ed⟩ := (he i d).mp hd
    exact ⟨(hJ i).mp hi ▸ hzω, ed.symm ▸ hc⟩⟩
  have hsingle : M.mem z J → ∃ i d, M.PairMember I i d H ∧ ∀ j q, M.PairMember I j q H → j = i :=
    fun _ => ⟨z, c, (he z c).mpr ⟨(hJ z).mpr rfl, rfl⟩, fun j q h => (hJ j).mp ((he j q).mp h).1⟩
  obtain ⟨d, _, hd, hv⟩ := bjoin_exists_l I hZF hω hA hz hzω hH' hsingle
  refine ⟨d, hd, fun x => ?_⟩
  have ex : (∃ i q, M.PairMember I i q H ∧ Bsat_d I ω A S q x) ↔ Bsat_d I ω A S c x :=
    ⟨fun ⟨i, q, hiq, hx⟩ => ((he i q).mp hiq).2 ▸ hx,
      fun hx => ⟨z, c, (he z c).mpr ⟨(hJ z).mpr rfl, rfl⟩, hx⟩⟩
  simpa only [ex, (hJ z).mpr rfl, true_and, not_true, false_and, or_false] using hv x

end YesMetaZFC.SetTheory.Descriptive

/-! ## 可逐项调用的唯一补码与内部部分指标域 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bneg_d (ω c d : M.Domain) : Prop := ∃ z E H p,
  (∀ x, ¬ M.mem x z) ∧ (∀ x, M.mem x E ↔ x = z) ∧ I.Codes p z c ∧
  (∀ x, M.mem x H ↔ x = p) ∧ Bjoin_d I ω z H E d
def bneg_m {d} (ω c e : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (Formula.isEmpty (.bound 3)) (.conj (Formula.isSingleton (.bound 2) (.bound 3)) (.conj
    (𝒞.code .newest (.bound 3) c.weaken.weaken.weaken.weaken) (.conj
    (Formula.isSingleton (.bound 1) .newest)
    (bjoin_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) (.bound 2) e.weaken.weaken.weaken.weaken))))))))
derive_free_closed bneg_m
theorem bneg_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω c e : Term d) :
    Formula.satisfies ρ (bneg_m (𝒞 := 𝒞) ω c e) ↔ Bneg_d I (ω.eval ρ) (c.eval ρ) (e.eval ρ) := by
  simp only [bneg_m, Bneg_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_isSingleton_iff hE, I.satisfies_code_iff,
    bjoin_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem bneg_unique_l (hE : Extensional M) {ω c d e} (h : Bneg_d I ω c d) (k : Bneg_d I ω c e) : d = e := by
  obtain ⟨z, E, H, p, hz, he, hp, hh, hd⟩ := h
  obtain ⟨z', E', H', p', hz', he', hp', hh', hk⟩ := k
  have e := hE.eq_of_same_members z' z (fun x => iff_of_false (hz' x) (hz x))
  subst z'
  have e := I.unique hp' hp
  subst p'
  have e := hE.eq_of_same_members E' E (fun x => (he' x).trans (he x).symm)
  subst E'
  have e := hE.eq_of_same_members H' H (fun x => (hh' x).trans (hh x).symm)
  subst H'
  exact bjoin_unique_l I hE hd hk

theorem bneg_exists_l (hZF : M.Models ZF) {ω A S c} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Bcode_d I ω A S c) :
    ∃ d, Bneg_d I ω c d ∧ Bcode_d I ω A S d ∧ ∀ x, Bsat_d I ω A S d x ↔ ¬ Bsat_d I ω A S c x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨E, he⟩ := KP.exists_singleton (ZF.modelsKP hZF) z
  obtain ⟨p, hp⟩ := I.total z c
  obtain ⟨H, hh⟩ := KP.exists_singleton (ZF.modelsKP hZF) p
  have pair i d : M.PairMember I i d H ↔ i = z ∧ d = c :=
    ⟨fun ⟨q, hq, hqH⟩ => I.injective ((hh q).mp hqH ▸ hq) hp,
      fun ⟨rfl, rfl⟩ => ⟨p, hp, (hh p).mpr rfl⟩⟩
  have fam : Bfam_d I ω A S H := ⟨⟨fun q hq => ⟨z, c, ((hh q).mp hq).symm ▸ hp⟩,
    fun i d e hd he => ((pair i d).mp hd).2.trans ((pair i e).mp he).2.symm⟩,
    fun i d hd => ⟨((pair i d).mp hd).1.symm ▸ hzω, ((pair i d).mp hd).2.symm ▸ hc⟩⟩
  obtain ⟨d, hd, hc', hv⟩ := bjoin_exists_l I hZF hω hA hz hzω fam
    (E := E) (fun _ => ⟨z, c, (pair z c).mpr ⟨rfl, rfl⟩, fun j d h => ((pair j d).mp h).1⟩)
  refine ⟨d, ⟨z, E, H, p, hz, he, hp, hh, hd⟩, hc', fun x => ?_⟩
  have ex : (∃ i d, M.PairMember I i d H ∧ Bsat_d I ω A S d x) ↔ Bsat_d I ω A S c x :=
    ⟨fun ⟨i, d, hd, hv⟩ => ((pair i d).mp hd).2 ▸ hv, fun h => ⟨z, c, (pair z c).mpr ⟨rfl, rfl⟩, h⟩⟩
  simpa only [ex, (he z).mpr rfl, true_and, not_true, false_and, or_false] using hv x

theorem family_domain_l (hZF : M.Models ZF) {ω H} (hH : ∀ i c, M.PairMember I i c H → M.mem i ω) :
    ∃ D, M.MemberSubset D ω ∧ M.IsDomainOf I D H := by
  let ρ : Env M 1 := ⟨fun _ => H, fun _ => H⟩
  let φ : UnarySchema 1 := { body := .existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2)) }
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ ω
  have hp i : φ.denote ρ i ↔ ∃ c, M.PairMember I i c H := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  exact ⟨D, fun i hi => ((hD i).mp hi).1, fun i => ((hD i).trans (and_congr_right fun _ => hp i)).trans
    ⟨And.right, fun ⟨c, hc⟩ => ⟨hH i c hc, c, hc⟩⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## Borel 码的二元布尔运算 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bcode_union_two_l (hZF : M.Models ZF) {ω A S c d} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Bcode_d I ω A S c) (hd : Bcode_d I ω A S d) :
    ∃ e, Bcode_d I ω A S e ∧ ∀ x, Bsat_d I ω A S e x ↔ Bsat_d I ω A S c x ∨ Bsat_d I ω A S d x := by
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  obtain ⟨o, ho, hoω⟩ := hω.1.2 z hzω
  have hzo : z ≠ o := fun e => hz z (e.symm ▸ ho.predecessor_mem)
  obtain ⟨p, hp⟩ := I.total z c
  obtain ⟨q, hq⟩ := I.total o d
  obtain ⟨H, hH⟩ := KP.exists_pair (ZF.modelsKP hZF) p q
  have pair i a : M.PairMember I i a H ↔ (i = z ∧ a = c) ∨ (i = o ∧ a = d) := by
    constructor
    · rintro ⟨r, hr, hrH⟩
      exact ((hH r).mp hrH).elim (fun e => Or.inl (I.injective (e ▸ hr) hp))
        (fun e => Or.inr (I.injective (e ▸ hr) hq))
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨p, hp, (hH p).mpr (Or.inl rfl)⟩
      · exact ⟨q, hq, (hH q).mpr (Or.inr rfl)⟩
  have family : Bfam_d I ω A S H := by
    refine ⟨⟨fun r hr => ((hH r).mp hr).elim (fun e => ⟨z, c, e.symm ▸ hp⟩) (fun e => ⟨o, d, e.symm ▸ hq⟩), ?_⟩, ?_⟩
    · intro i a b ha hb
      rcases (pair i a).mp ha with ha | ha <;> rcases (pair i b).mp hb with hb | hb
      · exact ha.2.trans hb.2.symm
      · exact (hzo (ha.1.symm.trans hb.1)).elim
      · exact (hzo (hb.1.symm.trans ha.1)).elim
      · exact ha.2.trans hb.2.symm
    · intro i a ha
      exact ((pair i a).mp ha).elim (fun h => ⟨h.1.symm ▸ hzω, h.2.symm ▸ hc⟩)
        (fun h => ⟨h.1.symm ▸ hoω, h.2.symm ▸ hd⟩)
  obtain ⟨e, he, hv⟩ := bcode_union_l I hZF hω hA family
  refine ⟨e, he, fun x => (hv x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨i, a, ha, hx⟩
    exact ((pair i a).mp ha).elim (fun h => Or.inl (h.2 ▸ hx)) (fun h => Or.inr (h.2 ▸ hx))
  · exact fun h => h.elim (fun h => ⟨z, c, (pair z c).mpr (Or.inl ⟨rfl, rfl⟩), h⟩)
      (fun h => ⟨o, d, (pair o d).mpr (Or.inr ⟨rfl, rfl⟩), h⟩)

theorem bcode_inter_l (hZF : M.Models ZF) {ω A S c d} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hc : Bcode_d I ω A S c) (hd : Bcode_d I ω A S d) :
    ∃ e, Bcode_d I ω A S e ∧ ∀ x, Bsat_d I ω A S e x ↔ Bsat_d I ω A S c x ∧ Bsat_d I ω A S d x := by
  classical
  obtain ⟨c', hc', hcv⟩ := bcode_compl_l I hZF hω hA hc
  obtain ⟨d', hd', hdv⟩ := bcode_compl_l I hZF hω hA hd
  obtain ⟨u, hu, huv⟩ := bcode_union_two_l I hZF hω hA hc' hd'
  obtain ⟨e, he, hev⟩ := bcode_compl_l I hZF hω hA hu
  exact ⟨e, he, fun x => by simp only [hev x, huv x, hcv x, hdv x, not_or, Classical.not_not]⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## Borel 码的内部叶标签映射

沿实际标签函数图复合旧叶函数，保留原来的良基运算树。求值对应直接复用
同一个真值集；本接口用于下面的实数对角嵌入。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bcode_relabel_l (hZF : M.Models ZF) {ω A S Q c H}
    (hH : M.IsSetFunctionFromTo I H S Q) (hc : Bcode_d I ω A S c) :
    ∃ d, Bcode_d I ω A Q d ∧ ∀ x y,
      (∀ s t, M.mem s S → M.PairMember I s t H → (M.MemberSubset t y ↔ M.MemberSubset s x)) →
      (Bsat_d I ω A Q d y ↔ Bsat_d I ω A S c x) := by
  obtain ⟨T, R, N, F, hp, hc⟩ := hc
  obtain ⟨W, hW⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) T Q
  let ρ : Env M 2 := (⟨fun _ => F, fun _ => F⟩ : Env M 1).push H
  let φ : BinarySchema 2 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 4))
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3))) }
  have hφ a t : φ.denote ρ a t ↔ ∃ s, M.PairMember I a s F ∧ M.PairMember I s t H := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I]; rfl
  obtain ⟨G, hG, he⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  have pair a t : M.PairMember I a t G ↔ ∃ s, M.PairMember I a s F ∧ M.PairMember I s t H := by
    refine ((he a t).trans (and_congr_right fun _ => and_congr_right fun _ => hφ a t)).trans
      ⟨fun h => h.2.2, fun ⟨s, hs, ht⟩ => ?_⟩
    exact ⟨(hW a).mpr (Or.inl (hc.leaf a s hs).1), (hW t).mpr (Or.inr (hH.output_mem_of_pairMember ht)), s, hs, ht⟩
  have fn : M.IsSetFunction I G := by
    refine ⟨hG.1, fun a t u ht hu => ?_⟩
    obtain ⟨s, hs, ht⟩ := (pair a t).mp ht
    obtain ⟨r, hr, hu⟩ := (pair a u).mp hu
    exact hH.1.2 s t u ht (hc.leaf_fn.2 a r s hr hs ▸ hu)
  have dom a : (∃ t, M.PairMember I a t G) ↔ ∃ s, M.PairMember I a s F := by
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨s, hs, _⟩ := (pair a t).mp ht
      exact ⟨s, hs⟩
    · rintro ⟨s, hs⟩
      obtain ⟨t, _, ht⟩ := hH.2.2 s (hc.leaf a s hs).2.1
      exact ⟨t, (pair a t).mpr ⟨s, hs, ht⟩⟩
  have hg : Btree_d I ω A Q T R N G := by
    refine ⟨hc.tree, hc.edges, hc.wf, hc.root, hc.neg_sub, fn, ?_, hc.neg⟩
    intro a t ht
    obtain ⟨s, hs, ht⟩ := (pair a t).mp ht
    have leaf := hc.leaf a s hs
    exact ⟨leaf.1, hH.output_mem_of_pairMember ht, leaf.2.2⟩
  obtain ⟨d, hd⟩ := bpack_exists_l I T R N G
  refine ⟨d, ⟨T, R, N, G, hd, hg⟩, fun x y map => ?_⟩
  have lit a : Blit_d I G y a ↔ Blit_d I F x a := by
    constructor
    · rintro ⟨t, ht, hty⟩
      obtain ⟨s, hs, ht⟩ := (pair a t).mp ht
      exact ⟨s, hs, (map s t (hc.leaf a s hs).2.1 ht).mp hty⟩
    · rintro ⟨s, hs, hsx⟩
      obtain ⟨t, _, ht⟩ := hH.2.2 s (hc.leaf a s hs).2.1
      exact ⟨t, (pair a t).mpr ⟨s, hs, ht⟩, (map s t (hc.leaf a s hs).2.1 ht).mpr hsx⟩
  obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF hc.wf N F x
  have hv' : Bsem_d I T R N G y V := by
    obtain ⟨L, U, hL, hU, hV⟩ := hv
    exact ⟨L, U, fun a => (hL a).trans (and_congr_right fun _ => (lit a).symm),
      fun a => (hU a).trans (and_congr_right fun _ =>
        and_congr Iff.rfl (not_congr (dom a).symm)), hV⟩
  obtain ⟨z, hz, _⟩ := hc.root
  exact (bsat_root_l I hZF hd hg hv' hz).trans (bsat_root_l I hZF hp hc hv hz).symm

end YesMetaZFC.SetTheory.Descriptive
