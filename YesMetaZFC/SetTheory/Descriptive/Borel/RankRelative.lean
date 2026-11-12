import YesMetaZFC.SetTheory.Descriptive.Borel.Relabel
import YesMetaZFC.SetTheory.Collapse.RelationRank
import YesMetaZFC.SetTheory.Descriptive.Game.Closed
import YesMetaZFC.SetTheory.Collapse.RelationGap
import YesMetaZFC.SetTheory.Descriptive.Tree.Trace

/-! # Borel 码树的内部序数秩

Brank 是整棵码树上的实际秩函数；Bcr 是其根值，叶和空并的树秩为零。
这是具体语法码的高度，不将它混同于取遍等价表示后的集合层级秩。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Brank_d (ω A S c H : M.Domain) : Prop := ∃ T R N F,
  Bpack_d I c T R N F ∧ Btree_d I ω A S T R N F ∧ Wr_d I T R H
def brank_m {d} (ω A S c H : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.existsE (.conj
  (bpack_m (𝒞 := 𝒞) c.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest) (.conj
  (btree_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken S.weaken.weaken.weaken.weaken (.bound 3) (.bound 2) (.bound 1) .newest)
  (wr_m (𝒞 := 𝒞) (.bound 3) (.bound 2) H.weaken.weaken.weaken.weaken))))))
derive_free_closed brank_m
theorem brank_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S c H : Term d) :
    Formula.satisfies ρ (brank_m (𝒞 := 𝒞) ω A S c H) ↔
      Brank_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (c.eval ρ) (H.eval ρ) := by
  simp only [brank_m, Brank_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bpack_sat_l I, btree_sat_l I hE, wr_sat_l I hE, Definitional.Term.eval_weaken]; rfl
theorem brank_unique_l (hZF : M.Models ZF) {ω A S c H G}
    (h : Brank_d I ω A S c H) (k : Brank_d I ω A S c G) : H = G := by
  obtain ⟨T, R, N, F, hp, ht, hr⟩ := h
  obtain ⟨T', R', N', F', hq, _, hs⟩ := k
  obtain ⟨rfl, rfl, rfl, rfl⟩ := bpack_unique_l I hp hq
  exact wr_unique_l I hZF ht.wf hr hs
theorem brank_exists_l (hZF : M.Models ZF) {ω A S c} (hc : Bcode_d I ω A S c) :
    ∃ H, Brank_d I ω A S c H := by
  obtain ⟨T, R, N, F, hp, ht⟩ := hc
  obtain ⟨_, H, _, _, _, hr⟩ := wr_exists_l I hZF ht.wf
  exact ⟨H, T, R, N, F, hp, ht, hr⟩

def Bcr_d (ω A S c α : M.Domain) : Prop := ∃ H z,
  Brank_d I ω A S c H ∧ (∀ p, ¬ M.mem p z) ∧ M.PairMember I z α H
def bcr_m {d} (ω A S c α : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (brank_m (𝒞 := 𝒞) ω.weaken.weaken A.weaken.weaken S.weaken.weaken c.weaken.weaken (.bound 1)) (.conj
  (Formula.isEmpty .newest) (Formula.orderedPairMem 𝒞 .newest α.weaken.weaken (.bound 1)))))
derive_free_closed bcr_m
theorem bcr_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A S c α : Term d) :
    Formula.satisfies ρ (bcr_m (𝒞 := 𝒞) ω A S c α) ↔
      Bcr_d I (ω.eval ρ) (A.eval ρ) (S.eval ρ) (c.eval ρ) (α.eval ρ) := by
  simp only [bcr_m, Bcr_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, brank_sat_l I hE,
    Formula.satisfies_isEmpty_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]; rfl
theorem bcr_unique_l (hZF : M.Models ZF) {ω A S c α β} (h : Bcr_d I ω A S c α) (k : Bcr_d I ω A S c β) : α = β := by
  obtain ⟨H, z, hh, hz, ha⟩ := h
  obtain ⟨G, w, hg, hw, hb⟩ := k
  have e := brank_unique_l I hZF hg hh
  subst G
  have e := hZF.1.eq_of_same_members w z (fun p => iff_of_false (hw p) (hz p))
  subst w
  obtain ⟨_, _, _, _, _, _, hr⟩ := hh
  exact hr.1.2 z α β ha hb

/-- 根秩实际存在、唯一且内部可数，整树也有一个共同的可数秩界。 -/
theorem bcr_exists_l (hZF : M.Models ZF) {ω A S c} (hω : M.IsOmega ω)
    (ha : M.CardinalLessOrEqual I A ω) (hc : Bcode_d I ω A S c) :
    ∃ α, M.IsOrdinal α ∧ M.CardinalLessOrEqual I α ω ∧ Bcr_d I ω A S c α := by
  obtain ⟨T, R, N, F, hp, ht⟩ := hc
  obtain ⟨E, he⟩ := ha
  obtain ⟨D, hd⟩ := ZF.exists_inclusionInjection hZF I ht.tree.1
  obtain ⟨β, H, hb, count, hh, hr⟩ := wr_countable_l I hZF hω ht.wf (ZF.exists_compositionInjection hZF I hd he)
  obtain ⟨z, hz, hzT⟩ := ht.root
  obtain ⟨α, hα, hza⟩ := hh.2.2 z hzT
  obtain ⟨V, hv⟩ := ZF.exists_inclusionInjection hZF I (hb.transitive.memberSubset hα)
  obtain ⟨W, hw⟩ := count
  exact ⟨α, hb.mem hα, ZF.exists_compositionInjection hZF I hv hw, H, z, ⟨T, R, N, F, hp, ht, hr⟩, hz, hza⟩

/-- 节点秩满足通常的 sup(子秩+1) 方程，而非任意下降标号。 -/
theorem brank_equation_l {ω A S c H T R N F a α} (h : Brank_d I ω A S c H)
    (hp : Bpack_d I c T R N F) (ha : M.PairMember I a α H) : M.IsOrdinal α ∧ ∀ β, M.mem β α ↔
      ∃ b γ, M.mem b T ∧ Rd_entry_d b a R ∧ M.PairMember I b γ H ∧ (β = γ ∨ M.mem β γ) := by
  obtain ⟨T', R', N', F', hq, _, hr⟩ := h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := bpack_unique_l I hp hq
  exact hr.2.2 a α ha

end YesMetaZFC.SetTheory.Descriptive

/-! ## 标准 Borel 层级的内部超限递归

Σ⁰₁ 为开集，Π⁰α 为相对补集；正层 Σ⁰α 由开集及较低 Π 层的内部可数并组成。
第零层为空。递归值是 P(B) 的实际子集，索引是模型的序数，允许外部非良基。
可数族是模型中的函数；在 ZF 中不把一族集合的存在偷换为一族码的存在。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 允许部分 ω 索引，因而空并不需另添人为索引。 -/
def Bu_d (ω H K : M.Domain) : Prop := M.IsSetFunction I H ∧
  (∀ i C, M.PairMember I i C H → M.mem i ω) ∧
  ∀ x, M.mem x K ↔ ∃ i C, M.PairMember I i C H ∧ M.mem x C
def bu_m {d} (ω H K : Term d) : Formula 1 d := .conj (Formula.isFunction 𝒞 H) (.conj
  (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken) (.mem (.bound 1) ω.weaken.weaken))))
  (.forallE (.iff (.mem .newest K.weaken) (.existsE (.existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest H.weaken.weaken.weaken) (.mem (.bound 2) .newest)))))))
derive_free_closed bu_m
theorem bu_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω H K : Term d) :
    Formula.satisfies ρ (bu_m (𝒞 := 𝒞) ω H K) ↔ Bu_d I (ω.eval ρ) (H.eval ρ) (K.eval ρ) := by
  simp only [bu_m, Bu_d, Formula.satisfies_conj_iff, Formula.satisfies_isFunction_iff I hE,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff, Definitional.Term.eval_weaken]; rfl

def Bh_prev_d (B F C : M.Domain) : Prop := ∃ β V L,
  M.PairMember I β V F ∧ M.mem L V ∧ Cm_d B L C
def bh_prev_m {d} (B F C : Term d) : Formula 1 d := .existsE (.existsE (.existsE (.conj
  (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) F.weaken.weaken.weaken) (.conj
  (.mem .newest (.bound 1)) (cm_m B.weaken.weaken.weaken .newest C.weaken.weaken.weaken)))))
derive_free_closed bh_prev_m
theorem bh_prev_sat_l {d} (ρ : Env M d) (B F C : Term d) :
    Formula.satisfies ρ (bh_prev_m (𝒞 := 𝒞) B F C) ↔ Bh_prev_d I (B.eval ρ) (F.eval ρ) (C.eval ρ) := by
  simp only [bh_prev_m, Bh_prev_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_mem_iff, cm_sat_l, Definitional.Term.eval_weaken]; rfl

def Bh_build_d (ω A B F K : M.Domain) : Prop := M.MemberSubset K B ∧
  (∃ β V, M.PairMember I β V F) ∧ (Open_d A B K ∨ ∃ H,
    Bu_d I ω H K ∧ ∀ i C, M.PairMember I i C H → Bh_prev_d I B F C)
def bh_build_m {d} (ω A B F K : Term d) : Formula 1 d := .conj (Formula.subset K B) (.conj
  (.existsE (.existsE (Formula.orderedPairMem 𝒞 (.bound 1) .newest F.weaken.weaken)))
  (.disj (open_m A B K) (.existsE (.conj (bu_m (𝒞 := 𝒞) ω.weaken .newest K.weaken)
  (.forallE (.forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (bh_prev_m (𝒞 := 𝒞) B.weaken.weaken.weaken F.weaken.weaken.weaken .newest))))))))
derive_free_closed bh_build_m
theorem bh_build_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B F K : Term d) :
    Formula.satisfies ρ (bh_build_m (𝒞 := 𝒞) ω A B F K) ↔
      Bh_build_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (F.eval ρ) (K.eval ρ) := by
  simp only [bh_build_m, Bh_build_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_disj_iff,
    open_sat_l, bu_sat_l I hE, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    bh_prev_sat_l I, Definitional.Term.eval_weaken]; rfl

def Bh_step_d (ω A B F S : M.Domain) : Prop := ∀ K, M.mem K S ↔ Bh_build_d I ω A B F K
def bh_op_s : BinarySchema 3 := { body := .forallE (.iff (.mem .newest (.bound 1))
  (bh_build_m (𝒞 := 𝒞) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest)) }
def bh_env_l (ω A B : M.Domain) : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B
theorem bh_op_l (hE : Extensional M) (ρ : Env M 3) :
    (bh_op_s (𝒞 := 𝒞)).denote ρ = Bh_step_d I (ρ.bound 2) (ρ.bound 1) (ρ.bound 0) := by
  funext F S
  apply propext
  simp only [bh_op_s, BinarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, bh_build_sat_l I hE]; rfl

def Bh_d (ω A B α S : M.Domain) : Prop := M.IsRecursionValue I (Bh_step_d I ω A B) α S
def bh_m {d} (ω A B α S : Term d) : Formula 1 d := Formula.isRecursionValue 𝒞 (bh_op_s (𝒞 := 𝒞))
  (Definitional.TermVector.ofFn (Fin.cases B (Fin.cases A (fun _ => ω)))) α S
@[simp] theorem bh_closed_l {d} (ω A B α S : Term d) (hω : ω.freeSupport = []) (hA : A.freeSupport = [])
    (hB : B.freeSupport = []) (hα : α.freeSupport = []) (hS : S.freeSupport = []) : (bh_m (𝒞 := 𝒞) ω A B α S).FreeClosed := by
  have he : (Definitional.TermVector.ofFn (Fin.cases B (Fin.cases A (fun _ : Fin 1 => ω)))).FreeClosed := by
    intro i
    cases i using Fin.cases with
    | zero => exact hB
    | succ i => cases i using Fin.cases with
      | zero => exact hA
      | succ i => simpa only [Definitional.TermVector.get_ofFn, Fin.cases_succ] using hω
  exact Formula.isRecursionValue_freeClosed _ _ _ _ _ he hα hS
theorem bh_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B α S : Term d) :
    Formula.satisfies ρ (bh_m (𝒞 := 𝒞) ω A B α S) ↔
      Bh_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (α.eval ρ) (S.eval ρ) := by
  rw [bh_m, Formula.satisfies_isRecursionValue_iff I hE, bh_op_l I hE]; rfl

theorem bh_class_l (hZF : M.Models ZF) (ω A B : M.Domain) : M.IsClassFunctionOnTransfiniteSequences I (Bh_step_d I ω A B) := by
  intro F _
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF B
  let φ : UnarySchema 4 := { body := bh_build_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨S, hs⟩ := ZF.separation_exists_d hZF φ ((bh_env_l ω A B).push F) P
  have step : Bh_step_d I ω A B F S := by
    intro K
    have hv : φ.denote ((bh_env_l ω A B).push F) K ↔ Bh_build_d I ω A B F K := bh_build_sat_l I hZF.1 _ _ _ _ _ _
    exact (hs K).trans ((and_congr (hp K) hv).trans ⟨And.right, fun h => ⟨h.1, h⟩⟩)
  exact ⟨S, step, fun U hu => hZF.1.eq_of_same_members U S (fun K => (hu K).trans (step K).symm)⟩
theorem bh_exists_l (hZF : M.Models ZF) {ω A B α} (hα : M.IsOrdinal α) : ∃ S, Bh_d I ω A B α S := by
  have hc := bh_class_l I hZF ω A B
  have op : (bh_op_s (𝒞 := 𝒞)).denote (bh_env_l ω A B) = Bh_step_d I ω A B := bh_op_l I hZF.1 _
  rw [← op] at hc
  obtain ⟨S, hs⟩ := ZF.recursionValue_exists hZF I (bh_env_l ω A B) bh_op_s hc hα
  exact ⟨S, by simpa only [Bh_d, op] using hs⟩
theorem bh_unique_l (hZF : M.Models ZF) {ω A B α S T} (h : Bh_d I ω A B α S) (k : Bh_d I ω A B α T) : S = T := by
  have hc := bh_class_l I hZF ω A B
  have op : (bh_op_s (𝒞 := 𝒞)).denote (bh_env_l ω A B) = Bh_step_d I ω A B := bh_op_l I hZF.1 _
  rw [← op] at hc
  exact ZF.recursionValue_unique hZF I (bh_env_l ω A B) bh_op_s hc
    (by simpa only [Bh_d, op] using h) (by simpa only [Bh_d, op] using k)

def Bsig_d (ω A B α K : M.Domain) : Prop := ∃ S, Bh_d I ω A B α S ∧ M.mem K S
def Bpi_d (ω A B α K : M.Domain) : Prop := ∃ L, Bsig_d I ω A B α L ∧ Cm_d B L K
def bsig_m {d} (ω A B α K : Term d) : Formula 1 d := .existsE (.conj
  (bh_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken α.weaken .newest) (.mem K.weaken .newest))
def bpi_m {d} (ω A B α K : Term d) : Formula 1 d := .existsE (.conj
  (bsig_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken α.weaken .newest) (cm_m B.weaken .newest K.weaken))
derive_free_closed bsig_m
derive_free_closed bpi_m
theorem bsig_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B α K : Term d) :
    Formula.satisfies ρ (bsig_m (𝒞 := 𝒞) ω A B α K) ↔ Bsig_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (α.eval ρ) (K.eval ρ) := by
  simp only [bsig_m, Bsig_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bh_sat_l I hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl
theorem bpi_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B α K : Term d) :
    Formula.satisfies ρ (bpi_m (𝒞 := 𝒞) ω A B α K) ↔ Bpi_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (α.eval ρ) (K.eval ρ) := by
  simp only [bpi_m, Bpi_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    bsig_sat_l I hE, cm_sat_l, Definitional.Term.eval_weaken]; rfl

theorem bsig_ordinal_l {ω A B α K} (h : Bsig_d I ω A B α K) : M.IsOrdinal α :=
  h.elim fun _ h => h.1.elim fun _ h => h.1.1.1
theorem bsig_subset_l {ω A B α K} (h : Bsig_d I ω A B α K) : M.MemberSubset K B := by
  obtain ⟨S, ⟨F, _, hf⟩, hs⟩ := h
  exact ((hf K).mp hs).1

/-- 递归方程：量词遍历真实的较低序数层与真实的内部可数族。 -/
theorem bsig_unfold_l (hZF : M.Models ZF) {ω A B α K} (hα : M.IsOrdinal α) :
    Bsig_d I ω A B α K ↔ M.MemberSubset K B ∧ (∃ β, M.mem β α) ∧
      (Open_d A B K ∨ ∃ H, Bu_d I ω H K ∧ ∀ i C, M.PairMember I i C H → ∃ β, M.mem β α ∧ Bpi_d I ω A B β C) := by
  obtain ⟨S, hS⟩ := bh_exists_l I hZF (ω := ω) (A := A) (B := B) hα
  have eqv : Bsig_d I ω A B α K ↔ M.mem K S :=
    ⟨fun ⟨V, hv, hk⟩ => bh_unique_l I hZF hv hS ▸ hk, fun hk => ⟨S, hS, hk⟩⟩
  obtain ⟨F, hf, hs⟩ := hS
  have prev C : Bh_prev_d I B F C ↔ ∃ β, M.mem β α ∧ Bpi_d I ω A B β C := by
    constructor
    · rintro ⟨β, V, L, hv, hl, hc⟩
      have hb := (hf.1.2.2 β).mpr ⟨V, hv⟩
      exact ⟨β, hb, L, ⟨V, hf.recursionValue_of_pairMember hb hv, hl⟩, hc⟩
    · rintro ⟨β, hb, L, ⟨V, hv, hl⟩, hc⟩
      obtain ⟨W, hw⟩ := (hf.1.2.2 β).mp hb
      exact ⟨β, W, L, hw, bh_unique_l I hZF hv (hf.recursionValue_of_pairMember hb hw) ▸ hl, hc⟩
  refine eqv.trans ((hs K).trans (and_congr_right fun _ => and_congr ?_ ?_))
  · constructor
    · exact fun ⟨β, V, hv⟩ => ⟨β, (hf.1.2.2 β).mpr ⟨V, hv⟩⟩
    · rintro ⟨β, hb⟩
      obtain ⟨V, hv⟩ := (hf.1.2.2 β).mp hb
      exact ⟨β, V, hv⟩
  · exact or_congr Iff.rfl (exists_congr fun H => and_congr_right fun _ =>
      forall_congr' fun i => forall_congr' fun C => imp_congr_right fun _ => prev C)

end YesMetaZFC.SetTheory.Descriptive

/-! ## Borel 层级的基层、补集、升层与可数并规则 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bsig_nonempty_l {ω A B α K} (h : Bsig_d I ω A B α K) : ∃ β, M.mem β α := by
  obtain ⟨S, ⟨F, hf, hs⟩, hk⟩ := h
  obtain ⟨β, V, hv⟩ := ((hs K).mp hk).2.1
  exact ⟨β, (hf.1.2.2 β).mpr ⟨V, hv⟩⟩
theorem bpi_subset_l {ω A B α K} (h : Bpi_d I ω A B α K) : M.MemberSubset K B :=
  h.elim fun _ h => fun x hx => ((h.2 x).mp hx).1
theorem bsig_open_l (hZF : M.Models ZF) {ω A B α K} (hα : M.IsOrdinal α)
    (hne : ∃ β, M.mem β α) (ho : Open_d A B K) : Bsig_d I ω A B α K :=
  (bsig_unfold_l I hZF hα).mpr ⟨ho.1, hne, Or.inl ho⟩
theorem bpi_closed_l (hZF : M.Models ZF) {ω A B α K} (hα : M.IsOrdinal α)
    (hne : ∃ β, M.mem β α) (hc : Cl_d A B K) : Bpi_d I ω A B α K := by
  obtain ⟨sub, L, hl, ho⟩ := hc
  exact ⟨L, bsig_open_l I hZF hα hne ho, cm_symm_l sub hl⟩

theorem bsig_compl_l (hE : Extensional M) {ω A B α K L}
    (sub : M.MemberSubset K B) (hc : Cm_d B K L) : Bsig_d I ω A B α L ↔ Bpi_d I ω A B α K :=
  ⟨fun h => ⟨L, h, cm_symm_l sub hc⟩, fun ⟨_, hv, hk⟩ =>
    cm_unique_l hE (cm_symm_l (bsig_subset_l I hv) hk) hc ▸ hv⟩
theorem bpi_compl_l (hE : Extensional M) {ω A B α K L}
    (sub : M.MemberSubset K B) (hc : Cm_d B K L) : Bpi_d I ω A B α L ↔ Bsig_d I ω A B α K := by
  exact (bsig_compl_l I hE (fun x hx => ((hc x).mp hx).1) (cm_symm_l sub hc)).symm

theorem bsig_mono_l (hZF : M.Models ZF) {ω A B α β K} (hβ : M.IsOrdinal β)
    (hab : M.MemberSubset α β) (h : Bsig_d I ω A B α K) : Bsig_d I ω A B β K := by
  obtain ⟨sub, ⟨γ, hγ⟩, ho | ⟨H, hu, hh⟩⟩ := (bsig_unfold_l I hZF (bsig_ordinal_l I h)).mp h
  · exact bsig_open_l I hZF hβ ⟨γ, hab γ hγ⟩ ho
  · exact (bsig_unfold_l I hZF hβ).mpr ⟨sub, ⟨γ, hab γ hγ⟩, Or.inr ⟨H, hu,
      fun i C hc => (hh i C hc).elim fun δ hd => ⟨δ, hab δ hd.1, hd.2⟩⟩⟩
theorem bpi_mono_l (hZF : M.Models ZF) {ω A B α β K} (hβ : M.IsOrdinal β)
    (hab : M.MemberSubset α β) (h : Bpi_d I ω A B α K) : Bpi_d I ω A B β K :=
  h.elim fun L h => ⟨L, bsig_mono_l I hZF hβ hab h.1, h.2⟩

theorem bsig_union_l (hZF : M.Models ZF) {ω A B α H K} (hα : M.IsOrdinal α)
    (hne : ∃ β, M.mem β α) (hu : Bu_d I ω H K)
    (hh : ∀ i C, M.PairMember I i C H → ∃ β, M.mem β α ∧ Bpi_d I ω A B β C) : Bsig_d I ω A B α K := by
  refine (bsig_unfold_l I hZF hα).mpr ⟨?_, hne, Or.inr ⟨H, hu, hh⟩⟩
  intro x hx
  obtain ⟨i, C, hc, hx⟩ := (hu.2.2 x).mp hx
  obtain ⟨_, _, h⟩ := hh i C hc
  exact bpi_subset_l I h x hx

/-- 单元素族给出严格升层 Π⁰α ⊆ Σ⁰β；这里只需 ω 非空。 -/
theorem bpi_bsig_l (hZF : M.Models ZF) {ω A B α β K} (hne : ∃ i, M.mem i ω)
    (hβ : M.IsOrdinal β) (hab : M.mem α β) (h : Bpi_d I ω A B α K) : Bsig_d I ω A B β K := by
  obtain ⟨D, hd⟩ := KP.exists_singleton (ZF.modelsKP hZF) K
  obtain ⟨H, hh, eh⟩ := ZF.exists_constantFunction hZF I (source := ω) ((hd K).mpr rfl)
  have hu : Bu_d I ω H K := by
    refine ⟨hh.1, fun i C hc => ((eh i C).mp hc).1, fun x => ⟨?_, ?_⟩⟩
    · intro hx
      obtain ⟨i, hi⟩ := hne
      exact ⟨i, K, (eh i K).mpr ⟨hi, rfl⟩, hx⟩
    · rintro ⟨i, C, hc, hx⟩
      exact ((eh i C).mp hc).2 ▸ hx
  exact bsig_union_l I hZF hβ ⟨α, hab⟩ hu (fun i C hc => ⟨α, hab, ((eh i C).mp hc).2 ▸ h⟩)
theorem bsig_bpi_l (hZF : M.Models ZF) {ω A B α β K} (hne : ∃ i, M.mem i ω)
    (hβ : M.IsOrdinal β) (hab : M.mem α β) (h : Bsig_d I ω A B α K) : Bpi_d I ω A B β K := by
  obtain ⟨L, hl⟩ := cm_exists_l (ZF.modelsKP hZF) B K
  exact ⟨L, bpi_bsig_l I hZF hne hβ hab ⟨K, h, hl⟩, cm_symm_l (bsig_subset_l I h) hl⟩

/-- 第一层恰好是开集；较低层只有零层，不能贡献任何非空索引。 -/
theorem bsig_one_l (hZF : M.Models ZF) {ω A B o K} (ho : M.IsOrdinalOne o) :
    Bsig_d I ω A B o K ↔ Open_d A B K := by
  obtain ⟨z, hz, hs⟩ := ho
  have hα := KP.successor_isOrdinal (ZF.modelsKP hZF) (Structure.IsOrdinal.of_no_members hz) hs
  constructor
  · intro h
    obtain ⟨sub, _, hopen | ⟨H, hu, hh⟩⟩ := (bsig_unfold_l I hZF hα).mp h
    · exact hopen
    · have empty : ∀ x, ¬ M.mem x K := by
        intro x hx
        obtain ⟨i, C, hc, _⟩ := (hu.2.2 x).mp hx
        obtain ⟨β, hb, L, hl, _⟩ := hh i C hc
        rcases (hs β).mp hb with hb | hb
        · exact hz β hb
        · obtain ⟨γ, hγ⟩ := bsig_nonempty_l I hl
          exact hz γ (hZF.1.eq_of_same_members β z hb ▸ hγ)
      exact ds_open_empty_l empty
  · exact bsig_open_l I hZF hα ⟨z, hs.predecessor_mem⟩
theorem bpi_one_l (hZF : M.Models ZF) {ω A B o K} (ho : M.IsOrdinalOne o) :
    Bpi_d I ω A B o K ↔ Cl_d A B K := by
  constructor
  · rintro ⟨L, hl, hc⟩
    exact ⟨fun x hx => ((hc x).mp hx).1, L, cm_symm_l (bsig_subset_l I hl) hc, (bsig_one_l I hZF ho).mp hl⟩
  · rintro ⟨sub, L, hc, hl⟩
    exact ⟨L, (bsig_one_l I hZF ho).mpr hl, cm_symm_l sub hc⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## Borel 树全部节点的实际解释集合

一次分离和替代给出整树的解释函数，因而可数并处不需要可数选择。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Bn_d (B T R N F a K : M.Domain) : Prop := ∀ x, M.mem x K ↔
  M.mem x B ∧ ∃ V, Bsem_d I T R N F x V ∧ M.mem a V
def bn_m {d} (B T R N F a K : Term d) : Formula 1 d := .forallE (.iff (.mem .newest K.weaken)
  (.conj (.mem .newest B.weaken) (.existsE (.conj
    (bsem_m (𝒞 := 𝒞) T.weaken.weaken R.weaken.weaken N.weaken.weaken F.weaken.weaken (.bound 1) .newest)
    (.mem a.weaken.weaken .newest)))))
derive_free_closed bn_m
theorem bn_sat_l (hE : Extensional M) {d} (ρ : Env M d) (B T R N F a K : Term d) :
    Formula.satisfies ρ (bn_m (𝒞 := 𝒞) B T R N F a K) ↔
      Bn_d I (B.eval ρ) (T.eval ρ) (R.eval ρ) (N.eval ρ) (F.eval ρ) (a.eval ρ) (K.eval ρ) := by
  simp only [bn_m, Bn_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    bsem_sat_l I hE, Definitional.Term.eval_weaken]; rfl

theorem bn_graph_l (hZF : M.Models ZF) (B T R N F : M.Domain) :
    ∃ P G, M.IsPowerSetOf P B ∧ M.IsSetFunctionFromTo I G T P ∧
      ∀ a K, M.PairMember I a K G → Bn_d I B T R N F a K := by
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push T).push R).push N).push F
  let φ : BinarySchema 5 := { body := bn_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have ep a K : φ.denote ρ a K ↔ Bn_d I B T R N F a K := bn_sat_l I hZF.1 _ _ _ _ _ _ _ _
  have total a : ∃ K, Bn_d I B T R N F a K := by
    let ψ : UnarySchema 6 := { body := .existsE (.conj
      (bsem_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)
      (.mem (.bound 2) .newest)) }
    obtain ⟨K, hk⟩ := ZF.separation_exists_d hZF ψ (ρ.push a) B
    refine ⟨K, fun x => ?_⟩
    simpa only [ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      bsem_sat_l I hZF.1, Formula.satisfies_mem_iff] using! hk x
  obtain ⟨G, hg, eg⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := T) (target := P)
    (fun a _ => (total a).imp fun K hk => (ep a K).mpr hk)
    (fun a _ K L hk hl => hZF.1.eq_of_same_members K L (fun x => ((ep a K).mp hk x).trans ((ep a L).mp hl x).symm))
    (fun a K _ hk => (hp K).mpr (fun x hx => (((ep a K).mp hk x).mp hx).1))
  exact ⟨P, G, hp, hg, fun a K hk => (ep a K).mp ((eg a K).mp hk).2⟩

theorem bn_mem_l (hZF : M.Models ZF) {B T R N F a K x V} (hw : Wf_rel_d T R)
    (h : Bn_d I B T R N F a K) (hv : Bsem_d I T R N F x V) : M.mem x K ↔ M.mem x B ∧ M.mem a V := by
  obtain ⟨W, _, unique⟩ := bsem_exists_unique_l I hZF hw N F x
  exact (h x).trans (and_congr_right fun _ => ⟨fun ⟨U, hu, ha⟩ => ((unique U hu).trans (unique V hv).symm) ▸ ha,
    fun ha => ⟨V, hv, ha⟩⟩)

theorem bn_leaf_l (hZF : M.Models ZF) {ω A S B T R N F a s K} (ht : Btree_d I ω A S T R N F)
    (hs : M.PairMember I a s F) (hk : Bn_d I B T R N F a K) : Cyl_d B s K := by
  intro x
  obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF ht.wf N F x
  exact (bn_mem_l I hZF ht.wf hk hv).trans (and_congr_right fun _ =>
    bsem_leaf_l I hv ht.leaf_fn (ht.leaf a s hs).1 (ht.leaf a s hs).2.2.1 hs)

theorem bn_neg_l (hZF : M.Models ZF) {ω A S B T R N F a b K L} (ht : Btree_d I ω A S T R N F)
    (hn : M.mem a N) (hb : M.mem b T) (hba : Rd_entry_d b a R)
    (hu : ∀ c, M.mem c T → Rd_entry_d c a R → c = b)
    (hk : Bn_d I B T R N F a K) (hl : Bn_d I B T R N F b L) : Cm_d B L K := by
  intro x
  obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF ht.wf N F x
  have no : ¬ ∃ s, M.PairMember I a s F := fun ⟨s, hs⟩ => (ht.leaf a s hs).2.2.1 hn
  refine (bn_mem_l I hZF ht.wf hk hv).trans (and_congr_right fun hx => ?_)
  exact (bsem_neg_l I hv (ht.neg_sub a hn) hn no hb hba hu).trans
    (not_congr ((bn_mem_l I hZF ht.wf hl hv).trans ⟨And.right, fun h => ⟨hx, h⟩⟩)).symm

/-- 把子节点的解释函数按一个已有的自然数单射重新索引。 -/
theorem bn_union_family_l (hZF : M.Models ZF) {ω A S B T R N F a K P G}
    (ht : Btree_d I ω A S T R N F) (hc : M.CardinalLessOrEqual I T ω)
    (hg : M.IsSetFunctionFromTo I G T P)
    (eg : ∀ b C, M.PairMember I b C G → Bn_d I B T R N F b C)
    (ha : M.mem a T) (hn : ¬ M.mem a N) (hf : ¬ ∃ s, M.PairMember I a s F)
    (hk : Bn_d I B T R N F a K) :
    ∃ H, Bu_d I ω H K ∧ ∀ i C, M.PairMember I i C H →
      ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.PairMember I b C G := by
  obtain ⟨E, he⟩ := hc
  obtain ⟨W, hw⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) ω P
  let ρ : Env M 5 := ((((⟨fun _ => T, fun _ => T⟩ : Env M 1).push R).push a).push E).push G
  let φ : BinarySchema 5 := { body := .existsE (.conj (.mem .newest (.bound 7)) (.conj
    (rd_entry_m .newest (.bound 5) (.bound 6)) (.conj
    (Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 4))
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3))))) }
  have ep i C : φ.denote ρ i C ↔ ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.PairMember I b i E ∧ M.PairMember I b C G := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, rd_entry_sat_l hZF.1, Formula.satisfies_orderedPairMem_iff I]; rfl
  obtain ⟨H, hh, eh⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  have pair i C : M.PairMember I i C H ↔ ∃ b, M.mem b T ∧ Rd_entry_d b a R ∧ M.PairMember I b i E ∧ M.PairMember I b C G := by
    refine ((eh i C).trans (and_congr_right fun _ => and_congr_right fun _ => ep i C)).trans ⟨fun h => h.2.2, ?_⟩
    intro h
    obtain ⟨b, hb, hba, hbi, hbC⟩ := h
    exact ⟨(hw i).mpr (Or.inl (he.1.output_mem_of_pairMember hbi)), (hw C).mpr (Or.inr (hg.output_mem_of_pairMember hbC)), b, hb, hba, hbi, hbC⟩
  refine ⟨H, ⟨⟨hh.1, ?_⟩, ?_, ?_⟩, fun i C h => (pair i C).mp h |>.elim fun b h => ⟨b, h.1, h.2.1, h.2.2.2⟩⟩
  · intro i C D hc hd
    obtain ⟨b, _, _, hbi, hbC⟩ := (pair i C).mp hc
    obtain ⟨c, _, _, hci, hcD⟩ := (pair i D).mp hd
    exact hg.1.2 b C D hbC (he.2 c b i hci hbi ▸ hcD)
  · intro i C h
    obtain ⟨_, _, _, hbi, _⟩ := (pair i C).mp h
    exact he.1.output_mem_of_pairMember hbi
  · intro x
    obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF ht.wf N F x
    constructor
    · intro hx
      obtain ⟨hxB, hav⟩ := (bn_mem_l I hZF ht.wf hk hv).mp hx
      obtain ⟨b, hb, hba, hbV⟩ := (bsem_union_l I hv ha hn hf).mp hav
      obtain ⟨C, _, hbC⟩ := hg.2.2 b hb
      obtain ⟨i, _, hbi⟩ := he.1.2.2 b hb
      exact ⟨i, C, (pair i C).mpr ⟨b, hb, hba, hbi, hbC⟩, (bn_mem_l I hZF ht.wf (eg b C hbC) hv).mpr ⟨hxB, hbV⟩⟩
    · rintro ⟨i, C, hc, hx⟩
      obtain ⟨b, hb, hba, _, hbC⟩ := (pair i C).mp hc
      obtain ⟨hxB, hbV⟩ := (bn_mem_l I hZF ht.wf (eg b C hbC) hv).mp hx
      exact (bn_mem_l I hZF ht.wf hk hv).mpr ⟨hxB, (bsem_union_l I hv ha hn hf).mpr ⟨b, hb, hba, hbV⟩⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 从任意内部 Borel 码导出可数的标准层级界

难点是并节点：先在较低的上界形成 Σ 集，再升一层进入 Δ。
双层秩为此提供严格间隙，整树的节点解释函数提供实际可数族；全程只用 ZF。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bcode_level_l (hZF : M.Models ZF) {ω X A S B c K} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hc : M.CardinalLessOrEqual I A ω) (hcode : Bcode_d I ω A S c) (hden : Bden_d I ω A S B c K) :
    ∃ α, M.IsOrdinal α ∧ M.CardinalLessOrEqual I α ω ∧ Bsig_d I ω S B α K ∧ Bpi_d I ω S B α K := by
  classical
  obtain ⟨T, R, N, F, pack, ht⟩ := hcode
  obtain ⟨E, he⟩ := hc
  obtain ⟨D, hd⟩ := ZF.exists_inclusionInjection hZF I ht.tree.1
  have count := ZF.exists_compositionInjection hZF I hd he
  obtain ⟨κ, L, H, hk, hkω, hl, hh, gap⟩ := wr_gap_l I hZF hω ht.wf count
  obtain ⟨P, G, hp, hg, eg⟩ := bn_graph_l I hZF B T R N F
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push S).push B).push H).push G
  let φ : UnarySchema 5 := { body := .forallE (.forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) (.bound 1) (.bound 4)) (.imp
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (.conj
    (bsig_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 1) .newest)
    (bpi_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 1) .newest))))) }
  have ep a : φ.denote ρ a ↔ ∀ α C, M.PairMember I a α H → M.PairMember I a C G →
      Bsig_d I ω S B α C ∧ Bpi_d I ω S B α C := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_conj_iff, bsig_sat_l I hZF.1, bpi_sat_l I hZF.1]; rfl
  have all := wf_rel_ind_l hZF ht.wf φ ρ (fun a ha ih => (ep a).mpr (by
    intro α C haα haC
    have hα := hk.mem (hh.output_mem_of_pairMember haα)
    obtain ⟨δ, hδκ, haδ⟩ := hl.2.2 a ha
    obtain ⟨hδα, below⟩ := gap a δ α haδ haα
    have hδ := hk.mem hδκ
    have hC := eg a C haC
    -- 叶解释为开闭柱集，在任意正层同时属于 Σ 与 Π。
    by_cases leaf : ∃ s, M.PairMember I a s F
    · obtain ⟨s, hs⟩ := leaf
      have cyl := bn_leaf_l I hZF ht hs hC
      obtain ⟨ho, hc⟩ := ds_cyl_clopen_l I hZF hω hB hS (ht.leaf a s hs).2.1 cyl
      exact ⟨bsig_open_l I hZF hα ⟨δ, hδα⟩ ho,
        bpi_closed_l I hZF hα ⟨δ, hδα⟩ ⟨ho.1, hc⟩⟩
    · by_cases neg : M.mem a N
      -- 补节点交换两种极性，再沿序数包含升层。
      · obtain ⟨b, hb, hba, unique⟩ := ht.neg a neg
        obtain ⟨γ, _, hbγ⟩ := hh.2.2 b hb
        obtain ⟨V, hvP, hbV⟩ := hg.2.2 b hb
        obtain ⟨sig, pi⟩ := (ep b).mp (ih b hb hba) γ V hbγ hbV
        have cm := bn_neg_l I hZF ht neg hb hba unique hC (eg b V hbV)
        have sub := (hp V).mp hvP
        have hγα := hα.transitive δ hδα γ (below b γ hb hba hbγ)
        exact ⟨bsig_mono_l I hZF hα (hα.transitive.memberSubset hγα) ((bsig_compl_l I hZF.1 sub cm).mpr pi),
          bpi_mono_l I hZF hα (hα.transitive.memberSubset hγα) ((bpi_compl_l I hZF.1 sub cm).mpr sig)⟩
      · obtain ⟨U, hu, eu⟩ := bn_union_family_l I hZF ht count hg eg ha neg leaf hC
        -- 子秩严格低于 δ，故并先落入 Σ⁰δ；δ < α 再给出 Π⁰α。
        by_cases ne : ∃ β, M.mem β δ
        · have low : Bsig_d I ω S B δ C := bsig_union_l I hZF hδ ne hu (by
            intro i V hi
            obtain ⟨b, hb, hba, hbV⟩ := eu i V hi
            obtain ⟨γ, _, hbγ⟩ := hh.2.2 b hb
            exact ⟨γ, below b γ hb hba hbγ, ((ep b).mp (ih b hb hba) γ V hbγ hbV).2⟩)
          exact ⟨bsig_mono_l I hZF hα (hα.transitive.memberSubset hδα) low,
            bsig_bpi_l I hZF (hω.1.1.elim fun z h => ⟨z, h.2⟩) hα hδα low⟩
        · have empty : ∀ x, ¬ M.mem x C := by
            intro x hx
            obtain ⟨i, V, hi, _⟩ := (hu.2.2 x).mp hx
            obtain ⟨b, hb, hba, _⟩ := eu i V hi
            obtain ⟨γ, _, hbγ⟩ := hh.2.2 b hb
            exact ne ⟨γ, below b γ hb hba hbγ⟩
          exact ⟨bsig_open_l I hZF hα ⟨δ, hδα⟩ (ds_open_empty_l empty),
            bpi_closed_l I hZF hα ⟨δ, hδα⟩ ⟨fun x hx => (empty x hx).elim, B,
              fun x => ⟨fun hx => ⟨hx, empty x⟩, And.left⟩, ds_open_whole_l I hZF hω hB hS⟩⟩))
  obtain ⟨z, hz, hzT⟩ := ht.root
  obtain ⟨α, hακ, hza⟩ := hh.2.2 z hzT
  obtain ⟨C, _, hzC⟩ := hg.2.2 z hzT
  have eqK : C = K := by
    apply hZF.1.eq_of_same_members C K
    intro x
    obtain ⟨V, hv, _⟩ := bsem_exists_unique_l I hZF ht.wf N F x
    exact (bn_mem_l I hZF ht.wf (eg z C hzC) hv).trans
      ((and_congr_right fun _ => (bsat_root_l I hZF pack ht hv hz).symm).trans (hden x).symm)
  obtain ⟨J, hj⟩ := ZF.exists_inclusionInjection hZF I (hk.transitive.memberSubset hακ)
  obtain ⟨Q, hq⟩ := hkω
  exact ⟨α, hk.mem hακ, ZF.exists_compositionInjection hZF I hj hq, eqK ▸ (ep z).mp (all z hzT) α C hza hzC⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 集合的标准 Borel 秩

Bsr(K,α) 表示 α 是 K 所属 Σ⁰α 或 Π⁰α 的最小阶数，从一开始计数。
它只依赖集合 K；与具体码的根树秩 Bcr 分开。有码集合在 ZF 中有唯一可数秩。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Blev_d (ω S B α K : M.Domain) : Prop := Bsig_d I ω S B α K ∨ Bpi_d I ω S B α K
def blev_m {d} (ω S B α K : Term d) : Formula 1 d := .disj
  (bsig_m (𝒞 := 𝒞) ω S B α K) (bpi_m (𝒞 := 𝒞) ω S B α K)
derive_free_closed blev_m
theorem blev_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω S B α K : Term d) :
    Formula.satisfies ρ (blev_m (𝒞 := 𝒞) ω S B α K) ↔ Blev_d I (ω.eval ρ) (S.eval ρ) (B.eval ρ) (α.eval ρ) (K.eval ρ) := by
  simp only [blev_m, Blev_d, Formula.satisfies_disj_iff, bsig_sat_l I hE, bpi_sat_l I hE]
theorem blev_ordinal_l {ω S B α K} (h : Blev_d I ω S B α K) : M.IsOrdinal α :=
  h.elim (bsig_ordinal_l I) (fun ⟨_, h, _⟩ => bsig_ordinal_l I h)
theorem blev_nonempty_l {ω S B α K} (h : Blev_d I ω S B α K) : ∃ β, M.mem β α :=
  h.elim (bsig_nonempty_l I) (fun ⟨_, h, _⟩ => bsig_nonempty_l I h)
theorem blev_subset_l {ω S B α K} (h : Blev_d I ω S B α K) : M.MemberSubset K B :=
  h.elim (bsig_subset_l I) (bpi_subset_l I)

def Bsr_d (ω S B K α : M.Domain) : Prop := Blev_d I ω S B α K ∧
  ∀ β, Blev_d I ω S B β K → M.MemberSubset α β
def bsr_m {d} (ω S B K α : Term d) : Formula 1 d := .conj (blev_m (𝒞 := 𝒞) ω S B α K)
  (.forallE (.imp (blev_m (𝒞 := 𝒞) ω.weaken S.weaken B.weaken .newest K.weaken) (Formula.subset α.weaken .newest)))
derive_free_closed bsr_m
theorem bsr_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω S B K α : Term d) :
    Formula.satisfies ρ (bsr_m (𝒞 := 𝒞) ω S B K α) ↔ Bsr_d I (ω.eval ρ) (S.eval ρ) (B.eval ρ) (K.eval ρ) (α.eval ρ) := by
  simp only [bsr_m, Bsr_d, Formula.satisfies_conj_iff, blev_sat_l I hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl
theorem bsr_unique_l (hE : Extensional M) {ω S B K α β} (h : Bsr_d I ω S B K α) (k : Bsr_d I ω S B K β) : α = β :=
  hE.eq_of_same_members α β (fun x => ⟨h.2 β k.1 x, k.2 α h.1 x⟩)

/-- 最小化发生在内部序数的实际分离子集上，而非外部良序归纳。 -/
theorem bsr_min_l (hZF : M.Models ZF) {ω S B K β} (hb : Blev_d I ω S B β K) :
    ∃ α, Bsr_d I ω S B K α ∧ M.MemberSubset α β := by
  obtain ⟨δ, hd⟩ := KP.exists_successor (ZF.modelsKP hZF) β
  have hδ := KP.successor_isOrdinal (ZF.modelsKP hZF) (blev_ordinal_l I hb) hd
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push S).push B).push K
  let φ : UnarySchema 4 := { body := blev_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) .newest (.bound 1) }
  obtain ⟨C, hc⟩ := ZF.separation_exists_d hZF φ ρ δ
  have ec γ : M.mem γ C ↔ M.mem γ δ ∧ Blev_d I ω S B γ K :=
    (hc γ).trans (and_congr_right fun _ => blev_sat_l I hZF.1 _ _ _ _ _ _)
  obtain ⟨α, ha, least⟩ := hδ.wellOrder.least C (fun γ h => ((ec γ).mp h).1)
    ⟨β, (ec β).mpr ⟨hd.predecessor_mem, hb⟩⟩
  obtain ⟨haδ, level⟩ := (ec α).mp ha
  have low γ (hγ : Blev_d I ω S B γ K) : M.MemberSubset α γ := by
    have hα := blev_ordinal_l I level
    have hγo := blev_ordinal_l I hγ
    rcases Structure.IsOrdinal.trichotomy hZF.1 hα hγo (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) α γ) with e | e | e
    · exact fun x hx => (e x).mp hx
    · exact hγo.transitive.memberSubset e
    · rcases least γ ((ec γ).mpr ⟨hδ.transitive α haδ γ e, hγ⟩) with he | he
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) γ (hZF.1.eq_of_same_members α γ he ▸ e)).elim
      · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) α (hα.transitive γ e α he)).elim
  exact ⟨α, ⟨level, low⟩, low β hb⟩

theorem bsr_exists_l (hZF : M.Models ZF) {ω X A S B K} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hc : M.CardinalLessOrEqual I A ω) (hK : Borel_d I ω A S B K) :
    ∃ α, M.IsOrdinal α ∧ M.CardinalLessOrEqual I α ω ∧ Bsr_d I ω S B K α ∧
      ∀ β, Bsr_d I ω S B K β → β = α := by
  obtain ⟨c, ht, hd⟩ := hK
  obtain ⟨β, _, ⟨E, he⟩, hb, _⟩ := bcode_level_l I hZF hω hB hS hc ht hd
  obtain ⟨α, ha, sub⟩ := bsr_min_l I hZF (Or.inl hb)
  obtain ⟨D, hd⟩ := ZF.exists_inclusionInjection hZF I sub
  exact ⟨α, blev_ordinal_l I ha.1, ZF.exists_compositionInjection hZF I hd he, ha, fun β h => bsr_unique_l I hZF.1 h ha⟩

theorem blev_compl_l (hE : Extensional M) {ω S B α K L} (sub : M.MemberSubset K B) (hc : Cm_d B K L) :
    Blev_d I ω S B α L ↔ Blev_d I ω S B α K :=
  (or_congr (bsig_compl_l I hE sub hc) (bpi_compl_l I hE sub hc)).trans or_comm
theorem bsr_compl_l (hE : Extensional M) {ω S B α K L} (sub : M.MemberSubset K B) (hc : Cm_d B K L) :
    Bsr_d I ω S B L α ↔ Bsr_d I ω S B K α := by
  exact and_congr (blev_compl_l I hE sub hc) (forall_congr' fun β => imp_congr_left (blev_compl_l I hE sub hc))

/-- 秩一表示开或闭；并不要求既开又闭。 -/
theorem bsr_one_l (hZF : M.Models ZF) {ω S B o K} (ho : M.IsOrdinalOne o) :
    Bsr_d I ω S B K o ↔ Open_d S B K ∨ Cl_d S B K := by
  constructor
  · exact fun h => (or_congr (bsig_one_l I hZF ho) (bpi_one_l I hZF ho)).mp h.1
  · intro h
    refine ⟨(or_congr (bsig_one_l I hZF ho) (bpi_one_l I hZF ho)).mpr h, fun β hb x hx => ?_⟩
    obtain ⟨z, hz, hs⟩ := ho
    rcases (hs x).mp hx with hx | hx
    · exact (hz x hx).elim
    · exact hZF.1.eq_of_same_members z x (fun y => (hx y).symm) ▸
        (blev_ordinal_l I hb).empty_mem_of_nonempty (ZF.modelsKP hZF) (blev_nonempty_l I hb) hz

end YesMetaZFC.SetTheory.Descriptive

/-! ## 与通常 Borel 层级递归的对应

可数开闭基把开集规范地写成可数个闭柱集的并。
所以 α > 1 时，Σ⁰α 恰为较低 Π 层的可数并；尤其 Σ⁰₂ 恰为 Fσ。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem open_closed_union_l (hZF : M.Models ZF) {ω X S B K} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hc : M.CardinalLessOrEqual I S ω) (ho : Open_d S B K) :
    ∃ H, Bu_d I ω H K ∧ ∀ i C, M.PairMember I i C H → Cl_d S B C := by
  obtain ⟨E, he⟩ := hc
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF B
  obtain ⟨W, hw⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) ω P
  let ρ : Env M 4 := (((⟨fun _ => S, fun _ => S⟩ : Env M 1).push E).push B).push K
  let φ : BinarySchema 4 := { body := Formula.existsMem (.bound 5) (.conj
    (Formula.orderedPairMem 𝒞 .newest (.bound 2) (.bound 5)) (.conj
    (bcover_m (.bound 4) (.bound 3) .newest) (cyl_m (.bound 4) .newest (.bound 1)))) }
  have ep i C : φ.denote ρ i C ↔ ∃ s, M.mem s S ∧ M.PairMember I s i E ∧ Bcover_d B K s ∧ Cyl_d B s C := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, bcover_sat_l, cyl_sat_l]; rfl
  obtain ⟨H, hh, eh⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  have pair i C : M.PairMember I i C H ↔ ∃ s, M.mem s S ∧ M.PairMember I s i E ∧ Bcover_d B K s ∧ Cyl_d B s C := by
    refine ((eh i C).trans (and_congr_right fun _ => and_congr_right fun _ => ep i C)).trans ⟨fun h => h.2.2, ?_⟩
    rintro ⟨s, hs, hi, hk, hC⟩
    exact ⟨(hw i).mpr (Or.inl (he.1.output_mem_of_pairMember hi)),
      (hw C).mpr (Or.inr ((hp C).mpr (fun x hx => ((hC x).mp hx).1))), s, hs, hi, hk, hC⟩
  refine ⟨H, ⟨⟨hh.1, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro i C D hc hd
    obtain ⟨s, _, hi, _, hC⟩ := (pair i C).mp hc
    obtain ⟨t, _, hj, _, hD⟩ := (pair i D).mp hd
    have e := he.2 t s i hj hi
    exact hZF.1.eq_of_same_members C D (fun x => (hC x).trans (e ▸ hD x).symm)
  · intro i C h
    obtain ⟨_, _, hi, _, _⟩ := (pair i C).mp h
    exact he.1.output_mem_of_pairMember hi
  · intro x
    constructor
    · intro hx
      obtain ⟨s, hs, sub, cover⟩ := ho.2 x hx
      obtain ⟨C, hC⟩ := cyl_exists_l (ZF.modelsKP hZF) B s
      obtain ⟨i, _, hi⟩ := he.1.2.2 s hs
      exact ⟨i, C, (pair i C).mpr ⟨s, hs, hi, cover, hC⟩, (hC x).mpr ⟨ho.1 x hx, sub⟩⟩
    · rintro ⟨i, C, hi, hx⟩
      obtain ⟨s, _, _, cover, hC⟩ := (pair i C).mp hi
      exact cover x ((hC x).mp hx).1 ((hC x).mp hx).2
  · intro i C hi
    obtain ⟨s, hs, _, _, hC⟩ := (pair i C).mp hi
    obtain ⟨ho, hc⟩ := ds_cyl_clopen_l I hZF hω hB hS hs hC
    exact ⟨ho.1, hc⟩

/-- 正序数大于一时的标准递归方程；包括内部极限序数。 -/
theorem bsig_standard_l (hZF : M.Models ZF) {ω X S B o α K} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hc : M.CardinalLessOrEqual I S ω) (ho : M.IsOrdinalOne o) (hα : M.IsOrdinal α) (hoα : M.mem o α) :
    Bsig_d I ω S B α K ↔ ∃ H, Bu_d I ω H K ∧
      ∀ i C, M.PairMember I i C H → ∃ β, M.mem β α ∧ Bpi_d I ω S B β C := by
  constructor
  · intro h
    obtain ⟨_, _, hopen | h⟩ := (bsig_unfold_l I hZF hα).mp h
    · obtain ⟨H, hu, eh⟩ := open_closed_union_l I hZF hω hB hS hc hopen
      exact ⟨H, hu, fun i C hi => ⟨o, hoα, (bpi_one_l I hZF ho).mpr (eh i C hi)⟩⟩
    · exact h
  · exact fun ⟨H, hu, eh⟩ => bsig_union_l I hZF hα ⟨o, hoα⟩ hu eh

theorem bsig_two_l (hZF : M.Models ZF) {ω X S B o t K} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω X) (hS : Fseq_space_d I ω X S)
    (hc : M.CardinalLessOrEqual I S ω) (ho : M.IsOrdinalOne o) (ht : M.SuccessorOf t o) :
    Bsig_d I ω S B t K ↔ ∃ H, Bu_d I ω H K ∧ ∀ i C, M.PairMember I i C H → Cl_d S B C := by
  have htord := KP.successor_isOrdinal (ZF.modelsKP hZF) (KP.ordinalOne_isOrdinal (ZF.modelsKP hZF) ho) ht
  refine (bsig_standard_l I hZF hω hB hS hc ho htord ht.predecessor_mem).trans (exists_congr fun H => and_congr_right fun _ =>
    forall_congr' fun i => forall_congr' fun C => imp_congr_right fun _ => ⟨?_, ?_⟩)
  · rintro ⟨β, hb, hpi⟩
    rcases (ht β).mp hb with hb | hb
    · obtain ⟨z, hz, hs⟩ := ho
      rcases (hs β).mp hb with hb | hb
      · exact (hz β hb).elim
      · obtain ⟨L, hl, _⟩ := hpi
        obtain ⟨γ, hγ⟩ := bsig_nonempty_l I hl
        exact (hz γ (hZF.1.eq_of_same_members β z hb ▸ hγ)).elim
    · exact (bpi_one_l I hZF ho).mp (hZF.1.eq_of_same_members β o hb ▸ hpi)
  · exact fun h => ⟨o, ht.predecessor_mem, (bpi_one_l I hZF ho).mpr h⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 标准 Borel 层级与秩的子空间限制

内部可数族逐项取迹有唯一实际函数图。沿内部序数归纳得到 Σ、Π 不升层，
故子空间中的标准秩不超过原秩；子空间无需闭、解析或有任何额外选择性质。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem bu_trace_l (hZF : M.Models ZF) {ω X H K L} (hu : Bu_d I ω H K) (ht : Tr_d X K L) :
    ∃ G, Bu_d I ω G L ∧ ∀ i D, M.PairMember I i D G ↔ ∃ C, M.PairMember I i C H ∧ Tr_d X C D := by
  obtain ⟨P, hp⟩ := ZF.exists_powerSet hZF X
  obtain ⟨W, hw⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) ω P
  let ρ : Env M 2 := (⟨fun _ => X, fun _ => X⟩ : Env M 1).push H
  let φ : BinarySchema 2 := { body := .existsE (.conj
    (Formula.orderedPairMem 𝒞 (.bound 2) .newest (.bound 3)) (tr_m (.bound 4) .newest (.bound 1))) }
  have ep i D : φ.denote ρ i D ↔ ∃ C, M.PairMember I i C H ∧ Tr_d X C D := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, tr_sat_l]; rfl
  obtain ⟨G, hg, eg⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ W
  have pair i D : M.PairMember I i D G ↔ ∃ C, M.PairMember I i C H ∧ Tr_d X C D := by
    refine ((eg i D).trans (and_congr_right fun _ => and_congr_right fun _ => ep i D)).trans ⟨fun h => h.2.2, ?_⟩
    rintro ⟨C, hi, hd⟩
    exact ⟨(hw i).mpr (Or.inl (hu.2.1 i C hi)), (hw D).mpr (Or.inr ((hp D).mpr (fun x hx => ((hd x).mp hx).1))), C, hi, hd⟩
  refine ⟨G, ⟨⟨hg.1, ?_⟩, ?_, ?_⟩, pair⟩
  · intro i C D hc hd
    obtain ⟨V, hi, hv⟩ := (pair i C).mp hc
    obtain ⟨U, hj, hw⟩ := (pair i D).mp hd
    exact tr_unique_l hZF.1 hv (hu.1.2 i U V hj hi ▸ hw)
  · intro i D hd
    obtain ⟨C, hi, _⟩ := (pair i D).mp hd
    exact hu.2.1 i C hi
  · intro x
    constructor
    · intro hx
      obtain ⟨hxX, hxK⟩ := (ht x).mp hx
      obtain ⟨i, C, hi, hxC⟩ := (hu.2.2 x).mp hxK
      obtain ⟨D, hd⟩ := tr_exists_l (ZF.modelsKP hZF) X C
      exact ⟨i, D, (pair i D).mpr ⟨C, hi, hd⟩, (hd x).mpr ⟨hxX, hxC⟩⟩
    · rintro ⟨i, D, hi, hx⟩
      obtain ⟨C, hi, hd⟩ := (pair i D).mp hi
      obtain ⟨hxX, hxC⟩ := (hd x).mp hx
      exact (ht x).mpr ⟨hxX, (hu.2.2 x).mpr ⟨i, C, hi, hxC⟩⟩

theorem bh_trace_l (hZF : M.Models ZF) {ω S B X α} (hX : M.MemberSubset X B) (hα : M.IsOrdinal α) :
    ∀ K L, Tr_d X K L →
      (Bsig_d I ω S B α K → Bsig_d I ω S X α L) ∧
      (Bpi_d I ω S B α K → Bpi_d I ω S X α L) := by
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push S).push B).push X
  let φ : UnarySchema 4 := { body := .forallE (.forallE (.imp (tr_m (.bound 3) (.bound 1) .newest) (.conj
    (.imp (bsig_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 1))
      (bsig_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 3) (.bound 2) .newest))
    (.imp (bpi_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 2) (.bound 1))
      (bpi_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 3) (.bound 2) .newest))))) }
  have ep β : φ.denote ρ β ↔ ∀ K L, Tr_d X K L →
      (Bsig_d I ω S B β K → Bsig_d I ω S X β L) ∧ (Bpi_d I ω S B β K → Bpi_d I ω S X β L) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      tr_sat_l, Formula.satisfies_conj_iff, bsig_sat_l I hZF.1, bpi_sat_l I hZF.1]; rfl
  apply (ep α).mp
  apply hα.induction (φ.denote ρ)
  · obtain ⟨C, hc⟩ := ZF.separation_exists_d hZF φ.neg ρ α
    exact ⟨C, fun β => by simpa only [UnarySchema.neg, UnarySchema.denote, Formula.satisfies_neg_iff] using hc β⟩
  · intro β hβ ih
    have sig K L (ht : Tr_d X K L) (hs : Bsig_d I ω S B β K) : Bsig_d I ω S X β L := by
      obtain ⟨_, ne, ho | ⟨H, hu, eh⟩⟩ := (bsig_unfold_l I hZF hβ).mp hs
      · apply bsig_open_l I hZF hβ ne
        refine ⟨fun x hx => ((ht x).mp hx).1, fun x hx => ?_⟩
        obtain ⟨s, hs, sub, cover⟩ := ho.2 x ((ht x).mp hx).2
        exact ⟨s, hs, sub, fun y hy hsy => (ht y).mpr ⟨hy, cover y (hX y hy) hsy⟩⟩
      · obtain ⟨G, hg, eg⟩ := bu_trace_l I hZF hu ht
        apply bsig_union_l I hZF hβ ne hg
        intro i D hi
        obtain ⟨C, hc, tr⟩ := (eg i D).mp hi
        obtain ⟨γ, hγ, hpi⟩ := eh i C hc
        exact ⟨γ, hγ, ((ep γ).mp (ih γ hγ) C D tr).2 hpi⟩
    apply (ep β).mpr
    intro K L ht
    refine ⟨sig K L ht, fun ⟨C, hc, cm⟩ => ?_⟩
    obtain ⟨D, hd⟩ := tr_exists_l (ZF.modelsKP hZF) X C
    exact ⟨D, sig C D hd hc, tr_compl_l hX cm hd ht⟩

theorem bsr_trace_l (hZF : M.Models ZF) {ω S B X K L α} (hX : M.MemberSubset X B)
    (ht : Tr_d X K L) (hr : Bsr_d I ω S B K α) :
    ∃ β, Bsr_d I ω S X L β ∧ M.MemberSubset β α := by
  have tr := bh_trace_l I hZF (ω := ω) (S := S) hX (blev_ordinal_l I hr.1) K L ht
  exact bsr_min_l I hZF (hr.1.elim (fun h => Or.inl (tr.1 h)) (fun h => Or.inr (tr.2 h)))

/-- 一个码在任意内部子空间的解释同样具有唯一的内部可数标准秩。 -/
theorem bsr_relative_exists_l (hZF : M.Models ZF) {ω D A S B X K} (hω : M.IsOmega ω)
    (hB : M.IsFunctionSpace I B ω D) (hS : Fseq_space_d I ω D S)
    (hc : M.CardinalLessOrEqual I A ω) (hX : M.MemberSubset X B) (hK : Borel_d I ω A S X K) :
    ∃ α, M.IsOrdinal α ∧ M.CardinalLessOrEqual I α ω ∧ Bsr_d I ω S X K α ∧
      ∀ β, Bsr_d I ω S X K β → β = α := by
  obtain ⟨c, code, den⟩ := hK
  obtain ⟨C, hcC, _⟩ := bden_exists_unique_l I hZF ω A S B c
  have tr : Tr_d X C K := by
    intro x
    exact (den x).trans (and_congr_right fun hx =>
      ⟨fun h => (hcC x).mpr ⟨hX x hx, h⟩, fun h => ((hcC x).mp h).2⟩)
  obtain ⟨β, _, ⟨E, he⟩, hb, _⟩ := bsr_exists_l I hZF hω hB hS hc ⟨c, code, hcC⟩
  obtain ⟨α, ha, sub⟩ := bsr_trace_l I hZF hX tr hb
  obtain ⟨D, hd⟩ := ZF.exists_inclusionInjection hZF I sub
  exact ⟨α, blev_ordinal_l I ha.1, ZF.exists_compositionInjection hZF I hd he, ha, fun β h => bsr_unique_l I hZF.1 h ha⟩

end YesMetaZFC.SetTheory.Descriptive
