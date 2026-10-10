import YesMetaZFC.SetTheory.Descriptive.Path
import YesMetaZFC.SetTheory.Collapse.RelationSyntax

/-! # 模型内部前缀树与闭集

树是全部内部有限列中对前缀封闭的集合。分支为模型内部无限列；树体是实际
集合且闭，反过来每个闭集由其可延伸前缀树精确表示，允许模型的 ω 非标准。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Tree_d (S T : M.Domain) : Prop := M.MemberSubset T S ∧
  ∀ s, M.mem s T → ∀ t, M.mem t S → M.MemberSubset t s → M.mem t T
def tree_m {d} (S T : Term d) : Formula 1 d := .conj (Formula.subset T S)
  (Formula.forallMem T (Formula.forallMem S.weaken
    (.imp (Formula.subset .newest (.bound 1)) (.mem .newest T.weaken.weaken))))
derive_free_closed tree_m

theorem tree_sat_l {d} (ρ : Env M d) (S T : Term d) :
    Formula.satisfies ρ (tree_m S T) ↔ Tree_d (M := M) (S.eval ρ) (T.eval ρ) := by
  simp only [tree_m, Tree_d, Formula.satisfies_conj_iff, Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Definitional.Term.eval_weaken]; rfl

def Branch_d (S T f : M.Domain) : Prop := ∀ s, M.mem s S → M.MemberSubset s f → M.mem s T
def branch_m {d} (S T f : Term d) : Formula 1 d := Formula.forallMem S
  (.imp (Formula.subset .newest f.weaken) (.mem .newest T.weaken))
derive_free_closed branch_m
theorem branch_sat_l {d} (ρ : Env M d) (S T f : Term d) :
    Formula.satisfies ρ (branch_m S T f) ↔ Branch_d (M := M) (S.eval ρ) (T.eval ρ) (f.eval ρ) := by
  simp only [branch_m, Branch_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]; rfl

def Body_d (S B T K : M.Domain) : Prop := ∀ f, M.mem f K ↔ M.mem f B ∧ Branch_d S T f
def body_m {d} (S B T K : Term d) : Formula 1 d := .forallE (.iff (.mem .newest K.weaken)
  (.conj (.mem .newest B.weaken) (branch_m S.weaken T.weaken .newest)))
derive_free_closed body_m
theorem body_sat_l {d} (ρ : Env M d) (S B T K : Term d) :
    Formula.satisfies ρ (body_m S B T K) ↔ Body_d (M := M) (S.eval ρ) (B.eval ρ) (T.eval ρ) (K.eval ρ) := by
  simp only [body_m, Body_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, branch_sat_l, Definitional.Term.eval_weaken]; rfl

/-- 按全部前缀定义的分支，等价于每个内部长度都有树内前缀。 -/
theorem tree_branch_l (hZF : M.Models ZF) {ω X S T f} (hω : M.IsOmega ω)
    (hS : Fseq_space_d I ω X S) (hf : M.IsSetFunctionFromTo I f ω X) :
    Branch_d S T f ↔ ∀ n, M.mem n ω → ∃ s, M.mem s T ∧ M.IsRestrictionOf I s f n := by
  constructor
  · intro h n hn
    obtain ⟨s, hs, hr, _⟩ := ds_prefix_l I hZF hω hf hn
    exact ⟨s, h s ((hS s).mpr ⟨n, hn, hs⟩) ((ds_restrict_iff_l I hs hf.1).mp hr), hr⟩
  · intro h s hs hsf
    obtain ⟨n, hn, hs⟩ := (hS s).mp hs
    obtain ⟨t, ht, hr⟩ := h n hn
    exact (((ds_restrict_iff_l I hs hf.1).mpr hsf).eq hZF.1 hr).symm ▸ ht

theorem tree_body_exists_l (hKP : M.Models KP) (S B T : M.Domain) : ∃ K, Body_d S B T K := by
  let ρ : Env M 2 := (⟨fun _ => S, fun _ => S⟩ : Env M 1).push T
  let φ : Delta0UnarySchema 2 := {
    body := branch_m (.bound 2) (.bound 1) .newest
    delta0 := .forallMem _ (.imp (.atom _ _ _) (.mem _ _)) }
  obtain ⟨K, hK⟩ := KP.separation_exists_d hKP φ ρ B
  exact ⟨K, fun f => (hK f).trans (and_congr_right fun _ => branch_sat_l _ _ _ _)⟩

theorem tree_body_unique_l (hE : Extensional M) {S B T K L : M.Domain}
    (hK : Body_d S B T K) (hL : Body_d S B T L) : K = L :=
  hE.eq_of_same_members K L (fun f => (hK f).trans (hL f).symm)

/-- 树体的相对补开；不在树内的一个有限前缀即为开邻域见证。 -/
theorem tree_body_closed_l (hKP : M.Models KP) {S B T K : M.Domain} (hK : Body_d S B T K) :
    ∃ U, (∀ f, M.mem f U ↔ M.mem f B ∧ ¬ M.mem f K) ∧ Open_d S B U := by
  classical
  obtain ⟨U, hU⟩ := KP.difference_exists_d hKP K B
  refine ⟨U, hU, fun f hf => ((hU f).mp hf).1, fun f hf => ?_⟩
  obtain ⟨hfB, hfK⟩ := (hU f).mp hf
  have bad : ∃ s, M.mem s S ∧ M.MemberSubset s f ∧ ¬ M.mem s T := by
    apply Classical.byContradiction
    intro h
    exact hfK ((hK f).mpr ⟨hfB, fun s hs hsf => Classical.byContradiction (fun hn => h ⟨s, hs, hsf, hn⟩)⟩)
  obtain ⟨s, hs, hsf, hst⟩ := bad
  exact ⟨s, hs, hsf, fun g hg hsg => (hU g).mpr ⟨hg, fun hgK => hst (((hK g).mp hgK).2 s hs hsg)⟩⟩

def Ktree_d (S K T : M.Domain) : Prop := ∀ s,
  M.mem s T ↔ M.mem s S ∧ ∃ f, M.mem f K ∧ M.MemberSubset s f
def ktree_m {d} (S K T : Term d) : Formula 1 d := .forallE (.iff (.mem .newest T.weaken)
  (.conj (.mem .newest S.weaken) (Formula.existsMem K.weaken (Formula.subset (.bound 1) .newest))))
derive_free_closed ktree_m

theorem ktree_sat_l {d} (ρ : Env M d) (S K T : Term d) :
    Formula.satisfies ρ (ktree_m S K T) ↔ Ktree_d (M := M) (S.eval ρ) (K.eval ρ) (T.eval ρ) := by
  simp only [ktree_m, Ktree_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

theorem ktree_exists_l (hKP : M.Models KP) (S K : M.Domain) : ∃ T, Ktree_d S K T := by
  let ρ : Env M 1 := ⟨fun _ => K, fun _ => K⟩
  let φ : Delta0UnarySchema 1 := {
    body := Formula.existsMem (.bound 1) (Formula.subset (.bound 1) .newest)
    delta0 := .existsMem _ (.atom _ _ _) }
  obtain ⟨T, hT'⟩ := KP.separation_exists_d hKP φ ρ S
  refine ⟨T, fun s => ?_⟩
  simpa only [φ, Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff] using! hT' s

theorem ktree_unique_l (hE : Extensional M) {S K T U : M.Domain} (h : Ktree_d S K T) (k : Ktree_d S K U) : T = U :=
  hE.eq_of_same_members T U (fun s => (h s).trans (k s).symm)

/-- 任意闭集由唯一的规范前缀树表示，同时返回其原公式刻画。 -/
theorem tree_of_closed_l (hKP : M.Models KP) {S B K U : M.Domain} (hKB : M.MemberSubset K B)
    (hU : ∀ f, M.mem f U ↔ M.mem f B ∧ ¬ M.mem f K) (ho : Open_d S B U) :
    ∃ T, Ktree_d S K T ∧ Tree_d S T ∧ Body_d S B T K := by
  obtain ⟨T, hT⟩ := ktree_exists_l hKP S K
  refine ⟨T, hT, ⟨fun s hs => ((hT s).mp hs).1, fun s hs t ht hts => ?_⟩, fun f => ⟨?_, ?_⟩⟩
  · obtain ⟨_, f, hf, hsf⟩ := (hT s).mp hs
    exact (hT t).mpr ⟨ht, f, hf, fun p hp => hsf p (hts p hp)⟩
  · intro hf
    exact ⟨hKB f hf, fun s hs hsf => (hT s).mpr ⟨hs, f, hf, hsf⟩⟩
  · rintro ⟨hf, hb⟩
    apply Classical.byContradiction
    intro hn
    obtain ⟨s, hs, hsf, hu⟩ := ho.2 f ((hU f).mpr ⟨hf, hn⟩)
    obtain ⟨_, g, hg, hsg⟩ := (hT s).mp (hb s hs hsf)
    exact ((hU g).mp (hu g (hKB g hg) hsg)).2 hg

def Edge_d (ω T R : M.Domain) : Prop :=
  (∀ p, M.mem p R → ∃ a b, KPair_d M p a b) ∧ ∀ s t,
    Rd_entry_d t s R ↔ M.mem s T ∧ M.mem t T ∧ Step_d I ω s t
def edge_m {d} (ω T R : Term d) : Formula 1 d := .conj (Formula.isRelation kpair_convention_l R) (.forallE (.forallE
  (.iff (rd_entry_m .newest (.bound 1) R.weaken.weaken) (.conj (.mem (.bound 1) T.weaken.weaken)
    (.conj (.mem .newest T.weaken.weaken) (step_m (𝒞 := 𝒞) ω.weaken.weaken (.bound 1) .newest))))))
derive_free_closed edge_m
theorem edge_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω T R : Term d) :
    Formula.satisfies ρ (edge_m (𝒞 := 𝒞) ω T R) ↔ Edge_d I (ω.eval ρ) (T.eval ρ) (R.eval ρ) := by
  simp only [edge_m, Edge_d, Formula.isRelation, kpair_convention_l,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, kpair_sat_l M hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    rd_entry_sat_l hE, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    step_sat_l I hE, Definitional.Term.eval_weaken]; rfl

/-- 子节点指向父节点，固定为既有内部良基接口使用的 Kuratowski 关系码。 -/
theorem tree_edges_l (hZF : M.Models ZF) (ω T : M.Domain) : ∃ R, Edge_d I ω T R := by
  let φ : BinarySchema 1 := { body := step_m (𝒞 := 𝒞) (.bound 2) .newest (.bound 1) }
  obtain ⟨R, hr, hR⟩ := ZF.exists_setRelationOn_of_denote hZF (kp_pair_l (ZF.modelsKP hZF)) φ
    ⟨fun _ => ω, fun _ => ω⟩ T
  refine ⟨R, hr.1, fun s t => ?_⟩
  have h := (hR t s).trans (and_congr_right fun _ => and_congr_right fun _ => step_sat_l I hZF.1 _ _ _ _)
  exact h.trans ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

theorem tree_step_not_empty_l {ω s e : M.Domain} (he : ∀ p, ¬ M.mem p e) : ¬ Step_d I ω s e := by
  rintro ⟨a, n, m, h⟩
  obtain ⟨p, _, hp⟩ := h.last_value
  exact he p hp

theorem tree_edges_unique_l (hE : Extensional M) {ω T R Q}
    (h : Edge_d I ω T R) (k : Edge_d I ω T Q) : R = Q := by
  have incl {R Q} (h : Edge_d I ω T R) (k : Edge_d I ω T Q) : M.MemberSubset R Q := by
    intro p hp
    obtain ⟨a, b, hc⟩ := h.1 p hp
    obtain ⟨q, hq, hqQ⟩ := (k.2 b a).mpr ((h.2 b a).mp ⟨p, hc, hp⟩)
    exact (kpair_unique_l M hE hc hq).symm ▸ hqQ
  exact hE.eq_of_same_members R Q (fun p => ⟨incl h k p, incl k h p⟩)

end YesMetaZFC.SetTheory.Descriptive
