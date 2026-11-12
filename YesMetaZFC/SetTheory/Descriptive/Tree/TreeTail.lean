import YesMetaZFC.SetTheory.Descriptive.Topology.Topology
import YesMetaZFC.SetTheory.Card.FiniteSequenceEnd
import YesMetaZFC.SetTheory.CountableChain
import YesMetaZFC.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.Collapse.RelationSyntax
import YesMetaZFC.SetTheory.InnerModel.Recursion.Graph

/-! # 内部逐项延拓的分支

在实际后继函数图上沿内部 ω 迭代，再取前缀图的并。长度归纳使用原公式，
递增性复用内部关系链；不把非标准长度转成外部递归。取并本身无需选择，
既可消费实际后继函数的迭代，也可消费依赖选择已经给出的内部链。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Step_d (ω s t : M.Domain) : Prop := ∃ a, Fseq_end_d I ω t s a
def step_m {d} (ω s t : Term d) : Formula 1 d :=
  .existsE (fseq_end_m (𝒞 := 𝒞) ω.weaken t.weaken s.weaken .newest)
derive_free_closed step_m

theorem step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω s t : Term d) :
    Formula.satisfies ρ (step_m (𝒞 := 𝒞) ω s t) ↔ Step_d I (ω.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [step_m, Step_d, Formula.satisfies_exists_iff, fseq_end_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem ds_empty_fun_l {e X : M.Domain} (he : ∀ x, ¬ M.mem x e) : M.IsSetFunctionFromTo I e e X :=
  ⟨⟨fun p hp => (he p hp).elim, fun _ _ _ h => (h.elim fun p hp => he p hp.2).elim⟩,
    fun i => ⟨fun hi => (he i hi).elim, fun ⟨_, p, _, hp⟩ => (he p hp).elim⟩,
    fun i hi => (he i hi).elim⟩

/-- 追加图在旧定义域保留原值，在新坐标取指定值。 -/
theorem ds_append_sub_l (hE : Extensional M) {ω s t n X f a}
    (hs : M.IsSetFunctionFromTo I s n X) (ht : Fseq_end_d I ω t s a)
    (hsf : M.MemberSubset s f) (hfa : M.PairMember I n a f) : M.MemberSubset t f := by
  obtain ⟨j, k, ht⟩ := ht
  have e := ht.prefix_sequence.2.2.2.eq hE hs.2.1
  subst k
  intro p hp
  obtain ⟨i, x, hc⟩ := ht.source.2.2.1.1 p hp
  have hx : M.PairMember I i x t := ⟨p, hc, hp⟩
  have hi := (ht.source.2.2.2 i).mpr ⟨x, hx⟩
  have hfx : M.PairMember I i x f := by
    rcases (ht.length_successor i).mp hi with hi | hi
    · exact ((ht.prefix_restriction.2 i x).mpr ⟨hi, hx⟩).elim fun q hq => ⟨q, hq.1, hsf q hq.2⟩
    · have e := hE.eq_of_same_members i n hi
      subst i
      exact ht.source.2.2.1.2 n a x ht.last_value hx ▸ hfa
  obtain ⟨q, hq, hqf⟩ := hfx
  exact (I.unique hc hq).symm ▸ hqf

/-- 内部逐项延长链在第 n 步恰有长度 n。 -/
theorem ds_path_length_l (hZF : M.Models ZF) {ω X T H e} (hω : M.IsOmega ω)
    (hT : ∀ s, M.mem s T → ∃ n, M.mem n ω ∧ M.IsSetFunctionFromTo I s n X)
    (hH : M.IsSetFunctionFromTo I H ω T) (he : ∀ x, ¬ M.mem x e)
    (hz : ∀ o, (∀ x, ¬ M.mem x o) → M.PairMember I o e H)
    (hnext : ∀ i j s t, M.SuccessorOf j i → M.PairMember I i s H →
      M.PairMember I j t H → Step_d I ω s t) :
    ∀ n, M.mem n ω → ∀ s, M.PairMember I n s H → M.IsSetFunctionFromTo I s n X := by
  let ρ : Env M 2 := (⟨fun _ => X, fun _ => X⟩ : Env M 1).push H
  let φ : UnarySchema 2 := { body := .forallE (.imp
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (Formula.isFunctionFromTo 𝒞 .newest (.bound 1) (.bound 3))) }
  have hp n : φ.denote ρ n ↔ ∀ s, M.PairMember I n s H → M.IsSetFunctionFromTo I s n X := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isFunctionFromTo_iff I hZF.1]; rfl
  apply hω.induction (fun n => ∀ s, M.PairMember I n s H → M.IsSetFunctionFromTo I s n X)
  · obtain ⟨A, hA⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨A, fun n => (hA n).trans (and_congr_right fun _ => hp n)⟩
  · intro o ho s hs
    have eo := hZF.1.eq_of_same_members e o (fun x => iff_of_false (he x) (ho x))
    have es := hH.1.2 o e s (hz o ho) hs
    subst s o
    exact ds_empty_fun_l I he
  · intro n hn ih j hj t ht
    obtain ⟨s, _, hs⟩ := hH.2.2 n hn
    obtain ⟨a, k, m, h⟩ := hnext n j s t hj hs ht
    have em := h.prefix_sequence.2.2.2.eq hZF.1 (ih s hs).2.1
    subst m
    have ek := Structure.SuccessorOf.eq hZF.1 h.length_successor hj
    subst k
    obtain ⟨r, _, hr⟩ := hT t (hH.output_mem_of_pairMember ht)
    have er := hr.2.1.eq hZF.1 h.source.2.2.2
    exact er ▸ hr

/-- 从空列出发的内部逐项延长链取并，得到贯穿全部内部长度的分支。 -/
theorem ds_path_run_l (hZF : M.Models ZF) {ω X T H e} (hω : M.IsOmega ω)
    (hT : ∀ s, M.mem s T → ∃ n, M.mem n ω ∧ M.IsSetFunctionFromTo I s n X)
    (hH : M.IsSetFunctionFromTo I H ω T) (he : ∀ x, ¬ M.mem x e)
    (hz : ∀ o, (∀ x, ¬ M.mem x o) → M.PairMember I o e H)
    (hnext : ∀ i j s t, M.SuccessorOf j i → M.PairMember I i s H →
      M.PairMember I j t H → Step_d I ω s t) :
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧ ∀ n s, M.PairMember I n s H →
      M.IsSetFunctionFromTo I s n X ∧ M.MemberSubset s f := by
  have len := ds_path_length_l I hZF hω hT hH he hz hnext
  have inc := ZF.cc_increasing_of_successor_l I hZF hω hH (fun i j s t hij hs ht => by
    obtain ⟨a, n, m, h⟩ := hnext i j s t hij hs ht
    have em := h.prefix_sequence.2.2.2.eq hZF.1 (len i (hH.input_mem_of_pairMember hs) s hs).2.1
    subst m
    exact (ds_restrict_iff_l I (len i (hH.input_mem_of_pairMember hs) s hs)
      (len j (hH.input_mem_of_pairMember ht) t ht).1).mp h.prefix_restriction)
  obtain ⟨R, hR⟩ := ZF.exists_range_of_setFunction hZF I hH.1 hH.2.1
  obtain ⟨f, hf⟩ := KP.exists_union (ZF.modelsKP hZF) R
  have sub {i s} (hs : M.PairMember I i s H) : M.MemberSubset s f :=
    fun p hp => (hf p).mpr ⟨s, (hR s).mpr ⟨i, hs⟩, hp⟩
  have pair i x : M.PairMember I i x f ↔ ∃ n s, M.PairMember I n s H ∧ M.PairMember I i x s := by
    constructor
    · rintro ⟨p, hp, hpf⟩
      obtain ⟨s, hs, hps⟩ := (hf p).mp hpf
      obtain ⟨n, hn⟩ := (hR s).mp hs
      exact ⟨n, s, hn, p, hp, hps⟩
    · rintro ⟨n, s, hs, p, hp, hps⟩
      exact ⟨p, hp, sub hs p hps⟩
  have total i (hi : M.mem i ω) : ∃ x, M.mem x X ∧ M.PairMember I i x f := by
    obtain ⟨j, hj, hjω⟩ := hω.1.2 i hi
    obtain ⟨s, _, hs⟩ := hH.2.2 j hjω
    obtain ⟨x, hx, hix⟩ := (len j hjω s hs).2.2 i hj.predecessor_mem
    exact ⟨x, hx, (pair i x).mpr ⟨j, s, hs, hix⟩⟩
  refine ⟨f, ⟨⟨?_, ?_⟩, fun i => ⟨fun hi => (total i hi).elim fun x hx => ⟨x, hx.2⟩, ?_⟩, total⟩,
    fun n s hs => ⟨len n (hH.input_mem_of_pairMember hs) s hs, sub hs⟩⟩
  · intro p hp
    obtain ⟨s, hs, hps⟩ := (hf p).mp hp
    obtain ⟨n, hn⟩ := (hR s).mp hs
    exact (len n (hH.input_mem_of_pairMember hn) s hn).1.1 p hps
  · intro i x y hx hy
    obtain ⟨n, s, hs, hx⟩ := (pair i x).mp hx
    obtain ⟨m, t, ht, hy⟩ := (pair i y).mp hy
    have hn := hH.input_mem_of_pairMember hs
    have hm := hH.input_mem_of_pairMember ht
    rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare n hn m hm with e | hnm | hmn
    · have e := hZF.1.eq_of_same_members n m e
      subst m
      have e := hH.1.2 n s t hs ht
      exact (len n hn t ht).1.2 i x y (e ▸ hx) hy
    · exact (len m hm t ht).1.2 i x y
        (hx.elim fun p hp => ⟨p, hp.1, inc n m s t hnm hs ht p hp.2⟩) hy
    · exact (len n hn s hs).1.2 i x y hx
        (hy.elim fun p hp => ⟨p, hp.1, inc m n t s hmn ht hs p hp.2⟩)
  · rintro ⟨x, hx⟩
    obtain ⟨n, s, hs, hx⟩ := (pair i x).mp hx
    have hn := hH.input_mem_of_pairMember hs
    exact hω.transitive (ZF.modelsKP hZF) n hn i ((len n hn s hs).input_mem_of_pairMember hx)

/-- 给定实际后继函数时，用 ZF 内部迭代构造上述链。 -/
theorem ds_path_l (hZF : M.Models ZF) {ω X T F e} (hω : M.IsOmega ω)
    (hT : ∀ s, M.mem s T → ∃ n, M.mem n ω ∧ M.IsSetFunctionFromTo I s n X)
    (hF : M.IsSetFunctionFromTo I F T T) (he : ∀ x, ¬ M.mem x e) (het : M.mem e T)
    (hstep : ∀ s t, M.PairMember I s t F → Step_d I ω s t) :
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧ ∀ n, M.mem n ω →
      ∃ s, M.mem s T ∧ M.IsSetFunctionFromTo I s n X ∧ M.MemberSubset s f := by
  obtain ⟨H, hH, hz, hnext⟩ := ZFC.iterate_l I hZF hω hF het
  obtain ⟨f,ff,actual⟩ := ds_path_run_l I hZF hω hT hH he hz
    (fun i j s t hj hs ht => hstep s t (hnext i j s t hj hs ht))
  exact ⟨f,ff,fun n hn => (hH.2.2 n hn).elim fun s hs =>
    ⟨s,hs.1,(actual n s hs.2).1,(actual n s hs.2).2⟩⟩

/-- 二分后继优先取第一项；这在 ZF 内给出实际选择图，不使用 DC。 -/
theorem ds_binary_path_l (hZF : M.Models ZF) {ω X T e a b} (hω : M.IsOmega ω)
    (hT : ∀ s, M.mem s T → ∃ n, M.mem n ω ∧ M.IsSetFunctionFromTo I s n X)
    (he : ∀ x, ¬ M.mem x e) (het : M.mem e T)
    (hs : ∀ s, M.mem s T → ∃ t, M.mem t T ∧
      (Fseq_end_d I ω t s a ∨ Fseq_end_d I ω t s b)) :
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧ ∀ n, M.mem n ω →
      ∃ s, M.mem s T ∧ M.IsSetFunctionFromTo I s n X ∧ M.MemberSubset s f := by
  classical
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push T).push a).push b
  let φ : BinarySchema 4 := {
    body := .conj (.mem .newest (.bound 4)) (.disj
      (fseq_end_m (𝒞 := 𝒞) (.bound 5) .newest (.bound 1) (.bound 3))
      (.conj (.neg (.existsE (.conj (.mem .newest (.bound 5))
        (fseq_end_m (𝒞 := 𝒞) (.bound 6) .newest (.bound 2) (.bound 4)))))
        (fseq_end_m (𝒞 := 𝒞) (.bound 5) .newest (.bound 1) (.bound 2)))) }
  have hp s t : φ.denote ρ s t ↔ M.mem t T ∧ (Fseq_end_d I ω t s a ∨
      ((¬ ∃ r, M.mem r T ∧ Fseq_end_d I ω r s a) ∧ Fseq_end_d I ω t s b)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_neg_iff, Formula.satisfies_exists_iff,
      fseq_end_sat_l I hZF.1]; rfl
  obtain ⟨F, hF, hf⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := T) (target := T)
    (by
      intro s hst
      by_cases h : ∃ t, M.mem t T ∧ Fseq_end_d I ω t s a
      · obtain ⟨t, ht, ha⟩ := h
        exact ⟨t, (hp s t).mpr ⟨ht, Or.inl ha⟩⟩
      · obtain ⟨t, ht, ha | hb⟩ := hs s hst
        · exact (h ⟨t, ht, ha⟩).elim
        · exact ⟨t, (hp s t).mpr ⟨ht, Or.inr ⟨h, hb⟩⟩⟩)
    (by
      intro s _ t u ht hu
      obtain ⟨ht, ha | ⟨h, hb⟩⟩ := (hp s t).mp ht <;>
        obtain ⟨hu, ha' | ⟨h', hb'⟩⟩ := (hp s u).mp hu
      · exact fseq_end_rebuild_l I hZF.1 ha ha'
      · exact (h' ⟨t, ht, ha⟩).elim
      · exact (h ⟨u, hu, ha'⟩).elim
      · exact fseq_end_rebuild_l I hZF.1 hb hb')
    (fun s t _ ht => ((hp s t).mp ht).1)
  exact ds_path_l I hZF hω hT hF he het (fun s t h =>
    (((hp s t).mp ((hf s t).mp h).2).2).elim (fun h => ⟨a, h⟩) (fun h => ⟨b, h.2⟩))

end YesMetaZFC.SetTheory.Descriptive

/-! ## 模型内部前缀树与闭集

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

/-! ## 内部前缀树地址的首项拼接

用后继坐标把有限列整体右移，再在零处插入首项。全部长度属于模型内部 ω；
首项拼接保持并反映前缀与直接子边，供带索引子树的无交拼接使用。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Cons_d (z a s t : M.Domain) : Prop := M.IsSetRelation I t ∧ ∀ j x,
  M.PairMember I j x t ↔ (j = z ∧ x = a) ∨ ∃ i, M.PairMember I i x s ∧ M.SuccessorOf j i
def cons_m {d} (z a s t : Term d) : Formula 1 d := .conj (Formula.isRelation 𝒞 t)
  (.forallE (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest t.weaken.weaken)
    (.disj (.conj (Formula.extensionalEq (.bound 1) z.weaken.weaken) (Formula.extensionalEq .newest a.weaken.weaken))
      (.existsE (.conj (Formula.orderedPairMem 𝒞 .newest (.bound 1) s.weaken.weaken.weaken)
        (Formula.isSuccessor (.bound 2) .newest)))))))
derive_free_closed cons_m
theorem cons_sat_l (hE : Extensional M) {d} (ρ : Env M d) (z a s t : Term d) :
    Formula.satisfies ρ (cons_m (𝒞 := 𝒞) z a s t) ↔
      Cons_d I (z.eval ρ) (a.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [cons_m, Cons_d, Formula.satisfies_conj_iff, Formula.satisfies_isRelation_iff I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hE, Formula.satisfies_exists_iff,
    Formula.satisfies_isSuccessor_iff, Definitional.Term.eval_weaken]; rfl

omit I in
theorem tree_successor_le_l (hZF : M.Models ZF) {ω n i j : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hi : M.mem i n) (hj : M.SuccessorOf j i) : j = n ∨ M.mem j n := by
  obtain ⟨j', hj', hjω⟩ := hω.1.2 i (hω.transitive (ZF.modelsKP hZF) n hn i hi)
  have e := Structure.SuccessorOf.eq hZF.1 hj' hj
  have hjω := e ▸ hjω
  rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare j hjω n hn with e | h | h
  · exact Or.inl (hZF.1.eq_of_same_members j n e)
  · exact Or.inr h
  · rcases (hj n).mp h with h | e
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (((hω.isOrdinal (ZF.modelsKP hZF)).mem hn).transitive i hi n h)).elim
    · have e := hZF.1.eq_of_same_members n i e
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (e.symm ▸ hi)).elim

theorem cons_unique_l (hE : Extensional M) {z a s t u : M.Domain} (h : Cons_d I z a s t)
    (k : Cons_d I z a s u) : t = u := h.1.eq_of_pairMember_iff hE k.1 (fun j x => (h.2 j x).trans (k.2 j x).symm)

/-- 首项拼接生成后继长度的实际函数图。 -/
theorem cons_exists_l (hZF : M.Models ZF) {ω X z a s n} (hω : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z)
    (ha : M.mem a X) (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n X) :
    ∃ k t, M.mem k ω ∧ M.SuccessorOf k n ∧ M.IsSetFunctionFromTo I t k X ∧ Cons_d I z a s t := by
  obtain ⟨k, hk, hkω⟩ := hω.1.2 n hn
  have hzK := Structure.IsOrdinal.empty_mem_of_nonempty (ZF.modelsKP hZF)
    ((hω.isOrdinal (ZF.modelsKP hZF)).mem hkω) ⟨n, hk.predecessor_mem⟩ hz
  let ρ : Env M 3 := ((⟨fun _ => s, fun _ => s⟩ : Env M 1).push a).push z
  let φ : BinarySchema 3 := {
    body := .disj (.conj (Formula.extensionalEq (.bound 1) (.bound 2)) (Formula.extensionalEq .newest (.bound 3)))
      (.existsE (.conj (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 5))
        (Formula.isSuccessor (.bound 2) .newest))) }
  have hp j x : φ.denote ρ j x ↔ (j = z ∧ x = a) ∨ ∃ i, M.PairMember I i x s ∧ M.SuccessorOf j i := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_exists_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isSuccessor_iff]; rfl
  obtain ⟨t, ht, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := k) (target := X)
    (by
      intro j hj
      classical
      by_cases h0 : ∀ x, ¬ M.mem x j
      · exact ⟨a, (hp j a).mpr (Or.inl ⟨hZF.1.eq_of_same_members j z (fun x => iff_of_false (h0 x) (hz x)), rfl⟩)⟩
      · have hne : ∃ x, M.mem x j := Classical.byContradiction (fun h => h0 (fun x hx => h ⟨x, hx⟩))
        obtain ⟨i, _, hji⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF (hω.transitive (ZF.modelsKP hZF) k hkω j hj) hne
        have hiK := ((hω.isOrdinal (ZF.modelsKP hZF)).mem hkω).transitive j hj i hji.predecessor_mem
        have hi : M.mem i n := ((hk i).mp hiK).elim id (fun e => by
          have ei := hZF.1.eq_of_same_members i n e
          have ej := Structure.SuccessorOf.eq hZF.1 (ei ▸ hji) hk
          exact (KP.mem_irrefl_d (ZF.modelsKP hZF) k (ej ▸ hj)).elim)
        obtain ⟨x, _, hx⟩ := hs.2.2 i hi
        exact ⟨x, (hp j x).mpr (Or.inr ⟨i, hx, hji⟩)⟩)
    (by
      intro j _ x y hx hy
      rcases (hp j x).mp hx with ⟨e, rfl⟩ | ⟨i, hi, hji⟩ <;>
        rcases (hp j y).mp hy with ⟨e', rfl⟩ | ⟨i', hi', hji'⟩
      · rfl
      · exact (hz i' (e ▸ hji'.predecessor_mem)).elim
      · exact (hz i (e' ▸ hji.predecessor_mem)).elim
      · have e := Structure.SuccessorOf.predecessor_eq hZF.1
          (((hω.isOrdinal (ZF.modelsKP hZF)).mem hn).mem (hs.input_mem_of_pairMember hi)) hji hji'
        exact hs.1.2 i x y hi (e.symm ▸ hi'))
    (fun j x _ hx => ((hp j x).mp hx).elim (fun h => h.2.symm ▸ ha)
      (fun ⟨_, hi, _⟩ => hs.output_mem_of_pairMember hi))
  refine ⟨k, t, hkω, hk, ht, ht.1.1, fun j x => (he j x).trans ?_⟩
  rw [hp j x]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rcases h with ⟨e, _⟩ | ⟨i, hi, hji⟩
  · exact e.symm ▸ hzK
  · exact (tree_successor_le_l hZF hω hn (hs.input_mem_of_pairMember hi) hji).elim
      (fun e => e.symm ▸ hk.predecessor_mem) (fun h => (hk j).mpr (Or.inl h))

/-- 拼接的图包含恰好对应首项相同和尾列包含。 -/
theorem cons_subset_l (hZF : M.Models ZF) {ω X z a b s t u v n} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n X)
    (hu : Cons_d I z a s u) (hv : Cons_d I z b t v) :
    M.MemberSubset u v ↔ a = b ∧ M.MemberSubset s t := by
  have lift {P Q i x} (h : M.MemberSubset P Q) (hp : M.PairMember I i x P) : M.PairMember I i x Q :=
    hp.elim fun p hp => ⟨p, hp.1, h p hp.2⟩
  constructor
  · intro h
    have hab : a = b := ((hv.2 z a).mp (lift h ((hu.2 z a).mpr (Or.inl ⟨rfl, rfl⟩)))).elim And.right
      (fun ⟨i, _, hi⟩ => (hz i hi.predecessor_mem).elim)
    refine ⟨hab, fun p hp => ?_⟩
    obtain ⟨i, x, hpx⟩ := hs.1.1 p hp
    have hi := hs.input_mem_of_pairMember ⟨p, hpx, hp⟩
    obtain ⟨j, hj, _⟩ := hω.1.2 i (hω.transitive (ZF.modelsKP hZF) n hn i hi)
    have hx := (hv.2 j x).mp (lift h ((hu.2 j x).mpr (Or.inr ⟨i, ⟨p, hpx, hp⟩, hj⟩)))
    have hxt : M.PairMember I i x t := by
      rcases hx with ⟨e, _⟩ | ⟨i', hx, hj'⟩
      · exact (hz i (e ▸ hj.predecessor_mem)).elim
      · have e := Structure.SuccessorOf.predecessor_eq hZF.1 (((hω.isOrdinal (ZF.modelsKP hZF)).mem hn).mem hi) hj hj'
        exact e.symm ▸ hx
    obtain ⟨q, hq, hqt⟩ := hxt
    exact (I.unique hpx hq).symm ▸ hqt
  · rintro ⟨rfl, hst⟩ p hp
    obtain ⟨j, x, hc⟩ := hu.1 p hp
    have hx := (hu.2 j x).mp ⟨p, hc, hp⟩
    have hxt : M.PairMember I j x v := (hv.2 j x).mpr (hx.imp_right
      (fun ⟨i, hi, hij⟩ => ⟨i, lift hst hi, hij⟩))
    obtain ⟨q, hq, hqv⟩ := hxt
    exact (I.unique hc hq).symm ▸ hqv

theorem cons_type_l (hZF : M.Models ZF) {ω X z a s t n} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a X) (hn : M.mem n ω)
    (hs : M.IsSetFunctionFromTo I s n X) (ht : Cons_d I z a s t) :
    ∃ k, M.mem k ω ∧ M.SuccessorOf k n ∧ M.IsSetFunctionFromTo I t k X := by
  obtain ⟨k, u, hk, hkn, hu, hc⟩ := cons_exists_l I hZF hω hz ha hn hs
  exact ⟨k, hk, hkn, cons_unique_l I hZF.1 hc ht ▸ hu⟩

theorem cons_injective_l (hZF : M.Models ZF) {ω X z a b s t v n m} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (hn : M.mem n ω) (hm : M.mem m ω)
    (hs : M.IsSetFunctionFromTo I s n X) (ht : M.IsSetFunctionFromTo I t m X)
    (hu : Cons_d I z a s v) (hv : Cons_d I z b t v) : a = b ∧ s = t := by
  have h := (cons_subset_l I hZF hω hz hn hs hu hv).mp (fun _ => id)
  have k := (cons_subset_l I hZF hω hz hm ht hv hu).mp (fun _ => id)
  exact ⟨h.1, hZF.1.eq_of_same_members s t (fun p => ⟨h.2 p, k.2 p⟩)⟩

/-- 直接子边等价于图包含与长度相差一个后继。 -/
theorem tree_step_iff_l (hZF : M.Models ZF) {ω X s t n m} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.mem m ω) (hs : M.IsSetFunctionFromTo I s n X)
    (ht : M.IsSetFunctionFromTo I t m X) :
    Step_d I ω s t ↔ M.SuccessorOf m n ∧ M.MemberSubset s t := by
  constructor
  · rintro ⟨a, j, k, h⟩
    have e := h.source.2.2.2.eq hZF.1 ht.2.1
    subst j
    have e := h.prefix_sequence.2.2.2.eq hZF.1 hs.2.1
    subst k
    exact ⟨h.length_successor, (ds_restrict_iff_l I hs ht.1).mp h.prefix_restriction⟩
  · rintro ⟨h, hst⟩
    obtain ⟨a, _, ha⟩ := ht.2.2 n h.predecessor_mem
    exact ⟨a, m, n, ⟨⟨hm, (hω.isOrdinal (ZF.modelsKP hZF)).mem hm, ht.1, ht.2.1⟩, hn, h,
      ⟨hn, (hω.isOrdinal (ZF.modelsKP hZF)).mem hn, hs.1, hs.2.1⟩,
      (ds_restrict_iff_l I hs ht.1).mpr hst, ha⟩⟩

theorem cons_step_l (hZF : M.Models ZF) {ω X z a b s t u v n m} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a X) (hb : M.mem b X)
    (hn : M.mem n ω) (hm : M.mem m ω) (hs : M.IsSetFunctionFromTo I s n X)
    (ht : M.IsSetFunctionFromTo I t m X) (hu : Cons_d I z a s u) (hv : Cons_d I z b t v) :
    Step_d I ω u v ↔ a = b ∧ Step_d I ω s t := by
  obtain ⟨j, hj, hjn, huf⟩ := cons_type_l I hZF hω hz ha hn hs hu
  obtain ⟨k, hk, hkm, hvf⟩ := cons_type_l I hZF hω hz hb hm ht hv
  rw [tree_step_iff_l I hZF hω hj hk huf hvf, cons_subset_l I hZF hω hz hn hs hu hv,
    tree_step_iff_l I hZF hω hn hm hs ht]
  constructor
  · rintro ⟨hkj, hab, hst⟩
    have e := Structure.SuccessorOf.predecessor_eq hZF.1 ((hω.isOrdinal (ZF.modelsKP hZF)).mem hm) hkm hkj
    exact ⟨hab, e.symm ▸ hjn, hst⟩
  · rintro ⟨hab, hmn, hst⟩
    have e := Structure.SuccessorOf.eq hZF.1 hmn hjn
    exact ⟨e ▸ hkm, hab, hst⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 补齐树的第一层而不改变无限枝

补入长度不超过一的全部有限列。任何无限枝在两个额外后继长度处已经
越过新增层，原树的前缀封闭性随即恢复所有较短节点。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tr_first_d (F one T U : M.Domain) : Prop := ∀ s, M.mem s U ↔ M.mem s F ∧
  (M.mem s T ∨ ∃ n, M.IsDomainOf I n s ∧ M.MemberSubset n one)

theorem tr_first_exists_l (F one T : M.Domain) : ∃ U, Tr_first_d hZF F one T U := by
  let ρ : Env M 2 := ⟨fun i => [one,T].get i,fun _ => one⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪⌜(.newest : Term 3)⌝ₛ ∈ ⌜(.bound 2 : Term 3)⌝ₛ ∨
    (∃ n, ⌜(Formula.isDomain kpair_convention_l)⌝ₚ(n,⌜(.newest : Term 3)⌝ₛ) ∧ n ⊆ ⌜(.bound 1 : Term 3)⌝ₛ)⟫ }
  obtain ⟨U,read⟩ := ZF.separation_exists_d hZF φ ρ F
  refine ⟨U,fun s => (read s).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ,Formula.satisfies_disj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,Formula.satisfies_isDomain_iff I,
    Formula.satisfies_subset_iff,Definitional.Term.eval_weaken]
  rfl

theorem Tr_first_d.tree_l {ω A F one T U : M.Domain} (fill : Tr_first_d hZF F one T U)
    (space : Fseq_space_d I ω A F) (tree : Tree_d F T) : Tree_d F U := by
  refine ⟨fun s hs => ((fill s).mp hs).1,?_⟩
  intro s hs t ht sub
  refine (fill t).mpr ⟨ht,?_⟩
  rcases ((fill s).mp hs).2 with hs | ⟨n,dom,bound⟩
  · exact Or.inl (tree.2 s hs t ht sub)
  · obtain ⟨m,_,ft⟩ := (space t).mp ht
    refine Or.inr ⟨m,ft.2.1,fun i hi => ?_⟩
    obtain ⟨a,_,ia⟩ := ft.2.2 i hi
    exact bound i ((dom i).mpr ⟨a,ia.elim fun p hp => ⟨p,hp.1,sub p hp.2⟩⟩)

theorem Tr_first_d.branch_l {ω A F e one T U f : M.Domain} (fill : Tr_first_d hZF F one T U)
    (hw : M.IsOmega ω) (space : Fseq_space_d I ω A F) (tree : Tree_d F T)
    (empty : ∀ x, ¬ M.mem x e) (succ : M.SuccessorOf one e) (ff : Fn0_d ω A f) :
    Branch_d F U f ↔ Branch_d F T f := by
  have function := fn0_function_l (ZF.modelsKP hZF) ff
  constructor
  · intro branch s hs sub
    obtain ⟨n,hn,fs⟩ := (space s).mp hs
    obtain ⟨j,sj,hj⟩ := hw.1.2 n hn
    obtain ⟨m,sm,hm⟩ := hw.1.2 j hj
    obtain ⟨t,ft,cut,_⟩ := ds_prefix_l I hZF hw function hm
    have ht := branch t ((space t).mpr ⟨m,hm,ft⟩) ((ds_restrict_iff_l I ft function.1).mp cut)
    have member : M.mem t T := by
      rcases ((fill t).mp ht).2 with ht | ⟨l,dom,short⟩
      · exact ht
      · have eq := dom.eq hZF.1 ft.2.1
        subst l
        have ne i (hi : M.mem i one) : i = e := ((succ i).mp hi).elim
          (fun h => (empty i h).elim) (hZF.1.eq_of_same_members i e)
        have en := ne n (short n ((sm n).mpr (Or.inl sj.predecessor_mem)))
        have ej := ne j (short j sm.predecessor_mem)
        exact (KP.mem_irrefl_d (ZF.modelsKP hZF) j (en.trans ej.symm ▸ sj.predecessor_mem)).elim
    exact tree.2 t member s hs (ds_prefix_mono_l I fs ft.1 ((ds_restrict_iff_l I fs function.1).mpr sub) cut
      (fun i hi => (sm i).mpr (Or.inl ((sj i).mpr (Or.inl hi)))))
  · intro branch s hs sub
    exact (fill s).mpr ⟨hs,Or.inl (branch s hs sub)⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 第一层补全的有界定义

在指定完整有限空间内，长度界可由有界函数公式读取。
因此补全关系在传递模型和成员满扩张中保持同一含义。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def tr_first_bound_m {d} (ω A F one T W : Term d) : Formula 1 d := set[d] ⟪
  ⌜W⌝ₛ ⊆ ⌜F⌝ₛ ∧ (∀ s ∈ ⌜F⌝ₛ, s ∈ ⌜W⌝ₛ ↔
    (s ∈ ⌜T⌝ₛ ∨ (∃ n ∈ ⌜ω⌝ₛ, ⌜fn0_m⌝ₚ(n,⌜A⌝ₛ,s) ∧ n ⊆ ⌜one⌝ₛ)))⟫
derive_free_closed tr_first_bound_m

theorem tr_first_bound_delta_l {d} (ω A F one T W : Term d) :
    (tr_first_bound_m ω A F one T W).IsDelta0 := by
  unfold tr_first_bound_m
  repeat first
    | exact fn0_delta_l .. | exact Formula.IsDelta0.mem ..
    | exact Formula.IsDelta0.atom _ (by trivial) _
    | apply Formula.IsDelta0.conj | apply Formula.IsDelta0.disj
    | apply Formula.IsDelta0.forallMem | apply Formula.IsDelta0.existsMem | apply Formula.IsDelta0.iff

theorem tr_first_bound_sat_l {d} (ρ : Env M d) (ω A F one T W : Term d)
    (space : Fseq_space_d I (ω.eval ρ) (A.eval ρ) (F.eval ρ)) :
    Formula.satisfies ρ (tr_first_bound_m ω A F one T W) ↔
      Tr_first_d hZF (F.eval ρ) (one.eval ρ) (T.eval ρ) (W.eval ρ) := by
  simp only [tr_first_bound_m,Formula.satisfies_conj_iff,Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_iff_iff,Formula.satisfies_disj_iff,
    Formula.satisfies_mem_iff,Formula.satisfies_existsMem_iff,fn0_sat_l hZF.1,Definitional.Term.eval_weaken]
  have short s (hs : M.mem s (F.eval ρ)) :
      (∃ n, M.mem n (ω.eval ρ) ∧ Fn0_d n (A.eval ρ) s ∧ M.MemberSubset n (one.eval ρ)) ↔
      ∃ n, M.IsDomainOf I n s ∧ M.MemberSubset n (one.eval ρ) := by
    constructor
    · rintro ⟨n,_,fn,sub⟩; exact ⟨n,(fn0_function_l (ZF.modelsKP hZF) fn).2.1,sub⟩
    · rintro ⟨n,dom,sub⟩
      obtain ⟨m,hm,fn⟩ := (space s).mp hs
      have eq := fn.2.1.eq hZF.1 dom
      subst m
      exact ⟨n,hm,fn0_of_function_l (ZF.modelsKP hZF) fn,sub⟩
  constructor
  · rintro ⟨sub,read⟩ s
    exact ⟨fun hs => ⟨sub s hs,((read s (sub s hs)).trans (or_congr Iff.rfl (short s (sub s hs)))).mp hs⟩,
      fun ⟨hs,h⟩ => (read s hs).mpr ((or_congr Iff.rfl (short s hs)).mpr h)⟩
  · intro fill
    exact ⟨fun s hs => ((fill s).mp hs).1,fun s hs => (fill s).trans
      ((and_iff_right hs).trans (or_congr Iff.rfl (short s hs).symm))⟩

end YesMetaZFC.SetTheory.Descriptive

/-! ## 内部有限地址的首尾分解

首尾分解由内部后继坐标的函数图构造，不对外部自然数长度递归。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem tree_empty_domain_l (hE : Extensional M) {z t X} (hz : ∀ x, ¬ M.mem x z)
    (ht : M.IsSetFunctionFromTo I t z X) : t = z := by
  apply hE.eq_of_same_members
  intro p
  exact iff_of_false (fun hp => (ht.1.1 p hp).elim fun i ⟨x, hc⟩ =>
    hz i (ht.input_mem_of_pairMember ⟨p, hc, hp⟩)) (hz p)

/-- 空列或唯一的首项加尾列；尾列仍属于同一内部有限列空间。 -/
theorem cons_cases_l (hZF : M.Models ZF) {ω X A z t} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω X A) (hz : ∀ x, ¬ M.mem x z) (ht : M.mem t A) :
    t = z ∨ ∃ a s, M.mem a X ∧ M.mem s A ∧ Cons_d I z a s t := by
  classical
  obtain ⟨n, hn, ht⟩ := (hA t).mp ht
  by_cases h0 : ∀ x, ¬ M.mem x n
  · have en := hZF.1.eq_of_same_members n z (fun x => iff_of_false (h0 x) (hz x))
    exact Or.inl (tree_empty_domain_l I hZF.1 hz (en ▸ ht))
  have hne : ∃ x, M.mem x n := Classical.byContradiction (fun h => h0 (fun x hx => h ⟨x, hx⟩))
  obtain ⟨m, hm, hnm⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF hn hne
  obtain ⟨a, ha, hza⟩ := ht.2.2 z (Structure.IsOrdinal.empty_mem_of_nonempty
    (ZF.modelsKP hZF) ((hω.isOrdinal (ZF.modelsKP hZF)).mem hn) hne hz)
  let ρ : Env M 1 := ⟨fun _ => t, fun _ => t⟩
  let φ : BinarySchema 1 := { body := .existsE (.conj (Formula.isSuccessor .newest (.bound 2))
    (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 3))) }
  have hp i x : φ.denote ρ i x ↔ ∃ j, M.SuccessorOf j i ∧ M.PairMember I j x t := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_isSuccessor_iff, Formula.satisfies_orderedPairMem_iff I]; rfl
  obtain ⟨s, hs, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := m) (target := X)
    (by
      intro i hi
      obtain ⟨j, hj, _⟩ := hω.1.2 i (hω.transitive (ZF.modelsKP hZF) m hm i hi)
      have hjn : M.mem j n := (tree_successor_le_l hZF hω hm hi hj).elim
        (fun e => e.symm ▸ hnm.predecessor_mem) (fun h => (hnm j).mpr (Or.inl h))
      obtain ⟨x, _, hx⟩ := ht.2.2 j hjn
      exact ⟨x, (hp i x).mpr ⟨j, hj, hx⟩⟩)
    (by
      intro i _ x y hx hy
      obtain ⟨j, hj, hx⟩ := (hp i x).mp hx
      obtain ⟨k, hk, hy⟩ := (hp i y).mp hy
      exact ht.1.2 j x y hx (Structure.SuccessorOf.eq hZF.1 hk hj ▸ hy))
    (fun i x _ hx => ((hp i x).mp hx).elim fun _ h => ht.output_mem_of_pairMember h.2)
  refine Or.inr ⟨a, s, ha, (hA s).mpr ⟨m, hm, hs⟩, ht.1.1, fun j x => ⟨?_, ?_⟩⟩
  · intro hx
    by_cases h0 : ∀ i, ¬ M.mem i j
    · have e := hZF.1.eq_of_same_members j z (fun i => iff_of_false (h0 i) (hz i))
      exact Or.inl ⟨e, ht.1.2 j x a hx (e.symm ▸ hza)⟩
    · have hne : ∃ i, M.mem i j := Classical.byContradiction (fun h => h0 (fun i hi => h ⟨i, hi⟩))
      have hj := ht.input_mem_of_pairMember hx
      obtain ⟨i, _, hji⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF (hω.transitive (ZF.modelsKP hZF) n hn j hj) hne
      have hin := ((hω.isOrdinal (ZF.modelsKP hZF)).mem hn).transitive j hj i hji.predecessor_mem
      have hi : M.mem i m := ((hnm i).mp hin).elim id (fun e => by
        have ei := hZF.1.eq_of_same_members i m e
        have ej := Structure.SuccessorOf.eq hZF.1 (ei ▸ hji) hnm
        exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (ej ▸ hj)).elim)
      exact Or.inr ⟨i, (he i x).mpr ⟨hi, (hp i x).mpr ⟨j, hji, hx⟩⟩, hji⟩
  · rintro (⟨rfl, rfl⟩ | ⟨i, hi, hj⟩)
    · exact hza
    · obtain ⟨k, hk, hx⟩ := (hp i x).mp ((he i x).mp hi).2
      exact Structure.SuccessorOf.eq hZF.1 hk hj ▸ hx

theorem cons_ne_empty_l {z a s t : M.Domain} (hz : ∀ p, ¬ M.mem p z)
    (h : Cons_d I z a s t) : t ≠ z := by
  intro e
  obtain ⟨p, _, hp⟩ := (h.2 z a).mpr (Or.inl ⟨rfl, rfl⟩)
  exact hz p (e ▸ hp)

/-- 加首项后的节点直接接在根上，当且仅当其尾列为空。 -/
theorem cons_root_l (hZF : M.Models ZF) {ω A z a s t} (hω : M.IsOmega ω)
    (hA : Fseq_space_d I ω ω A) (hz : ∀ x, ¬ M.mem x z) (hzω : M.mem z ω)
    (ha : M.mem a ω) (hs : M.mem s A) (ht : Cons_d I z a s t) : Step_d I ω z t ↔ s = z := by
  obtain ⟨n, hn, hs⟩ := (hA s).mp hs
  obtain ⟨k, hk, hkn, htf⟩ := cons_type_l I hZF hω hz ha hn hs ht
  rw [tree_step_iff_l I hZF hω hzω hk (ds_empty_fun_l I hz) htf]
  constructor
  · rintro ⟨hkz, _⟩
    have e := Structure.SuccessorOf.predecessor_eq hZF.1 ((hω.isOrdinal (ZF.modelsKP hZF)).mem hn) hkn hkz
    exact tree_empty_domain_l I hZF.1 hz (e ▸ hs)
  · intro e
    have en := hs.2.1.eq hZF.1 (e.symm ▸ (ds_empty_fun_l I (X := ω) hz).2.1)
    exact ⟨en.trans e ▸ hkn, fun p hp => (hz p hp).elim⟩

end YesMetaZFC.SetTheory.Descriptive
