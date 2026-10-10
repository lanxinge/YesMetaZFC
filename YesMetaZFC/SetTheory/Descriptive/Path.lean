import YesMetaZFC.SetTheory.Descriptive.Topology
import YesMetaZFC.SetTheory.Card.FiniteSequenceEnd
import YesMetaZFC.SetTheory.CountableChain
import YesMetaZFC.SetTheory.DependentChoice

/-! # 内部逐项延拓的分支

在实际后继函数图上沿内部 ω 迭代，再取前缀图的并。长度归纳使用原公式，
递增性复用内部关系链；不把非标准长度转成外部递归，也不使用依赖选择。
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

/-- 从空列出发的内部后继函数实际产生一条贯穿全部阶段的分支。 -/
theorem ds_path_l (hZF : M.Models ZF) {ω X T F e} (hω : M.IsOmega ω)
    (hT : ∀ s, M.mem s T → ∃ n, M.mem n ω ∧ M.IsSetFunctionFromTo I s n X)
    (hF : M.IsSetFunctionFromTo I F T T) (he : ∀ x, ¬ M.mem x e) (het : M.mem e T)
    (hstep : ∀ s t, M.PairMember I s t F → Step_d I ω s t) :
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧ ∀ n, M.mem n ω →
      ∃ s, M.mem s T ∧ M.IsSetFunctionFromTo I s n X ∧ M.MemberSubset s f := by
  obtain ⟨H, hH, hz, hnext⟩ := ZFC.iterate_l I hZF hω hF het
  have len : ∀ n, M.mem n ω → ∀ s, M.PairMember I n s H → M.IsSetFunctionFromTo I s n X := by
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
      obtain ⟨a, k, m, h⟩ := hstep s t (hnext n j s t hj hs ht)
      have em := h.prefix_sequence.2.2.2.eq hZF.1 (ih s hs).2.1
      subst m
      have ek := Structure.SuccessorOf.eq hZF.1 h.length_successor hj
      subst k
      obtain ⟨r, _, hr⟩ := hT t (hH.output_mem_of_pairMember ht)
      have er := hr.2.1.eq hZF.1 h.source.2.2.2
      exact er ▸ hr
  have inc := ZF.cc_increasing_of_successor_l I hZF hω hH (fun i j s t hij hs ht => by
    obtain ⟨a, n, m, h⟩ := hstep s t (hnext i j s t hij hs ht)
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
    fun n hn => (hH.2.2 n hn).elim fun s hs => ⟨s, hs.1, len n hn s hs.2, sub hs.2⟩⟩
  · intro p hp
    obtain ⟨s, hs, hps⟩ := (hf p).mp hp
    obtain ⟨n, hn⟩ := (hR s).mp hs
    exact (len n (hH.input_mem_of_pairMember hn) s hn).1.1 p hps
  · intro i x y hx hy
    obtain ⟨n, s, hs, hx⟩ := (pair i x).mp hx
    obtain ⟨m, t, ht, hy⟩ := (pair i y).mp hy
    have hn := hH.input_mem_of_pairMember hs
    have hm := hH.input_mem_of_pairMember ht
    rcases (hω.isOrdinal hZF).wellOrder.linear.compare n hn m hm with e | hnm | hmn
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
    exact hω.transitive hZF n hn i ((len n hn s hs).input_mem_of_pairMember hx)

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
