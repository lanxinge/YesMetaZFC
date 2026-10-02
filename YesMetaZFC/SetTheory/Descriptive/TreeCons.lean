import YesMetaZFC.SetTheory.Descriptive.Tree

/-! # 内部前缀树地址的首项拼接

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
  obtain ⟨j', hj', hjω⟩ := hω.1.2 i (hω.transitive hZF n hn i hi)
  have e := Structure.SuccessorOf.eq hZF.1 hj' hj
  have hjω := e ▸ hjω
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare j hjω n hn with e | h | h
  · exact Or.inl (hZF.1.eq_of_same_members j n e)
  · exact Or.inr h
  · rcases (hj n).mp h with h | e
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (((hω.isOrdinal hZF).mem hn).transitive i hi n h)).elim
    · have e := hZF.1.eq_of_same_members n i e
      exact (KP.mem_irrefl_d (ZF.modelsKP hZF) n (e.symm ▸ hi)).elim

theorem cons_unique_l (hE : Extensional M) {z a s t u : M.Domain} (h : Cons_d I z a s t)
    (k : Cons_d I z a s u) : t = u := h.1.eq_of_pairMember_iff hE k.1 (fun j x => (h.2 j x).trans (k.2 j x).symm)

/-- 首项拼接生成后继长度的实际函数图。 -/
theorem cons_exists_l (hZF : M.Models ZF) {ω z a s n} (hω : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z)
    (ha : M.mem a ω) (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n ω) :
    ∃ k t, M.mem k ω ∧ M.SuccessorOf k n ∧ M.IsSetFunctionFromTo I t k ω ∧ Cons_d I z a s t := by
  obtain ⟨k, hk, hkω⟩ := hω.1.2 n hn
  have hzK := Structure.IsOrdinal.empty_mem_of_nonempty (ZF.modelsKP hZF)
    ((hω.isOrdinal hZF).mem hkω) ⟨n, hk.predecessor_mem⟩ hz
  let ρ : Env M 3 := ((⟨fun _ => s, fun _ => s⟩ : Env M 1).push a).push z
  let φ : BinarySchema 3 := {
    body := .disj (.conj (Formula.extensionalEq (.bound 1) (.bound 2)) (Formula.extensionalEq .newest (.bound 3)))
      (.existsE (.conj (Formula.orderedPairMem 𝒞 .newest (.bound 1) (.bound 5))
        (Formula.isSuccessor (.bound 2) .newest))) }
  have hp j x : φ.denote ρ j x ↔ (j = z ∧ x = a) ∨ ∃ i, M.PairMember I i x s ∧ M.SuccessorOf j i := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_exists_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_isSuccessor_iff]; rfl
  obtain ⟨t, ht, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := k) (target := ω)
    (by
      intro j hj
      classical
      by_cases h0 : ∀ x, ¬ M.mem x j
      · exact ⟨a, (hp j a).mpr (Or.inl ⟨hZF.1.eq_of_same_members j z (fun x => iff_of_false (h0 x) (hz x)), rfl⟩)⟩
      · have hne : ∃ x, M.mem x j := Classical.byContradiction (fun h => h0 (fun x hx => h ⟨x, hx⟩))
        obtain ⟨i, _, hji⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF (hω.transitive hZF k hkω j hj) hne
        have hiK := ((hω.isOrdinal hZF).mem hkω).transitive j hj i hji.predecessor_mem
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
          (((hω.isOrdinal hZF).mem hn).mem (hs.input_mem_of_pairMember hi)) hji hji'
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
theorem cons_subset_l (hZF : M.Models ZF) {ω z a b s t u v n} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (hn : M.mem n ω) (hs : M.IsSetFunctionFromTo I s n ω)
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
    obtain ⟨j, hj, _⟩ := hω.1.2 i (hω.transitive hZF n hn i hi)
    have hx := (hv.2 j x).mp (lift h ((hu.2 j x).mpr (Or.inr ⟨i, ⟨p, hpx, hp⟩, hj⟩)))
    have hxt : M.PairMember I i x t := by
      rcases hx with ⟨e, _⟩ | ⟨i', hx, hj'⟩
      · exact (hz i (e ▸ hj.predecessor_mem)).elim
      · have e := Structure.SuccessorOf.predecessor_eq hZF.1 (((hω.isOrdinal hZF).mem hn).mem hi) hj hj'
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

theorem cons_type_l (hZF : M.Models ZF) {ω z a s t n} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a ω) (hn : M.mem n ω)
    (hs : M.IsSetFunctionFromTo I s n ω) (ht : Cons_d I z a s t) :
    ∃ k, M.mem k ω ∧ M.SuccessorOf k n ∧ M.IsSetFunctionFromTo I t k ω := by
  obtain ⟨k, u, hk, hkn, hu, hc⟩ := cons_exists_l I hZF hω hz ha hn hs
  exact ⟨k, hk, hkn, cons_unique_l I hZF.1 hc ht ▸ hu⟩

theorem cons_injective_l (hZF : M.Models ZF) {ω z a b s t v n m} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (hn : M.mem n ω) (hm : M.mem m ω)
    (hs : M.IsSetFunctionFromTo I s n ω) (ht : M.IsSetFunctionFromTo I t m ω)
    (hu : Cons_d I z a s v) (hv : Cons_d I z b t v) : a = b ∧ s = t := by
  have h := (cons_subset_l I hZF hω hz hn hs hu hv).mp (fun _ => id)
  have k := (cons_subset_l I hZF hω hz hm ht hv hu).mp (fun _ => id)
  exact ⟨h.1, hZF.1.eq_of_same_members s t (fun p => ⟨h.2 p, k.2 p⟩)⟩

/-- 直接子边等价于图包含与长度相差一个后继。 -/
theorem tree_step_iff_l (hZF : M.Models ZF) {ω s t n m} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hm : M.mem m ω) (hs : M.IsSetFunctionFromTo I s n ω)
    (ht : M.IsSetFunctionFromTo I t m ω) :
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
    exact ⟨a, m, n, ⟨⟨hm, (hω.isOrdinal hZF).mem hm, ht.1, ht.2.1⟩, hn, h,
      ⟨hn, (hω.isOrdinal hZF).mem hn, hs.1, hs.2.1⟩,
      (ds_restrict_iff_l I hs ht.1).mpr hst, ha⟩⟩

theorem cons_step_l (hZF : M.Models ZF) {ω z a b s t u v n m} (hω : M.IsOmega ω)
    (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a ω) (hb : M.mem b ω)
    (hn : M.mem n ω) (hm : M.mem m ω) (hs : M.IsSetFunctionFromTo I s n ω)
    (ht : M.IsSetFunctionFromTo I t m ω) (hu : Cons_d I z a s u) (hv : Cons_d I z b t v) :
    Step_d I ω u v ↔ a = b ∧ Step_d I ω s t := by
  obtain ⟨j, hj, hjn, huf⟩ := cons_type_l I hZF hω hz ha hn hs hu
  obtain ⟨k, hk, hkm, hvf⟩ := cons_type_l I hZF hω hz hb hm ht hv
  rw [tree_step_iff_l I hZF hω hj hk huf hvf, cons_subset_l I hZF hω hz hn hs hu hv,
    tree_step_iff_l I hZF hω hn hm hs ht]
  constructor
  · rintro ⟨hkj, hab, hst⟩
    have e := Structure.SuccessorOf.predecessor_eq hZF.1 ((hω.isOrdinal hZF).mem hm) hkm hkj
    exact ⟨hab, e.symm ▸ hjn, hst⟩
  · rintro ⟨hab, hmn, hst⟩
    have e := Structure.SuccessorOf.eq hZF.1 hmn hjn
    exact ⟨e ▸ hkm, hab, hst⟩

end YesMetaZFC.SetTheory.Descriptive
