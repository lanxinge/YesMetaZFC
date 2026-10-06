import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessible

/-! # 原始不可达性在严格极限秩段中的保持

共尾序列及其值域、幂集上的单射都由原源提供，再由实际秩闭包回收。
秩段的相对幂集包含原源已有的全部子集；不假定外部子集也在原源中。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem Sc_inaccessible_d.rank_l (hZF : M.Models ZF) {ω X α V κ : M.Domain}
    (hX : M.TransitiveSet X) (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (hV : M.mem V X) (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α) (hκ : M.mem κ V)
    (h : Sc_inaccessible_d ω X κ) : Sc_inaccessible_d ω V κ := by
  obtain ⟨hωX, hκX, h⟩ := h
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hωX⟩⟩
  let N := rt_model_l X nx
  let J := rt_pair_l hX nx hZF.1 hp
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff J (rt_model_ext_l hZF.1 hX nx),
    Formula.satisfies_isStrongLimitCardinal_iff J (rt_model_ext_l hZF.1 hX nx)] at h
  change M.mem ω κ ∧ N.IsRegularCardinal J ⟨κ, hκX⟩ ∧ N.IsStrongLimitCardinal J ⟨κ, hκX⟩ at h
  obtain ⟨above, hr, hs⟩ := h
  have ht := rank.transitive_l hZF hX hV
  have hωV := ht κ hκ ω above
  let nv : Nonempty {x // M.mem x V} := ⟨⟨ω, hωV⟩⟩
  let Q := rt_model_l V nv
  have pq : ∀ a b, M.mem a V → M.mem b V → ∃ p, M.mem p V ∧ Pair_d M p a b := by
    intro a b ha hb
    obtain ⟨p, hpx, pair⟩ := hp a b (hX V hV a ha) (hX V hV b hb)
    exact ⟨p, rank.pair_mem_l hZF hX hV hα ha hb hpx pair, pair⟩
  let K := rt_pair_l ht nv hZF.1 pq
  let l (x : Q.Domain) : N.Domain := ⟨x.val, hX V hV x.val x.property⟩
  let k : Q.Domain := ⟨κ, hκ⟩
  have cardinal := rt_cardinal_restrict_l hX nx hZF.1 hp
    (ZF.modelsKP hZF) ht nv pq (hX V hV) k hr.1
  refine ⟨hωV, hκ, ?_⟩
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff K (rt_model_ext_l hZF.1 ht nv),
    Formula.satisfies_isStrongLimitCardinal_iff K (rt_model_ext_l hZF.1 ht nv)]
  change M.mem ω κ ∧ Q.IsRegularCardinal K k ∧ Q.IsStrongLimitCardinal K k
  refine ⟨above, ⟨cardinal, ?_, ?_⟩, cardinal, ?_⟩
  -- 保留原共尾图及其实际值域；较短共尾序列反向读入原源，违反原正则性。
  · obtain ⟨f, cofinal⟩ := hr.2.1
    have cf := rt_cofinal_up_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp (ZF.modelsKP hZF) f (l k) (l k) cofinal
    have ff := cf.isSetFunctionFromTo
    have hf := rank.relation_mem_l hZF hX hV hα hκ hκ f.property (fun p hpf => by
      obtain ⟨a, b, pair⟩ := ff.1.1 p hpf
      exact ⟨a, ff.input_mem_of_pairMember ⟨p, pair, hpf⟩, b, ff.output_mem_of_pairMember ⟨p, pair, hpf⟩, pair⟩)
    obtain ⟨R, range, _⟩ := cofinal.2.2.1.2.2
    have range := (rt_range_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp R f).mp range
    have hR := rank.subset_mem_l hX hV hκ R.property (cf.range_isCofinalSubset hZF.1 range).2.1
    exact ⟨⟨f.val, hf⟩, rt_cofinal_down_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq
      ⟨f.val, hf⟩ k k ⟨R.val, hR⟩ range cf⟩
  · rintro μ ⟨f, cofinal⟩
    have cf := rt_cofinal_up_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq (ZF.modelsKP hZF) f μ k cofinal
    obtain ⟨R, range, _⟩ := cofinal.2.2.1.2.2
    have range := (rt_range_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq R f).mp range
    rcases hr.2.2 (l μ) ⟨l f, rt_cofinal_down_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp
      (l f) (l μ) (l k) (l R) range cf⟩ with eq | lt
    · exact Or.inl (Subtype.ext (congrArg (fun x : N.Domain => x.val) eq))
    · exact Or.inr lt
  -- 截断包含原源已有的每个小子集，所以两源的相对幂集相同。
  · intro a ha P power
    have pow : N.IsPowerSetOf (l P) (l a) := by
      intro B
      refine ⟨fun hb z hz => ?_, fun sub => ?_⟩
      · have hB := ht P.val P.property B.val hb
        exact (power ⟨B.val, hB⟩).mp hb ⟨z.val, ht B.val hB z.val hz⟩ hz
      · have sub' : M.MemberSubset B.val a.val := fun z hz => sub ⟨z, hX B.val B.property z hz⟩ hz
        have hB := rank.subset_mem_l hX hV a.property B.property sub'
        exact (power ⟨B.val, hB⟩).mpr (fun z hz => sub (l z) hz)
    obtain ⟨⟨f, ff⟩, not_bij⟩ := hs.2 (l a) ha (l P) pow
    have ff := (rt_injection_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp f (l P) (l k)).mp ff
    have hf := rank.relation_mem_l hZF hX hV hα P.property hκ f.property (fun p hpf => by
      obtain ⟨a, b, pair⟩ := ff.1.1.1 p hpf
      exact ⟨a, ff.1.input_mem_of_pairMember ⟨p, pair, hpf⟩, b, ff.1.output_mem_of_pairMember ⟨p, pair, hpf⟩, pair⟩)
    refine ⟨⟨⟨f.val, hf⟩, (rt_injection_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq ⟨f.val, hf⟩ P k).mpr ff⟩, ?_⟩
    rintro ⟨g, gg⟩
    exact not_bij ⟨l g, (rt_bijection_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp (l g) (l P) (l k)).mpr
      ((rt_bijection_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq g P k).mp gg)⟩

end YesMetaZFC.SetTheory.Internal
