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

/-- 截断也包含原源中所有相关图和小幂集，故原不可达性判断反向保持。 -/
theorem Sc_inaccessible_d.of_rank_l (hZF : M.Models ZF) {ω X α V κ : M.Domain}
    (hX : M.TransitiveSet X) (hp : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (hV : M.mem V X) (rank : Vr_d X α V) (hα : M.IsLimitOrdinal α)
    (h : Sc_inaccessible_d ω V κ) : Sc_inaccessible_d ω X κ := by
  obtain ⟨hω, hκ, h⟩ := h
  have ht := rank.transitive_l hZF hX hV
  have hωX := hX V hV ω hω
  have hκX := hX V hV κ hκ
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hωX⟩⟩
  let nv : Nonempty {x // M.mem x V} := ⟨⟨ω, hω⟩⟩
  let N := rt_model_l X nx
  let Q := rt_model_l V nv
  have pq : ∀ a b, M.mem a V → M.mem b V → ∃ p, M.mem p V ∧ Pair_d M p a b := by
    intro a b ha hb
    obtain ⟨p, hpx, pair⟩ := hp a b (hX V hV a ha) (hX V hV b hb)
    exact ⟨p, rank.pair_mem_l hZF hX hV hα ha hb hpx pair, pair⟩
  let I := rt_pair_l hX nx hZF.1 hp
  let J := rt_pair_l ht nv hZF.1 pq
  let l (x : Q.Domain) : N.Domain := ⟨x.val, hX V hV x.val x.property⟩
  let k : Q.Domain := ⟨κ, hκ⟩
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff J (rt_model_ext_l hZF.1 ht nv),
    Formula.satisfies_isStrongLimitCardinal_iff J (rt_model_ext_l hZF.1 ht nv)] at h
  change M.mem ω κ ∧ Q.IsRegularCardinal J k ∧ Q.IsStrongLimitCardinal J k at h
  obtain ⟨above, hr, hs⟩ := h
  have ho := (rt_ordinal_iff_l ht nv (ZF.modelsKP hZF) k).mp hr.1.1
  have cardinal : N.IsCardinal I (l k) := by
    refine ⟨rt_ordinal_l hX nx (l k) ho, ?_⟩
    rintro μ hμ ⟨f, bf⟩
    have bf := (rt_bijection_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp f μ (l k)).mp bf
    have hμV := ht κ hκ μ.val hμ
    have hf := rank.relation_mem_l hZF hX hV hα hμV hκ f.property (fn0_of_function_l (ZF.modelsKP hZF) bf.1.1).1
    exact hr.1.2 ⟨μ.val, hμV⟩ hμ ⟨⟨f.val, hf⟩,
      (rt_bijection_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq ⟨f.val, hf⟩ ⟨μ.val, hμV⟩ k).mpr bf⟩
  refine ⟨hωX, hκX, ?_⟩
  simp only [sc_inaccessible_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isRegularCardinal_iff I (rt_model_ext_l hZF.1 hX nx),
    Formula.satisfies_isStrongLimitCardinal_iff I (rt_model_ext_l hZF.1 hX nx)]
  change M.mem ω κ ∧ N.IsRegularCardinal I (l k) ∧ N.IsStrongLimitCardinal I (l k)
  refine ⟨above, ⟨cardinal, ?_, ?_⟩, cardinal, ?_⟩
  · obtain ⟨f, cf⟩ := hr.2.1
    obtain ⟨R, range, _⟩ := cf.2.2.1.2.2
    exact ⟨l f, rt_cofinal_down_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp (l f) (l k) (l k) (l R)
      ((rt_range_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq R f).mp range)
      (rt_cofinal_up_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq (ZF.modelsKP hZF) f k k cf)⟩
  · rintro μ ⟨f, cf⟩
    have cf' := rt_cofinal_up_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp (ZF.modelsKP hZF) f μ (l k) cf
    rcases ho.trichotomy hZF.1 cf'.2.1.1.1.1 (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) κ μ.val) with eq | lt | gt
    · exact Or.inl (Subtype.ext (hZF.1.eq_of_same_members κ μ.val eq))
    · exact Or.inr lt
    · have hμV := ht κ hκ μ.val gt
      have hf := rank.relation_mem_l hZF hX hV hα hμV hκ f.property
        (fn0_of_function_l (ZF.modelsKP hZF) cf'.isSetFunctionFromTo).1
      obtain ⟨R, range, _⟩ := cf.2.2.1.2.2
      have range := (rt_range_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp R f).mp range
      have hR := rank.subset_mem_l hX hV hκ R.property (cf'.range_isCofinalSubset hZF.1 range).2.1
      exact (hr.2.2 ⟨μ.val, hμV⟩ ⟨⟨f.val, hf⟩, rt_cofinal_down_l ht nv hZF.1
        (KP.exists_pair (ZF.modelsKP hZF)) pq ⟨f.val, hf⟩ ⟨μ.val, hμV⟩ k ⟨R.val, hR⟩ range cf'⟩).imp
        (fun eq => Subtype.ext (congrArg (fun x : Q.Domain => x.val) eq)) id
  · intro a ha P power
    have haV := ht κ hκ a.val ha
    have bound : ∀ B, M.mem B P.val → M.MemberSubset B a.val := fun B hb z hz =>
      (power ⟨B, hX P.val P.property B hb⟩).mp hb ⟨z, hX B (hX P.val P.property B hb) z hz⟩ hz
    have hPV := rank.subsets_mem_l hX hV hα haV P.property bound
    have pow : Q.IsPowerSetOf ⟨P.val, hPV⟩ ⟨a.val, haV⟩ := fun B =>
      ⟨fun hb z hz => (power (l B)).mp hb (l z) hz,
        fun sub => (power (l B)).mpr (fun z hz => sub ⟨z.val, ht B.val B.property z.val hz⟩ hz)⟩
    obtain ⟨⟨f, inj⟩, not_bij⟩ := hs.2 ⟨a.val, haV⟩ ha ⟨P.val, hPV⟩ pow
    refine ⟨⟨l f, (rt_injection_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp (l f) P (l k)).mpr
      ((rt_injection_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq f ⟨P.val, hPV⟩ k).mp inj)⟩, ?_⟩
    rintro ⟨g, bg⟩
    have bg := (rt_bijection_l hX nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hp g P (l k)).mp bg
    have hg := rank.relation_mem_l hZF hX hV hα hPV hκ g.property (fn0_of_function_l (ZF.modelsKP hZF) bg.1.1).1
    exact not_bij ⟨⟨g.val, hg⟩, (rt_bijection_l ht nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pq ⟨g.val, hg⟩ ⟨P.val, hPV⟩ k).mpr bg⟩

end YesMetaZFC.SetTheory.Internal
