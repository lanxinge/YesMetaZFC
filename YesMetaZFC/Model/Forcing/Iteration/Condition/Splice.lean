import YesMetaZFC.Model.Forcing.Iteration.Condition.Support
import YesMetaZFC.SetTheory.Card.CountablePair

/-! # 内部迭代条件的前缀替换

用 q 替换 p 在 α 以内的坐标，保留 α 以外的尾部。实际集合由分离和二元并
构造；互不相交的坐标保证函数性，支撑包含于两份原支撑的并。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Row_splice_d (α q p r : M.Domain) : Prop :=
  ∀ v, M.mem v r ↔ M.mem v q ∨ ∃ i s, KPair_d M v i s ∧ M.mem v p ∧ ¬ M.mem i α

def row_splice_m {n} (α q p r : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest r.weaken) (.disj (.mem .newest q.weaken)
    (.existsE (.existsE (.conj (kpair_m (.bound 2) (.bound 1) .newest)
      (.conj (.mem (.bound 2) p.weaken.weaken.weaken) (.neg (.mem (.bound 1) α.weaken.weaken.weaken))))))))
derive_free_closed row_splice_m

theorem row_splice_sat_l (hE : Extensional M) {n} (ρ : Env M n) (α q p r : Term n) :
    Formula.satisfies ρ (row_splice_m α q p r) ↔
      Row_splice_d M (α.eval ρ) (q.eval ρ) (p.eval ρ) (r.eval ρ) := by
  simp only [row_splice_m, Row_splice_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_disj_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, kpair_sat_l M hE, Formula.satisfies_neg_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem row_splice_exists_l (hZF : M.Models ZF) (α q p : M.Domain) : ∃ r, Row_splice_d M α q p r := by
  let ρ : Env M 1 := ⟨fun _ => α, fun _ => α⟩
  let φ : UnarySchema 1 := {
    body := .existsE (.existsE (.conj (kpair_m (.bound 2) (.bound 1) .newest)
      (.neg (.mem (.bound 1) (.bound 3))))) }
  have hφ v : φ.denote ρ v ↔ ∃ i s, KPair_d M v i s ∧ ¬ M.mem i α := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff]
    rfl
  obtain ⟨a, ha⟩ := ZF.separation_exists_d hZF φ ρ p
  obtain ⟨r, hr⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) q a
  refine ⟨r, fun v => (hr v).trans ?_⟩
  simp only [UnarySchema.denote] at hφ
  rw [ha v, hφ v]
  exact or_congr_right ⟨fun ⟨hv, i, s, his, hi⟩ => ⟨i, s, his, hv, hi⟩,
    fun ⟨i, s, his, hv, hi⟩ => ⟨hv, i, s, his, hi⟩⟩

theorem row_splice_unique_l (hE : Extensional M) {α q p r r'}
    (h : Row_splice_d M α q p r) (h' : Row_splice_d M α q p r') : r = r' :=
  hE.eq_of_same_members r r' (fun v => (h v).trans (h' v).symm)

theorem row_splice_entry_l {α q p r} (h : Row_splice_d M α q p r) (i s) :
    Entry_d M i s r ↔ Entry_d M i s q ∨ (Entry_d M i s p ∧ ¬ M.mem i α) := by
  constructor
  · rintro ⟨v, hv, hvr⟩
    rcases (h v).mp hvr with hvq | ⟨j, t, hvt, hvp, hj⟩
    · exact Or.inl ⟨v, hv, hvq⟩
    · obtain ⟨rfl, rfl⟩ := kpair_injective_l M hv hvt
      exact Or.inr ⟨⟨v, hv, hvp⟩, hj⟩
  · rintro (⟨v, hv, hvq⟩ | ⟨⟨v, hv, hvp⟩, hi⟩)
    · exact ⟨v, hv, (h v).mpr (Or.inl hvq)⟩
    · exact ⟨v, hv, (h v).mpr (Or.inr ⟨i, s, hv, hvp, hi⟩)⟩

variable {M}

theorem row_splice_row_l {α β q p r} (hq : Row_d M α q) (hp : Row_d M β p)
    (hαβ : M.MemberSubset α β) (h : Row_splice_d M α q p r) : Row_d M β r := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact ((h v).mp hv).elim (hq.graph v) (fun ⟨i, s, hv, _, _⟩ => ⟨i, s, hv⟩)
  · intro i s t hs ht
    rcases (row_splice_entry_l M h i s).mp hs with hs | ⟨hs, hi⟩ <;>
      rcases (row_splice_entry_l M h i t).mp ht with ht | ⟨ht, hj⟩
    · exact hq.functional i s t hs ht
    · exact False.elim (hj (hq.domain i s hs))
    · exact False.elim (hi (hq.domain i t ht))
    · exact hp.functional i s t hs ht
  · intro i s hs
    exact ((row_splice_entry_l M h i s).mp hs).elim (fun hs => hαβ i (hq.domain i s hs))
      (fun hs => hp.domain i s hs.1)

theorem row_splice_prefix_l {α q p r} (hq : Row_d M α q) (h : Row_splice_d M α q p r) (i s) :
    Entry_d M i s q ↔ M.mem i α ∧ Entry_d M i s r := by
  constructor
  · intro hs
    exact ⟨hq.domain i s hs, (row_splice_entry_l M h i s).mpr (Or.inl hs)⟩
  · rintro ⟨hi, hs⟩
    exact ((row_splice_entry_l M h i s).mp hs).elim id (fun hs => False.elim (hs.2 hi))

theorem row_splice_absorb_l (hE : Extensional M) {α q p r} (hp : Row_d M α p)
    (h : Row_splice_d M α q p r) : r = q := by
  apply hE.eq_of_same_members r q
  intro v
  exact (h v).trans ⟨fun hh => hh.elim id (fun ⟨i, s, his, hv, hi⟩ =>
    False.elim (hi (hp.domain i s ⟨v, his, hv⟩))), Or.inl⟩

/-- 在较长位置再次替换前缀，会覆盖较短位置的替换，原尾部完全不变。 -/
theorem row_splice_overwrite_l {α β c p w d r} (hαβ : M.MemberSubset α β) (hc : Row_d M α c)
    (hw : Row_splice_d M α c p w) (hr : Row_splice_d M β d w r) : Row_splice_d M β d p r := by
  intro v
  refine (hr v).trans (or_congr_right ⟨?_, ?_⟩)
  · rintro ⟨i, s, his, hvw, hi⟩
    rcases (hw v).mp hvw with hvc | ⟨j, t, _, hvp, _⟩
    · exact (hi (hαβ i (hc.domain i s ⟨v, his, hvc⟩))).elim
    · exact ⟨i, s, his, hvp, hi⟩
  · rintro ⟨i, s, his, hvp, hi⟩
    exact ⟨i, s, his, (hw v).mpr (Or.inr ⟨i, s, his, hvp, fun h => hi (hαβ i h)⟩), hi⟩

/-- 原函数图由其限制和对应尾部精确拼回。 -/
theorem row_splice_restore_l (hE : Extensional M) {α a p}
    (hp : ∀ v, M.mem v p → ∃ i s, KPair_d M v i s)
    (ha : ∀ v, M.mem v a → ∃ i s, KPair_d M v i s)
    (hcut : ∀ i s, Entry_d M i s a ↔ M.mem i α ∧ Entry_d M i s p) : Row_splice_d M α a p p := by
  intro v
  constructor
  · intro hv
    obtain ⟨i, s, his⟩ := hp v hv
    classical
    by_cases hi : M.mem i α
    · obtain ⟨w, hw, hwa⟩ := (hcut i s).mpr ⟨hi, v, his, hv⟩
      exact Or.inl ((kpair_unique_l M hE hw his) ▸ hwa)
    · exact Or.inr ⟨i, s, his, hv, hi⟩
  · rintro (hv | ⟨_, _, _, hv, _⟩)
    · obtain ⟨i, s, his⟩ := ha v hv
      obtain ⟨w, hw, hwp⟩ := ((hcut i s).mp ⟨v, his, hv⟩).2
      exact (kpair_unique_l M hE hw his) ▸ hwp
    · exact hv

/-- 限制到包含被替换前缀的阶段，与前缀替换交换。 -/
theorem row_splice_cut_l (hE : Extensional M) {α β q p r b d}
    (hαβ : M.MemberSubset α β) (hq : ∀ v, M.mem v q → ∃ i s, KPair_d M v i s)
    (hdom : ∀ i s, Entry_d M i s q → M.mem i α)
    (hd : ∀ v, M.mem v d → ∃ i s, KPair_d M v i s)
    (hb : ∀ i s, Entry_d M i s b ↔ M.mem i β ∧ Entry_d M i s p)
    (hrd : ∀ i s, Entry_d M i s d ↔ M.mem i β ∧ Entry_d M i s r)
    (hr : Row_splice_d M α q p r) : Row_splice_d M α q b d := by
  have mem {v i s X} (hv : KPair_d M v i s) (hs : Entry_d M i s X) : M.mem v X := by
    obtain ⟨w, hw, hwX⟩ := hs
    exact (kpair_unique_l M hE hw hv) ▸ hwX
  intro v
  constructor
  · intro hv
    obtain ⟨i, s, his⟩ := hd v hv
    obtain ⟨hi, hir⟩ := (hrd i s).mp ⟨v, his, hv⟩
    rcases (row_splice_entry_l M hr i s).mp hir with hq | ⟨hp, hiα⟩
    · exact Or.inl (mem his hq)
    · exact Or.inr ⟨i, s, his, mem his ((hb i s).mpr ⟨hi, hp⟩), hiα⟩
  · rintro (hv | ⟨i, s, his, hv, hi⟩)
    · obtain ⟨i, s, his⟩ := hq v hv
      have hqs : Entry_d M i s q := ⟨v, his, hv⟩
      exact mem his ((hrd i s).mpr ⟨hαβ i (hdom i s hqs), (row_splice_entry_l M hr i s).mpr (Or.inl hqs)⟩)
    · obtain ⟨hiβ, hp⟩ := (hb i s).mp ⟨v, his, hv⟩
      exact mem his ((hrd i s).mpr ⟨hiβ, (row_splice_entry_l M hr i s).mpr (Or.inr ⟨hp, hi⟩)⟩)

/-- 两层限制之间的拼接结合律；先替换较短前缀，再提升到较长前缀，尾部不变。 -/
theorem row_splice_nested_l (hE : Extensional M) {α β q b p d r} (hαβ : M.MemberSubset α β)
    (hcut : ∀ i s, Entry_d M i s b ↔ M.mem i β ∧ Entry_d M i s p)
    (hd : Row_splice_d M α q b d) (hr : Row_splice_d M α q p r) : Row_splice_d M β d p r := by
  have cut v i s (hv : KPair_d M v i s) : M.mem v b ↔ M.mem i β ∧ M.mem v p := by
    constructor
    · intro hvb
      obtain ⟨hi, w, hw, hwp⟩ := (hcut i s).mp ⟨v, hv, hvb⟩
      exact ⟨hi, (kpair_unique_l M hE hw hv) ▸ hwp⟩
    · rintro ⟨hi, hvp⟩
      obtain ⟨w, hw, hwb⟩ := (hcut i s).mpr ⟨hi, v, hv, hvp⟩
      exact (kpair_unique_l M hE hw hv) ▸ hwb
  intro v
  rw [hr v, hd v]
  constructor
  · rintro (hv | ⟨i, s, his, hv, hi⟩)
    · exact Or.inl (Or.inl hv)
    · classical
      by_cases hiβ : M.mem i β
      · exact Or.inl (Or.inr ⟨i, s, his, (cut v i s his).mpr ⟨hiβ, hv⟩, hi⟩)
      · exact Or.inr ⟨i, s, his, hv, hiβ⟩
  · rintro ((hv | ⟨i, s, his, hv, hi⟩) | ⟨i, s, his, hv, hi⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨i, s, his, ((cut v i s his).mp hv).2, hi⟩
    · exact Or.inr ⟨i, s, his, hv, fun h => hi (hαβ i h)⟩

/-- 后继步保留同一末坐标名称，正是对旧条件作前缀替换。 -/
theorem row_append_splice_l (hE : Extensional M) {α t a q s p r}
    (hα : ¬ M.mem α α) (ha : Row_d M α a)
    (hp : Row_append_d M α t a s p) (hr : Row_append_d M α t q s r) : Row_splice_d M α q p r := by
  have noTail v (hv : M.mem v a) i s (his : KPair_d M v i s) (hi : ¬ M.mem i α) : False :=
    hi (ha.domain i s ⟨v, his, hv⟩)
  rcases hp with ⟨hs, rfl⟩ | ⟨hs, v, hv, hp⟩ <;> rcases hr with ⟨hs', rfl⟩ | ⟨hs', w, hw, hr⟩
  · exact fun v => ⟨Or.inl, fun hh => hh.elim id (fun ⟨i, s, his, hv, hi⟩ => False.elim (noTail v hv i s his hi))⟩
  · exact False.elim (hs' hs)
  · exact False.elim (hs hs')
  · have he := kpair_unique_l M hE hw hv
    subst w
    intro w
    rw [hr w]
    refine or_congr_right ⟨?_, ?_⟩
    · intro he
      subst w
      exact ⟨α, s, hv, (hp v).mpr (Or.inr rfl), hα⟩
    · rintro ⟨i, s', his, hwp, hi⟩
      exact ((hp w).mp hwp).elim (fun hwa => False.elim (noTail w hwa i s' his hi)) id

/-- 替换前缀只合并两份支撑；有限和可数两种情形都在 ZF 中封闭。 -/
theorem row_splice_supp_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
    {k ω α q p r} (hω : M.IsOmega ω) (hq : Row_supp_d I k ω q) (hp : Row_supp_d I k ω p)
    (h : Row_splice_d M α q p r) : Row_supp_d I k ω r := by
  obtain ⟨D, hD, hd⟩ := hq
  obtain ⟨E, hE, he⟩ := hp
  obtain ⟨U, hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) D E
  obtain ⟨F, hF⟩ := coord_exists_l M hZF r
  have hu : Supp_size_d I k ω U := by
    cases k with
    | false => exact ZF.finite_union_l I hZF hω hd he hU
    | true => exact ZF.countable_union_two_l I hZF hω hd he hU
  refine ⟨F, hF, supp_size_subset_l I hZF hu (fun i hi => ?_)⟩
  obtain ⟨s, hs⟩ := (hF i).mp hi
  exact (hU i).mpr (((row_splice_entry_l M h i s).mp hs).elim
    (fun hs => Or.inl ((hD i).mpr ⟨s, hs⟩)) (fun hs => Or.inr ((hE i).mpr ⟨s, hs.1⟩)))

end YesMetaZFC.Model.Forcing.Internal
