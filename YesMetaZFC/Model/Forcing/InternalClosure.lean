import YesMetaZFC.Model.Forcing.InternalNames
import YesMetaZFC.SetTheory.Collection
import YesMetaZFC.SetTheory.Separation

/-! # 内部名称的递归刻画与集合闭包

反向递归刻画在地模型内部收集子名称的支撑，再分离有效支撑并取并集。集合族与
分离、收集正文都由原公式给出；不将宿主任意谓词当成地模型的分离实例。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Entry_supp_d (B p S : M.Domain) : Prop :=
  ∃ s b, KPair_d M p s b ∧ M.mem s S ∧ M.mem b B ∧ Supp_d M B S

def entry_supp_m {n} (B p S : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m p.weaken.weaken (.bound 1) .newest)
    (.conj (.mem (.bound 1) S.weaken.weaken)
      (.conj (.mem .newest B.weaken.weaken) (supp_m B.weaken.weaken S.weaken.weaken)))))

derive_free_closed entry_supp_m

private def supp_schema_m : UnarySchema 1 where
  body := supp_m (.bound 1) (.bound 0)

private def entry_supp_schema_m : BinarySchema 1 where
  body := entry_supp_m (.bound 2) (.bound 1) (.bound 0)

theorem entry_supp_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B p S : Term n) :
    Formula.satisfies ρ (entry_supp_m B p S) ↔
      Entry_supp_d M (B.eval ρ) (p.eval ρ) (S.eval ρ) := by
  simp only [entry_supp_m, Entry_supp_d, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, kpair_sat_l M hE, supp_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_one_push, Term.eval_bound_zero_push]

/-- 递归刻画只需配对、并集及上面两个明确的模式实例。 -/
structure Name_ops_d : Prop where
  pair : ∀ a b, ∃ p, Pair_d M p a b
  union : ∀ F, ∃ S, M.IsUnionOf S F
  separation : ∀ B T, ∃ F, ∀ S, M.mem S F ↔ M.mem S T ∧ Supp_d M B S
  collection : ∀ B t, (∀ p, M.mem p t → ∃ S, Entry_supp_d M B p S) →
    ∃ T, ∀ p, M.mem p t → ∃ S, M.mem S T ∧ Entry_supp_d M B p S

/-- 已有 ZF 模型自动提供具体实例；调用名称定理时只传所需的窄片段。 -/
theorem name_ops_l (hZF : M.Models ZF) : Name_ops_d M where
  pair := KP.exists_pair (ZF.modelsKP hZF)
  union := KP.exists_union (ZF.modelsKP hZF)
  separation B T := by
    let ρ : Env M 1 := ⟨fun _ => B, fun _ => B⟩
    obtain ⟨F, hF⟩ := ZF.separation_exists_d hZF supp_schema_m ρ T
    refine ⟨F, fun S => (hF S).trans (and_congr_right fun _ => ?_)⟩
    exact supp_sat_l M hZF.1 (ρ.push S) (.bound 1) (.bound 0)
  collection B t h := by
    let ρ : Env M 1 := ⟨fun _ => B, fun _ => B⟩
    obtain ⟨T, hT⟩ := ZF.collection_exists_d hZF entry_supp_schema_m ρ t (fun p hp => by
      obtain ⟨S, hS⟩ := h p hp
      exact ⟨S, (entry_supp_sat_l M hZF.1 ((ρ.push p).push S) (.bound 2) (.bound 1) (.bound 0)).mpr hS⟩)
    refine ⟨T, fun p hp => ?_⟩
    obtain ⟨S, hS, hs⟩ := hT p hp
    exact ⟨S, hS, (entry_supp_sat_l M hZF.1 ((ρ.push p).push S) (.bound 2) (.bound 1) (.bound 0)).mp hs⟩

/-- 配对与并集给出插入操作，供内部支撑和递归图共同使用。 -/
theorem set_insert_l (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (hU : ∀ F, ∃ S, M.IsUnionOf S F) (S t : M.Domain) :
    ∃ W, ∀ z, M.mem z W ↔ M.mem z S ∨ z = t := by
  obtain ⟨T, hT⟩ := hP t t
  obtain ⟨F, hF⟩ := hP S T
  obtain ⟨W, hW⟩ := hU F
  refine ⟨W, fun z => (hW z).trans ?_⟩
  constructor
  · rintro ⟨V, hV, hz⟩
    rcases (hF V).mp hV with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr (((hT z).mp hz).elim id id)
  · rintro (h | rfl)
    · exact ⟨S, (hF S).mpr (Or.inl rfl), h⟩
    · exact ⟨T, (hF T).mpr (Or.inr rfl), (hT z).mpr (Or.inl rfl)⟩

/-- 向一个已有支撑添加新根，只需模型内配对与并集。 -/
theorem name_adjoin_l (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (hU : ∀ F, ∃ S, M.IsUnionOf S F) {B S t} (hS : Supp_d M B S)
    (ht : ∀ p, M.mem p t → ∃ s b, KPair_d M p s b ∧ M.mem s S ∧ M.mem b B) :
    Name_d M B t := by
  obtain ⟨W, hW⟩ := set_insert_l M hP hU S t
  refine ⟨W, (hW t).mpr (Or.inr rfl), fun s hs p hp => ?_⟩
  rcases (hW s).mp hs with hs | rfl
  · obtain ⟨v, b, h, hv, hb⟩ := hS s hs p hp
    exact ⟨v, b, h, (hW v).mpr (Or.inl hv), hb⟩
  · obtain ⟨v, b, h, hv, hb⟩ := ht p hp
    exact ⟨v, b, h, (hW v).mpr (Or.inl hv), hb⟩

theorem name_subset_l (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (hU : ∀ F, ∃ S, M.IsUnionOf S F) {B s t} (ht : Name_d M B t)
    (h : ∀ p, M.mem p s → M.mem p t) : Name_d M B s := by
  obtain ⟨S, ht, hS⟩ := ht
  exact name_adjoin_l M hP hU hS (fun p hp => hS t ht p (h p hp))

/-- 两个内部名称具有同一个模型内闭支撑；不要求条件集非空。 -/
theorem name_support_l (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (hU : ∀ F, ∃ S, M.IsUnionOf S F) {B s t}
    (hs : Name_d M B s) (ht : Name_d M B t) :
    ∃ W, M.mem s W ∧ M.mem t W ∧ Supp_d M B W := by
  obtain ⟨S, hsS, hS⟩ := hs
  obtain ⟨T, htT, hT⟩ := ht
  obtain ⟨F, hF⟩ := hP S T
  obtain ⟨W, hW⟩ := hU F
  have hw V (hV : V = S ∨ V = T) {z} (hz : M.mem z V) : M.mem z W :=
    (hW z).mpr ⟨V, (hF V).mpr hV, hz⟩
  have hC : Supp_d M B W := by
    intro z hz p hp
    obtain ⟨V, hv, hz⟩ := (hW z).mp hz
    rcases (hF V).mp hv with rfl | rfl
    · obtain ⟨a, d, h, ha, hd⟩ := hS z hz p hp
      exact ⟨a, d, h, hw V (Or.inl rfl) ha, hd⟩
    · obtain ⟨a, d, h, ha, hd⟩ := hT z hz p hp
      exact ⟨a, d, h, hw V (Or.inr rfl) ha, hd⟩
  exact ⟨W, hw S (Or.inl rfl) hsS, hw T (Or.inr rfl) htT, hC⟩

/-- 两个带权子名称直接组成模型内名称；有限构造不消费分离或收集。 -/
theorem name_pair_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (hU : ∀ F, ∃ S, M.IsUnionOf S F) {B s t b c}
    (hs : Name_d M B s) (ht : Name_d M B t) (hb : M.mem b B) (hc : M.mem c B) :
    ∃ q, Name_d M B q ∧ ∀ p, M.mem p q ↔ KPair_d M p s b ∨ KPair_d M p t c := by
  obtain ⟨W, hsW, htW, hC⟩ := name_support_l M hP hU hs ht
  obtain ⟨v, hv⟩ := (kpair_interpretation_l M hE hP).total s b
  obtain ⟨w, hw'⟩ := (kpair_interpretation_l M hE hP).total t c
  obtain ⟨q, hq⟩ := hP v w
  refine ⟨q, name_adjoin_l M hP hU hC (fun p hp => ?_), fun p => (hq p).trans ?_⟩
  · rcases (hq p).mp hp with rfl | rfl
    · exact ⟨s, b, hv, hsW, hb⟩
    · exact ⟨t, c, hw', htW, hc⟩
  · exact or_congr ⟨fun h => h ▸ hv, fun h => kpair_unique_l M hE h hv⟩
      ⟨fun h => h ▸ hw', fun h => kpair_unique_l M hE h hw'⟩

/-- 与通常的递归定义等价；反向所需的支撑收集完全发生在地模型内部。 -/
theorem name_unfold_l (O : Name_ops_d M) (B t : M.Domain) :
    Name_d M B t ↔ ∀ p, M.mem p t →
      ∃ s b, KPair_d M p s b ∧ M.mem b B ∧ Name_d M B s := by
  constructor
  · rintro ⟨S, ht, hS⟩ p hp
    obtain ⟨s, b, h, hs, hb⟩ := hS t ht p hp
    exact ⟨s, b, h, hb, S, hs, hS⟩
  · intro h
    obtain ⟨T, hT⟩ := O.collection B t (fun p hp => by
      obtain ⟨s, b, h, hb, S, hs, hS⟩ := h p hp
      exact ⟨S, s, b, h, hs, hb, hS⟩)
    obtain ⟨F, hF⟩ := O.separation B T
    obtain ⟨S, hS⟩ := O.union F
    have hs : Supp_d M B S := by
      intro s hss p hp
      obtain ⟨V, hv, hsV⟩ := (hS s).mp hss
      obtain ⟨v, b, h, hvV, hb⟩ := ((hF V).mp hv).2 s hsV p hp
      exact ⟨v, b, h, (hS v).mpr ⟨V, hv, hvV⟩, hb⟩
    apply name_adjoin_l M O.pair O.union hs
    intro p hp
    obtain ⟨V, hv, s, b, h, hsV, hb, hV⟩ := hT p hp
    exact ⟨s, b, h, (hS s).mpr ⟨V, (hF V).mpr ⟨hv, hV⟩, hsV⟩, hb⟩

end YesMetaZFC.Model.Forcing.Internal
