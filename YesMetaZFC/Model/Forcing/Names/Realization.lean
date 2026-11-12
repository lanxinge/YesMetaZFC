import YesMetaZFC.SetTheory.Kuratowski
import YesMetaZFC.SetTheory.Collection
import YesMetaZFC.SetTheory.Separation
import YesMetaZFC.Model.Forcing.External.Extension
import YesMetaZFC.Model.SmallGraph.ZFC

/-! # 地模型内部的名称谓词

名称是模型中的集合 τ：模型内部存在包含 τ 的支撑集 S，S 中每个对象的成员
都编码为 (σ,b)，其中 σ 仍在 S，b 属于给定条件集。所有量词均遍历模型对象，
并给出同一条件的实际 Project 公式；定义不预设宿主名称域或外部良基性。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Entry_d (s b t : M.Domain) : Prop := ∃ p, KPair_d M p s b ∧ M.mem p t

/-- 实际有序对图由逐条目关系唯一确定；不要求图是函数。 -/
theorem entry_ext_l (hE : Extensional M) {P Q}
    (hP : ∀ v, M.mem v P → ∃ a b, KPair_d M v a b)
    (hQ : ∀ v, M.mem v Q → ∃ a b, KPair_d M v a b)
    (h : ∀ a b, Entry_d M a b P ↔ Entry_d M a b Q) : P = Q := by
  have sub {P Q} (hP : ∀ v, M.mem v P → ∃ a b, KPair_d M v a b)
      (h : ∀ a b, Entry_d M a b P → Entry_d M a b Q) : M.MemberSubset P Q := by
    intro v hv
    obtain ⟨a, b, hab⟩ := hP v hv
    obtain ⟨w, hw, hwQ⟩ := h a b ⟨v, hab, hv⟩
    exact (kpair_unique_l M hE hw hab) ▸ hwQ
  exact hE.eq_of_same_members P Q (fun v =>
    ⟨sub hP (fun a b => (h a b).mp) v, sub hQ (fun a b => (h a b).mpr) v⟩)

def Supp_d (B S : M.Domain) : Prop :=
  ∀ t, M.mem t S → ∀ p, M.mem p t →
    ∃ s b, KPair_d M p s b ∧ M.mem s S ∧ M.mem b B

def Name_d (B t : M.Domain) : Prop := ∃ S, M.mem t S ∧ Supp_d M B S

def supp_m {n} (B S : Term n) : Formula 1 n :=
  Formula.forallMem S (Formula.forallMem .newest (.existsE (.existsE
    (.conj (kpair_m (.bound 2) (.bound 1) .newest)
      (.conj (.mem (.bound 1) S.weaken.weaken.weaken.weaken)
        (.mem .newest B.weaken.weaken.weaken.weaken))))))

derive_free_closed supp_m

def name_m {n} (B t : Term n) : Formula 1 n :=
  .existsE (.conj (.mem t.weaken .newest) (supp_m B.weaken .newest))

derive_free_closed name_m

theorem supp_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B S : Term n) :
    Formula.satisfies ρ (supp_m B S) ↔ Supp_d M (B.eval ρ) (S.eval ρ) := by
  simp only [supp_m, Supp_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, kpair_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]

theorem name_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B t : Term n) :
    Formula.satisfies ρ (name_m B t) ↔ Name_d M (B.eval ρ) (t.eval ρ) := by
  simp only [name_m, Name_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, supp_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

theorem supp_entry_l {B S s b t} (hS : Supp_d M B S) (ht : M.mem t S)
    (h : Entry_d M s b t) : M.mem s S ∧ M.mem b B := by
  obtain ⟨p, hp, hpt⟩ := h
  obtain ⟨s', b', hp', hs, hb⟩ := hS t ht p hpt
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hp'
  exact ⟨hs, hb⟩

/-- 子名称与标签都来自同一个模型内支撑集和条件集。 -/
theorem name_entry_l {B s b t} (ht : Name_d M B t) (h : Entry_d M s b t) :
    Name_d M B s ∧ M.mem b B := by
  obtain ⟨S, ht, hS⟩ := ht
  obtain ⟨hs, hb⟩ := supp_entry_l M hS ht h
  exact ⟨⟨S, hs, hS⟩, hb⟩

theorem entry_descent_l {s b t} (h : Entry_d M s b t) : Relation.TransGen M.mem s t :=
  h.elim fun _ h => kpair_descent_l M h.1 h.2

/-- 空名称只需要模型内的一个空集和它的单元素支撑。 -/
theorem name_empty_l (hP : ∀ a b, ∃ p, Pair_d M p a b) (B e : M.Domain)
    (he : ∀ z, ¬ M.mem z e) : Name_d M B e := by
  obtain ⟨S, hS⟩ := hP e e
  refine ⟨S, (hS e).mpr (Or.inl rfl), ?_⟩
  intro t ht p hp
  have ht : t = e := ((hS t).mp ht).elim id id
  exact False.elim (he p (ht ▸ hp))

end YesMetaZFC.Model.Forcing.Internal

/-! ## 内部名称的递归刻画与集合闭包

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

theorem entry_union_l {C F} (hF : M.IsUnionOf F C) (x t : M.Domain) :
    Entry_d M x t F ↔ ∃ G, M.mem G C ∧ Entry_d M x t G := by
  constructor
  · rintro ⟨p, hp, ht⟩
    obtain ⟨G, hG, ht⟩ := (hF p).mp ht
    exact ⟨G, hG, p, hp, ht⟩
  · rintro ⟨G, hG, p, hp, ht⟩
    exact ⟨p, hp, (hF p).mpr ⟨G, hG, ht⟩⟩

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

/-! ## 内部名称的小图呈现

节点取支撑集与条件集的小呈现的乘积，再添一个根。标签仍是地模型中的条件对象，
不假设内部布尔代数具有宿主任意上确界。空条件集也允许，根的非成员标签不参与求值。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open Boolean SmallGraph SetTheory
universe u v
variable (M : SetTheory.Structure.{u})

/-- 模型中每个集合有指定层级的小呈现；只要求存在，不选择全局呈现函数。 -/
def Setlike_d : Prop := ∀ x : M.Domain, ∃ (I : Type v) (f : I → M.Domain),
  ∀ z, M.mem z x ↔ ∃ i, z = f i

def node_l {I J : Type v} (t : M.Domain) (s : I → M.Domain) : Option (I × J) → M.Domain
  | none => t
  | some a => s a.1

def decode_graph_l (hM : _root_.WellFounded M.mem) {I J : Type v}
    (t : M.Domain) (s : I → M.Domain) (b : J → M.Domain) : BV_graph.{v, u} M.Domain where
  Domain := Option (I × J)
  nonempty := ⟨none⟩
  root := none
  mem a c := match a with
    | none => False
    | some a => Entry_d M (s a.1) (b a.2) (node_l M t s c)
  val a _ := match a with
    | none => t
    | some a => b a.2
  wf := ⟨fun a => (InvImage.wf (node_l M t s) hM.transGen).induction a fun a ih =>
    Acc.intro a fun c hc => by
      cases c with
      | none => exact hc.elim
      | some c => exact ih _ (entry_descent_l M hc)⟩

/-- 逐节点保留并覆盖全部内部带权成员；重复呈现同一子名称是允许的。 -/
def Rep_d (B t : M.Domain) (G : BV_graph.{v, u} M.Domain) : Prop :=
  Name_d M B t ∧ ∃ c : G.Domain → M.Domain, c G.root = t ∧
    (∀ a d, G.mem a d → Entry_d M (c a) (G.val a d) (c d)) ∧
    (∀ d s b, Entry_d M s b (c d) → ∃ a, G.mem a d ∧ c a = s ∧ G.val a d = b)

theorem decode_rep_l (hM : _root_.WellFounded M.mem) {I J : Type v}
    {B S t : M.Domain} (s : I → M.Domain) (b : J → M.Domain)
    (hs : ∀ z, M.mem z S ↔ ∃ i, z = s i) (hb : ∀ z, M.mem z B ↔ ∃ j, z = b j)
    (ht : M.mem t S) (hS : Supp_d M B S) : Rep_d M B t (decode_graph_l M hM t s b) := by
  have hn (a : Option (I × J)) : M.mem (node_l M t s a) S := by
    cases a with
    | none => exact ht
    | some a => exact (hs _).mpr ⟨a.1, rfl⟩
  refine ⟨⟨S, ht, hS⟩, node_l M t s, rfl, ?_, ?_⟩
  · intro a d h
    cases a with
    | none => exact h.elim
    | some a => exact h
  · intro d x c h
    obtain ⟨hx, hc⟩ := supp_entry_l M hS (hn d) h
    obtain ⟨i, rfl⟩ := (hs x).mp hx
    obtain ⟨j, rfl⟩ := (hb c).mp hc
    exact ⟨some (i, j), h, rfl, rfl⟩

/-- 直接从内部名称取得原节点层级的小图；所有存在见证均留在 Prop 中。 -/
theorem decode_exists_l (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
    {B t : M.Domain} (h : Name_d M B t) : ∃ G : BV_graph.{v, u} M.Domain, Rep_d M B t G := by
  obtain ⟨S, ht, hS⟩ := h
  obtain ⟨I, s, hs⟩ := hL S
  obtain ⟨J, b, hb⟩ := hL B
  exact ⟨decode_graph_l M hM t s b, decode_rep_l M hM s b hs hb ht hS⟩

theorem rep_child_l {B t : M.Domain} {G : BV_graph.{v, u} M.Domain}
    (h : Rep_d M B t G) (a : G.Child G.root) :
    ∃ s, Entry_d M s (G.val a G.root) t ∧ Rep_d M B s (G.at_node a) := by
  obtain ⟨ht, c, hr, hf, hb⟩ := h
  have ha : Entry_d M (c a) (G.val a G.root) t := hr ▸ hf a G.root a.2
  exact ⟨c a, ha, (name_entry_l M ht ha).1, c, rfl, hf, hb⟩

/-- 同一内部名称的不同图呈现给出同一个实际求值，不需要泛型性假设。 -/
theorem rep_val_eq_l (U : M.Domain → Prop) {B t : M.Domain}
    {G H : BV_graph.{v, u} M.Domain} (h : Rep_d M B t G) (k : Rep_d M B t H) :
    val_l U G = val_l U H := by
  obtain ⟨_, c, hc, hf, hb⟩ := h
  obtain ⟨_, d, hd, kf, kb⟩ := k
  apply SG_set.mk_eq.mpr
  refine ⟨fun a b => c a = d b, ?_, hc.trans hd.symm⟩
  intro a b hab
  constructor
  · rintro a' ⟨ha, hu⟩
    have he := hf a' a ha
    rw [hab] at he
    obtain ⟨b', hb', hc', hv⟩ := kb b _ _ he
    exact ⟨b', ⟨hb', hv.symm ▸ hu⟩, hc'.symm⟩
  · rintro b' ⟨hb', hu⟩
    have he := kf b' b hb'
    rw [← hab] at he
    obtain ⟨a', ha', hd', hv⟩ := hb a _ _ he
    exact ⟨a', ⟨ha', hv.symm ▸ hu⟩, hd'⟩

def Val_d (B : M.Domain) (U : M.Domain → Prop) (t : M.Domain) (x : SG_set.{v}) : Prop :=
  ∃ G : BV_graph.{v, u} M.Domain, Rep_d M B t G ∧ val_l U G = x

theorem val_exists_unique_l (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
    (B : M.Domain) (U : M.Domain → Prop) {t : M.Domain} (h : Name_d M B t) :
    ∃ x : SG_set.{v}, Val_d M B U t x ∧ ∀ y, Val_d M B U t y → y = x := by
  obtain ⟨G, hG⟩ := decode_exists_l M hM hL h
  refine ⟨val_l U G, ⟨G, hG, rfl⟩, ?_⟩
  rintro y ⟨H, hH, rfl⟩
  exact rep_val_eq_l M U hH hG

/-- 求值递归式直接使用地模型内的有序对成员和条件对象。 -/
theorem val_mem_l {B t : M.Domain} {U : M.Domain → Prop} {x y : SG_set.{v}}
    (h : Val_d M B U t x) : y ∈ x ↔
      ∃ s b, Entry_d M s b t ∧ U b ∧ Val_d M B U s y := by
  obtain ⟨G, hG, rfl⟩ := h
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := (Forcing.val_mem_l U G y).mp hy
    obtain ⟨s, hs, hg⟩ := rep_child_l M hG a
    exact ⟨s, G.val a G.root, hs, ha, G.at_node a, hg, rfl⟩
  · rintro ⟨s, b, hs, hu, H, hH, rfl⟩
    obtain ⟨ht, c, hr, hf, hb⟩ := hG
    obtain ⟨a, ha, hc, hv⟩ := hb G.root s b (hr ▸ hs)
    have hg : Rep_d M B s (G.at_node a) :=
      ⟨(name_entry_l M ht hs).1, c, hc, hf, hb⟩
    exact (Forcing.val_mem_l U G _).mpr
      ⟨⟨a, ha⟩, hv.symm ▸ hu, rep_val_eq_l M U hH hg⟩

/-- 内部名称的全部小图呈现接入现有相对名称域；非空性只要求存在一个内部名称。 -/
def name_domain_l (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
    (B : M.Domain) (hN : ∃ t, Name_d M B t) : Name_domain_l.{v, u} M.Domain where
  mem G := ∃ t, Rep_d M B t G
  inhabited := by
    obtain ⟨t, ht⟩ := hN
    obtain ⟨G, hG⟩ := decode_exists_l M hM hL ht
    exact ⟨G, t, hG⟩
  child_closed := by
    rintro G ⟨t, ht⟩ a
    obtain ⟨s, _, hs⟩ := rep_child_l M ht a
    exact ⟨s, hs⟩

theorem ext_iff_l (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
    (B : M.Domain) (hN : ∃ t, Name_d M B t) (U : M.Domain → Prop) (x : SG_set.{v}) :
    Ext_l (name_domain_l M hM hL B hN) U x ↔ ∃ t, Val_d M B U t x :=
  ⟨fun ⟨G, ⟨t, hG⟩, e⟩ => ⟨t, G, hG, e⟩,
    fun ⟨t, G, hG, e⟩ => ⟨G, ⟨t, hG⟩, e⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 小图地模型中的实际内部名称

把原布尔名称逐节点编码成模型内的有序对集合，条件集和全体子名称支撑也直接由
小图并合构造。编码、解码与求值保持原小节点层级；不存在代表元选择函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open Boolean SmallGraph SetTheory
universe u

def sg_kpair_l : kpair_convention_l.Interpretation sg_structure.{u} :=
  kpair_interpretation_l sg_structure sg_extensional SG_set.pair

def pair_graph_l (G H : WF_graph.{u}) : WF_graph.{u} :=
  WF_graph.root_sum (fun i : PUnit.{u+1} ⊕ PUnit.{u+1} => i.elim (fun _ => G) (fun _ => H))

theorem pair_graph_spec_l (G H : WF_graph.{u}) :
    Pair_d sg_structure (SG_set.mk (pair_graph_l G H)) (SG_set.mk G) (SG_set.mk H) := by
  intro z
  refine (SG_set.mem_sum _ z).trans ?_
  constructor
  · rintro ⟨i, h⟩
    cases i with
    | inl _ => exact Or.inl h
    | inr _ => exact Or.inr h
  · exact fun h => h.elim (fun h => ⟨.inl PUnit.unit, h⟩) (fun h => ⟨.inr PUnit.unit, h⟩)

def kpair_graph_l (G H : WF_graph.{u}) : WF_graph.{u} :=
  pair_graph_l (pair_graph_l G G) (pair_graph_l G H)

theorem kpair_graph_spec_l (G H : WF_graph.{u}) :
    KPair_d sg_structure (SG_set.mk (kpair_graph_l G H)) (SG_set.mk G) (SG_set.mk H) :=
  ⟨SG_set.mk (pair_graph_l G G), SG_set.mk (pair_graph_l G H),
    fun z => (pair_graph_spec_l G G z).trans ⟨fun h => h.elim id id, Or.inl⟩,
    pair_graph_spec_l G H, pair_graph_spec_l _ _⟩

variable {B : Type u}

def encode_graph_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) : G.Domain → WF_graph.{u} :=
  G.wf.fix fun a ih => WF_graph.root_sum
    (fun i : G.Child a => kpair_graph_l (ih i i.2) (c (G.val i a)))

def encode_set_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) (a : G.Domain) : SG_set.{u} :=
  SG_set.mk (encode_graph_l c G a)

def condition_set_l (c : B → WF_graph.{u}) : SG_set.{u} := SG_set.mk (WF_graph.root_sum c)

def coded_graph_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) : BV_graph.{u, u+1} SG_set.{u} where
  toWF_graph := G.toWF_graph
  val a b := SG_set.mk (c (G.val a b))

theorem encode_graph_eq_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) (a : G.Domain) :
    encode_graph_l c G a = WF_graph.root_sum
      (fun i : G.Child a => kpair_graph_l (encode_graph_l c G i) (c (G.val i a))) := by
  rw [encode_graph_l, WellFounded.fix_eq]

theorem encode_mem_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B)
    (a : G.Domain) (p : SG_set.{u}) : p ∈ encode_set_l c G a ↔
      ∃ i : G.Child a, KPair_d sg_structure p (encode_set_l c G i) (SG_set.mk (c (G.val i a))) := by
  change p ∈ SG_set.mk (encode_graph_l c G a) ↔ _
  rw [encode_graph_eq_l, SG_set.mem_sum]
  apply exists_congr
  intro i
  exact ⟨fun h => h ▸ kpair_graph_spec_l _ _,
    fun h => kpair_unique_l sg_structure sg_extensional h (kpair_graph_spec_l _ _)⟩

/-- 整幅图的编码子名称共同组成一个实际模型集合，允许无限节点域。 -/
theorem encode_name_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) (a : G.Domain) :
    Name_d sg_structure (condition_set_l c) (encode_set_l c G a) := by
  let S := SG_set.mk (WF_graph.root_sum (encode_graph_l c G))
  have hs (a : G.Domain) : encode_set_l c G a ∈ S := (SG_set.mem_sum _ _).mpr ⟨a, rfl⟩
  refine ⟨S, hs a, ?_⟩
  intro t ht p hp
  obtain ⟨d, rfl⟩ := (SG_set.mem_sum _ t).mp ht
  obtain ⟨i, hi⟩ := (encode_mem_l c G d p).mp hp
  exact ⟨encode_set_l c G i, SG_set.mk (c (G.val i d)), hi, hs i,
    (SG_set.mem_sum c _).mpr ⟨G.val i d, rfl⟩⟩

theorem encode_rep_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) (a : G.Domain) :
    Rep_d sg_structure (condition_set_l c) (encode_set_l c G a) (coded_graph_l c (G.at_node a)) := by
  refine ⟨encode_name_l c G a, encode_set_l c G, rfl, ?_, ?_⟩
  · intro x y hxy
    let P := SG_set.mk (kpair_graph_l (encode_graph_l c G x) (c (G.val x y)))
    have hP : KPair_d sg_structure P (encode_set_l c G x) (SG_set.mk (c (G.val x y))) :=
      kpair_graph_spec_l _ _
    exact ⟨P, hP, (encode_mem_l c G y P).mpr ⟨⟨x, hxy⟩, hP⟩⟩
  · rintro y s b ⟨p, hp, hpy⟩
    obtain ⟨i, hi⟩ := (encode_mem_l c G y p).mp hpy
    obtain ⟨hs, hb⟩ := kpair_injective_l sg_structure hi hp
    exact ⟨i.1, i.2, hs, hb⟩

/-- 标签按给定模型对象编码时，内部解释与原名称求值完全一致。 -/
theorem encode_val_l (c : B → WF_graph.{u}) (G : BV_graph.{u, u} B) (U : SG_set.{u} → Prop) :
    Val_d sg_structure (condition_set_l c) U (encode_set_l c G G.root)
      (Forcing.val_l (fun b => U (SG_set.mk (c b))) G) :=
  ⟨coded_graph_l c G, encode_rep_l c G G.root, rfl⟩

/-- 外部条件谓词沿实际编码送到模型对象，不要求该谓词本身是地模型的集合。 -/
def code_pred_l (c : B → WF_graph.{u}) (U : B → Prop) (z : SG_set.{u}) : Prop :=
  ∃ b, z = SG_set.mk (c b) ∧ U b

theorem code_pred_iff_l (c : B → WF_graph.{u})
    (hc : Function.Injective (fun b => SG_set.mk (c b))) (U : B → Prop) (b : B) :
    code_pred_l c U (SG_set.mk (c b)) ↔ U b :=
  ⟨fun ⟨_, h, hd⟩ => hc h ▸ hd, fun hb => ⟨b, rfl, hb⟩⟩

theorem encode_pred_val_l (c : B → WF_graph.{u})
    (hc : Function.Injective (fun b => SG_set.mk (c b))) (G : BV_graph.{u, u} B) (U : B → Prop) :
    Val_d sg_structure (condition_set_l c) (code_pred_l c U) (encode_set_l c G G.root)
      (Forcing.val_l U G) := by
  have h := encode_val_l c G (code_pred_l c U)
  have he : (fun b => code_pred_l c U (SG_set.mk (c b))) = U :=
    funext fun b => propext (code_pred_iff_l c hc U b)
  rwa [he] at h

/-- 小图模型的实际集合构造直接提供内部名称所需的两个模式实例。 -/
theorem sg_name_ops_l : Name_ops_d sg_structure.{u} where
  pair := SG_set.pair
  union := SG_set.union
  separation B T := SG_set.separation T (Supp_d sg_structure B)
  collection B t h := SG_set.collection t (Entry_supp_d sg_structure B) h

theorem sg_setlike_l : Setlike_d.{u+1, u} sg_structure.{u} := SG_set.small_presentation

/-- 可直接调用的内部名称域实例，使用原 SG_set 层级作为扩张的求值载体。 -/
def sg_name_domain_l (B : SG_set.{u}) : Name_domain_l.{u, u+1} SG_set.{u} :=
  name_domain_l sg_structure SG_set.mem_wf sg_setlike_l B
    ⟨SG_set.empty, name_empty_l sg_structure SG_set.pair B SG_set.empty SG_set.not_mem_empty⟩

theorem sg_decode_l {B t : SG_set.{u}} (h : Name_d sg_structure B t) :
    ∃ G : BV_graph.{u, u+1} SG_set.{u}, Rep_d sg_structure B t G :=
  decode_exists_l sg_structure SG_set.mem_wf sg_setlike_l h

end YesMetaZFC.Model.Forcing.Internal
