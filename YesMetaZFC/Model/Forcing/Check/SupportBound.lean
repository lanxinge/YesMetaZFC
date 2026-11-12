import YesMetaZFC.Model.Forcing.Check.Syntax
import YesMetaZFC.Model.Forcing.Names.Realization
import YesMetaZFC.SetTheory.MembershipInduction
import YesMetaZFC.Model.Forcing.Ground.Graph
import YesMetaZFC.Model.Forcing.Truth.Truth
import YesMetaZFC.Model.Forcing.Maximum.UniqueRules
import YesMetaZFC.SetTheory.Card.InfiniteBound
import YesMetaZFC.SetTheory.Card.PowerBound
import YesMetaZFC.SetTheory.Card.OrdinalImage

/-! # 规范名称递归的存在性与唯一性

先用内部成员归纳证明所有部分递归图相容，再收集前驱图、取并并添加新值。
本层不使用外部良基性、布尔代数律或条件泛型性，标签只需是一个模型对象。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

/-- 只保留递归实际消费的集合操作；原 ZF 和小图模型的实例在后续模块构造。 -/
structure Check_ops_d : Prop where
  pair : ∀ a b, ∃ p, Pair_d M p a b
  union : ∀ F, ∃ S, M.IsUnionOf S F
  collect : ∀ b x, (∀ y, M.mem y x → ∃ F, Check_graph_d M b F ∧ ∃ t, Entry_d M y t F) →
    ∃ C, (∀ F, M.mem F C → Check_graph_d M b F) ∧
      ∀ y, M.mem y x → ∃ F t, M.mem F C ∧ Entry_d M y t F
  image : ∀ b F x, (∀ y, M.mem y x → ∃ s, Entry_d M y s F) →
    (∀ y, M.mem y x → ∀ s t, Entry_d M y s F → Entry_d M y t F → s = t) →
    ∃ t, ∀ p, M.mem p t ↔ ∃ y s, M.mem y x ∧ Entry_d M y s F ∧ KPair_d M p s b

private def ck_unique_m {n} (b x : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp
    (.conj (check_m b.weaken.weaken x.weaken.weaken (.bound 1))
      (check_m b.weaken.weaken x.weaken.weaken .newest))
    (Formula.extensionalEq (.bound 1) .newest)))

derive_free_closed ck_unique_m

/-- 唯一性只使用实际公式的成员归纳与外延性。 -/
theorem check_unique_l (hE : Extensional M) (hI : Mem_ind_d M) (b x : M.Domain) :
    ∀ s t, Check_d M b x s → Check_d M b x t → s = t := by
  let ρ : Env M 1 := ⟨fun _ => b, fun _ => b⟩
  let φ : UnarySchema 1 := { body := ck_unique_m (.bound 1) (.bound 0) }
  have hφ x : φ.denote ρ x ↔ ∀ s t, Check_d M b x s → Check_d M b x t → s = t := by
    simp only [UnarySchema.denote, φ, ck_unique_m, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_conj_iff, check_sat_l M hE,
      Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_newest,
      Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push]
    exact ⟨fun h s t hs ht => h s t ⟨hs, ht⟩, fun h s t ⟨hs, ht⟩ => h s t hs ht⟩
  apply (hφ x).mp
  apply hI φ ρ
  intro y ih
  apply (hφ y).mpr
  rintro s t ⟨F, hF, hs⟩ ⟨G, hG, ht⟩
  have hf {F G s t} (hF : Check_graph_d M b F) (hG : Check_graph_d M b G)
      (hs : Entry_d M y s F) (ht : Entry_d M y t G) : ∀ p, M.mem p s → M.mem p t := by
    intro p hp
    obtain ⟨z, a, hz, ha, hp⟩ := ((hF.2 y s hs).2 p).mp hp
    obtain ⟨c, hc⟩ := (hG.2 y t ht).1 z hz
    have he := (hφ z).mp (ih z hz) a c ⟨F, hF, ha⟩ ⟨G, hG, hc⟩
    exact ((hG.2 y t ht).2 p).mpr ⟨z, c, hz, hc, he ▸ hp⟩
  exact hE.eq_of_same_members s t (fun p => ⟨hf hF hG hs ht p, hf hG hF ht hs p⟩)

/-- 规范名称的成员递归式，不再向调用者暴露部分递归图。 -/
theorem check_mem_l (hE : Extensional M) (hI : Mem_ind_d M)
    {b x t} (h : Check_d M b x t) (p : M.Domain) :
    M.mem p t ↔ ∃ y s, M.mem y x ∧ Check_d M b y s ∧ KPair_d M p s b := by
  obtain ⟨F, hF, ht⟩ := h
  constructor
  · intro hp
    obtain ⟨y, s, hy, hs, hp⟩ := ((hF.2 x t ht).2 p).mp hp
    exact ⟨y, s, hy, ⟨F, hF, hs⟩, hp⟩
  · rintro ⟨y, s, hy, hs, hp⟩
    obtain ⟨a, ha⟩ := (hF.2 x t ht).1 y hy
    have he := check_unique_l M hE hI b y s a hs ⟨F, hF, ha⟩
    exact ((hF.2 x t ht).2 p).mpr ⟨y, a, hy, ha, he ▸ hp⟩

/-- 相容性由唯一性定理给出，因此任意内部集合族的递归图可以直接取并。 -/
theorem check_union_l (hE : Extensional M) (hI : Mem_ind_d M)
    {b C F} (hC : ∀ G, M.mem G C → Check_graph_d M b G) (hF : M.IsUnionOf F C) :
    Check_graph_d M b F := by
  constructor
  · intro p hp
    obtain ⟨G, hG, hp⟩ := (hF p).mp hp
    exact (hC G hG).1 p hp
  · intro x t ht
    obtain ⟨G, hG, ht⟩ := (entry_union_l M hF x t).mp ht
    have hg := hC G hG
    constructor
    · intro y hy
      obtain ⟨s, hs⟩ := (hg.2 x t ht).1 y hy
      exact ⟨s, (entry_union_l M hF y s).mpr ⟨G, hG, hs⟩⟩
    · intro p
      constructor
      · intro hp
        obtain ⟨y, s, hy, hs, hp⟩ := ((hg.2 x t ht).2 p).mp hp
        exact ⟨y, s, hy, (entry_union_l M hF y s).mpr ⟨G, hG, hs⟩, hp⟩
      · rintro ⟨y, s, hy, hs, hp⟩
        obtain ⟨H, hH, hs⟩ := (entry_union_l M hF y s).mp hs
        obtain ⟨a, ha⟩ := (hg.2 x t ht).1 y hy
        have he := check_unique_l M hE hI b y s a ⟨H, hC H hH, hs⟩ ⟨G, hg, ha⟩
        exact ((hg.2 x t ht).2 p).mpr ⟨y, a, hy, ha, he ▸ hp⟩

/-- 向部分解加入下一递归值；即使输入已在旧定义域中，也由外延性保证相容。 -/
theorem check_adjoin_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b) (hU : ∀ F, ∃ S, M.IsUnionOf S F)
    {b F x t} (hF : Check_graph_d M b F) (ht : Check_step_d M b F x t) : Check_d M b x t := by
  obtain ⟨p, hp⟩ := (kpair_interpretation_l M hE hP).total x t
  obtain ⟨G, hG⟩ := set_insert_l M hP hU F p
  have he y s : Entry_d M y s G ↔ Entry_d M y s F ∨ (y = x ∧ s = t) := by
    constructor
    · rintro ⟨q, hq, hqG⟩
      rcases (hG q).mp hqG with hf | rfl
      · exact Or.inl ⟨q, hq, hf⟩
      · exact Or.inr (kpair_injective_l M hq hp)
    · rintro (⟨q, hq, hf⟩ | ⟨rfl, rfl⟩)
      · exact ⟨q, hq, (hG q).mpr (Or.inl hf)⟩
      · exact ⟨p, hp, (hG p).mpr (Or.inr rfl)⟩
  have hc {y s a} (hs : Entry_d M y s G) (ha : Entry_d M y a F) : s = a := by
    rcases (he y s).mp hs with hs | ⟨rfl, rfl⟩
    · exact check_unique_l M hE hI b y s a ⟨F, hF, hs⟩ ⟨F, hF, ha⟩
    · exact hE.eq_of_same_members _ _ (fun q => (ht.2 q).trans ((hF.2 y a ha).2 q).symm)
  have hstep {y s} (hs : Check_step_d M b F y s) : Check_step_d M b G y s := by
    constructor
    · intro z hz
      obtain ⟨a, ha⟩ := hs.1 z hz
      exact ⟨a, (he z a).mpr (Or.inl ha)⟩
    · intro q
      constructor
      · intro hq
        obtain ⟨z, a, hz, ha, hq⟩ := (hs.2 q).mp hq
        exact ⟨z, a, hz, (he z a).mpr (Or.inl ha), hq⟩
      · rintro ⟨z, a, hz, ha, hq⟩
        obtain ⟨c, hc'⟩ := hs.1 z hz
        exact (hs.2 q).mpr ⟨z, c, hz, hc', hc ha hc' ▸ hq⟩
  refine ⟨G, ⟨?_, ?_⟩, (he x t).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro q hq
    rcases (hG q).mp hq with hq | rfl
    · exact hF.1 q hq
    · exact ⟨x, t, hp⟩
  · intro y s hs
    rcases (he y s).mp hs with hs | ⟨rfl, rfl⟩
    · exact hstep (hF.2 y s hs)
    · exact hstep ht

/-- 模型内收集前驱图并添加新根；不存在外部递归结果的隐式回填。 -/
theorem check_exists_l (hE : Extensional M) (hI : Mem_ind_d M)
    (O : Check_ops_d M) (b x : M.Domain) : ∃ t, Check_d M b x t := by
  let ρ : Env M 1 := ⟨fun _ => b, fun _ => b⟩
  let φ : UnarySchema 1 := { body := .existsE (check_m (.bound 2) (.bound 1) .newest) }
  have hφ x : φ.denote ρ x ↔ ∃ t, Check_d M b x t := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, check_sat_l M hE,
      Definitional.Term.eval_newest, Term.eval_bound_zero_push,
      Term.eval_bound_one_push, Term.eval_bound_two_push]
    rfl
  apply (hφ x).mp
  apply hI φ ρ
  intro y ih
  apply (hφ y).mpr
  obtain ⟨C, hC, hc⟩ := O.collect b y (fun z hz => by
    obtain ⟨t, F, hF, ht⟩ := (hφ z).mp (ih z hz)
    exact ⟨F, hF, t, ht⟩)
  obtain ⟨F, hF⟩ := O.union C
  have hf := check_union_l M hE hI hC hF
  have hd z (hz : M.mem z y) : ∃ s, Entry_d M z s F := by
    obtain ⟨G, s, hG, hs⟩ := hc z hz
    exact ⟨s, (entry_union_l M hF z s).mpr ⟨G, hG, hs⟩⟩
  obtain ⟨t, ht⟩ := O.image b F y hd (fun z _ s t hs ht =>
    check_unique_l M hE hI b z s t ⟨F, hf, hs⟩ ⟨F, hf, ht⟩)
  exact ⟨t, check_adjoin_l M hE hI O.pair O.union hf ⟨hd, ht⟩⟩

/-- 部分递归图的值域就是内部名称支撑，无需再次进行递归或收集。 -/
theorem check_name_l (hR : ∀ F, ∃ S, ∀ t, M.mem t S ↔ ∃ x, Entry_d M x t F)
    {B b x t} (hb : M.mem b B) (h : Check_d M b x t) : Name_d M B t := by
  obtain ⟨F, hF, ht⟩ := h
  obtain ⟨S, hS⟩ := hR F
  refine ⟨S, (hS t).mpr ⟨x, ht⟩, ?_⟩
  intro s hs p hp
  obtain ⟨y, hy⟩ := (hS s).mp hs
  obtain ⟨z, a, _, ha, hp⟩ := ((hF.2 y s hy).2 p).mp hp
  exact ⟨a, b, hp, (hS a).mpr ⟨z, ha⟩, hb⟩

theorem check_entry_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b) {b x t} (h : Check_d M b x t) (s c : M.Domain) :
    Entry_d M s c t ↔ c = b ∧ ∃ y, M.mem y x ∧ Check_d M b y s := by
  constructor
  · rintro ⟨p, hp, hpt⟩
    obtain ⟨y, a, hy, ha, hpa⟩ := (check_mem_l M hE hI h p).mp hpt
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp hpa
    exact ⟨rfl, y, hy, ha⟩
  · rintro ⟨rfl, y, hy, hs⟩
    obtain ⟨p, hp⟩ := (kpair_interpretation_l M hE hP).total s c
    exact ⟨p, hp, (check_mem_l M hE hI h p).mpr ⟨y, s, hy, hs, hp⟩⟩

private def injective_m {n} (b x : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp
    (.conj (check_m b.weaken.weaken x.weaken.weaken .newest)
      (check_m b.weaken.weaken (.bound 1) .newest))
    (Formula.extensionalEq x.weaken.weaken (.bound 1))))

derive_free_closed injective_m

/-- 规范名称忠实区分地模型对象；仍只消费内部公式归纳。 -/
theorem check_injective_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b) (b x : M.Domain) :
    ∀ y t, Check_d M b x t → Check_d M b y t → x = y := by
  let ρ : Env M 1 := ⟨fun _ => b, fun _ => b⟩
  let φ : UnarySchema 1 := { body := injective_m (.bound 1) (.bound 0) }
  have hφ x : φ.denote ρ x ↔ ∀ y t, Check_d M b x t → Check_d M b y t → x = y := by
    simp only [UnarySchema.denote, φ, injective_m, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_conj_iff, check_sat_l M hE,
      Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_newest,
      Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push]
    exact ⟨fun h y t hx hy => h y t ⟨hx, hy⟩, fun h y t ⟨hx, hy⟩ => h y t hx hy⟩
  apply (hφ x).mp
  apply hI φ ρ
  intro a ih
  apply (hφ a).mpr
  intro y t ha hy
  apply hE.eq_of_same_members a y
  intro z
  constructor
  · intro hz
    obtain ⟨s, hs⟩ := check_child_l M ha hz
    have he := (check_entry_l M hE hI hP ha s b).mpr ⟨rfl, z, hz, hs⟩
    obtain ⟨_, w, hw, hs'⟩ := (check_entry_l M hE hI hP hy s b).mp he
    exact ((hφ z).mp (ih z hz) w s hs hs').symm ▸ hw
  · intro hz
    obtain ⟨s, hs⟩ := check_child_l M hy hz
    have he := (check_entry_l M hE hI hP hy s b).mpr ⟨rfl, z, hz, hs⟩
    obtain ⟨_, w, hw, hs'⟩ := (check_entry_l M hE hI hP ha s b).mp he
    exact ((hφ w).mp (ih w hw) z s hs' hs) ▸ hw

/-- 地模型隶属恰好对应规范名称中的带权成员。 -/
theorem check_mem_iff_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b) {b x y s t}
    (hs : Check_d M b x s) (ht : Check_d M b y t) : Entry_d M s b t ↔ M.mem x y := by
  constructor
  · intro h
    obtain ⟨_, z, hz, hs'⟩ := (check_entry_l M hE hI hP ht s b).mp h
    exact (check_injective_l M hE hI hP b x z s hs hs').symm ▸ hz
  · exact fun h => (check_entry_l M hE hI hP ht s b).mpr ⟨rfl, x, h, hs⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 规范名称解释还原地模型对象

将规范名称递归图直接作为名称图与地模型成员图之间的双模拟。只需标签 b
被接受，不需要超滤子、完备性或泛型性；取布尔顶值即得到通常的 check 定理。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SmallGraph Boolean
universe u v
variable (M : SetTheory.Structure.{u})

theorem check_val_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b) {B b x t : M.Domain}
    {G : WF_graph.{v}} {H : BV_graph.{v, u} M.Domain}
    (hx : Ground_rep_d M x G) (ht : Check_d M b x t) (hH : Rep_d M B t H)
    {U : M.Domain → Prop} (hb : U b) : Forcing.val_l U H = SG_set.mk G := by
  obtain ⟨c, hc, hf, hk⟩ := hx
  obtain ⟨_, d, hd, hh, hj⟩ := hH
  apply SG_set.mk_eq.mpr
  refine ⟨fun a z => Check_d M b (c z) (d a), ?_, by
    change Check_d M b (c G.root) (d H.root)
    rw [hc, hd]; exact ht⟩
  intro a z haz
  constructor
  · rintro a' ⟨ha, _⟩
    obtain ⟨_, y, hy, hs⟩ := (check_entry_l M hE hI hP haz _ _).mp (hh a' a ha)
    obtain ⟨z', hz, he⟩ := hk z y hy
    exact ⟨z', hz, show Check_d M b (c z') (d a') from he.symm ▸ hs⟩
  · intro z' hz
    obtain ⟨s, hs⟩ := check_child_l M haz (hf z' z hz)
    have he := (check_entry_l M hE hI hP haz s b).mpr ⟨rfl, c z', hf z' z hz, hs⟩
    obtain ⟨a', ha, had, hav⟩ := hj a s b he
    exact ⟨a', ⟨ha, hav.symm ▸ hb⟩, show Check_d M b (c z') (d a') from had.symm ▸ hs⟩

/-- 同一内部规范名称对所有接受 b 的条件谓词都还原同一个地模型对象。 -/
theorem check_val_exists_l (hE : Extensional M) (hI : Mem_ind_d M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b)
    (hR : ∀ F, ∃ S, ∀ t, M.mem t S ↔ ∃ x, Entry_d M x t F)
    (hM : _root_.WellFounded M.mem) (hL : Setlike_d.{u, v} M)
    {B b x t : M.Domain} (hb : M.mem b B) (ht : Check_d M b x t)
    {y : SG_set.{v}} (hy : Ground_d M x y) :
    ∀ U : M.Domain → Prop, U b → Val_d M B U t y := by
  obtain ⟨G, hG, rfl⟩ := hy
  obtain ⟨H, hH⟩ := decode_exists_l M hM hL (check_name_l M hR hb ht)
  exact fun U hU => ⟨H, hH, check_val_l M hE hI hP hG ht hH hU⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 从原 ZF 公理取得规范名称递归

收集、分离及替换均使用下面写出的实际 Project 公式。调用端只传原 ZF 模型，
不必额外提供递归存在性、闭包或函数性证书。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable (M : SetTheory.Structure.{u})

private def cover_m {n} (b x F : Term n) : Formula 1 n :=
  .conj (check_graph_m b F) (.existsE (entry_m x.weaken .newest F.weaken))

derive_free_closed cover_m

private def weight_m {n} (b F y p : Term n) : Formula 1 n :=
  .existsE (.conj (entry_m y.weaken .newest F.weaken) (kpair_m p.weaken .newest b.weaken))

derive_free_closed weight_m

private theorem cover_sat_l (hE : Extensional M) {n} (ρ : Env M n) (b x F : Term n) :
    Formula.satisfies ρ (cover_m b x F) ↔
      Check_graph_d M (b.eval ρ) (F.eval ρ) ∧ ∃ t, Entry_d M (x.eval ρ) t (F.eval ρ) := by
  simp only [cover_m, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    check_graph_sat_l M hE, entry_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

private theorem weight_sat_l (hE : Extensional M) {n} (ρ : Env M n) (b F y p : Term n) :
    Formula.satisfies ρ (weight_m b F y p) ↔
      ∃ s, Entry_d M (y.eval ρ) s (F.eval ρ) ∧ KPair_d M (p.eval ρ) s (b.eval ρ) := by
  simp only [weight_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    entry_sat_l M hE, kpair_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 原 ZF 的具体模式实例实现全部递归操作。 -/
theorem check_ops_l (hZF : M.Models ZF) : Check_ops_d M where
  pair := KP.exists_pair (ZF.modelsKP hZF)
  union := KP.exists_union (ZF.modelsKP hZF)
  collect b x h := by
    let ρ : Env M 1 := ⟨fun _ => b, fun _ => b⟩
    let φ : BinarySchema 1 := { body := cover_m (.bound 2) (.bound 1) (.bound 0) }
    have hφ y F : φ.denote ρ y F ↔ Check_graph_d M b F ∧ ∃ t, Entry_d M y t F :=
      cover_sat_l M hZF.1 ((ρ.push y).push F) (.bound 2) (.bound 1) (.bound 0)
    obtain ⟨T, hT⟩ := ZF.collection_exists_d hZF φ ρ x (fun y hy => by
      obtain ⟨F, hF⟩ := h y hy
      exact ⟨F, (hφ y F).mpr hF⟩)
    let ψ : UnarySchema 1 := { body := check_graph_m (.bound 1) (.bound 0) }
    obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF ψ ρ T
    have hc F : M.mem F C ↔ M.mem F T ∧ Check_graph_d M b F :=
      (hC F).trans (and_congr_right fun _ => check_graph_sat_l M hZF.1 (ρ.push F) (.bound 1) (.bound 0))
    refine ⟨C, fun F hF => ((hc F).mp hF).2, ?_⟩
    intro y hy
    obtain ⟨F, hF, hf⟩ := hT y hy
    obtain ⟨hf, t, ht⟩ := (hφ y F).mp hf
    exact ⟨F, t, (hc F).mpr ⟨hF, hf⟩, ht⟩
  image b F x h hu := by
    let ρ : Env M 2 := (⟨fun _ => b, fun _ => b⟩ : Env M 1).push F
    let φ : BinarySchema 2 := { body := weight_m (.bound 3) (.bound 2) (.bound 1) (.bound 0) }
    have hφ y p : φ.denote ρ y p ↔ ∃ s, Entry_d M y s F ∧ KPair_d M p s b :=
      weight_sat_l M hZF.1 ((ρ.push y).push p) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    obtain ⟨t, ht⟩ := ZF.exists_functionalImageOn hZF φ ρ x (fun y hy => by
      obtain ⟨s, hs⟩ := h y hy
      obtain ⟨p, hp⟩ := (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))).total s b
      exact ⟨p, (hφ y p).mpr ⟨s, hs, hp⟩⟩) (by
        intro y hy p q hp hq
        obtain ⟨s, hs, hp⟩ := (hφ y p).mp hp
        obtain ⟨t, ht, hq⟩ := (hφ y q).mp hq
        exact kpair_unique_l M hZF.1 ((hu y hy s t hs ht) ▸ hp) hq)
    refine ⟨t, fun p => (ht p).trans ?_⟩
    constructor
    · rintro ⟨y, hy, hp⟩
      obtain ⟨s, hs, hp⟩ := (hφ y p).mp hp
      exact ⟨y, s, hy, hs, hp⟩
    · rintro ⟨y, s, hy, hs, hp⟩
      exact ⟨y, hy, (hφ y p).mpr ⟨s, hs, hp⟩⟩

/-- 有序对右坐标在二重并集中，以实际值域公式分离即可。 -/
theorem check_range_l (hZF : M.Models ZF) (F : M.Domain) :
    ∃ S, ∀ t, M.mem t S ↔ ∃ x, Entry_d M x t F := by
  obtain ⟨A, hA⟩ := KP.exists_union (ZF.modelsKP hZF) F
  obtain ⟨D, hD⟩ := KP.exists_union (ZF.modelsKP hZF) A
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : UnarySchema 1 := { body := .existsE (entry_m .newest (.bound 1) (.bound 2)) }
  obtain ⟨S, hS⟩ := ZF.separation_exists_d hZF φ ρ D
  have hφ t : φ.denote ρ t ↔ ∃ x, Entry_d M x t F := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, entry_sat_l M hZF.1,
      Definitional.Term.eval_newest, Term.eval_bound_one_push, Term.eval_bound_two_push,
      Term.eval_bound_zero_push]
    rfl
  refine ⟨S, fun t => (hS t).trans ?_⟩
  constructor
  · exact fun h => (hφ t).mp h.2
  · rintro ⟨x, p, hp, hpf⟩
    obtain ⟨v, hv, htv⟩ := (kpair_union_l M hp t).mpr (Or.inr rfl)
    exact ⟨(hD t).mpr ⟨v, (hA v).mpr ⟨p, hpf, hv⟩, htv⟩,
      (hφ t).mpr ⟨x, p, hp, hpf⟩⟩

theorem check_ind_l (hZF : M.Models ZF) : Mem_ind_d M :=
  ZF.mem_ind_l M hZF (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)))

/-- 一次调用取得规范名称、内部名称证书及唯一性；无需选择一个全局名称函数。 -/
theorem zf_check_l (hZF : M.Models ZF) {B b : M.Domain} (hb : M.mem b B) (x : M.Domain) :
    ∃ t, Check_d M b x t ∧ Name_d M B t ∧ ∀ s, Check_d M b x s → s = t := by
  obtain ⟨t, ht⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) b x
  exact ⟨t, ht, check_name_l M (check_range_l M hZF) hb ht,
    fun s hs => check_unique_l M hZF.1 (check_ind_l M hZF) b x s t hs ht⟩

/-- 同时构造地模型对象的实际小图解释和内部规范名称，并核验求值还原。 -/
theorem zf_check_val_l (hZF : M.Models ZF) (hM : _root_.WellFounded M.mem)
    (hL : Setlike_d.{u, v} M) {B b : M.Domain} (hb : M.mem b B) (x : M.Domain) :
    ∃ t, Check_d M b x t ∧ Name_d M B t ∧ ∃ y : SmallGraph.SG_set.{v},
      Ground_d M x y ∧ ∀ U : M.Domain → Prop, U b → Val_d M B U t y := by
  obtain ⟨t, ht, hn, _⟩ := zf_check_l M hZF hb x
  obtain ⟨S, hx, hS⟩ := ZF.mem_hull_l M hZF
    (kpair_interpretation_l M hZF.1 (check_ops_l M hZF).pair) x
  obtain ⟨G, hG⟩ := ground_decode_l M hM hL hx hS
  exact ⟨t, ht, hn, SmallGraph.SG_set.mk G, ⟨G, hG, rfl⟩,
    check_val_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF).pair
      (check_range_l M hZF) hM hL hb ht ⟨G, hG, rfl⟩⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 规范名称在泛型商中的忠实性

对地模型对象使用实际公式的内部成员归纳。等号力迫的双向匹配给出原对象的
相同成员，故规范名称嵌入在非标准及外部非良基模型上仍为单射。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

/-- 两个基点下的规范名称在共同加强处相等；证书是共享闭支撑内的实际双模拟。 -/
theorem check_force_bases_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    {b c x s t p} (hb : M.mem b B) (hc : M.mem c B)
    (hs : Check_d M b x s) (ht : Check_d M c x t) (hp : M.mem p B)
    (hpb : Entry_d M p b R) (hpc : Entry_d M p c R) : Eq_force_d M B R z p s t := by
  obtain ⟨S, hsS, htS, hS⟩ := name_support_l M (KP.exists_pair (ZF.modelsKP hZF))
    (KP.exists_union (ZF.modelsKP hZF)) (check_name_l M (check_range_l M hZF) hb hs)
      (check_name_l M (check_range_l M hZF) hc ht)
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push c
  let φ : BinarySchema 6 := {
    body := .existsE (.conj (check_m (.bound 5) .newest (.bound 2))
      (.conj (check_m (.bound 4) .newest (.bound 1))
        (.conj (entry_m (.bound 3) (.bound 5) (.bound 7)) (entry_m (.bound 3) (.bound 4) (.bound 7))))) }
  obtain ⟨F, hF⟩ := rel_separation_l hZF φ ρ B S
  have he p s t : Rel_d M F p s t ↔ M.mem p B ∧ M.mem s S ∧ M.mem t S ∧
      ∃ x, Check_d M b x s ∧ Check_d M c x t ∧ Entry_d M p b R ∧ Entry_d M p c R := by
    simpa only [BinarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      check_sat_l M hZF.1, entry_sat_l M hZF.1] using! hF p s t
  refine ⟨hp, F, ?_, (he p s t).mpr ⟨hp, hsS, htS, x, hs, ht, hpb, hpc⟩⟩
  intro p s t hf
  obtain ⟨hp, hsS, htS, x, hs, ht, hpb, hpc⟩ := (he p s t).mp hf
  constructor
  · intro a d had q hq _
    obtain ⟨_, y, hy, ha⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) hs a d).mp had
    obtain ⟨a', ha'⟩ := check_child_l M ht hy
    have ha't := (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) ht a' c).mpr ⟨rfl, y, hy, ha'⟩
    have hqb := O.trans q p b hq.1 hp hb hq.2.2 hpb
    have hqc := O.trans q p c hq.1 hp hc hq.2.2 hpc
    exact ⟨q, a', c, below_refl_l O hq.1 hq.2.1, ha't, hqc, (he q a a').mpr
      ⟨hq.1, (supp_entry_l M hS hsS had).1, (supp_entry_l M hS htS ha't).1, y, ha, ha', hqb, hqc⟩⟩
  · intro a d had q hq _
    obtain ⟨_, y, hy, ha⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) ht a d).mp had
    obtain ⟨a', ha'⟩ := check_child_l M hs hy
    have ha's := (check_entry_l M hZF.1 (check_ind_l M hZF)
      (KP.exists_pair (ZF.modelsKP hZF)) hs a' b).mpr ⟨rfl, y, hy, ha'⟩
    have hqb := O.trans q p b hq.1 hp hb hq.2.2 hpb
    have hqc := O.trans q p c hq.1 hp hc hq.2.2 hpc
    exact ⟨q, a', b, below_refl_l O hq.1 hq.2.1, ha's, hqb, (he q a' a).mpr
      ⟨hq.1, (supp_entry_l M hS hsS ha's).1, (supp_entry_l M hS htS had).1, y, ha', ha, hqb, hqc⟩⟩

theorem check_force_reflect_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    {b p x y s t} (hb : M.mem b B) (hs : Check_d M b x s) (ht : Check_d M b y t)
    (hp : Below_d M B R z p b) (he : Eq_force_d M B R z p s t) : x = y := by
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b
  let φ : UnarySchema 4 := {
    body := .forallE (.forallE (.forallE (.forallE (.imp
      (.conj (check_m (.bound 5) (.bound 4) (.bound 2))
        (.conj (check_m (.bound 5) (.bound 3) (.bound 1))
          (.conj (below_m (.bound 8) (.bound 7) (.bound 6) .newest (.bound 5))
            (eq_force_m (.bound 8) (.bound 7) (.bound 6) .newest (.bound 2) (.bound 1)))))
      (Formula.extensionalEq (.bound 4) (.bound 3)))))) }
  have hφ a : φ.denote ρ a ↔ ∀ c s t p,
      Check_d M b a s ∧ Check_d M b c t ∧ Below_d M B R z p b ∧ Eq_force_d M B R z p s t → a = c := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, check_sat_l M hZF.1, below_sat_l M hZF.1, eq_force_sat_l M hZF.1,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]
    rfl
  have hall := check_ind_l M hZF φ ρ (fun a ih => (hφ a).mpr (by
    rintro c s t p ⟨hs, ht, hp, he⟩
    have hsN := check_name_l M (check_range_l M hZF) hb hs
    have htN := check_name_l M (check_range_l M hZF) hb ht
    obtain ⟨_, hl, hr⟩ := (eq_force_unfold_l M hZF hsN htN).mp he
    apply hZF.1.eq_of_same_members a c
    intro d
    constructor
    · intro hda
      obtain ⟨v, hv⟩ := check_child_l M hs hda
      have hd := (check_entry_l M hZF.1 (check_ind_l M hZF)
        (KP.exists_pair (ZF.modelsKP hZF)) hs v b).mpr ⟨rfl, d, hda, hv⟩
      obtain ⟨r, w, e, hpr, hw, _, hvw⟩ := hl v b hd p (below_refl_l O hp.1 hp.2.1) hp.2.2
      obtain ⟨_, f, hfc, hfw⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
        (KP.exists_pair (ZF.modelsKP hZF)) ht w e).mp hw
      have hef := (hφ d).mp (ih d hda) f v w r ⟨hv, hfw, below_trans_l O hb hpr hp, hvw⟩
      exact hef.symm ▸ hfc
    · intro hdc
      obtain ⟨v, hv⟩ := check_child_l M ht hdc
      have hd := (check_entry_l M hZF.1 (check_ind_l M hZF)
        (KP.exists_pair (ZF.modelsKP hZF)) ht v b).mpr ⟨rfl, d, hdc, hv⟩
      obtain ⟨r, w, e, hpr, hw, _, hwv⟩ := hr v b hd p (below_refl_l O hp.1 hp.2.1) hp.2.2
      obtain ⟨_, f, hfa, hfw⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
        (KP.exists_pair (ZF.modelsKP hZF)) hs w e).mp hw
      have hef := (hφ f).mp (ih f hfa) d w v r ⟨hfw, hv, below_trans_l O hb hpr hp, hwv⟩
      exact hef ▸ hfa))
  exact (hφ x).mp (hall x) y s t p ⟨hs, ht, hp, he⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 规范名称递归的小图地模型实例

使用实际小图集合操作实现递归所需片段，再调用同一通用递归定理。
构造证书的选择只留在 Prop 存在证明中，不导出不可计算的名称选择函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SmallGraph
universe u
attribute [local implicit_reducible] sg_model Definitional.Project.FirstOrderSemantics.reduct

theorem sg_mem_ind_l : Mem_ind_d sg_structure.{u} := by
  intro n φ ρ h x
  exact SG_set.mem_wf.induction x h

/-- 所有操作直接由小图并合、收集与分离证明，无额外递归假设。 -/
theorem sg_check_ops_l : Check_ops_d sg_structure.{u} where
  pair := SG_set.pair
  union := SG_set.union
  collect b x h := by
    obtain ⟨T, hT⟩ := SG_set.collection x
      (fun y F => Check_graph_d sg_structure b F ∧ ∃ t, Entry_d sg_structure y t F) h
    obtain ⟨C, hC⟩ := SG_set.separation T (Check_graph_d sg_structure b)
    refine ⟨C, fun F hF => ((hC F).mp hF).2, ?_⟩
    intro y hy
    obtain ⟨F, hF, hf, t, ht⟩ := hT y hy
    exact ⟨F, t, (hC F).mpr ⟨hF, hf⟩, ht⟩
  image b F x h hu := by
    let R (y p : SG_set.{u}) := ∃ s, Entry_d sg_structure y s F ∧ KPair_d sg_structure p s b
    obtain ⟨T, hT⟩ := SG_set.collection x R (fun y hy => by
      obtain ⟨s, hs⟩ := h y hy
      obtain ⟨p, hp⟩ := sg_kpair_l.total s b
      exact ⟨p, s, hs, hp⟩)
    obtain ⟨t, ht⟩ := SG_set.separation T (fun p => ∃ y, sg_structure.mem y x ∧ R y p)
    refine ⟨t, fun p => (ht p).trans ?_⟩
    constructor
    · rintro ⟨_, y, hy, s, hs, hp⟩
      exact ⟨y, s, hy, hs, hp⟩
    · rintro ⟨y, s, hy, hs, hp⟩
      obtain ⟨q, hq, a, ha, hqa⟩ := hT y hy
      have he := kpair_unique_l sg_structure sg_extensional ((hu y hy s a hs ha) ▸ hp) hqa
      exact ⟨he.symm ▸ hq, y, hy, s, hs, hp⟩

theorem sg_check_range_l (F : SG_set.{u}) :
    ∃ S, ∀ t, sg_structure.mem t S ↔ ∃ x, Entry_d sg_structure x t F := by
  obtain ⟨A, hA⟩ := SG_set.union F
  obtain ⟨D, hD⟩ := SG_set.union A
  obtain ⟨S, hS⟩ := SG_set.separation D (fun t => ∃ x, Entry_d sg_structure x t F)
  refine ⟨S, fun t => (hS t).trans ?_⟩
  constructor
  · exact And.right
  · rintro ⟨x, p, hp, hpf⟩
    obtain ⟨v, hv, htv⟩ := (kpair_union_l sg_structure hp t).mpr (Or.inr rfl)
    exact ⟨(hD t).mpr ⟨v, (hA v).mpr ⟨p, hpf, hv⟩, htv⟩, x, p, hp, hpf⟩

/-- 小图地模型的无权呈现解释为原对象本身。 -/
theorem sg_ground_l (x : SG_set.{u}) : Ground_d sg_structure x x := by
  induction x using Quotient.inductionOn with
  | _ G =>
    refine ⟨G, ⟨fun a => SG_set.mk (G.at_node a), rfl, ?_, ?_⟩, rfl⟩
    · intro a d h
      exact (SG_set.mem_mk (G.at_node d) _).mpr ⟨a, h, rfl⟩
    · intro d y hy
      obtain ⟨a, ha, he⟩ := (SG_set.mem_mk (G.at_node d) y).mp hy
      exact ⟨a, ha, he.symm⟩

theorem sg_check_val_l {B b x t : SG_set.{u}} (hb : b ∈ B)
    (ht : Check_d sg_structure b x t) (U : SG_set.{u} → Prop) (hU : U b) :
    Val_d sg_structure B U t x :=
  check_val_exists_l sg_structure sg_extensional sg_mem_ind_l SG_set.pair sg_check_range_l
    SG_set.mem_wf sg_setlike_l (B := B) (b := b) hb ht (sg_ground_l x) U hU

/-- 原小图规范名称入口现在也走通用内部递归，并同时返回规范性与唯一性。 -/
theorem sg_check_exists_l {B b : SG_set.{u}} (hb : b ∈ B) (x : SG_set.{u}) :
    ∃ t, Check_d sg_structure b x t ∧ Name_d sg_structure B t ∧
      (∀ s, Check_d sg_structure b x s → s = t) ∧
      ∀ U : SG_set.{u} → Prop, U b → Val_d sg_structure B U t x := by
  obtain ⟨t, ht⟩ := check_exists_l sg_structure sg_extensional sg_mem_ind_l sg_check_ops_l b x
  exact ⟨t, ht, check_name_l sg_structure sg_check_range_l (B := B) (b := b) hb ht,
    fun s hs => check_unique_l sg_structure sg_extensional sg_mem_ind_l b x s t hs ht,
    sg_check_val_l hb ht⟩

/-- 每个旧对象通过其实际内部规范名称进入解释扩张。 -/
theorem sg_check_ext_l {B b : SG_set.{u}} (hb : b ∈ B)
    (U : SG_set.{u} → Prop) (hU : U b) (x : SG_set.{u}) : Ext_l (sg_name_domain_l B) U x := by
  obtain ⟨t, _, _, _, hv⟩ := sg_check_exists_l hb x
  obtain ⟨G, hG, he⟩ := hv U hU
  exact ⟨G, ⟨t, hG⟩, he⟩

end YesMetaZFC.Model.Forcing.Internal

/-! ## 规范名称的最小闭支撑及混合库编码

在一个实际传递容器上一次构造规范名称图。其值域是闭名称支撑，故最小支撑
不比原容器大；混合库再沿支撑与条件的积单射进入同一序数的幂集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem Name_hull_d.check_bound_l {B b x a C S δ : M.Domain}
    (hull : Name_hull_d M B a a S) (check : Check_d M b x a) (hb : M.mem b B)
    (trans : M.TransitiveSet C) (hx : M.mem x C) (hδ : M.IsOrdinal δ)
    (small : M.CardinalLessOrEqual I C δ) : M.CardinalLessOrEqual I S δ := by
  let ρ : Env M 1 := ⟨fun _ => b,fun _ => b⟩
  let φ : BinarySchema 1 := { body := check_m (.bound 2) (.bound 1) .newest }
  have sat y t : φ.denote ρ y t ↔ Check_d M b y t := check_sat_l M hZF.1 ..
  have total y (_ : M.mem y C) : ∃ t, φ.denote ρ y t := by
    obtain ⟨t,ht,_,_⟩ := zf_check_l M hZF hb y
    exact ⟨t,(sat y t).mpr ht⟩
  have unique y (_ : M.mem y C) s t (hs : φ.denote ρ y s) (ht : φ.denote ρ y t) : s = t :=
    check_unique_l M hZF.1 (check_ind_l M hZF) b y s t ((sat y s).mp hs) ((sat y t).mp ht)
  obtain ⟨D,members⟩ := ZF.exists_functionalImageOn hZF φ ρ C total unique
  obtain ⟨f,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun y t hy ht => (members t).mpr ⟨y,hy,ht⟩)
  have onto : M.IsSetSurjectiveOnto I f C D := by
    intro t ht
    obtain ⟨y,hy,yt⟩ := (members t).mp ht
    exact ⟨y,hy,(values y t).mpr ⟨hy,yt⟩⟩
  have closed : Supp_d M B D := by
    intro t ht p hp
    obtain ⟨y,hy,yt⟩ := (members t).mp ht
    obtain ⟨z,s,hz,zs,ps⟩ := (check_mem_l M hZF.1 (check_ind_l M hZF) ((sat y t).mp yt) p).mp hp
    exact ⟨s,b,ps,(members s).mpr ⟨z,trans y hy z hz,(sat z s).mpr zs⟩,hb⟩
  have ha := (members a).mpr ⟨x,hx,(sat x a).mpr check⟩
  obtain ⟨g,fg⟩ := ZF.exists_inclusionInjection hZF I (hull.least D ha ha closed)
  obtain ⟨k,fk⟩ := ZF.ordinal_image_bound_l I hZF hδ small fn onto
  exact ZF.exists_compositionInjection hZF I fg fk

theorem Name_pool_d.check_code_l {ω δ B b x a C W P : M.Domain}
    (pool : Name_pool_d M B a a W) (check : Check_d M b x a) (hb : M.mem b B)
    (hw : M.IsOmega ω) (hδ : M.IsInfiniteCardinal I ω δ)
    (trans : M.TransitiveSet C) (hx : M.mem x C)
    (small : M.CardinalLessOrEqual I C δ) (conditions : M.CardinalLessOrEqual I B δ)
    (power : M.IsPowerSetOf P δ) : M.CardinalLessOrEqual I W P := by
  obtain ⟨S,hull,members⟩ := pool
  have support := hull.check_bound_l hZF check hb trans hx hδ.1.1 small
  obtain ⟨Q,product⟩ := ZF.exists_cartesianProduct hZF I S B
  obtain ⟨f,fn⟩ := ZF.infinite_product_l I hZF hw hδ support conditions product
  have library : M.IsPowerSetOf W Q := by
    intro t
    apply (members t).trans
    constructor
    · intro bound p hp
      obtain ⟨s,b,code,hs,hb⟩ := bound p hp
      exact (product p).mpr ⟨s,hs,b,hb,code⟩
    · intro sub p hp
      obtain ⟨s,hs,b,hb,code⟩ := (product p).mp (sub p hp)
      exact ⟨s,b,code,hs,hb⟩
  exact ZF.power_injection_l I hZF library power fn

end YesMetaZFC.Model.Forcing.Internal
