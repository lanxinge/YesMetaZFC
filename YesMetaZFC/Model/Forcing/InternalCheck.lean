import YesMetaZFC.Model.Forcing.InternalCheckSyntax
import YesMetaZFC.Model.Forcing.InternalClosure
import YesMetaZFC.SetTheory.MembershipInduction

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

private def unique_m {n} (b x : Term n) : Formula 1 n :=
  .forallE (.forallE (.imp
    (.conj (check_m b.weaken.weaken x.weaken.weaken (.bound 1))
      (check_m b.weaken.weaken x.weaken.weaken .newest))
    (Formula.extensionalEq (.bound 1) .newest)))

derive_free_closed unique_m

/-- 唯一性只使用实际公式的成员归纳与外延性。 -/
theorem check_unique_l (hE : Extensional M) (hI : Mem_ind_d M) (b x : M.Domain) :
    ∀ s t, Check_d M b x s → Check_d M b x t → s = t := by
  let ρ : Env M 1 := ⟨fun _ => b, fun _ => b⟩
  let φ : UnarySchema 1 := { body := unique_m (.bound 1) (.bound 0) }
  have hφ x : φ.denote ρ x ↔ ∀ s t, Check_d M b x s → Check_d M b x t → s = t := by
    simp only [UnarySchema.denote, φ, unique_m, Formula.satisfies_forall_iff,
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

private theorem entry_union_l {C F} (hF : M.IsUnionOf F C) (x t : M.Domain) :
    Entry_d M x t F ↔ ∃ G, M.mem G C ∧ Entry_d M x t G := by
  constructor
  · rintro ⟨p, hp, ht⟩
    obtain ⟨G, hG, ht⟩ := (hF p).mp ht
    exact ⟨G, hG, p, hp, ht⟩
  · rintro ⟨G, hG, p, hp, ht⟩
    exact ⟨p, hp, (hF p).mpr ⟨G, hG, ht⟩⟩

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
