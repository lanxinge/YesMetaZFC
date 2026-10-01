import YesMetaZFC.SetTheory.SetConstruction

/-! # 内部名称的有序对编码

名称采用 Kuratowski 对 {{a},{a,b}}。左坐标沿三条成员边下降到包含该对的名称，
因此地模型的外部良基性足以解释名称。编码接入已有 OrderedPairConvention，
不更改其他模块的平坦有序对约定。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Pair_d (p a b : M.Domain) : Prop := ∀ z, M.mem z p ↔ z = a ∨ z = b

def KPair_d (p a b : M.Domain) : Prop :=
  ∃ s t, M.IsSingletonOf s a ∧ Pair_d M t a b ∧ Pair_d M p s t

def kpair_m {n} (p a b : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (Formula.isSingleton (.bound 1) a.weaken.weaken)
    (.conj (Formula.isUnorderedPair .newest a.weaken.weaken b.weaken.weaken)
      (Formula.isUnorderedPair p.weaken.weaken (.bound 1) .newest))))

derive_free_closed kpair_m

def kpair_convention_l : OrderedPairConvention where
  code := kpair_m
  freeClosed_code := kpair_m_freeClosed

theorem pair_sat_l (hE : Extensional M) {n} (ρ : Env M n) (p a b : Term n) :
    Formula.satisfies ρ (Formula.isUnorderedPair p a b) ↔
      Pair_d M (p.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [Formula.isUnorderedPair, Pair_d, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken]

theorem kpair_sat_l (hE : Extensional M) {n} (ρ : Env M n) (p a b : Term n) :
    Formula.satisfies ρ (kpair_m p a b) ↔ KPair_d M (p.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [kpair_m, KPair_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isSingleton_iff hE, pair_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
    Term.eval_bound_one_push, Term.eval_bound_zero_push]

theorem kpair_unique_l (hE : Extensional M) {p q a b}
    (h : KPair_d M p a b) (k : KPair_d M q a b) : p = q := by
  obtain ⟨s, t, hs, ht, hp⟩ := h
  obtain ⟨v, w, hv, hw, hq⟩ := k
  have hs : s = v := hs.eq hE hv
  have ht : t = w := hE.eq_of_same_members _ _ (fun z => (ht z).trans (hw z).symm)
  subst v; subst w
  exact hE.eq_of_same_members _ _ (fun z => (hp z).trans (hq z).symm)

theorem kpair_union_l {p a b} (h : KPair_d M p a b) (z : M.Domain) :
    (∃ t, M.mem t p ∧ M.mem z t) ↔ z = a ∨ z = b := by
  obtain ⟨s, t, hs, ht, hp⟩ := h
  constructor
  · rintro ⟨v, hv, hz⟩
    rcases (hp v).mp hv with rfl | rfl
    · exact Or.inl ((hs z).mp hz)
    · exact (ht z).mp hz
  · intro hz
    exact ⟨t, (hp t).mpr (Or.inr rfl), (ht z).mpr hz⟩

theorem kpair_injective_l {p a b c d}
    (h : KPair_d M p a b) (k : KPair_d M p c d) : a = c ∧ b = d := by
  have ha : a = c := by
    obtain ⟨s, t, hs, ht, hp⟩ := h
    obtain ⟨v, w, hv, _, hq⟩ := k
    apply (hv a).mp
    rcases (hp v).mp ((hq v).mpr (Or.inl rfl)) with rfl | rfl
    · exact (hs a).mpr rfl
    · exact (ht a).mpr (Or.inl rfl)
  subst c
  refine ⟨rfl, ?_⟩
  rcases (kpair_union_l M k b).mp ((kpair_union_l M h b).mpr (Or.inr rfl)) with hb | hb
  · rcases (kpair_union_l M h d).mp ((kpair_union_l M k d).mpr (Or.inr rfl)) with hd | hd
    · exact hb.trans hd.symm
    · exact hd.symm
  · exact hb

/-- 只消费外延性与配对存在，给出已实现的编码解释。 -/
def kpair_interpretation_l (hE : Extensional M)
    (hP : ∀ a b, ∃ p, Pair_d M p a b) : kpair_convention_l.Interpretation M where
  Codes := KPair_d M
  realizes := kpair_sat_l M hE
  total a b := by
    obtain ⟨s, hs⟩ := hP a a
    obtain ⟨t, ht⟩ := hP a b
    obtain ⟨p, hp⟩ := hP s t
    exact ⟨p, s, t, fun z => (hs z).trans ⟨fun h => h.elim id id, Or.inl⟩, ht, hp⟩
  unique := kpair_unique_l M hE
  injective := kpair_injective_l M

/-- 左坐标 a ∈ {a} ∈ (a,b) ∈ τ，严格下降由实际成员路径给出。 -/
theorem kpair_descent_l {p a b t} (h : KPair_d M p a b) (hp : M.mem p t) :
    Relation.TransGen M.mem a t := by
  obtain ⟨s, v, hs, _, hv⟩ := h
  exact .tail (.tail (.single ((hs a).mpr rfl)) ((hv s).mpr (Or.inl rfl))) hp

end YesMetaZFC.Model.Forcing.Internal
