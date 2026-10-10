import YesMetaZFC.SetTheory.Kuratowski

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
