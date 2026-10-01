import YesMetaZFC.Model.Forcing.Internal.Names.Construction

/-! # 内部集合中名称的泛型像 N[G]

先在地模型中分离 N 的名称成员，再给每个名称赋全部条件作为权重。所得名称
在任意泛型下恰好解释为这些名称的值组成的集合，不选择商类代表元。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Ng_source_d (B N S : M.Domain) : Prop := ∀ s, M.mem s S ↔ M.mem s N ∧ Name_d M B s

def ng_source_m {n} (B N S : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest S.weaken) (.conj (.mem .newest N.weaken) (name_m B.weaken .newest)))
derive_free_closed ng_source_m

theorem ng_source_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B N S : Term n) :
    Formula.satisfies ρ (ng_source_m B N S) ↔ Ng_source_d M (B.eval ρ) (N.eval ρ) (S.eval ρ) := by
  simp only [ng_source_m, Ng_source_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, name_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def Ng_name_d (B N t : M.Domain) : Prop := Name_d M B t ∧
  ∀ s p, Entry_d M s p t ↔ M.mem s N ∧ Name_d M B s ∧ M.mem p B

def ng_name_m {n} (B N t : Term n) : Formula 1 n :=
  .conj (name_m B t) (.forallE (.forallE (.iff (entry_m (.bound 1) .newest t.weaken.weaken)
    (.conj (.mem (.bound 1) N.weaken.weaken) (.conj (name_m B.weaken.weaken (.bound 1)) (.mem .newest B.weaken.weaken))))))
derive_free_closed ng_name_m

theorem ng_name_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B N t : Term n) :
    Formula.satisfies ρ (ng_name_m B N t) ↔ Ng_name_d M (B.eval ρ) (N.eval ρ) (t.eval ρ) := by
  simp only [ng_name_m, Ng_name_d, Formula.satisfies_conj_iff, name_sat_l M hE,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, entry_sat_l M hE,
    Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  rfl

theorem ng_source_exists_l (hZF : M.Models ZF) (B N : M.Domain) : ∃ S, Ng_source_d M B N S := by
  let ρ : Env M 1 := ⟨fun _ => B, fun _ => B⟩
  let φ : UnarySchema 1 := { body := name_m (.bound 1) .newest }
  obtain ⟨S, hS⟩ := ZF.separation_exists_d hZF φ ρ N
  exact ⟨S, fun s => (hS s).trans (and_congr_right fun _ => name_sat_l M hZF.1 _ _ _)⟩

theorem ng_name_exists_l (hZF : M.Models ZF) (B N : M.Domain) : ∃ t, Ng_name_d M B N t := by
  obtain ⟨S, hS⟩ := ng_source_exists_l M hZF B N
  let φ : BinarySchema 0 := { body := .truth }
  obtain ⟨t, ht, _, he⟩ := name_comp_l M hZF φ ⟨Fin.elim0, fun _ => B⟩ B S (fun s hs => ((hS s).mp hs).2)
  refine ⟨t, ht, fun s p => (he s p).trans ?_⟩
  simp only [BinarySchema.denote, φ, Formula.satisfies_truth_iff, and_true, hS s]
  exact and_assoc

theorem ng_name_unique_l (hE : Extensional M) {B N s t} (hs : Ng_name_d M B N s) (ht : Ng_name_d M B N t) : s = t := by
  have rel {t} (ht : Name_d M B t) : ∀ p, M.mem p t → ∃ a b, KPair_d M p a b := by
    obtain ⟨S, ht, hS⟩ := ht
    exact fun p hp => (hS t ht p hp).elim fun a h => h.elim fun b h => ⟨a, b, h.1⟩
  exact entry_ext_l M hE (rel hs.1) (rel ht.1) (fun a b => (hs.2 a b).trans (ht.2 a b).symm)

def Ng_mem_d (B R z : M.Domain) (U : M.Domain → Prop) (N : M.Domain) (x : Name_quot_l M B R z U) : Prop :=
  ∃ s, M.mem s N ∧ Qval_d M B R z U s x

variable {M} {B R z : M.Domain} {U : M.Domain → Prop}

/-- 规范名称的泛型值正是 N 中名称的全部值；没有遗漏或额外的商类。 -/
theorem ng_value_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
    {N t} {Y : Name_quot_l M B R z U} (ht : Ng_name_d M B N t) (hY : Qval_d M B R z U t Y)
    (x : Name_quot_l M B R z U) : x ∈ Y ↔ Ng_mem_d M B R z U N x := by
  rw [qval_mem_l O hZF hU hY]
  constructor
  · rintro ⟨s, p, hs, _, hx⟩
    exact ⟨s, ((ht.2 s p).mp hs).1, hx⟩
  · rintro ⟨s, hs, hx⟩
    obtain ⟨p, hp⟩ := hU.inhabited
    exact ⟨s, p, (ht.2 s p).mpr ⟨hs, qval_name_l hx, (hU.proper p hp).1⟩, hp, hx⟩

/-- 从任意内部集合 N 直接构造扩张中的实际集合 N[G] 及其逐成员刻画。 -/
theorem ng_set_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U) (N : M.Domain) :
    ∃ Y : (extension_l M hZF B R z U).Domain, ∀ x, x ∈ Y ↔ Ng_mem_d M B R z U N x := by
  obtain ⟨t, ht⟩ := ng_name_exists_l M hZF B N
  obtain ⟨Y, hY⟩ := name_value_l (R := R) (z := z) (U := U) ht.1
  exact ⟨Y, ng_value_l O hZF hU ht hY⟩

/-- 传递地集合的全部名称值仍组成传递集合；直接沿名称条目的有限成员路径回拉。 -/
theorem ng_transitive_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) (hU : Generic_d M B R z U)
    {X} {Y : (extension_l M hZF B R z U).Domain} (hX : M.TransitiveSet X)
    (hY : ∀ x, x ∈ Y ↔ Ng_mem_d M B R z U X x) : (extension_l M hZF B R z U).TransitiveSet Y := by
  intro x hx y hy
  obtain ⟨t, htX, htx⟩ := (hY x).mp hx
  obtain ⟨s, b, ⟨p, hp, hpt⟩, _, hsy⟩ := (qval_mem_l O hZF hU htx).mp hy
  obtain ⟨v, hvp, hsv⟩ := (kpair_union_l M hp s).mpr (Or.inl rfl)
  exact (hY y).mpr ⟨s, hX v (hX p (hX t htX p hpt) v hvp) s hsv, hsy⟩

end YesMetaZFC.Model.Forcing.Internal
