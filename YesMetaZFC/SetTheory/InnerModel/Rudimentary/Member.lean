import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Graph

/-! # rud 输出成员关系的 Δ₀ 定义

成员公式与函数图分开：构造整族输出时，先收集成员真值表，再取参数纤维。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def ri_member_m {n} (k : Ri_sym) (a b t : Term n) : Formula 1 n :=
  Formula.existsMem (ri_left_l k a b) (Formula.existsMem (ri_right_l k a b).weaken
    (ri_value_m k a.weaken.weaken (.bound 1) .newest t.weaken.weaken))
@[simp] theorem ri_member_closed_l {n} (k : Ri_sym) (a b t : Term n)
    (ha : a.freeSupport = []) (hb : b.freeSupport = []) (ht : t.freeSupport = []) :
    (ri_member_m k a b t).FreeClosed := by
  have hl : (ri_left_l k a b).freeSupport = [] := by cases k <;> assumption
  have hr : (ri_right_l k a b).freeSupport = [] := by cases k <;> assumption
  simp -implicitDefEqProofs [ri_member_m, ha, ht, hl, hr]

theorem ri_member_delta_l {n} (k : Ri_sym) (a b t : Term n) : (ri_member_m k a b t).IsDelta0 :=
  .existsMem _ (.existsMem _ (ri_value_delta_l ..))

theorem ri_member_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (k : Ri_sym) (a b t : Term n) :
    Formula.satisfies ρ (ri_member_m k a b t) ↔ Rd_mem_d (ri_symbol_l k) (a.eval ρ) (b.eval ρ) (a.eval ρ) (t.eval ρ) := by
  have hl : (ri_left_l k a b).eval ρ = ri_left_l k (a.eval ρ) (b.eval ρ) := by cases k <;> rfl
  have hr : (ri_right_l k a b).eval ρ = ri_right_l k (a.eval ρ) (b.eval ρ) := by cases k <;> rfl
  simp only [ri_member_m, Formula.satisfies_existsMem_iff, ri_value_sat_l hKP.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, hl, hr]
  obtain ⟨V, hv⟩ := rd_fun_exists_l hKP (ri_symbol_l k) (a.eval ρ) (b.eval ρ) (a.eval ρ)
  exact (((ri_image_value_l k _ _ _ V).mpr hv) (t.eval ρ)).symm.trans (hv (t.eval ρ))

def rd_member_m {n} : Rd_sym → Term n → Term n → Term n → Term n → Formula 1 n
  | .pair, a, b, _, t => .disj (Formula.extensionalEq t a) (Formula.extensionalEq t b)
  | .diff, a, b, _, t => .conj (.mem t a) (.neg (.mem t b))
  | .prod, a, b, _, t => ri_member_m .prod a b t
  | .mid, a, b, _, t => ri_member_m .mid a b t
  | .last, a, b, _, t => ri_member_m .last a b t
  | .union, a, _, _, t => Formula.existsMem a (.mem t.weaken .newest)
  | .range, a, b, _, t => ri_member_m .range a b t
  | .mem, a, b, _, t => ri_member_m .mem a b t
  | .fibers, a, b, _, t => ri_member_m .fibers a b t
  | .opair, a, b, _, t => .disj (pair0_m t a a) (pair0_m t a b)
  | .triple, a, b, c, t => .disj (pair0_m t a a)
      (Formula.existsMem t (.conj (kpair0_m .newest b.weaken c.weaken) (pair0_m t.weaken a.weaken .newest)))
  | .adj, a, b, c, t => .disj (Formula.extensionalEq t a) (kpair0_m t b c)
  | .fiber, a, b, _, t => rd_entry0_m t b a

@[simp] theorem rd_member_closed_l {n} (k : Rd_sym) (a b c t : Term n)
    (ha : a.freeSupport = []) (hb : b.freeSupport = []) (hc : c.freeSupport = []) (ht : t.freeSupport = []) :
    (rd_member_m k a b c t).FreeClosed := by
  cases k <;> simp -implicitDefEqProofs [rd_member_m, Definitional.Formula.FreeClosed, ha, hb, hc, ht]

theorem rd_member_delta_l {n} (k : Rd_sym) (a b c t : Term n) : (rd_member_m k a b c t).IsDelta0 := by
  cases k <;> first
    | exact ri_member_delta_l ..
    | exact .disj (.atom _ _ _) (.atom _ _ _)
    | exact .conj (.mem _ _) (.neg (.mem _ _))
    | exact .existsMem _ (.mem _ _)
    | exact .disj (pair0_delta_l ..) (pair0_delta_l ..)
    | exact .disj (pair0_delta_l ..) (.existsMem _ (.conj (kpair0_delta_l ..) (pair0_delta_l ..)))
    | exact .disj (.atom _ _ _) (kpair0_delta_l ..)
    | exact rd_entry0_delta_l ..

theorem rd_member_sat_l (hKP : M.Models KP) {n} (ρ : Env M n) (k : Rd_sym) (a b c t : Term n) :
    Formula.satisfies ρ (rd_member_m k a b c t) ↔ Rd_mem_d k (a.eval ρ) (b.eval ρ) (c.eval ρ) (t.eval ρ) := by
  have singleton (p x : M.Domain) : Pair_d M p x x ↔ M.IsSingletonOf p x := by
    apply forall_congr'; intro z
    exact iff_congr Iff.rfl ⟨fun h => h.elim id id, Or.inl⟩
  cases k <;> first | exact ri_member_sat_l hKP ρ _ a b t | skip
  all_goals simp only [rd_member_m, Rd_mem_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_existsMem_iff, pair0_sat_l hKP.1, kpair0_sat_l hKP.1, rd_entry0_sat_l hKP.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, singleton]
  constructor
  · exact fun h => h.elim Or.inl (fun ⟨p, _, hp⟩ => Or.inr ⟨p, hp⟩)
  · exact fun h => h.elim Or.inl (fun ⟨p, hp, ht⟩ => Or.inr ⟨p, (ht p).mpr (Or.inr rfl), hp, ht⟩)

end YesMetaZFC.SetTheory.InnerModel
