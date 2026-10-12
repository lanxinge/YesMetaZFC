import YesMetaZFC.Model.SetTheory.Internal.TransitiveSource
import YesMetaZFC.SetTheory.Card.Syntax

/-! # 任意传递集合中的原函数公式

已有图的坐标由传递性回收；读取公式不需要子模型对配对封闭。
这使原函数、单射与双射语法也能直接用于后继秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {X : M.Domain} (hX : M.TransitiveSet X)
  (nx : Nonempty {x // M.mem x X}) (hE : Extensional M)
include hX hE
local notation "N" => rt_model_l X nx

theorem rt_kpair_formula_l {d} (ρ : Env N d) (p a b : Term d) :
    Formula.satisfies ρ (kpair_convention_l.code p a b) ↔ KPair_d M (p.eval ρ).val (a.eval ρ).val (b.eval ρ).val := by
  exact (kpair_sat_l N (rt_model_ext_l hE hX nx) ρ p a b).trans
    ((kpair0_sat_l (rt_model_ext_l hE hX nx) ρ p a b).symm.trans
      ((rt_model_delta_l hX nx (kpair0_delta_l ..) ρ).trans (by
        simpa only [@eval_image_env_l (rt_model_l X nx) M Subtype.val] using kpair0_sat_l hE (image_env_l Subtype.val ρ) p a b)))

theorem rt_entry_formula_l {d} (ρ : Env N d) (a b f : Term d) :
    Formula.satisfies ρ (Formula.orderedPairMem kpair_convention_l a b f) ↔
      Rd_entry_d (a.eval ρ).val (b.eval ρ).val (f.eval ρ).val := by
  simp only [Formula.orderedPairMem, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, rt_kpair_formula_l hX nx hE, Formula.satisfies_mem_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨p, hp, hf⟩ => ⟨p.val, hp, hf⟩,
    fun ⟨p, hp, hf⟩ => ⟨⟨p, hX _ (f.eval ρ).property p hf⟩, hp, hf⟩⟩

variable (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
local notation "I" => kpair_interpretation_l M hE hP

theorem rt_function_formula_l {d} (ρ : Env N d) (f : Term d) :
    Formula.satisfies ρ (Formula.isFunction kpair_convention_l f) ↔ M.IsSetFunction I (f.eval ρ).val := by
  simp only [Formula.isFunction, Formula.isRelation,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, rt_kpair_formula_l hX nx hE,
    rt_entry_formula_l hX nx hE, Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hE hX nx),
    Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]
  constructor
  · rintro ⟨rel, func⟩
    refine ⟨fun p hp => ?_, fun a b c hab hac => ?_⟩
    · obtain ⟨a, b, hp'⟩ := rel ⟨p, hX _ (f.eval ρ).property p hp⟩ hp
      exact ⟨a.val, b.val, hp'⟩
    · have ab := rd_entry_transitive_l hX (f.eval ρ).property hab
      have ac := rd_entry_transitive_l hX (f.eval ρ).property hac
      exact congrArg Subtype.val (func ⟨a, ab.1⟩ ⟨b, ab.2⟩ ⟨c, ac.2⟩ ⟨hab, hac⟩)
  · rintro ⟨rel, func⟩
    refine ⟨fun p hp => ?_, fun a b c h => ?_⟩
    · obtain ⟨a, b, pair⟩ := rel p.val hp
      have ab := pair.mem_l M hX p.property
      exact ⟨⟨a, ab.1⟩, ⟨b, ab.2⟩, pair⟩
    · exact Subtype.ext (func a.val b.val c.val h.1 h.2)

theorem rt_domain_formula_l {d} (ρ : Env N d) (A f : Term d) :
    Formula.satisfies ρ (Formula.isDomain kpair_convention_l A f) ↔ M.IsDomainOf I (A.eval ρ).val (f.eval ρ).val := by
  simp only [Formula.isDomain, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, rt_entry_formula_l hX nx hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_zero_push, Term.eval_bound_one_push]
  constructor
  · intro h x
    refine ⟨fun hx => ?_, fun ⟨y, hxy⟩ => ?_⟩
    · obtain ⟨y, hxy⟩ := (h ⟨x, hX _ (A.eval ρ).property x hx⟩).mp hx
      exact ⟨y.val, hxy⟩
    · have xy := rd_entry_transitive_l hX (f.eval ρ).property hxy
      exact (h ⟨x, xy.1⟩).mpr ⟨⟨y, xy.2⟩, hxy⟩
  · intro h x
    exact (h x.val).trans ⟨fun ⟨y, hxy⟩ => ⟨⟨y, (rd_entry_transitive_l hX (f.eval ρ).property hxy).2⟩, hxy⟩,
      fun ⟨y, hxy⟩ => ⟨y.val, hxy⟩⟩

theorem rt_range_formula_l {d} (ρ : Env N d) (A f : Term d) :
    Formula.satisfies ρ (Formula.isRange kpair_convention_l A f) ↔ M.IsRangeOf I (A.eval ρ).val (f.eval ρ).val := by
  simp only [Formula.isRange, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, rt_entry_formula_l hX nx hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest, Term.eval_bound_zero_push, Term.eval_bound_one_push]
  constructor
  · intro h y
    refine ⟨fun hy => ?_, fun ⟨x, hxy⟩ => ?_⟩
    · obtain ⟨x, hxy⟩ := (h ⟨y, hX _ (A.eval ρ).property y hy⟩).mp hy
      exact ⟨x.val, hxy⟩
    · have xy := rd_entry_transitive_l hX (f.eval ρ).property hxy
      exact (h ⟨y, xy.2⟩).mpr ⟨⟨x, xy.1⟩, hxy⟩
  · intro h y
    exact (h y.val).trans ⟨fun ⟨x, hxy⟩ => ⟨⟨x, (rd_entry_transitive_l hX (f.eval ρ).property hxy).1⟩, hxy⟩,
      fun ⟨x, hxy⟩ => ⟨x.val, hxy⟩⟩

theorem rt_function_from_formula_l {d} (ρ : Env N d) (f A B : Term d) :
    Formula.satisfies ρ (Formula.isFunctionFromTo kpair_convention_l f A B) ↔
      M.IsSetFunctionFromTo I (f.eval ρ).val (A.eval ρ).val (B.eval ρ).val := by
  simp only [Formula.isFunctionFromTo, Formula.satisfies_conj_iff, rt_function_formula_l hX nx hE hP,
    rt_domain_formula_l hX nx hE hP, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    rt_entry_formula_l hX nx hE, Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h a ha => ?_, fun h a ha => ?_⟩)
  · obtain ⟨b, hb, hab⟩ := h ⟨a, hX _ (A.eval ρ).property a ha⟩ ha
    exact ⟨b.val, hb, hab⟩
  · obtain ⟨b, hb, hab⟩ := h a.val ha
    exact ⟨⟨b, hX _ (B.eval ρ).property b hb⟩, hb, hab⟩

theorem rt_injection_formula_l {d} (ρ : Env N d) (f A B : Term d) :
    Formula.satisfies ρ (Formula.isInjectionFromTo kpair_convention_l f A B) ↔
      M.IsSetInjectionFromTo I (f.eval ρ).val (A.eval ρ).val (B.eval ρ).val := by
  simp only [Formula.isInjectionFromTo, Formula.isInjective, Formula.satisfies_conj_iff,
    rt_function_from_formula_l hX nx hE hP, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rt_entry_formula_l hX nx hE, Formula.satisfies_extensionalEq_iff_eq (rt_model_ext_l hE hX nx),
    Definitional.Term.eval_weaken, Term.eval_bound_zero_push, Term.eval_bound_one_push, Term.eval_bound_two_push]
  refine and_congr Iff.rfl ⟨fun h a b x ha hb => ?_, fun h a b x hh => ?_⟩
  · have ax := rd_entry_transitive_l hX (f.eval ρ).property ha
    have bx := rd_entry_transitive_l hX (f.eval ρ).property hb
    exact congrArg Subtype.val (h ⟨a, ax.1⟩ ⟨b, bx.1⟩ ⟨x, ax.2⟩ ⟨ha, hb⟩)
  · exact Subtype.ext (h a.val b.val x.val hh.1 hh.2)

theorem rt_bijection_formula_l {d} (ρ : Env N d) (f A B : Term d) :
    Formula.satisfies ρ (Formula.isBijectionFromTo kpair_convention_l f A B) ↔
      M.IsSetBijectionFromTo I (f.eval ρ).val (A.eval ρ).val (B.eval ρ).val := by
  simp only [Formula.isBijectionFromTo, Formula.isSurjectiveOnto, Formula.satisfies_conj_iff,
    rt_injection_formula_l hX nx hE hP, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    rt_entry_formula_l hX nx hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
    Term.eval_bound_zero_push, Term.eval_bound_one_push]
  refine and_congr Iff.rfl ⟨fun h b hb => ?_, fun h b hb => ?_⟩
  · obtain ⟨a, ha, hab⟩ := h ⟨b, hX _ (B.eval ρ).property b hb⟩ hb
    exact ⟨a.val, ha, hab⟩
  · obtain ⟨a, ha, hab⟩ := h b.val hb
    exact ⟨⟨a, hX _ (A.eval ρ).property a ha⟩, ha, hab⟩

end YesMetaZFC.SetTheory.Internal
