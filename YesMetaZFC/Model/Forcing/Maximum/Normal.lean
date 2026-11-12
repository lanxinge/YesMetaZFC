import YesMetaZFC.Model.Forcing.Atomic.Equivalence
import YesMetaZFC.SetTheory.CumulativeSelection

/-! # 全局力迫等号类的规范名称构造式

先在全局力迫等号类的最早累积层中收集全部名称，再对它们的原名称图取并。
两个阶段都有唯一集合规格，未定义不可计算的名称选择函数。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def All_eq_d (B R z s t : M.Domain) : Prop :=
  ∀ p, M.mem p B → p ≠ z → Eq_force_d M B R z p s t

def all_eq_m {n} (B R z s t : Term n) : Formula 1 n :=
  .forallE (.imp (.mem .newest B.weaken) (.imp (.neg (Formula.extensionalEq .newest z.weaken))
    (eq_force_m B.weaken R.weaken z.weaken .newest s.weaken t.weaken)))
derive_free_closed all_eq_m

def norm_pred_s : UnarySchema 4 := {
  body := .conj (name_m (.bound 4) .newest) (all_eq_m (.bound 4) (.bound 3) (.bound 2) .newest (.bound 1)) }

def norm_env_l (B R z t : M.Domain) : Env M 4 :=
  ⟨(fun i => match i.val with | 0 => t | 1 => z | 2 => R | _ => B), fun _ => B⟩

def norm_args_l {n} (B R z t : Term n) (i : Fin 4) : Term n :=
  match i.val with | 0 => t | 1 => z | 2 => R | _ => B

def Norm_name_d (I : kpair_convention_l.Interpretation M) (B R z t q : M.Domain) : Prop :=
  ∃ α S, V_min_d I norm_pred_s (norm_env_l M B R z t) α S ∧ M.IsUnionOf q S

def norm_name_m {n} (B R z t q : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj
    (v_min_m kpair_convention_l norm_pred_s
      (norm_args_l B.weaken.weaken R.weaken.weaken z.weaken.weaken t.weaken.weaken)
      (.bound 1) .newest) (Formula.isUnion q.weaken.weaken .newest)))
@[simp] theorem norm_name_closed_l {n} (B R z t q : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (ht : t.freeSupport = []) (hq : q.freeSupport = []) : (norm_name_m B R z t q).FreeClosed := by
  let e : Fin 4 → Term (n+2) :=
    norm_args_l B.weaken.weaken R.weaken.weaken z.weaken.weaken t.weaken.weaken
  have he : ∀ i, (e i).freeSupport = [] := by
    intro i
    dsimp [e, norm_args_l]
    split
    · simpa using ht
    · simpa using hz
    · simpa using hR
    · simpa using hB
  have hv := v_min_closed_l kpair_convention_l norm_pred_s e (.bound 1) .newest he rfl rfl
  simpa only [norm_name_m, Definitional.Formula.FreeClosed] using
    And.intro hv (Formula.isUnion_freeClosed q.weaken.weaken .newest (by simpa using hq) rfl)

theorem all_eq_sat_l (hE : Extensional M) {n} (ρ : Env M n) (B R z s t : Term n) :
    Formula.satisfies ρ (all_eq_m B R z s t) ↔ All_eq_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [all_eq_m, All_eq_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    eq_force_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem norm_pred_sat_l (hE : Extensional M) (ρ : Env M 4) (s) :
    norm_pred_s.denote ρ s ↔ Name_d M (ρ.bound 3) s ∧ All_eq_d M (ρ.bound 3) (ρ.bound 2) (ρ.bound 1) s (ρ.bound 0) := by
  simp only [UnarySchema.denote, norm_pred_s, Formula.satisfies_conj_iff, name_sat_l M hE, all_eq_sat_l M hE]
  rfl

theorem norm_name_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (B R z t q : Term n) : Formula.satisfies ρ (norm_name_m B R z t q) ↔
      Norm_name_d M I (B.eval ρ) (R.eval ρ) (z.eval ρ) (t.eval ρ) (q.eval ρ) := by
  simp only [norm_name_m, Norm_name_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    v_min_sat_l I hE, Formula.satisfies_isUnion_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  refine exists_congr fun α => exists_congr fun S => and_congr_left fun _ => ?_
  apply v_min_congr_l I
  intro s
  rw [norm_pred_sat_l M hE, norm_pred_sat_l M hE]
  simp [norm_env_l, norm_args_l, Definitional.Term.eval_weaken]

end YesMetaZFC.Model.Forcing.Internal

/-! ## 任意内部名称的确定规范代表

同一全局力迫等号类的最早层候选集唯一。候选名称图的并仍是名称，并通过
原子力迫的双向匹配方程证明与原名称全局相等；全过程不选择候选中的元素。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem norm_name_l (hZF : M.Models ZF) {t q} (ht : Name_d M B t)
    (h : Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t q) :
    Name_d M B q ∧ All_eq_d M B R z q t := by
  obtain ⟨α, S, ⟨_, _, hn, hS, _⟩, hU⟩ := h
  have names s (hs : M.mem s S) : Name_d M B s ∧ All_eq_d M B R z s t :=
    (norm_pred_sat_l M hZF.1 (norm_env_l M B R z t) s).mp (((hS s).mp hs).2)
  have hq : Name_d M B q := (name_unfold_l M (name_ops_l M hZF) B q).mpr (by
    intro v hv
    obtain ⟨s, hs, hvs⟩ := (hU v).mp hv
    exact (name_unfold_l M (name_ops_l M hZF) B s).mp (names s hs).1 v hvs)
  refine ⟨hq, fun p hp hz => (eq_force_unfold_l M hZF hq ht).mpr ⟨hp, ?_, ?_⟩⟩
  · intro a b hab
    obtain ⟨s, hs, hab⟩ := (entry_union_l M hU a b).mp hab
    exact ((eq_force_unfold_l M hZF (names s hs).1 ht).mp ((names s hs).2 p hp hz)).2.1 a b hab
  · obtain ⟨s, hs⟩ := hn
    intro a b hab r hr hrb
    obtain ⟨v, d, c, hv, hdc, hvc, he⟩ :=
      ((eq_force_unfold_l M hZF (names s hs).1 ht).mp ((names s hs).2 p hp hz)).2.2 a b hab r hr hrb
    exact ⟨v, d, c, hv, (entry_union_l M hU d c).mpr ⟨s, hs, hdc⟩, hvc, he⟩

theorem norm_name_unique_l (hZF : M.Models ZF) {t q r}
    (hq : Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t q)
    (hr : Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t r) : q = r := by
  obtain ⟨α, S, hS, hq⟩ := hq
  obtain ⟨β, T, hT, hr⟩ := hr
  obtain ⟨_, he⟩ := ZF.v_min_unique_l _ hZF hS hT
  subst T
  exact hq.eq hZF.1 hr

/-- 全局被迫相等的输入名称具有完全相同的规范构造关系。 -/
theorem norm_name_class_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {s t}
    (hs : Name_d M B s) (ht : Name_d M B t) (hst : All_eq_d M B R z s t) (q) :
    Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z s q ↔
      Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t q := by
  have hc x : norm_pred_s.denote (norm_env_l M B R z s) x ↔ norm_pred_s.denote (norm_env_l M B R z t) x := by
    rw [norm_pred_sat_l M hZF.1, norm_pred_sat_l M hZF.1]
    change (Name_d M B x ∧ All_eq_d M B R z x s) ↔ (Name_d M B x ∧ All_eq_d M B R z x t)
    refine and_congr_right fun hx => ⟨?_, ?_⟩
    · exact fun h p hp hz => eq_force_trans_l O hZF hx hs ht (h p hp hz) (hst p hp hz)
    · exact fun h p hp hz => eq_force_trans_l O hZF hx ht hs (h p hp hz) (eq_force_symm_l hZF hs ht (hst p hp hz))
  exact exists_congr fun α => exists_congr fun S => and_congr_left fun _ => v_min_congr_l _ hc α S

/-- 一次给出规范名称、规范幂等证书和与输入的全局等号；只需原 ZF。 -/
theorem norm_name_exists_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {t} (ht : Name_d M B t) :
    ∃ q, Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t q ∧
      Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z q q ∧
      Name_d M B q ∧ All_eq_d M B R z q t := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨α, S, hS⟩ := ZF.v_min_exists_l I hZF norm_pred_s (norm_env_l M B R z t)
    ⟨t, (norm_pred_sat_l M hZF.1 _ t).mpr ⟨ht, fun p hp _ => eq_force_refl_l O hZF hp ht⟩⟩
  obtain ⟨q, hq⟩ := KP.exists_union (ZF.modelsKP hZF) S
  have hn : Norm_name_d M I B R z t q := ⟨α, S, hS, hq⟩
  obtain ⟨hqN, he⟩ := norm_name_l hZF ht hn
  exact ⟨q, hn, (norm_name_class_l O hZF hqN ht he q).mpr hn, hqN, he⟩

theorem norm_name_congr_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {s t q r}
    (hs : Name_d M B s) (ht : Name_d M B t) (hst : All_eq_d M B R z s t)
    (hq : Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z s q)
    (hr : Norm_name_d M (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) B R z t r) : q = r :=
  norm_name_unique_l hZF ((norm_name_class_l O hZF hs ht hst q).mp hq) hr

end YesMetaZFC.Model.Forcing.Internal
