import YesMetaZFC.Model.Forcing.Internal.Atomic.Equivalence
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
