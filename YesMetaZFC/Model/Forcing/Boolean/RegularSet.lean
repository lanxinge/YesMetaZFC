import YesMetaZFC.Model.Forcing.Boolean.NameValue

/-! # 地模型内部的正则开集合与任意并的正则化

载体由模型自己的幂集分离。正则化和上确界也在模型内构造，
不把宿主谓词的全部集合误认为地模型的布尔完备化。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}}

def Ropen_d (B R z V : M.Domain) : Prop :=
  (∀ p, M.mem p V → M.mem p B ∧ p ≠ z) ∧ Regular_d M B R z (fun p => M.mem p V)

def ropen_m {d} (B R z V : Term d) : Formula 1 d := set[d] ⟪
  (∀ p ∈ ⌜V⌝ₛ, p ∈ ⌜B⌝ₛ ∧ p ≠ ⌜z⌝ₛ) ∧
  (∀ p ∈ ⌜V⌝ₛ, ∀ q ∈ ⌜B⌝ₛ, ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,q,p) → q ∈ ⌜V⌝ₛ) ∧
  (∀ p ∈ ⌜B⌝ₛ, p ≠ ⌜z⌝ₛ →
    (∀ q ∈ ⌜B⌝ₛ, ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,q,p) →
      (∃ r ∈ ⌜B⌝ₛ, ⌜below_m⌝ₚ(⌜B⌝ₛ,⌜R⌝ₛ,⌜z⌝ₛ,r,q) ∧ r ∈ ⌜V⌝ₛ)) → p ∈ ⌜V⌝ₛ)⟫
derive_free_closed ropen_m

variable (hZF : M.Models ZF)
include hZF

theorem ropen_sat_l {d} (ρ : Env M d) (B R z V : Term d) :
    Formula.satisfies ρ (ropen_m B R z V) ↔ Ropen_d (B.eval ρ) (R.eval ρ) (z.eval ρ) (V.eval ρ) := by
  simp only [ropen_m,Formula.satisfies_conj_iff,Formula.satisfies_forallMem_iff,
    Formula.satisfies_mem_iff,Formula.extensionalNe,Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1,Formula.satisfies_imp_iff,
    Formula.satisfies_existsMem_iff,below_sat_l M hZF.1,Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨bound,lower,closed⟩
    exact ⟨bound,⟨fun p q _ hq hp => lower p hp q hq.1 hq,
      fun p hp hz dense => closed p hp hz (fun q _ hq => (dense q hq).imp fun r hr => ⟨hr.1.1,hr⟩)⟩⟩
  · rintro ⟨bound,lower,closed⟩
    exact ⟨bound,(fun p hp q _ hq => lower p q (bound p hp).1 hq hp),
      fun p hp hz dense => closed p hp hz (fun q hq => (dense q hq.1 hq).imp fun r hr => hr.2)⟩

theorem ropen_family_l (B R z : M.Domain) : ∃ K, ∀ V, M.mem V K ↔ Ropen_d B R z V := by
  obtain ⟨P,power⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 3 := ⟨fun i => [B,R,z].get i,fun _ => B⟩
  let φ : UnarySchema 3 := { body := ropen_m (.bound 1) (.bound 2) (.bound 3) .newest }
  obtain ⟨K,members⟩ := ZF.separation_exists_d hZF φ ρ P
  refine ⟨K,fun V => (members V).trans ?_⟩
  have sat : φ.denote ρ V ↔ Ropen_d B R z V := ropen_sat_l hZF ..
  exact ⟨fun h => sat.mp h.2,fun h => ⟨(power V).mpr (fun p hp => (h.1 p hp).1),sat.mpr h⟩⟩

theorem ropen_inter_l {B R z A C : M.Domain} (left : Ropen_d B R z A) (right : Ropen_d B R z C) :
    ∃ V, Ropen_d B R z V ∧ ∀ p, M.mem p V ↔ M.mem p A ∧ M.mem p C := by
  obtain ⟨V,meet⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) A C
  refine ⟨V,⟨fun p hp => left.1 p ((meet p).mp hp).1,?_,?_⟩,meet⟩
  · intro p q hp hq h
    exact (meet q).mpr ⟨left.2.1 p q hp hq ((meet p).mp h).1,right.2.1 p q hp hq ((meet p).mp h).2⟩
  · intro p hp hz dense
    exact (meet p).mpr ((regular_conj_l left.2 right.2).2 p hp hz
      (fun q hq => (dense q hq).imp fun r hr => ⟨hr.1,(meet r).mp hr.2⟩))

omit hZF in
theorem Ropen_d.empty_l {B R z V : M.Domain} (O : Cond_order_d M B R z)
    (empty : ∀ p, ¬ M.mem p V) : Ropen_d B R z V := by
  refine ⟨fun p hp => (empty p hp).elim,⟨fun p _ _ _ hp => (empty p hp).elim,?_⟩⟩
  intro p hp hz dense
  obtain ⟨q,_,hq⟩ := dense p (below_refl_l O hp hz)
  exact (empty q hq).elim

theorem ropen_closure_l {B R z : M.Domain} (O : Cond_order_d M B R z) (U : M.Domain) :
    ∃ V, Ropen_d B R z V ∧ ∀ p, M.mem p V ↔ M.mem p B ∧ p ≠ z ∧ Dense_d M B R z (fun q => M.mem q U) p := by
  let ρ : Env M 4 := ⟨fun i => [B,R,z,U].get i,fun _ => B⟩
  let φ : UnarySchema 4 := { body := set[5] ⟪⌜(.newest : Term 5)⌝ₛ ≠ ⌜(.bound 3 : Term 5)⌝ₛ ∧
    (∀ q, ⌜below_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ,⌜(.bound 2 : Term 5)⌝ₛ,⌜(.bound 3 : Term 5)⌝ₛ,q,⌜(.newest : Term 5)⌝ₛ) →
      ∃ r, ⌜below_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ,⌜(.bound 2 : Term 5)⌝ₛ,⌜(.bound 3 : Term 5)⌝ₛ,r,q) ∧ r ∈ ⌜(.bound 4 : Term 5)⌝ₛ)⟫ }
  obtain ⟨V,values⟩ := ZF.separation_exists_d hZF φ ρ B
  have read p : M.mem p V ↔ M.mem p B ∧ p ≠ z ∧ Dense_d M B R z (fun q => M.mem q U) p := by
    apply (values p).trans (and_congr_right fun _ => ?_)
    simp only [φ,Formula.extensionalNe,Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_exists_iff,below_sat_l M hZF.1,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
    rfl
  refine ⟨V,⟨fun p hp => ⟨((read p).mp hp).1,((read p).mp hp).2.1⟩,?_,?_⟩,read⟩
  · intro p q hp hq h
    exact (read q).mpr ⟨hq.1,hq.2.1,dense_lower_l O _ p q hp hq ((read p).mp h).2.2⟩
  · intro p hp hz dense
    exact (read p).mpr ⟨hp,hz,dense_idem_l O (fun q hq => (dense q hq).imp
      fun r hr => ⟨hr.1,((read r).mp hr.2).2.2⟩)⟩

theorem ropen_sup_l {B R z K S : M.Domain} (O : Cond_order_d M B R z)
    (family : ∀ V, M.mem V K ↔ Ropen_d B R z V) (sub : M.MemberSubset S K) :
    ∃ V, M.mem V K ∧ (∀ U, M.mem U S → M.MemberSubset U V) ∧
      ∀ W, M.mem W K → (∀ U, M.mem U S → M.MemberSubset U W) → M.MemberSubset V W := by
  obtain ⟨D,union⟩ := KP.exists_union (ZF.modelsKP hZF) S
  have lower : Lower_d M B R z (fun p => M.mem p D) := by
    intro p q hp hq h
    obtain ⟨U,hU,pU⟩ := (union p).mp h
    exact (union q).mpr ⟨U,hU,((family U).mp (sub U hU)).2.1 p q hp hq pU⟩
  obtain ⟨V,regular,values⟩ := ropen_closure_l hZF O D
  refine ⟨V,(family V).mpr regular,?_,?_⟩
  · intro U hU p hp
    have bound := ((family U).mp (sub U hU)).1 p hp
    exact (values p).mpr ⟨bound.1,bound.2,dense_intro_l O lower bound.1 ((union p).mpr ⟨U,hU,hp⟩)⟩
  · intro W hW bound p hp
    obtain ⟨hp,hz,dense⟩ := (values p).mp hp
    apply ((family W).mp hW).2.2 p hp hz
    intro q hq
    obtain ⟨r,hr,hD⟩ := dense q hq
    obtain ⟨U,hU,hu⟩ := (union r).mp hD
    exact ⟨r,hr,bound U hU r hu⟩

end YesMetaZFC.Model.Forcing.Internal
