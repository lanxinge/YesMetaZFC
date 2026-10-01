import YesMetaZFC.Model.Forcing.Internal.Check.Relation
import YesMetaZFC.Model.Forcing.Internal.Reflection.Criterion
import YesMetaZFC.SetTheory.Card.Omega

/-! # 名称在旧集合中的覆盖证书

覆盖正文表达 t∩u⊆s。因此一张可数名称可同时处理其在任意旧集合中的部分，
无需先假定整张名称落在该旧集合内。旧可数覆盖的见证均为真实集合与规范名称。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u

def cover_body_m : Formula 1 3 := .forallE (.imp (.mem .newest (.bound 3))
  (.imp (.mem .newest (.bound 2)) (.mem .newest (.bound 1))))
@[simp] theorem cover_body_closed_l : cover_body_m.FreeClosed := by
  simp [cover_body_m, Definitional.Formula.FreeClosed]

def cover_env_l {M : SetTheory.Structure.{u}} (t u s : M.Domain) : Env M 3 :=
  ((⟨fun _ => t, fun _ => t⟩ : Env M 1).push u).push s

def cover_force_m {n} (B R z p t u s : Term n) : Formula 1 n :=
  force_at_m cover_body_m (Fin.cases s (Fin.cases u (fun _ => t))) B R z p
@[simp] theorem cover_force_closed_l {n} (B R z p t u s : Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hp : p.freeSupport = []) (ht : t.freeSupport = []) (hu : u.freeSupport = []) (hs : s.freeSupport = []) :
    (cover_force_m B R z p t u s).FreeClosed :=
  force_at_closed_l _ _ _ _ _ _ cover_body_closed_l (Fin.cases hs (Fin.cases hu (fun _ => ht))) hB hR hz hp

theorem cover_force_sat_l {M : SetTheory.Structure.{u}} (hE : Extensional M) {n} (ρ : Env M n)
    (B R z p t u s : Term n) : Formula.satisfies ρ (cover_force_m B R z p t u s) ↔
      Forces_d M (B.eval ρ) (R.eval ρ) (z.eval ρ) cover_body_m (cover_env_l (t.eval ρ) (u.eval ρ) (s.eval ρ)) (p.eval ρ) :=
  (force_at_sat_l _ _ _ _ _ _ _).trans (forces_env_l hE _ cover_body_closed_l _ _
    (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) _)

def Old_cover_d {M : SetTheory.Structure.{u}} (I : kpair_convention_l.Interpretation M)
    (ω B R z b X t u p : M.Domain) : Prop := ∃ A s,
  M.MemberSubset A X ∧ M.CardinalLessOrEqual I A ω ∧ Check_d M b A s ∧
    Forces_d M B R z cover_body_m (cover_env_l t u s) p

def old_cover_m {n} (ω B R z b X t u p : Term n) : Formula 1 n :=
  .existsE (.existsE (.conj (Formula.subset (.bound 1) X.weaken.weaken)
    (.conj (Formula.cardinalLessOrEqual kpair_convention_l (.bound 1) ω.weaken.weaken)
    (.conj (check_m b.weaken.weaken (.bound 1) .newest)
      (cover_force_m B.weaken.weaken R.weaken.weaken z.weaken.weaken p.weaken.weaken t.weaken.weaken u.weaken.weaken .newest)))))
derive_free_closed old_cover_m

theorem old_cover_sat_l {M : SetTheory.Structure.{u}} (I : kpair_convention_l.Interpretation M)
    (hE : Extensional M) {n} (ρ : Env M n) (ω B R z b X t u p : Term n) :
    Formula.satisfies ρ (old_cover_m ω B R z b X t u p) ↔
      Old_cover_d I (ω.eval ρ) (B.eval ρ) (R.eval ρ) (z.eval ρ) (b.eval ρ) (X.eval ρ) (t.eval ρ) (u.eval ρ) (p.eval ρ) := by
  simp only [old_cover_m, Old_cover_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_cardinalLessOrEqual_iff I hE,
    check_sat_l M hE, cover_force_sat_l hE, Definitional.Term.eval_weaken]
  rfl

variable {M : SetTheory.Structure.{u}} {B R z : M.Domain} (O : Cond_order_d M B R z) (hZF : M.Models ZF)
include O hZF

theorem cover_value_l {U} (hU : Generic_d M B R z U) {p t u s} (hp : U p)
    (h : Forces_d M B R z cover_body_m (cover_env_l t u s) p)
    {T X A : (extension_l M hZF B R z U).Domain} (ht : Qval_d M B R z U t T)
    (hu : Qval_d M B R z U u X) (hs : Qval_d M B R z U s A) : ∀ x, x ∈ T → x ∈ X → x ∈ A := by
  have hv : Env_val_d hZF (cover_env_l t u s) (cover_env_l T X A) := by
    intro v
    cases v with
    | free _ => exact ht
    | bound i => exact Fin.cases hs (Fin.cases hu (fun _ => ht)) i
  have h' := (forcing_truth_l O hZF hU cover_body_m cover_body_closed_l _ _ hv).mp ⟨p, hp, h⟩
  simp only [cover_body_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff] at h'
  change ∀ x, x ∈ T → x ∈ X → x ∈ A at h'
  exact h'

/-- 正条件下两个规范旧名称的覆盖，直接反射为地模型中的包含关系。 -/
theorem check_cover_reflect_l {b X A t s p} (hb : M.mem b B) (ht : Check_d M b X t) (hs : Check_d M b A s)
    (hp : Below_d M B R z p b) (h : Forces_d M B R z cover_body_m (cover_env_l t t s) p) : M.MemberSubset X A := by
  have htn := check_name_l M (check_range_l M hZF) hb ht
  have hsn := check_name_l M (check_range_l M hZF) hb hs
  let ρ := cover_env_l t t s
  intro x hx
  obtain ⟨v, hv, hvn, _⟩ := zf_check_l M hZF hb x
  let η := ρ.push v
  have hη : ∀ a : Term 4, Name_d M B (a.eval η) := by
    intro a
    cases a with
    | free _ => exact htn
    | bound i => exact Fin.cases hvn (Fin.cases hsn (Fin.cases htn (fun _ => htn))) i
  have mp {φ ψ : Formula 1 4} (hφ : Forces_d M B R z (.imp φ ψ) η p) (hh : Forces_d M B R z φ η p) :
      Forces_d M B R z ψ η p := forces_mp_l hZF.1 (forces_regular_l O hZF φ η hη).1
        (forces_regular_l O hZF ψ η hη) hp.1 hp.2.1 hφ hh
  have hmem := check_mem_force_l O hZF hb hv ht hp.1 hp.2.2 hx
  have h₁ := (forces_all_l hZF.1 _ ρ p).mp h v hvn
  have h₂ := mp h₁ ((forces_mem_l hZF.1 .newest (.bound 3) η p).mpr hmem)
  have h₃ := mp h₂ ((forces_mem_l hZF.1 .newest (.bound 2) η p).mpr hmem)
  exact check_mem_reflect_l O hZF hb hv hs hp ((forces_mem_l hZF.1 .newest (.bound 1) η p).mp h₃)

end YesMetaZFC.Model.Forcing.Internal
