import YesMetaZFC.Model.Forcing.Internal.Forcing.Congruence

/-! # 唯一见证的原公式与力迫消去

唯一性以真正的一阶公式给出。实例化两个名称并连续消去蕴涵，取得同一条件
下的原子等号；有限参数以外的默认自由赋值不需要名称假设。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

def unique_m {n} (φ : UnarySchema n) : Formula 1 n :=
  .forallE (.forallE (.imp (pred_m φ (fun i => .bound ⟨i.val+2, by omega⟩) (.bound 1))
    (.imp (pred_m φ (fun i => .bound ⟨i.val+2, by omega⟩) .newest) (Formula.extensionalEq (.bound 1) .newest))))
@[simp] theorem unique_closed_l {n} (φ : UnarySchema n) : (unique_m φ).FreeClosed := by
  simp -implicitDefEqProofs [unique_m, Definitional.Formula.FreeClosed]

theorem unique_sat_l (hE : Extensional M) {n} (φ : UnarySchema n) (ρ : Env M n) :
    Formula.satisfies ρ (unique_m φ) ↔ ∀ s t, φ.denote ρ s → φ.denote ρ t → s = t := by
  have he s t : (⟨fun i : Fin n => (Term.bound ⟨i.val+2, by omega⟩ : Term (n+2)).eval ((ρ.push s).push t),
      ((ρ.push s).push t).free⟩ : Env M n) = ρ := by cases ρ; rfl
  simp only [unique_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, pred_sat_l M, he,
    Formula.satisfies_extensionalEq_iff_eq hE, Definitional.Term.eval_newest]
  rfl

theorem forced_unique_l (O : Cond_order_d M B R z) (hZF : M.Models ZF) {n p s t}
    (φ : UnarySchema n) (ρ : Env M n) (hρ : ∀ i, Name_d M B (ρ.bound i))
    (hs : Name_d M B s) (ht : Name_d M B t) (hp : M.mem p B) (hz : p ≠ z)
    (hU : Forces_d M B R z (unique_m φ) ρ p)
    (hsφ : Forces_d M B R z φ.body (ρ.push s) p) (htφ : Forces_d M B R z φ.body (ρ.push t) p) :
    Eq_force_d M B R z p s t := by
  let η : Env M n := ⟨ρ.bound, fun _ => s⟩
  let ξ := (η.push s).push t
  let e : Fin n → Term (n+2) := fun i => .bound ⟨i.val+2, by omega⟩
  let a := pred_m φ e (.bound 1)
  let b := pred_m φ e .newest
  let c : Formula 1 (n+2) := Formula.extensionalEq (.bound 1) .newest
  have he : (⟨fun i => (e i).eval ξ, ξ.free⟩ : Env M n) = η := by cases ρ; rfl
  have hn : ∀ v : Term (n+2), Name_d M B (v.eval ξ) := by
    intro v
    cases v with
    | free _ => exact hs
    | bound i => exact Fin.cases ht (Fin.cases hs hρ) i
  have hU := (forces_env_l hZF.1 _ (unique_closed_l φ) ρ η (fun _ => rfl) p).mp hU
  have hU := (forces_all_l hZF.1 _ η p).mp hU s hs
  have hU := (forces_all_l hZF.1 _ (η.push s) p).mp hU t ht
  have ha : Forces_d M B R z a ξ p := by
    rw [forces_pred_l hZF.1, he]
    exact (forces_env_l hZF.1 φ.body φ.freeClosed (ρ.push s) (η.push s) (fun _ => rfl) p).mp hsφ
  have hb : Forces_d M B R z b ξ p := by
    rw [forces_pred_l hZF.1, he]
    exact (forces_env_l hZF.1 φ.body φ.freeClosed (ρ.push t) (η.push t) (fun _ => rfl) p).mp htφ
  have hImp := forces_mp_l hZF.1 (forces_regular_l O hZF a ξ hn).1
    (forces_regular_l O hZF (.imp b c) ξ hn) hp hz hU ha
  have hEq := forces_mp_l hZF.1 (forces_regular_l O hZF b ξ hn).1 (forces_regular_l O hZF c ξ hn) hp hz hImp hb
  exact (code_eq_l M hZF.1 B R z (.bound 1) .newest ξ p).mp hEq

end YesMetaZFC.Model.Forcing.Internal
