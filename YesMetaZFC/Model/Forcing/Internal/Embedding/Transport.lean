import YesMetaZFC.Model.SetTheory.ProjectEmbedding
import YesMetaZFC.Model.SetTheory.ProjectBounded
import YesMetaZFC.Model.Forcing.Internal.Extension.ZF
import YesMetaZFC.Model.Forcing.TwoStep.Basic

/-! # 初等嵌入保持内部名称与原力迫关系

名称、规范名称及力迫关系均使用已构造的原一阶公式。这里搬运同一公式，
不另设名称递归或力迫真值的操作参数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
open SetTheory.Definitional.Project.FirstOrderSemantics
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : Extensional M) (hN : Extensional N)
  (j : M.Domain → N.Domain) (hj : Pe_d j)
local notation "e" => j
include hM hN hj

theorem em_name_l {P t : M.Domain} : Name_d M P t ↔ Name_d N (e P) (e t) := by
  let ρ : Env M 2 := ⟨Fin.cases t (fun _ => P), fun _ => P⟩
  exact (name_sat_l M hM ρ (.bound 1) .newest).symm.trans
    ((hj (name_m (.bound 1) .newest) (by simp -implicitDefEqProofs) ρ).trans
      (name_sat_l N hN (image_env_l e ρ) (.bound 1) .newest))

theorem em_check_l {p a t : M.Domain} : Check_d M p a t ↔ Check_d N (e p) (e a) (e t) := by
  let ρ : Env M 3 := ⟨Fin.cases t (Fin.cases a (fun _ => p)), fun _ => p⟩
  exact (check_sat_l M hM ρ (.bound 2) (.bound 1) .newest).symm.trans
    ((hj (check_m (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ).trans (check_sat_l N hN (image_env_l e ρ) (.bound 2) (.bound 1) .newest))

theorem em_eq_force_l {P R z p s t : M.Domain} :
    Eq_force_d M P R z p s t ↔ Eq_force_d N (e P) (e R) (e z) (e p) (e s) (e t) := by
  let ρ : Env M 6 := ⟨fun i => [t,s,p,z,R,P].get i, fun _ => P⟩
  exact (eq_force_sat_l M hM ρ (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
    ((hj (eq_force_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ).trans
      (eq_force_sat_l N hN (image_env_l e ρ) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))

omit hM hN in
theorem em_forces_l {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (ρ : Env M n) (P R z p : M.Domain) :
    Forces_d M P R z φ ρ p ↔ Forces_d N (e P) (e R) (e z) φ (image_env_l e ρ) (e p) := by
  have tr := hj (force_code_m φ) (force_code_closed_l φ hc) (fenv_l ρ P R z p)
  have env : @image_env_l M N e (n + 4) (fenv_l ρ P R z p) =
      fenv_l (image_env_l e ρ) (e P) (e R) (e z) (e p) := by
    exact congrArg (fun b => (⟨b, fun i => e (ρ.free i)⟩ : Env N (n + 4)))
      (funext (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))))
  exact tr.trans (iff_of_eq (congrArg (fun η : Env N (n + 4) => Formula.satisfies η (force_code_m φ)) env))

theorem em_order_l {P R z : M.Domain} (O : Cond_order_d M P R z) : Cond_order_d N (e P) (e R) (e z) := by
  let ρ : Env M 3 := ⟨Fin.cases z (Fin.cases R (fun _ => P)), fun _ => P⟩
  exact (cond_order_sat_l hN (image_env_l e ρ) (.bound 2) (.bound 1) .newest).mp
    ((hj (cond_order_m (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ).mp ((cond_order_sat_l hM ρ (.bound 2) (.bound 1) .newest).mpr O))

end YesMetaZFC.Model.Forcing.Internal
