import YesMetaZFC.Model.SetTheory.ProjectElementary
import YesMetaZFC.Model.SetTheory.ProjectBounded

/-! # 初等嵌入作用于原 Project 公式

直接复用多排序结构嵌入及完整初等性。实际参数逐点映射，原公式不作
关系替换；这使原内部力迫公式也能沿同一个嵌入搬运。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}

/-- 原纯语言的逐公式初等性；内部初等图和原生初等嵌入均实际实现此关系。 -/
def Pe_d (j : M.Domain → N.Domain) : Prop := ∀ {n} (φ : Formula 1 n), φ.FreeClosed →
  ∀ ρ : Env M n, Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l j ρ) φ

theorem Pe_d.injective_l {j : M.Domain → N.Domain} (hM : Extensional M) (hN : Extensional N)
    (hj : Pe_d j) : Function.Injective j := by
  intro x y eq
  let ρ : Env M 2 := ⟨Fin.cases y (fun _ => x), fun _ => x⟩
  exact (Formula.satisfies_extensionalEq_iff_eq hM ρ (.bound 1) .newest).mp
    ((hj (Formula.extensionalEq (.bound 1) .newest) (by simp -implicitDefEqProofs) ρ).mpr
      ((Formula.satisfies_extensionalEq_iff_eq hN (image_env_l j ρ) (.bound 1) .newest).mpr eq))

namespace Definitional.Project.FirstOrderSemantics
open Logic.FirstOrder

theorem embedding_formula_l (j : Str_emb (model_l M) (model_l N)) (hj : j.Elementary_m)
    (hM : Extensional M) (hN : Extensional N) {n} (φ : Project.Formula 1 n)
    (hc : φ.FreeClosed) (ρ : SetTheory.Env M n) :
    Project.Formula.satisfies ρ φ ↔ Project.Formula.satisfies
      ⟨fun i => j.map .set (ρ.bound i), fun i => j.map .set (ρ.free i)⟩ φ := by
  have source := formula_correct (ℳ := model_l M) hM φ hc (native_env_l (ℳ := model_l M) ρ) ρ.free
  have target := formula_correct (ℳ := model_l N) hN φ hc ((native_env_l (ℳ := model_l M) ρ).map j.map)
    (fun i => j.map .set (ρ.free i))
  rw [project_native_l (ℳ := model_l M) ρ] at source
  have env : projectEnv ((native_env_l (ℳ := model_l M) ρ).map j.map) (fun i => j.map .set (ρ.free i)) =
      (⟨fun i => j.map .set (ρ.bound i), fun i => j.map .set (ρ.free i)⟩ : SetTheory.Env N n) := by
    exact congrArg (fun b => (⟨b, fun i => j.map .set (ρ.free i)⟩ : SetTheory.Env N n))
      (funext (fun i => congrArg (j.map .set) (native_bound_l (ℳ := model_l M) ρ.bound i)))
  rw [env] at target
  exact source.symm.trans ((hj (fo_formula φ hc) (native_env_l (ℳ := model_l M) ρ)).trans target)

end Definitional.Project.FirstOrderSemantics
end YesMetaZFC.SetTheory
