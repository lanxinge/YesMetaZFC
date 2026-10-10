import YesMetaZFC.SetTheory.InnerModel.Jensen.Hierarchy
import YesMetaZFC.SetTheory.InnerModel.Separation.Definable

/-! # 当前 J 层的定义集属于下一层

这是后续把层内可定义的短历史放入下一层所用的 Def(Jₐ)⊆Jₐ₊₁。
前提只涉及背景 KPi 及已构造的 J 层，不要求 Jₐ 可容许。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

theorem jh_definable_l (hM : M.Models KPi) {a s U C : M.Domain} (ha : M.IsOrdinal a)
    (hs : M.SuccessorOf s a) (hU : Jh_value_d a U) (hC : Jh_value_d s C)
    (hn : Nonempty {x : M.Domain // M.mem x U}) {n} (φ : UnarySchema n) (ρ : Env (rt_model_l U hn) n) :
    ∃ Y, M.mem Y C ∧ ∀ x, M.mem x Y ↔ ∃ hx : M.mem x U, φ.denote ρ ⟨x, hx⟩ := by
  have hc := jh_step_spec_l hM (jh_successor_l hM ha hs hU hC)
  exact rt_definable_l (KPi.models_iff_l.mp hM).1 hc.1 hc.2.2 hc.2.1 (jh_value_transitive_l hM hU) hn φ ρ

end YesMetaZFC.SetTheory.InnerModel
