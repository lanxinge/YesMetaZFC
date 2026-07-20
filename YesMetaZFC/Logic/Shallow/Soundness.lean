import YesMetaZFC.Logic.Shallow.Bridge

/-!
# 浅嵌入桥接 soundness 定理

本文件只抽出桥接结果的通用消费定理。搜索器或 tactic 后续拿到
`BridgeResult` 后，应使用这些定理进入深嵌入语义核。
-/

namespace YesMetaZFC
namespace Logic
namespace Shallow
namespace FirstOrder

universe u v w x

open _root_.YesMetaZFC.Logic.FirstOrder

theorem term_value_eq_eval {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {sort : σ.SortSymbol}
    (view : TermView M sort) :
    ∀ env : Env M, view.value env = Term.eval env view.deep :=
  view.sound

theorem formula_prop_iff_satisfies {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (view : FormulaView M) :
    ∀ env : Env M, view.prop env ↔ Formula.satisfies env view.deep :=
  view.sound

theorem bridge_result_sound {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (result : BridgeResult M) :
    ∀ env : Env M, result.prop env ↔ Formula.satisfies env result.deep :=
  BridgeResult.sound result

/-- 若浅层命题在所有环境中成立，则桥接出的深层公式在所有环境中满足。 -/
theorem satisfies_of_shallow_valid {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (result : BridgeResult M)
    (hValid : ∀ env : Env M, result.prop env) :
    ∀ env : Env M, Formula.satisfies env result.deep := by
  intro env
  exact (result.sound env).mp (hValid env)

/-- 若深层公式在所有环境中满足，则可回到浅层命题。 -/
theorem shallow_valid_of_satisfies {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (result : BridgeResult M)
    (hValid : ∀ env : Env M, Formula.satisfies env result.deep) :
    ∀ env : Env M, result.prop env := by
  intro env
  exact (result.sound env).mpr (hValid env)

end FirstOrder
end Shallow
end Logic
end YesMetaZFC
