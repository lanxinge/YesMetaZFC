import YesMetaZFC.Model.Boolean.Semantics

/-! # 布尔公式的变量操作

重命名归约为已有标准代入；实例化、自由量化和闭句提升复用原环境等式。
本模块不要求结构满足等词证书或任何对象理论。
-/

namespace YesMetaZFC.Model.Boolean.BV_str
open Logic Logic.FirstOrder
universe u v w x y
variable {σ : Signature.{u, v, w}} {B : Type y}
  (𝔹 : CB_alg B) (ℳ : BV_str.{u, v, w, x, y} σ B)

theorem value_rename {b f b' f'} (ξ : Renaming σ b f b' f') (φ : Formula σ b f)
    (ρ : ℳ.Env 𝔹.toBA_alg b' f') :
    value 𝔹 ℳ (φ.rename ξ) ρ = value 𝔹 ℳ φ (ρ.pullbackRenaming ξ) := by
  cases ξ with
  | id => rfl
  | map α β =>
      change value 𝔹 ℳ (φ.renameMapped α β) ρ = _
      rw [Formula.renameMapped_eq_substituteMapped]
      exact value_substitute 𝔹 ℳ (.map (fun i => .bvar (α i)) (fun i => .fvar (β i))) φ ρ

theorem value_sentence {f} (φ : Sentence σ) (ρ : ℳ.Env 𝔹.toBA_alg [] f) :
    value 𝔹 ℳ φ.fromSentence ρ = value 𝔹 ℳ φ FirstOrder.Env.empty := by
  rw [Formula.fromSentence, value_rename, FirstOrder.Env.pullbackRenaming_emptyFree]

theorem value_weaken {b f s} (φ : Formula σ b f) (ρ : ℳ.Env 𝔹.toBA_alg b f) (a : ℳ.Carrier s) :
    value 𝔹 ℳ (φ.weakenFree s) (ρ.pushFree a) = value 𝔹 ℳ φ ρ := by
  rw [Formula.weakenFree, value_rename]
  apply congrArg (value 𝔹 ℳ φ)
  apply FirstOrder.Env.ext <;> intro s i <;> rfl

theorem value_instantiate {b f s} (φ : Formula σ (s :: b) f) (t : Term σ b f s)
    (ρ : ℳ.Env 𝔹.toBA_alg b f) :
    value 𝔹 ℳ (φ.instantiateTop t) ρ = value 𝔹 ℳ φ (ρ.pushBound (t.eval ρ)) := by
  rw [Formula.instantiateTop, value_substitute, FirstOrder.Env.pullback_instantiateTop]

theorem value_abstract {b f s} (φ : Formula σ b (s :: f))
    (ρ : ℳ.Env 𝔹.toBA_alg b f) (a : ℳ.Carrier s) :
    value 𝔹 ℳ φ.abstractFreeTop (ρ.pushBound a) = value 𝔹 ℳ φ (ρ.pushFree a) := by
  rw [Formula.abstractFreeTop, value_substitute, FirstOrder.Env.pullback_abstractFreeTop]

theorem value_forall {b f} (s : σ.SortSymbol) (φ : Formula σ b (s :: f)) (ρ : ℳ.Env 𝔹.toBA_alg b f) :
    value 𝔹 ℳ (φ.forallFreeTop s) ρ = 𝔹.iInf (fun a => value 𝔹 ℳ φ (ρ.pushFree a)) :=
  congrArg 𝔹.iInf (funext (fun a => value_abstract 𝔹 ℳ φ ρ a))

theorem value_exists {b f} (s : σ.SortSymbol) (φ : Formula σ b (s :: f)) (ρ : ℳ.Env 𝔹.toBA_alg b f) :
    value 𝔹 ℳ (φ.existsFreeTop s) ρ = 𝔹.iSup (fun a => value 𝔹 ℳ φ (ρ.pushFree a)) :=
  congrArg 𝔹.iSup (funext (fun a => value_abstract 𝔹 ℳ φ ρ a))

end YesMetaZFC.Model.Boolean.BV_str
