import YesMetaZFC.Logic.FirstOrder.Derivation.Quantifier
import YesMetaZFC.Logic.FirstOrder.Derivation.Substitution.Basic

/-!
# 推导的类型化统一替换

统一 free 替换已经下沉为标准 Hilbert 推导规则。本层只证明它与局部上下文的规范
蕴含编译交换，因此不再逐公理复制替换封闭性证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w

namespace Context

/-- free 替换与局部上下文的蕴含编译交换。 -/
theorem substituteFree_discharge {σ : Signature.{u, v, w}}
    {sourceFree targetFree : SortContext σ}
    (substitution :
      VariableSubstitution σ sourceFree [] targetFree)
    (Γ : Context σ sourceFree)
    (formula : OpenFormula σ sourceFree) :
    Formula.substituteFree substitution (discharge Γ formula) =
      discharge (Γ.substituteFree substitution)
        (formula.substituteFree substitution) := by
  induction Γ generalizing formula with
  | nil =>
      rfl
  | cons assumption rest ih =>
      simpa [discharge, Context.substituteFree,
        Formula.substituteFree, Substitution.free_map, Formula.substitute,
        Formula.substituteMapped] using
        ih (Formula.imp assumption formula)

end Context

namespace Derives

/-- 对结论和全部局部假设同步执行一次类型化统一 free 替换。 -/
theorem free_substitution {σ : Signature.{u, v, w}}
    {T : Theory σ} {sourceFree targetFree : SortContext σ}
    {Γ : Context σ sourceFree} {formula : OpenFormula σ sourceFree}
    (substitution :
      VariableSubstitution σ sourceFree [] targetFree)
    (hFormula : Derives T Γ formula) :
    Derives T (Γ.substituteFree substitution)
      (formula.substituteFree substitution) := by
  change Provable T
    (Context.discharge (Γ.substituteFree substitution)
      (formula.substituteFree substitution))
  rw [← Context.substituteFree_discharge]
  exact Provable.free_substitution substitution hFormula

/-- 对结论和全部局部假设同步执行保排序 free 重命名。 -/
theorem free_renaming {σ : Signature.{u, v, w}}
    {T : Theory σ} {sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree)
    {Γ : Context σ sourceFree} {formula : OpenFormula σ sourceFree}
    (hFormula : Derives T Γ formula) :
    Derives T (Γ.map (Formula.renameFree ρ))
      (formula.renameFree ρ) := by
  let τ : VariableSubstitution σ sourceFree [] targetFree :=
    VariableSubstitution.of_renaming (bound := []) ρ
  have hContext : Context.substituteFree τ Γ =
      Γ.map (Formula.renameFree ρ) := by
    clear hFormula
    induction Γ with
    | nil => rfl
    | cons assumption rest ih =>
        change (assumption.substituteFree τ :: Context.substituteFree τ rest) =
          (assumption.renameFree ρ :: rest.map (Formula.renameFree ρ))
        exact congr
          (congrArg List.cons (Formula.substituteFree_of_renaming ρ assumption)) ih
  rw [← hContext]
  simpa [τ] using free_substitution τ hFormula

/-- 已 weakening 到 fresh 上下文的全称公式，以 newest 变量打开为原公式体。 -/
theorem forall_elim_newest_weakened {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ (sort :: free)}
    {body : OpenFormula σ (sort :: free)}
    (hUniversal :
      Derives T Γ ((body.forallFreeTop sort).weakenFree sort)) :
    Derives T Γ body := by
  rw [Formula.forallFreeTop, Formula.weakenFree_forallE] at hUniversal
  have hOpened :=
    forall_elim (FreshVariable.newest sort) hUniversal
  exact (Formula.instantiateTop_weakenFree_abstractFreeTop sort body) ▸ hOpened

/-- 全称公式进入规范 fresh 上下文后，以 newest 变量打开为原公式体。 -/
theorem forall_elim_newest {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ free} {body : OpenFormula σ (sort :: free)}
    (hUniversal : Derives T Γ (body.forallFreeTop sort)) :
    Derives T (FreshVariable.extendContext sort Γ) body := by
  have hWeakened : Derives T (FreshVariable.extendContext sort Γ)
      ((body.forallFreeTop sort).weakenFree sort) := by
    exact free_renaming (T := T) (VariableRenaming.weaken sort) hUniversal
  exact forall_elim_newest_weakened hWeakened

/-- fresh 上下文中的公式可用 newest 变量引入对应存在式。 -/
theorem exists_intro_newest {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {sort : σ.SortSymbol}
    {Γ : Context σ (sort :: free)}
    {body : OpenFormula σ (sort :: free)}
    (hBody : Derives T Γ body) :
    Derives T Γ
      ((body.existsFreeTop sort).weakenFree sort) := by
  have hInstance : Derives T Γ
      (((body.abstractFreeTop).weakenFree sort).instantiateTop
        (FreshVariable.newest sort)) := by
    simpa [FreshVariable.newest] using hBody
  have hExistential :=
    exists_intro (body := (body.abstractFreeTop).weakenFree sort)
      (FreshVariable.newest sort) hInstance
  simpa [Formula.existsFreeTop] using hExistential

end Derives

namespace Provable

/-- 推导结论沿保排序 free 重命名搬运。 -/
theorem free_renaming {σ : Signature.{u, v, w}}
    {T : Theory σ} {sourceFree targetFree : SortContext σ}
    (ρ : VariableRenaming sourceFree targetFree)
    {formula : OpenFormula σ sourceFree}
    (hFormula : Provable T formula) :
    Provable T (formula.renameFree ρ) := by
  simpa using
    (free_substitution
      (VariableSubstitution.of_renaming (bound := []) ρ) hFormula)

/--
逐个回放目标理论公理即可搬运整棵标准 Hilbert 推导树。归纳始终停留在 `Prop`，
因此不需要从 `Nonempty` 中选择证明对象。
-/
theorem theory_cut {σ : Signature.{u, v, w}}
    {source target : Theory σ} {free : SortContext σ}
    {formula : OpenFormula σ free}
    (replay : ∀ {sentence : Sentence σ},
      target sentence → Provable source sentence)
    (hFormula : Provable target formula) :
    Provable source formula := by
  rcases hFormula with ⟨proof⟩
  induction proof with
  | logical_axiom hAxiom =>
      exact logical_axiom hAxiom
  | @theory_axiom free sentence hTheory =>
      cases free with
      | nil =>
          exact replay hTheory
      | cons head tail =>
          simpa [Formula.fromSentence, Formula.renameFree,
            Renaming.emptyFree] using
            (free_renaming
              (VariableRenaming.empty :
                VariableRenaming [] (head :: tail))
              (replay hTheory))
  | modus_ponens _ _ ihAntecedent ihImplication =>
      exact modus_ponens ihAntecedent ihImplication
  | forall_generalization _ ihFormula =>
      exact forall_generalization ihFormula
  | free_strengthening _ ihFormula =>
      exact free_strengthening ihFormula
  | free_substitution substitution _ ihFormula =>
      exact free_substitution substitution ihFormula

end Provable

namespace Derives

/-- 理论公理逐项可回放时，任意有限上下文推导可整体切回源理论。 -/
theorem theory_cut {σ : Signature.{u, v, w}}
    {source target : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (replay : ∀ {sentence : Sentence σ},
      target sentence → Derives source [] sentence)
    (hFormula : Derives target Γ formula) :
    Derives source Γ formula :=
  Provable.theory_cut replay hFormula

end Derives
end FirstOrder
end Logic
end YesMetaZFC
