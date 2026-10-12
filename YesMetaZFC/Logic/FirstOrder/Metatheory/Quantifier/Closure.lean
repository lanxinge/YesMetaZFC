import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier

/-!
# 内在类型自由上下文的全称闭包

自由上下文已经完整记录公式可使用的自由变量及其排序，因此全称闭包只需从上下文
顶部逐层抽象。返回类型直接是 `Sentence`；旧实现中的变量编号、覆盖性、去重、
freshness 与 admissibility 证明义务全部由类型消去。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory

universe u v w

namespace Formula

/-- 按自由上下文的规范顺序关闭全部自由变量。 -/
def forall_close {σ : Signature.{u, v, w}}
    {free : SortContext σ} (body : OpenFormula σ free) : Sentence σ :=
  match free, body with
  | List.nil, body => body
  | List.cons sort _, body => forall_close (body.forallFreeTop sort)

@[simp]
theorem forall_close_nil {σ : Signature.{u, v, w}}
    (body : Sentence σ) :
    forall_close body = body :=
  rfl

@[simp]
theorem forall_close_cons {σ : Signature.{u, v, w}}
    {free : SortContext σ} (sort : σ.SortSymbol)
    (body : OpenFormula σ (sort :: free)) :
    forall_close body = forall_close (body.forallFreeTop sort) :=
  rfl

end Formula

namespace Derives

/-- 空局部上下文中的开放证明可沿自由上下文逐层全称化为闭句。 -/
theorem forall_close_of_derives {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {body : OpenFormula σ free}
    (hBody : Derives T ([] : Context σ free) body) :
    Derives T ([] : Context σ []) (Formula.forall_close body) := by
  induction free with
  | nil =>
      simpa [Formula.forall_close] using hBody
  | cons sort free ih =>
      simpa [Formula.forall_close] using
        ih (FirstOrder.Derives.forall_intro hBody)

/-- 纯逻辑中的开放定理闭包后，可嵌入任意理论、自由上下文与局部上下文。 -/
theorem forall_close_theorem {σ : Signature.{u, v, w}}
    {T : Theory σ} {sourceFree targetFree : SortContext σ}
    {Γ : Context σ targetFree}
    {body : OpenFormula σ sourceFree}
    (hBody : Derives (Theory.empty : Theory σ)
      ([] : Context σ sourceFree) body) :
    Derives T Γ
      (Formula.fromSentence (Formula.forall_close body)) := by
  have hClosed : Derives (Theory.empty : Theory σ)
      ([] : Context σ []) (Formula.forall_close body) :=
    forall_close_of_derives hBody
  have hEmbedded : Derives (Theory.empty : Theory σ)
      ([] : Context σ targetFree)
      (Formula.fromSentence (Formula.forall_close body)) := by
    cases targetFree with
    | nil =>
        simpa [Formula.fromSentence, Renaming.emptyFree] using hClosed
    | cons sort free =>
        simpa [Formula.fromSentence, Formula.renameFree,
          Renaming.emptyFree, Renaming.free] using
          (FirstOrder.Derives.free_renaming
            (VariableRenaming.empty :
              VariableRenaming [] (sort :: free))
            hClosed)
  exact FirstOrder.Derives.of_empty hEmbedded

/--
闭句形式的全称闭包可规范地重新打开为原开放公式。每一步都使用 free 上下文头部的
规范新变量，因此不需要变量编号、覆盖性或新鲜性旁证。
-/
theorem forall_close_open {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    (body : OpenFormula σ free)
    (hClosed : Derives T ([] : Context σ [])
      (Formula.fromSentence (Formula.forall_close body))) :
    Derives T ([] : Context σ free) body := by
  induction free with
  | nil =>
      simpa [Formula.forall_close, Formula.fromSentence,
        Renaming.emptyFree] using hClosed
  | cons sort free ih =>
      have hUniversal : Derives T ([] : Context σ free)
          (body.forallFreeTop sort) := by
        apply ih (body := body.forallFreeTop sort)
        simpa [Formula.forall_close] using hClosed
      have hBody := FirstOrder.Derives.forall_elim_newest hUniversal
      simpa [FreshVariable.extendContext] using hBody

/--
全称闭包可一次性在任意目标 free 上下文中按类型化项替换实例化，并随后进入任意
局部上下文。该接口是所有闭 schema 公理的公共实例化入口。
-/
theorem forall_close_elim {σ : Signature.{u, v, w}}
    {T : Theory σ} {sourceFree targetFree : SortContext σ}
    {Γ : Context σ targetFree} (body : OpenFormula σ sourceFree)
    (substitution :
      VariableSubstitution σ sourceFree [] targetFree)
    (hClosed : Derives T ([] : Context σ [])
      (Formula.fromSentence (Formula.forall_close body))) :
    Derives T Γ (body.substituteFree substitution) := by
  have hOpen := forall_close_open body hClosed
  have hInstance := FirstOrder.Derives.free_substitution substitution hOpen
  exact FirstOrder.Derives.context_weaken
    (by
      intro candidate hMember
      cases hMember)
    hInstance

end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
