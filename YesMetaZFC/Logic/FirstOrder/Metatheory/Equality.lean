import YesMetaZFC.Logic.FirstOrder.Derivation.Equality
import YesMetaZFC.Logic.FirstOrder.Metatheory.Notation
/-!
# 等词元定理
本模块把可信核的 Leibniz 替换规则整理为元数学记号下的公共接口。等式两端的
共同排序与公式模板的替换位置全部由类型索引固定，不再产生检查证书或良构义务。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
universe u v w
namespace Derives
/-- 等式允许在任意公式模板中从左项替换到右项。 -/
theorem equality_substitution {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {sort : σ.SortSymbol} (left right : OpenTerm σ free sort)
    (body : Formula σ [sort] free) :
    Γ ⊢ₘ[T] (left ≐ₘ right) ⟶ₘ
      (body.instantiateTop left ⟶ₘ body.instantiateTop right) :=
  FirstOrder.Derives.eq_subst_imp left right body

/-- 公式模板的规范变量等于替换项时，可沿等式完成一次实例化。 -/
theorem equality_substitute_free_variable {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ} {Γ : Context σ free}
    {sort : σ.SortSymbol} (source replacement : OpenTerm σ free sort)
    (body : Formula σ [sort] free) :
    Γ ⊢ₘ[T] (source ≐ₘ replacement) ⟶ₘ
      (body.instantiateTop source ⟶ₘ body.instantiateTop replacement) :=
  equality_substitution source replacement body
end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
