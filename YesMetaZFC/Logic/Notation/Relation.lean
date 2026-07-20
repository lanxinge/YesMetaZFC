import YesMetaZFC.Logic.Notation.SurfaceSyntax

/-!
# 关系 mixfix 记号

关系记号采用静态 `scoped syntax` 和宏归一化，不在环境中注册动态 parser。
核心只提供没有歧义的 `∈`；具体理论在自己的 scope 中用普通 Lean
`scoped notation` 声明 `a R b`、`a b R c` 等排版。

自定义关系的协议是 notation 展开后必须得到
`ℛ[关系符号](按参数顺序排列的项列表)`。对象语言核心不感知这些排版细节。

例如，三元关系可以在理论自己的 scope 中静态声明：

```lean
scoped syntax:55 foTerm:56 foTerm:56 "R" foTerm:56 : foFormula
scoped macro_rules
  | `(foFormula| $a:foTerm $b:foTerm R $c:foTerm) =>
      `(foFormula| ℛ[Geometry.between]($a, $b, $c))
```

这里的 `R` 是该理论明确选择的排版 token，不是全局动态注册的关系名。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Surface

/-- 为 `∈` 提供签名局部的关系解释；不同签名可以各自给出实例。 -/
class MembershipRelation (σ : Signature) where
  mem : σ.RelSymbol

def membershipRelation {σ : Signature} [MembershipRelation σ] : σ.RelSymbol :=
  MembershipRelation.mem

/- 常用二元关系：集合论中的隶属关系。 -/
scoped syntax:55 foTerm:56 "∈" foTerm:56 : foFormula

scoped macro_rules
  | `(foFormula| $left:foTerm ∈ $right:foTerm) =>
      `(foFormula| ℛ[Surface.membershipRelation]($left, $right))

end Surface
end FirstOrder
end Logic
end YesMetaZFC
