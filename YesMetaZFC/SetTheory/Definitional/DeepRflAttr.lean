import Lean.Elab.Tactic.Simp

/-!
# 新核受控约化属性

单独注册 `deep_rfl` simp 集，使后续模块可以在初始化完成后安全使用该属性。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional

/-- 新核受控定义约化集合。 -/
register_simp_attr deep_rfl

end Definitional
end SetTheory
end YesMetaZFC
