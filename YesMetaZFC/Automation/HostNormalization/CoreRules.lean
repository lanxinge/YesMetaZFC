import YesMetaZFC.Automation.HostNormalization.RuleRegistry

/-!
# `prove_auto` 宿主正规化基础规则

这里只放与具体对象理论无关的最小逻辑白名单。对象理论的定义、索引代数和语义对齐
规则仍在其声明所在模块注册。
-/

namespace YesMetaZFC
namespace Automation
namespace HostNormalization

/-- 反身等价是语义对齐后的标准固定点。 -/
@[prove_auto_norm logical]
theorem iffRefl (proposition : Prop) :
    (proposition ↔ proposition) = True :=
  iff_self proposition

end HostNormalization
end Automation
end YesMetaZFC
