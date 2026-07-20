import YesMetaZFC.Automation.Request
import YesMetaZFC.SetTheory.Separation

/-!
# 集合论按需相继式生成器

这里只登记可由明确 demand 激活的集合构造。登记不会把声明加入普通 APPLY/FORWARD
候选池；具体对象参数仍由相继式 overlap 分析确定。
-/

namespace YesMetaZFC
namespace SetTheory
namespace KP

register_prove_auto_binary_conjunction_generator exists_intersection

end KP
end SetTheory
end YesMetaZFC
