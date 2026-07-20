import YesMetaZFC.Logic.Notation.Raw
import YesMetaZFC.Logic.Notation.Surface

/-!
# 新语义核记号入口

* `FirstOrder.Raw`：A 层，直接暴露 locally nameless 构造；
* `fo[σ] ⟪...⟫`：B 层，使用具名 binder 的数学公式 DSL；
* `Surface`：提供静态的关系 mixfix 记号，并统一归一到 canonical 关系应用。
-/
