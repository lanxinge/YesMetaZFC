import YesMetaZFC.Model.SetTheory.Internal.ElementaryClub
import YesMetaZFC.Model.SetTheory.Internal.ElementaryTrace
import YesMetaZFC.Model.SetTheory.Internal.SourceElementary
import YesMetaZFC.Model.SetTheory.Internal.Membership
import YesMetaZFC.Model.SetTheory.Internal.MembershipSkolem
import YesMetaZFC.Model.SetTheory.Internal.Hereditary

/-! # 集合结构、公式码与满足关系的地模型内部编码

`smdl_membership_l` 构造任意非空内部集合的隶属结构码；`scode_exists_l` 收集全部
内部有限公式码；`smdl_satisfaction_l` 构造统一满足关系集合。`smdl_table_l` 一次
返回指定公式的赋值空间、唯一真值表及真值集。各构造仅需 ZF，不依赖外部良基性。
`smodels_theory_l` 给出编码理论及实际模型性实例；`source_compile_l` 把原 Project
AST 编译成内部码并证明对全部编码结构的语义对应，`source_satisfaction_l` 自动
装配有限参数赋值。`scode_numbering_l` 返回全部内部公式码到内部 ω 的单射图，
复用 ZF 中可数字母表的内部有限序列编号。`ssk_hull_l` 在 ZFC 中一次构造真实的
内部司寇伦选择图与任意可数种子的最小可数闭包，并给出所有内部有限参数下的
见证闭性。固定运算图的闭包存在、最小性与单步可数性分别保留 ZF 强度。
`selem_hull_l` 进一步一次构造内部可数初等子模型，初等性量化全部内部公式码
及全部内部赋值。有限支撑与完整内部 Tarski–Vaught 等价仅需 ZF；初等关系可
复合并保持内部编码理论的模型性。`selem_source_l`、`selem_witness_l` 通过同一编译码
把完整内部初等性接回原生产公式；力迫层用它反射见证池中的实际名称。
`selem_club_hull_l` 在任意指定内部 club 中构造这样的初等模型，供 proper 主条件装配使用。
`selem_trace_club_l` 以固定司寇伦图的最小闭包在任意子集上实际构造交集 club。
`ssk_mem_s` 在实际集合隶属结构上统一表达全部内部码的司寇伦见证，供泛型初等提升使用。
`Hsub_d` 将内部可数初等 H(χ) 子模型表示为原公式，供力迫证书和内部递归使用。
-/
