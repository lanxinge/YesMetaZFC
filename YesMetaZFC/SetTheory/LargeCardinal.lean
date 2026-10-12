import YesMetaZFC.SetTheory.LargeCardinal.SupportConstruction
import YesMetaZFC.SetTheory.LargeCardinal.SourceMeasure
import YesMetaZFC.SetTheory.LargeCardinal.SourceProjection
import YesMetaZFC.SetTheory.LargeCardinal.WellFoundedComponents
import YesMetaZFC.SetTheory.LargeCardinal.Extender
import YesMetaZFC.SetTheory.LargeCardinal.TypeMinusStretch
import YesMetaZFC.SetTheory.LargeCardinal.TypeElasticRead
import YesMetaZFC.SetTheory.LargeCardinal.LocalTypeTransportTuple
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameDecoding
import YesMetaZFC.SetTheory.LargeCardinal.WoodinGameReset
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRigidity
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameReplyBuild
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameDeterminacy
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameTreeStep
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameContinue
import YesMetaZFC.SetTheory.LargeCardinal.Iteration

/-! # 大基数与实际派生测度

武丁定义量化全部内部公式码。ZF 中已证明武丁基数下方的可测基数无界，
可测基数的正则性及小幂集无反向单射也在 ZF 中证明；ZFC 中据此实际选择不可达支撑。
并从其强嵌入构造全部有限支撑 κ 完备测度图、任意有限坐标投影及其协调律与共同纤维完备性。
分量内部商与全背景函数版本的内部 Łoś 已完成。源内部子集代数、相对派生超滤和
源内部函数族的商也已构造。对实际初等嵌入正则 H(χ) 的传递源，完整内部 Łoś、
常值初等嵌入、分量间初等映射及其恒等、复合、交换律已完成。
`es_source_projection_l` 从有限支撑协调律自动构造两侧源分量及初等交换图；
`woodin_wf_components_l` 在 ZF＋DC 中为同一测度族自动构造良基分量。
`woodin_short_l` 在 ZF 中构造标准短扩展器，并识别实际算子 E(A)=j(A)∩L^{<ω}。
通用层给出正规性、临界点坐标、布尔与乘积运算、有界投影、长度截断及原公式对应。
`woodin_extender_l` 直接消费同一个 Ex_short_d，装配全部有限支撑源分量、过渡图及实际极限结构码，
并用共同纤维证明整个极限内部良基；返回完整内部初等嵌入、传递坍塌和到原目标的关系因子。
武丁实例由 Hδ＝Vδ 采用原 Vδ 源；通用装配保留正则 H(χ) 初等源，背景为 ZFC。
通用初等极限与外延坍塌只需 ZF，良基性核心只需 ZF＋DC。
按 ν 选择不可达 L>ν，恢复整个 V_L 覆盖与谓词强性，并用原代表计数证明最大强度恰为 L。
所属源中的实际有界超幂及求值图记录这一强度，可沿完整初等图传输并由指定实际超幂读取。
源内原始不可达性及初始短扩展器判断已构造；不可达性随完整初等图和严格极限秩截断保持。
严格正则秩截断自动保留同一扩展器的最大强度、实际秩层枚举与全部所属判断。
完整类型的实际伸展已实现：任意 Vη 中的内部有限元组有无界多个 κ，
自动给出 V(η+1) 中的完整 κ 型及其 Vη 前驱；前驱的定义域由实际查询核验。
其前驱沿合适的实际强扩展器伸展后，精确投影为同一元组的 τ 型。
前驱类型由同一元组在前一秩层实现，并与同一实际扩展器的伸展交换。
实际迭代树、pad、任意树前驱上的
超幂后继扩张及后继子集一致性已经构造。实际树枝极限、传递坍塌与极限添枝已完成；
非可数共尾度及相容良基实现给出良基分支判据，可数共尾可延伸树已有实际选枝。
nice 树的 ω₁ 弱迭代策略已完成。`ee_definition_l` 实际构造定义 3.13 的四条原类型查询，
`Ee_elastic_d` 只检查查询成员关系，适用于未实现类型；偏前驱算子的定义域与唯一性已接合。
实现类型中的等价式读取同一元组的真实前驱与全部 τ<δ 的伸展，定义本身为 Δ₀ 并在传递源中绝对。
`woodin_elastic_l` 已完成 3.22：无界多个 κ 的上层完整类型满足固定四查询的弹性定义。
`Ee_language_d.realized_l` 从任意秩实现自动读取后继高度、δ 的不可达性、实际源和全部伸展。
`ee_one_step_l` 完成 3.23：保留内部任意元数及排列，按同一固定子类型查询把前驱伸展
提升为原类型在 τ+ω 上的伸展。`woodin_elastic_step_l` 自动构造两层弹性类型和实际一步实例。
`li_indiscernibles_l` 在 ZF 中以固定参数域 V(δ+ω) 构造无界多对局部不可分辨序数，
并提供 ν+ω<μ 的明确间隔。`li_canonical_l` 先最小化第二坐标，给出原约定的最小对及其唯一性。
`li_canonical_transport_l` 将参数带推广为任意 θ≥δ 的 V(θ+ω)，自动搬运任意内部有限
元组在 V(ν+k) 中的原完整 κ 型；到 V(μ+k) 后只移动高度对象，保留全部查询和原类型集合。
`tg_reset_type_l` 实际构造重置元组及其完整节点、空根与高度查询；`tg_one_graph_recovery_l`
从任意子类型排列恢复原树、末位及单点延长的函数图，并由查询反推实现高度。
`woodin_game_reset_l` 进一步给出任意参数域下界以上、dcp 弹性的实际重置类型。
`Tg_reply_d` 已接入规则 (7) 的子类型、空根、严格秩界及加二最大序数条件，
配有统一语言工厂、真实低层读取和实际回答构造；`tg_exceeds_rigid_l` 仅用 dcp⁻
的定义域证明超过关系中的后继高度刚性，不附加伸展或不可达性假设。
`tg_game_l` 已实际装配原七条规则、全部内部有限历史和闭收益集合；三张编码表在开局前固定。
`Tg_game_d.stage_l` 对任意内部时刻自动读出唯一轮号、责任玩家与原规则，策略空间有实际实例。
`Tg_game_d.determined_l` 已由闭博弈决定性给出原策略空间内某一方的获胜策略。
`Tg_low_d.step_l` 从原节点构造弹性回答及满足规则 (7) 的真实超幂像；
`Tg_context_d.round_l` 把给定回答的原扩展器加入当前完整模型的 nice 树，
从原武丁公式和回答支撑自动取得所需正则性、共同秩段及原类型成员性；目标层内的同一规则 (7) 已验证。
`Tg_game_d.tree_step_l` 从原 II 获胜策略自动提取首轮，添加 padding 后沿实际偶数边搬运策略控制记录与历史。
`tg_context_l` 保存回答更新、继续伸展、语言重建、子类型实现、高度刚性及图恢复六个已证句子，沿完整初等图覆盖目标层的新参数；
`Tg_context_d.continue_tree_l` 将继续分支的扩展器施加到指定较早节点，
识别实际旧类型像及新子类型，并把旧轮的完整实现与节点事实一并搬运到目标层。
候选语言的全部数据自动进入共同秩段；自然数程序沿实际树根图传递，原名字列及查询保持不变。
原 dcp 弹性与子类型程序同在目标反射层，并自动给出候选的低层完整实现，保留任意原排列。
旧回答查询沿固定的共同低秩层传递；超过关系与 dcp 定义域实际推出最大序数查询。
继续树边已经接上一张图恢复，输出目标层中的完整新元组、原排列、旧坐标对应及恰好一个新标签。
`Tg_context_d.restart_l` 直接把这些见证与原程序组成下一轮输入，并在同一层产生完整回答；
`continue_tree_l` 已直接消费该回答并建立下一条奇数树边，保存两条边的根图复合及原字母表锚点。
支撑列界由实际 nice 树末项推出，更新下界允许等号。
两侧共享的相对 Vκ 中每个对象均由临界点性质固定，不以整个工作模型满足 ZF 为前提。
工作模型无须满足整个 ZFC；整个有限历史的递归与偶数枝良基性矛盾尚待接合。
后续采用双树坍缩穷尽的直接决定性路线；5.15 的迭代论证、实数吸收和 AD 蕴涵仍待证明。
-/
