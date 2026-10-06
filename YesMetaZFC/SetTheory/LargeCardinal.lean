import YesMetaZFC.SetTheory.LargeCardinal.SupportConstruction
import YesMetaZFC.SetTheory.LargeCardinal.SourceMeasure
import YesMetaZFC.SetTheory.LargeCardinal.SourceProjection
import YesMetaZFC.SetTheory.LargeCardinal.WellFoundedComponents
import YesMetaZFC.SetTheory.LargeCardinal.Extender
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
实际迭代树、pad、任意树前驱上的
超幂后继扩张及后继子集一致性已经构造。实际树枝极限、传递坍塌与极限添枝已完成；
非可数共尾度及相容良基实现给出良基分支判据，可数共尾可延伸树已有实际选枝。
一般可迭代性策略与 AD 蕴涵仍待证明。
-/
