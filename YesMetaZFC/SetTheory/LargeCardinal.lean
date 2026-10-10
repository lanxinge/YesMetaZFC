import YesMetaZFC.SetTheory.LargeCardinal.SupportConstruction
import YesMetaZFC.SetTheory.LargeCardinal.SourceMeasure
import YesMetaZFC.SetTheory.LargeCardinal.SourceProjection
import YesMetaZFC.SetTheory.LargeCardinal.WellFoundedComponents
import YesMetaZFC.SetTheory.LargeCardinal.Extender

/-! # 大基数与实际派生测度

武丁定义量化全部内部公式码。ZF 中已证明武丁基数下方的可测基数无界，
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
原强性的恢复、迭代及 AD 蕴涵仍待证明。
-/
