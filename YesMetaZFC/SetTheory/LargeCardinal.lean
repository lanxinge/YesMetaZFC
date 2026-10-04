import YesMetaZFC.SetTheory.LargeCardinal.SupportConstruction
import YesMetaZFC.SetTheory.LargeCardinal.SourceMeasure
import YesMetaZFC.SetTheory.LargeCardinal.SourceProjection
import YesMetaZFC.SetTheory.LargeCardinal.WellFoundedComponents
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLimit

/-! # 大基数与实际派生测度

武丁定义量化全部内部公式码。ZF 中已证明武丁基数下方的可测基数无界，
并从其强嵌入构造全部有限支撑 κ 完备测度图、任意有限坐标投影及其协调律与共同纤维完备性。
分量内部商与全背景函数版本的内部 Łoś 已完成。源内部子集代数、相对派生超滤和
源内部函数族的商也已构造。对实际初等嵌入正则 H(χ) 的传递源，完整内部 Łoś、
常值初等嵌入、分量间初等映射及其恒等、复合、交换律已完成。
`es_source_projection_l` 从有限支撑协调律自动构造两侧源分量及初等交换图；
`woodin_wf_components_l` 在 ZF＋DC 中为同一测度族自动构造良基分量。
`woodin_extender_l` 自动装配同一测度族的全部有限支撑源分量、过渡图及实际极限结构码，
并用共同纤维证明整个极限内部良基。装配沿用 ZFC 的实际 H(χ) 初等源，良基性核心只需 ZF＋DC。
极限的完整内部初等性、标准短扩展器识别、迭代及 AD 蕴涵仍待证明。
-/
