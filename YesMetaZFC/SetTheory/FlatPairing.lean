import YesMetaZFC.SetTheory.FlatPairing.RankObjects
import YesMetaZFC.SetTheory.FlatPairing.AssignmentSource
import YesMetaZFC.SetTheory.FlatPairing.CumulativeSource
import YesMetaZFC.SetTheory.FlatPairing.StructureSource

/-! # 原平坦配对与秩内有限编码

`fp_interpretation_l` 实现原 Quine–Rosser 约定；`fp_rank_interpretation_l` 在包含 ω
的秩初段中解释同一公式。`fp_rank_pair_l` 对每个 ν≥ω 保持 Vν，
`fp_finite_rank_l` 在 Vν 内编码全部内部有限前缀。
`Fs_code_d.prefix_l` 刻画编码的精确信息，`rt_fs_code_l` 给出后继秩层内外的双向对应。
`rt_fp_v_l` 在后继秩层中读取全部累积层级，包括最大序数对应的前一层；
历史及其限制自动回收，不要求该后继层满足 ZF。
-/
