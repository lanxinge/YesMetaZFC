import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinExtender
import YesMetaZFC.SetTheory.LargeCardinal.Determinacy.LReal
import YesMetaZFC.SetTheory.InnerModel.Relative.PayoffQuerySound
import YesMetaZFC.Model.Forcing.Ground.GenericTree
import YesMetaZFC.Model.Forcing.Order.GenericTreeGround
import YesMetaZFC.Model.Forcing.Order.NameSound
import YesMetaZFC.Model.Forcing.Ground.QueryTree
import YesMetaZFC.Model.Forcing.Collapse.ProductRankAbsorption
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.DerivedPredicate
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.SourceProjection
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Overview
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRank
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawPowerStep
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ArchiveUpdate
import YesMetaZFC.SetTheory.LargeCardinal.Game.RelativeStart
import YesMetaZFC.SetTheory.LargeCardinal.Types.MinusStretch
import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStep
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.LocalTypeTransportTuple
import YesMetaZFC.SetTheory.LargeCardinal.Game.RecoverySyntax
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinTypeStep
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rigidity
import YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyDescent
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.Corollary610
import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedStrategy
import YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection
import YesMetaZFC.SetTheory.LargeCardinal.Game.GeneralProjection
import YesMetaZFC.SetTheory.LargeCardinal.Determinacy.TwinTreeOutward
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.ExternalBookkeeping
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.ExternalFunctionSection
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchSchedule
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Overview
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakBranch
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakAnswerTreeSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakTree
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableCover
import YesMetaZFC.Model.SetTheory.Relations.NativeSmemSlice
import YesMetaZFC.SetTheory.LargeCardinal.Demand.AlphabetImage
import YesMetaZFC.SetTheory.LargeCardinal.Demand.ResetRound
import YesMetaZFC.SetTheory.LargeCardinal.Demand.RawReset
import YesMetaZFC.SetTheory.LargeCardinal.Demand.Corollary712
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Return
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Pending
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.QueueStep
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.FrameStart
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Target
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.TestRun
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.Realization
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.QueryHull
import YesMetaZFC.SetTheory.LargeCardinal.Determinacy.QueryTreeTruth
import YesMetaZFC.SetTheory.LargeCardinal.Determinacy.TwinTreeSyntax
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.HeightPreserve
import YesMetaZFC.SetTheory.LargeCardinal.Absorption.CounterHeight
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinInitial
import YesMetaZFC.Model.Forcing.Order.QueryContext
import YesMetaZFC.Model.Forcing.Collapse.NameCode

/-! # 大基数与 L(ℝ) 的决定性

`wd_lr_ad_l` 从背景 ZFC 与真类 Woodin 得到原句子 `Axioms.lr_ad`。
`lr_ad_axiom_sat_l` 把它解释为规范 L(ℝ) 满足内部 AD。

本入口汇总 Cardinals、Extender、Iteration、Types、Game、Demand、Absorption、Determinacy。
原关系超幂、完整复制历史、奇枝深度调度、实数吸收与高度提升均由实际构造提供。
固定参数的双树决定性识别同一收益，规范策略实数和有界获胜条件完成最后下传。

目录职责及可调用模块见 [大基数导航](LargeCardinal/README.md)，
数学路线与较弱前提版本的边界见 [L(ℝ) 的 AD](../../markdown/LR_AD.md)。
-/
