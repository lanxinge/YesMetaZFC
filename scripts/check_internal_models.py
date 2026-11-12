"""审计内部模型、公式编译、司寇伦闭包、有限反射及 OD/HOD。

各切片仅允许既有标准 Lean 公理，不再放行原生句法闭合性公理。
编码和解码数据排除经典选择，司寇伦模块的 ZF 端点另逐项收紧。
复用实际声明审计，不生成常驻测试模块。
"""
import sys

from check_filters import BASELINE, main

MODULES = [
    'YesMetaZFC.Model.SetTheory.Internal.Quotient',
    'YesMetaZFC.Model.SetTheory.Internal.Theory',
    'YesMetaZFC.Model.SetTheory.Source.Basic',
    'YesMetaZFC.Model.SetTheory.Internal.FiniteSource',
    'YesMetaZFC.Model.SetTheory.Internal.Countable',
    'YesMetaZFC.Model.SetTheory.Reflection.SkolemSyntax',
    'YesMetaZFC.Model.SetTheory.Types.CanonicalCode',
    'YesMetaZFC.Model.SetTheory.Types.CanonicalSatisfaction',
    'YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace',
    'YesMetaZFC.Model.SetTheory.Types.MoveQuote',
    'YesMetaZFC.Model.SetTheory.Types.Embedding',
    'YesMetaZFC.Model.SetTheory.Internal.Support',
    'YesMetaZFC.Model.SetTheory.Internal.TarskiVaughtSyntax',
    'YesMetaZFC.Model.SetTheory.Internal.TarskiVaught',
    'YesMetaZFC.Model.SetTheory.Embedding.ElementarySyntax',
    'YesMetaZFC.Model.SetTheory.Embedding.Elementary',
    'YesMetaZFC.Model.SetTheory.Source.Elementary',
    'YesMetaZFC.Model.SetTheory.Internal.Hereditary',
    'YesMetaZFC.Model.SetTheory.LevyReflection.Parameters',
    'YesMetaZFC.Model.SetTheory.LevyReflection.WitnessSyntax',
    'YesMetaZFC.Model.SetTheory.LevyReflection.Collection',
    'YesMetaZFC.Model.SetTheory.LevyReflection.Step',
    'YesMetaZFC.Model.SetTheory.LevyReflection.Chain',
    'YesMetaZFC.Model.SetTheory.LevyReflection.Closure',
    'YesMetaZFC.Model.SetTheory.LevyReflection.Relativization',
    'YesMetaZFC.Model.SetTheory.LevyReflection.Decode',
    'YesMetaZFC.Model.SetTheory.LevyReflection.Bounded',
    'YesMetaZFC.Model.SetTheory.LevyReflection',
    'YesMetaZFC.SetTheory.CumulativeUnion',
    'YesMetaZFC.Model.SetTheory.ProjectEmbedding',
    'YesMetaZFC.SetTheory.RelationChain',
    'YesMetaZFC.Model.SetTheory.ClassResponse',
    'YesMetaZFC.SetTheory.FlatPairing',
    'YesMetaZFC.SetTheory.FlatPairing.Shift',
    'YesMetaZFC.SetTheory.FlatPairing.Tag',
    'YesMetaZFC.SetTheory.FlatPairing.Pair',
    'YesMetaZFC.SetTheory.FlatPairing.Rank',
    'YesMetaZFC.SetTheory.FlatPairing.Source',
    'YesMetaZFC.SetTheory.FlatPairing.Sequence',
    'YesMetaZFC.SetTheory.FlatPairing.Finite',
    'YesMetaZFC.SetTheory.FlatPairing.RankObjects',
    'YesMetaZFC.SetTheory.FlatPairing.Functions',
    'YesMetaZFC.SetTheory.FlatPairing.SequenceSource',
    'YesMetaZFC.SetTheory.FlatPairing.AssignmentSource',
    'YesMetaZFC.Model.SetTheory.Types.FlatSatisfaction',
    'YesMetaZFC.Model.SetTheory.Reflection.RankSatisfaction',
    'YesMetaZFC.Model.SetTheory.Internal.RelativizationCorrect',
    'YesMetaZFC.Model.SetTheory.Internal.LargestSet',
    'YesMetaZFC.Model.SetTheory.Types.Minus',
    'YesMetaZFC.Model.SetTheory.Types.SubtypeLift',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.MinusStretch',
    'YesMetaZFC.SetTheory.FunctionRecoding',
    'YesMetaZFC.SetTheory.CumulativePairing',
    'YesMetaZFC.SetTheory.FlatPairing.RecursionSource',
    'YesMetaZFC.SetTheory.FlatPairing.CumulativeSource',
    'YesMetaZFC.SetTheory.FlatPairing.StructureSource',
    'YesMetaZFC.Model.SetTheory.Reflection.RankLargest',
    'YesMetaZFC.Model.SetTheory.Types.FlatPredecessor',
    'YesMetaZFC.Model.SetTheory.Types.ProgramReflect',
    'YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence',
    'YesMetaZFC.Model.SetTheory.Internal.OrdinalFoldSource',
    'YesMetaZFC.Model.SetTheory.Internal.SyntaxSource',
    'YesMetaZFC.Model.SetTheory.Types.CanonicalSource',
    'YesMetaZFC.Model.SetTheory.Types.FlatTypePredecessor',
    'YesMetaZFC.Model.SetTheory.Internal.TupleCode',
    'YesMetaZFC.Model.SetTheory.Types.Roles',
    'YesMetaZFC.Model.SetTheory.Internal.LowerSatisfaction',
    'YesMetaZFC.Model.SetTheory.Types.PredecessorCode',
    'YesMetaZFC.Model.SetTheory.Internal.FiniteSpaceBounded',
    'YesMetaZFC.Model.SetTheory.Types.KappaCode',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawOwnedCopy',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalFormula',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticQuery',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticClauses',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticNumericTransfer',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.OneStep',
    'YesMetaZFC.Model.SetTheory.Types.SubtypeUp',
    'YesMetaZFC.Model.SetTheory.Types.LowerSource',
    'YesMetaZFC.Model.SetTheory.Types.SubtypeWitness',
    'YesMetaZFC.Model.SetTheory.Types.ExceedsSyntax',
    'YesMetaZFC.SetTheory.Card.Cofinality.OmegaAddition',
    'YesMetaZFC.SetTheory.Ord.UnboundedFiber',
    'YesMetaZFC.Model.SetTheory.Types.MoveRead',
    'YesMetaZFC.SetTheory.KP.OrdinalCore',
    'YesMetaZFC.SetTheory.Ord.Natural',
    'YesMetaZFC.SetTheory.CumulativeFinite',
    'YesMetaZFC.Model.SetTheory.Internal.FiniteTailSource',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.LocalTypeTransportTuple',
    'YesMetaZFC.Model.SetTheory.Internal.FiniteSetCode',
    'YesMetaZFC.Model.SetTheory.Game.NodeEmbedding',
    'YesMetaZFC.Model.SetTheory.Game.Graph',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.RecoverySyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Reset',
    'YesMetaZFC.Model.SetTheory.Types.DropEmbedding',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticDomain',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Elastic',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Rigidity',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyDescent',
    'YesMetaZFC.Model.SetTheory.Source.InaccessibleSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.CatalogRead',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.DigitsImage',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.RawReply',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.RoundNativeScope',
    'YesMetaZFC.SetTheory.Ord.FiniteTail',
    'YesMetaZFC.Model.SetTheory.Types.SubtypeReboundImage',
    'YesMetaZFC.Model.SetTheory.Types.SubtypeReflect',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.Renewal',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.CriticalPoint',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CriticalBound',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.OneStepDropImage',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.WorkingApply',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.TreeStep',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.AnswerAdvance',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.RunMove',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Rank',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.IssuedReset',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Continue',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNameSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.PastEvents',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.OddBranch',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.ControlCard',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.PastRoots',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.TreeSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Corollary610',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.ReturnSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.EvenLimit',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedStrategy',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.ReturnBranch',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.ReturnTree',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.FiniteArithmeticSource',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.StrategyPlay',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Tracked',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.GenericPreparation',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.GenericRun',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedProjection',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.LevelReply',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.TreeProjectionTransfer',
    'YesMetaZFC.SetTheory.LargeCardinal.Determinacy.TwinTreeSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Determinacy.TwinTreeOutward',
    'YesMetaZFC.SetTheory.LargeCardinal.Determinacy.TwinTreeRank',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Round',
    'YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative',
    'YesMetaZFC.Model.SetTheory.Game.GraphUnion',
    'YesMetaZFC.Model.SetTheory.Types.SubtypeInsertion',
    'YesMetaZFC.SetTheory.Descriptive.Demand.InputIteration',
    'YesMetaZFC.SetTheory.Descriptive.Tree.TreeTail',
    'YesMetaZFC.SetTheory.Descriptive.Tree.TreeWellFounded',
    'YesMetaZFC.SetTheory.Descriptive.Tree.HistoryTree',
    'YesMetaZFC.SetTheory.Descriptive.Game.GameAttemptRank',
    'YesMetaZFC.SetTheory.Descriptive.Coding.SequenceCons',
    'YesMetaZFC.SetTheory.Descriptive.Game.GameShift',
    'YesMetaZFC.SetTheory.Descriptive.Tree.TreeShift',
    'YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy',
    'YesMetaZFC.SetTheory.Descriptive.Tree.ScanStrategy',
    'YesMetaZFC.SetTheory.Descriptive.Game.FirstViolationMonotone',
    'YesMetaZFC.SetTheory.IndexedIteration',
    'YesMetaZFC.SetTheory.Ord.FirstCrossing',
    'YesMetaZFC.SetTheory.FinitaryTraceSyntax',
    'YesMetaZFC.SetTheory.FinitaryFamily',
    'YesMetaZFC.SetTheory.Card.FiniteParameters',
    'YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax',
    'YesMetaZFC.SetTheory.Card.FiniteSequenceRecursion',
    'YesMetaZFC.SetTheory.Card.FiniteSequenceNumbering',
    'YesMetaZFC.SetTheory.Card.FiniteSequenceCountable',
    'YesMetaZFC.SetTheory.Card.FiniteSequenceLift',
    'YesMetaZFC.SetTheory.Card.FiniteSequenceEnd',
    'YesMetaZFC.SetTheory.Card.FiniteSequenceRecode',
    'YesMetaZFC.SetTheory.Card.OrdinalImage',
    'YesMetaZFC.SetTheory.CountableChain',
    'YesMetaZFC.SetTheory.FinitaryHullSyntax',
    'YesMetaZFC.SetTheory.FinitaryHullStep',
    'YesMetaZFC.SetTheory.FinitaryHull',
    'YesMetaZFC.Model.SetTheory.Internal',
    'YesMetaZFC.Model.SetTheory.ReducedPower.Overview',
    'YesMetaZFC.SetTheory.Rank',
    'YesMetaZFC.SetTheory.TransitiveClosure',
    'YesMetaZFC.SetTheory.RankImage',
    'YesMetaZFC.SetTheory.Hereditary',
    'YesMetaZFC.SetTheory.Card.SmallBound',
    'YesMetaZFC.SetTheory.FunctionRetraction',
    'YesMetaZFC.SetTheory.FinitarySlice',
    'YesMetaZFC.SetTheory.Ord.Code.Transport',
    'YesMetaZFC.SetTheory.Ord.Code.Pair',
    'YesMetaZFC.SetTheory.Ord.Code.Natural',
    'YesMetaZFC.SetTheory.Ord.Code.Fold',
    'YesMetaZFC.SetTheory.Ord.Code.Prefix',
    'YesMetaZFC.SetTheory.Ord.Code.Sequence',
    'YesMetaZFC.SetTheory.Ord.Code',
    'YesMetaZFC.SetTheory.InnerModel.OD',
    'YesMetaZFC.SetTheory.InnerModel.OD.Syntax',
    'YesMetaZFC.SetTheory.InnerModel.OD.Source',
    'YesMetaZFC.SetTheory.InnerModel.OD.Code',
    'YesMetaZFC.SetTheory.InnerModel.OD.Definition',
    'YesMetaZFC.SetTheory.InnerModel.OD.Complexity',
    'YesMetaZFC.SetTheory.InnerModel.OD.Minimum',
    'YesMetaZFC.SetTheory.InnerModel.OD.Order',
    'YesMetaZFC.SetTheory.InnerModel.OD.Choice',
    'YesMetaZFC.SetTheory.CumulativeCertificate',
    'YesMetaZFC.SetTheory.Ord.DefinableMinimum',
    'YesMetaZFC.SetTheory.Definitional.Project.Hierarchy.Levy',
    'YesMetaZFC.SetTheory.InnerModel.HOD.Definition',
    'YesMetaZFC.SetTheory.InnerModel.HOD',
    'YesMetaZFC.SetTheory.InnerModel.OD.Graph',
    'YesMetaZFC.SetTheory.InnerModel.OD.Brackets',
    'YesMetaZFC.SetTheory.InnerModel.OD.Parameters',
    'YesMetaZFC.SetTheory.InnerModel.OD.Relative',
    'YesMetaZFC.SetTheory.InnerModel.OD.RelativeClosure',
    'YesMetaZFC.SetTheory.InnerModel.OD.Separation',
    'YesMetaZFC.SetTheory.InnerModel.OD.Relations',
    'YesMetaZFC.SetTheory.InnerModel.HOD.Relative',
    'YesMetaZFC.SetTheory.InnerModel.HOD.Relativization',
    'YesMetaZFC.SetTheory.InnerModel.HOD.Closure',
    'YesMetaZFC.SetTheory.InnerModel.HOD.Schemas',
    'YesMetaZFC.SetTheory.InnerModel.HOD.Models',
    'YesMetaZFC.SetTheory.InnerModel.HOD.Parameters',
    'YesMetaZFC.SetTheory.InnerModel.HOD.Coding',
    'YesMetaZFC.SetTheory.InnerModel.HOD.Presentation',
    'YesMetaZFC.SetTheory.Collapse.RelationSyntax',
    'YesMetaZFC.SetTheory.Collapse.RelationRecursion',
    'YesMetaZFC.SetTheory.Collapse.RelationExistence',
    'YesMetaZFC.SetTheory.Collapse.RelationIso',
    'YesMetaZFC.SetTheory.Collapse.RelationBounded',
    'YesMetaZFC.SetTheory.Collapse.RelationMap',
    'YesMetaZFC.SetTheory.Collapse',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthRank',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.StrengthAgreement',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RelativeRankEnumeration',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraSupport',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.Coherence',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptMember',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptLift',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptRank',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.Enumeration',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.ReturnFactor',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Countable',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax',
    'YesMetaZFC.Model.SetTheory.Source.ClosureSyntax',
    'YesMetaZFC.Model.SetTheory.Source.OmegaClosed',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.OmegaClosed',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemSource',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.InitialPull',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.Descent',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RelativeRankSegment',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.EmbeddingCountableBound',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.CopySuccessor',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.EmbeddingSetImage',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RankLift',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RankAgreement',
    'YesMetaZFC.Model.SetTheory.Embedding.RankFixed',
    'YesMetaZFC.Model.SetTheory.Source.RankSizeInitial',
    'YesMetaZFC.SetTheory.Card.Syntax',
    'YesMetaZFC.SetTheory.Card.Properties.Syntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.LevelTransfer',
    'YesMetaZFC.SetTheory.CumulativeRelativeAlgebra',
    'YesMetaZFC.SetTheory.CumulativeRelativeRestriction',
    'YesMetaZFC.SetTheory.CumulativeRelativeComparison',
    'YesMetaZFC.SetTheory.Descriptive',
    'YesMetaZFC.SetTheory.Card.FiniteSequenceJoin',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinInitial',
    'YesMetaZFC.SetTheory.InnerModel.Relative.Hierarchy',
    'YesMetaZFC.SetTheory.InnerModel.Relative.TruthSyntax',
    'YesMetaZFC.SetTheory.InnerModel.Relative.PayoffQuerySound',
    'YesMetaZFC.Model.SetTheory.Internal.Isomorphism',
    'YesMetaZFC.Model.SetTheory.Internal.Collapse',
    'YesMetaZFC.Model.SetTheory.Internal.SeparationHull',
    'YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax',
    'YesMetaZFC.Model.SetTheory.Internal.CollectionCode',
    'YesMetaZFC.Model.SetTheory.Internal.FunctionCode',
    'YesMetaZFC.Model.SetTheory.Internal.Uniformization',
    'YesMetaZFC.Model.SetTheory.Types.PointwiseWitness',
    'YesMetaZFC.Model.SetTheory.Internal.UniformizationSource',
    'YesMetaZFC.Model.SetTheory.Source.Field',
    'YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel',
    'YesMetaZFC.Model.SetTheory.ReducedPower.Los',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize',
    'YesMetaZFC.Model.SetTheory.ReducedPower.SourceProjection',
    'YesMetaZFC.Model.SetTheory.ReducedPower.Projection',
    'YesMetaZFC.Model.SetTheory.ReducedPower.ProjectionLaws',
    'YesMetaZFC.SetTheory.CumulativeFunction',
    'YesMetaZFC.SetTheory.KP.Ordinal',
    'YesMetaZFC.SetTheory.CumulativeClosure',
    'YesMetaZFC.SetTheory.InnerModel.Recursion.Graph',
    'YesMetaZFC.SetTheory.InnerModel.Recursion.Composition',
    'YesMetaZFC.SetTheory.Filter.Relative',
    'YesMetaZFC.SetTheory.Filter.Source',
    'YesMetaZFC.SetTheory.Filter.Projection',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.DerivedPredicate',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.SourceProjection',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinTypeStep',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinExtender',
    'YesMetaZFC.Model.SetTheory.DirectedSystem.Overview',
    'YesMetaZFC.Model.SetTheory.DirectedSystem.Basic',
    'YesMetaZFC.Model.SetTheory.DirectedSystem.Relative',
    'YesMetaZFC.Model.SetTheory.DirectedSystem.Isomorphism',
    'YesMetaZFC.SetTheory.Collapse.RelationSequence',
    'YesMetaZFC.SetTheory.Filter.Countable',
    'YesMetaZFC.SetTheory.CountableChoice',
    'YesMetaZFC.SetTheory.Filter.Finite',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.JointFiber',
    'YesMetaZFC.Model.SetTheory.DirectedSystem.ElementaryFactor',
    'YesMetaZFC.Model.SetTheory.Internal.SeparationTransport',
    'YesMetaZFC.Model.SetTheory.Source.Transport',
    'YesMetaZFC.Model.SetTheory.ReducedPower.Copy',
    'YesMetaZFC.Model.SetTheory.ReducedPower.CopyConstant',
    'YesMetaZFC.SetTheory.Filter.SourceUltrafilter',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.CopyApplication',
    'YesMetaZFC.Model.SetTheory.ReducedPower.DeltaImage',
    'YesMetaZFC.Model.SetTheory.Source.Relation',
    'YesMetaZFC.Model.SetTheory.Relations.CollectCode',
    'YesMetaZFC.Model.SetTheory.Relations.FunctionFamily',
    'YesMetaZFC.Model.SetTheory.Relations.Separation',
    'YesMetaZFC.Model.SetTheory.Source.CollectionBasis',
    'YesMetaZFC.Model.SetTheory.Relations.Collection',
    'YesMetaZFC.Model.SetTheory.Relations.Constant',
    'YesMetaZFC.Model.SetTheory.Relations.Ultrafilter',
    'YesMetaZFC.Model.SetTheory.Relations.PointwiseWitness',
    'YesMetaZFC.Model.SetTheory.Relations.SeparationSource',
    'YesMetaZFC.Model.SetTheory.Relations.Small',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationRestriction',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationSuccessor',
    'YesMetaZFC.Model.SetTheory.Relations.Composition',
    'YesMetaZFC.Model.SetTheory.Relations.Parity',
    'YesMetaZFC.Model.SetTheory.Relations.Hierarchy',
    'YesMetaZFC.Model.SetTheory.Relations.FunctionCapture',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationProjection',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationTrace',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationMeasure',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull',
    'YesMetaZFC.SetTheory.Collapse.RelationRealization',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.FunctionValue',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SeedCollapse',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedRaw',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedRealization',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyClass',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawProjection',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRank',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SetCode',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.NormalSource',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.CopySeed',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.Branch',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.Step',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.Overview',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.System',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.LimitDiagram',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.Padding',
    'YesMetaZFC.SetTheory.LargeCardinal',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.WellFounded',
    'YesMetaZFC.SetTheory.OrdinalChoice',
    'YesMetaZFC.Model.SetTheory.Embedding.Range',
    'YesMetaZFC.Model.SetTheory.Internal.Extensionality',
    'YesMetaZFC.Model.SetTheory.Relations.Collapse',
    'YesMetaZFC.Model.SetTheory.Internal.UniversalClosure',
    'YesMetaZFC.Model.SetTheory.Source.FinitePartial',
    'YesMetaZFC.Model.SetTheory.ReducedPower.SourceComposition',
    'YesMetaZFC.Model.SetTheory.ReducedPower.Restriction',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Coordinates',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Represent',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RankCover',
    'YesMetaZFC.SetTheory.Card.PowerBound',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.NormalSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Truncation',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Product',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Overview',
    'YesMetaZFC.SetTheory.Kuratowski',
    'YesMetaZFC.SetTheory.Card.SmallEnumeration',
    'YesMetaZFC.SetTheory.Collapse.EmbeddingFixed',
    'YesMetaZFC.SetTheory.CumulativeRelative',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Length',
    'YesMetaZFC.Model.SetTheory.Embedding.AttemptRelative',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.EmbeddingCountable',
    'YesMetaZFC.Model.SetTheory.Internal.RegularRankImage',
    'YesMetaZFC.Model.SetTheory.Internal.CollapseCountable',
    'YesMetaZFC.Model.SetTheory.Reflection.RelativeCountable',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptCoordinates',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.NiceReturn',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemStep',
    'YesMetaZFC.Model.SetTheory.Internal.FormulaRelation',
    'YesMetaZFC.Model.SetTheory.ReducedPower.SourceFormula',
    'YesMetaZFC.Model.SetTheory.Source.RankClosure',
    'YesMetaZFC.SetTheory.CumulativeRelativeClosure',
    'YesMetaZFC.SetTheory.InnerModel.Rudimentary.Closure',
    'YesMetaZFC.Model.SetTheory.Source.Cantor',
    'YesMetaZFC.Model.SetTheory.Source.Presentation',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraCertificate',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedGraph',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceLimit',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceJointFiber',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceNode',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedTransport',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedValue',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.FunctionMap',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.CopyBounded',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.CopySubsets',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SystemRead',
    'YesMetaZFC.Model.SetTheory.Embedding.Relative',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CutPull',
    'YesMetaZFC.SetTheory.Ord.Recursion',
    'YesMetaZFC.SetTheory.InnerModel.Rudimentary.Tuple',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakAnswerTreeSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.KeepTransfer',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakAnswer',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.Weak',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.ReplyReflect',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.ImageSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueAbsolute',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.PoolRead',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueRealizeSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Recovery',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Basis',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.QueryTransfer',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Restart',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.RelativeStart',
    'YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer',
    'YesMetaZFC.Model.SetTheory.Source.BinaryRelation',
    'YesMetaZFC.Model.SetTheory.Relations.OmegaCut',
    'YesMetaZFC.Model.SetTheory.Relations.LayerSeparation',
    'YesMetaZFC.Model.SetTheory.Relations.RecordImage',
    'YesMetaZFC.Model.SetTheory.Internal.MembershipSlice',
    'YesMetaZFC.Model.SetTheory.Relations.LayerMeasure',
    'YesMetaZFC.Model.SetTheory.Relations.LayerComposition',
    'YesMetaZFC.Model.SetTheory.Relations.NativeRank',
    'YesMetaZFC.Model.SetTheory.Relations.CrossMeasure',
    'YesMetaZFC.Model.SetTheory.Relations.CrossProjection',
    'YesMetaZFC.Model.SetTheory.Relations.CrossCapture',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationCrossBounded',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawPresent',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawStrength',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedIdentity',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawGraphSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawColimit',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawEvaluation',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawConstant',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationFormulaImage',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationApplication',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawApplication',
    'YesMetaZFC.Model.SetTheory.Relations.OmegaEvaluation',
    'YesMetaZFC.SetTheory.KP.TransitiveInduction',
    'YesMetaZFC.SetTheory.CumulativeComparison',
    'YesMetaZFC.Model.SetTheory.Relations.RankImage',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.ActivityRead',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyQuality',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAgreementRead',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawMembershipSystem',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Padding',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCountable',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableCover',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptRegular',
]


CHOICE_FREE = ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Num_d", "num_m", "num_unique_l", "Smdl_d", "smdl_m", "smdl_structure_l",
                "smdl_unique_l", "Senv_update_d", "senv_update_m", "senv_update_unique_l",
                "Sop_d", "sop_m", "Sfm_node_d", "sfm_node_m", "Sfm_d", "sfm_m",
                "Sarg_d", "sarg_m", "Snode_d", "snode_m", "Seval_at_d", "seval_at_m",
                "Seval_step_d", "seval_step_m", "seval_s", "seval_env_l", "Seval_d", "seval_m",
                "seval_step_unique_l", "Ssat_d", "ssat_m", "Sformula_d", "sformula_m",
                "sformula_unique_l", "Scode_d", "scode_m", "scode_unique_l",
                "Satisfies_d", "satisfies_m", "satisfies_decode_l", "Smodels_d", "smodels_m",
                "source_core_l", "Sbuild_d", "Scompile_d", "Senv_fill_d", "senv_fill_m",
                "senv_fill_unique_l", "Ssk_wit_d", "ssk_wit_m", "Ssk_choice_d", "ssk_choice_m",
                "Ssk_d", "ssk_m", "Ssk_closed_d", "ssk_closed_m", "Scoord_d", "scoord_m",
                "Sbound_d", "sbound_m", "Senv_agree_d", "senv_agree_m", "Stv_d", "stv_m",
                "Ssub_d", "ssub_m", "Selem_d", "selem_m", "selem_refl_l", "Selem_d.trans_l",
                "Smem_d", "smem_m", "smem_unique_l", "Ssk_mem_d", "ssk_mem_m", "ssk_mem_s", "Hsub_d", "hsub_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("lr_env_l", "lr_shift_l", "lr_all_m", "lr_and_m", "Lr_bound_d", "Lr_fiber_d",
                 "lr_fiber_m", "lr_bound_m", "Lr_family", "Lr_step_d", "lr_step_m", "lr_cover_s",
                 "Lr_next_d", "lr_next_m", "lr_iter_s", "lr_queries_l", "lr_rel_m", "Lr_reflect_d", "Lr_formula")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Fseq_space_d", "fseq_space_m", "Fseq_pair_d", "fseq_pair_m", "Fseq_snoc_d",
                 "fseq_snoc_m", "Fseq_at_d", "fseq_at_m", "Fseq_step_d", "fseq_step_m",
                 "fseq_env_l", "fseq_step_s", "Ord_image_d", "ord_image_m", "Fc_value_d", "fc_value_m",
                 "Fc_closed_d", "fc_closed_m", "Fc_step_d", "fc_step_m", "Fc_hull_d", "fc_hull_m",
                 "Fseq_end_d", "fseq_end_m", "fseq_end_unique_l", "fseq_end_rebuild_l", "Fc_slice_d", "fc_slice_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Fc_seed_d", "fc_seed_m", "Fc_trace_d", "fc_trace_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Sc_node_d", "sc_node_m", "Sc_rows_d", "sc_rows_m", "Sc_num_d", "sc_num_m", "Sc_sat_d", "sc_sat_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Oc_at_d", "oc_at_m", "Oc_pair_d", "oc_pair_m", "Oc_fold_d", "oc_fold_m", "Oc_seq_d", "oc_seq_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel." + name for name in
                ("Od_local_d", "od_local_m", "Od_code_d", "od_code_m", "Od_in_d", "od_in_m",
                 "Od_ext_d", "od_decoder_s", "Od_eval_d", "od_eval_m", "od_eval_s", "od_s", "Od_d", "od_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel." + name for name in
                ("Od_rank_d", "od_rank_m", "od_sigma_m", "Od_min_d", "od_min_m", "Od_pick_d", "od_pick_m",
                 "Od_choices_d", "od_choices_m", "Od_lt_d", "od_lt_m", "Hod_d", "hod_m", "hod_sigma_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("lr_truth_s", "Lr_truth_d", "lr_truth_m", "Vc_step_d", "vc_step_m", "Vc_d", "vc_matrix_m", "v_sigma_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel." + name for name in
                ("od_unique_s", "Od_graph_d", "od_graph_m", "od_graph_s", "ob_s", "Ob_d", "ob_m",
                 "Ob_eval_d", "ob_eval_m", "Ob_ext_d", "od_ex_m", "ob_subst_s", "Oa_seq_d", "oa_seq_m",
                 "Oa_param_d", "oa_param_m", "Oa_d", "oa_m", "Op_d", "Ha_d", "Hb_d", "Hp_d",
                 "ha_m", "ha_cut_s", "ha_rel_m", "oa_sep_s", "Hb_pick_d", "hb_pick_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Fs_tail_d", "YesMetaZFC.SetTheory.fs_tail_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Spred_d", "spred_m", "Smap_assign_d", "smap_assign_m", "Smap_d", "smap_m",
                 "Spred_emb_d", "spred_emb_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Descriptive." + name for name in
                ("Gm_even_d", "gm_even_m", "Gm_follows_d", "gm_follows_m", "Gm_win_d", "gm_win_m",
                 "Det_d", "det_m", "AD_d", "ad_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Wd_crit_d", "wd_crit_m", "Wd_witness_d", "wd_witness_m", "Wd_strong_d", "wd_strong_m",
                 "Woodin_d", "woodin_m", "Wd_proper_d", "wd_proper_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.spred_core_l"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Smap_assign_d.update_l", "Smap_row_d", "smap_row_m", "Smap_d.ssat_l", "Senv_update_d.agree_l", "Ssep_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in ("Sbin_d", "sbin_m", "Scollect_d", "sbin_update_l", "sbin_value_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.Suniform_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Sfun_d", "sfun_m", "Sfun_d.function_l", "Pe_assign_d", "pe_assign_m", "pe_atom_m",
                 "Pe_row_d", "pe_row_m", "Pe_state_d", "pe_state_m", "Pe_repr_d", "pe_repr_m",
                 "Pe_sat_d", "pe_sat_m", "Pe_holds_d", "pe_holds_m", "Rs_eval_d", "rs_eval_m", "Rs_los_d", "rs_los_m",
                 "Pe_repr_d.update_l", "Pe_assign_d.value_l", "Pe_assign_d.agree_right_l", "Rs_eval_d.repr_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.FilterZF.Rel_ultra_d.nor_l"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.FilterZF." + name for name in
                ("Pull_d", "pull_m", "Push_d", "push_m", "Pull_d.comp_l", "Push_d.comp_l", "Push_d.member_l", "push_id_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Rs_const_d", "rs_const_m", "rs_const_unique_l", "Rp_lift_d",
                 "rs_projection_id_l", "rs_projection_comp_l", "rs_projection_constant_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel." + name for name in
                ("Fn0_d.retarget_l", "Cp0_d.value_l", "Cp0_d.assoc_l", "Cp0_d.retarget_l",
                 "cp0_projection_id_l", "cp0_projection_comp_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Rp_eq_d", "rp_eq_m", "Rp_eq_d.symm_l", "Rp_rel_d", "rp_rel_m", "rp_rel_congr_l",
                "Rp_class_d", "rp_class_m", "Rp_map_d", "rp_map_m", "rp_kernel_l", "Rp_model_d", "rp_model_m",
                "Rp_holds_d", "rp_holds_m", "Rp_trace_d", "rp_trace_m", "Rp_update_d", "rp_update_m", "Rp_ex_d", "rp_ex_m",
                "Rp_column_d", "rp_column_m", "Rp_eval_d", "rp_eval_m", "Rp_los_d", "rp_los_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Ed_trace_d", "ed_trace_m", "Ed_filter_d", "ed_filter_m", "Ed_nonprincipal_d", "ed_nonprincipal_m",
                 "Ed_all_d", "ed_all_m", "Ed_complete_d", "ed_complete_m", "Measurable_d", "measurable_m",
                 "Eb_d", "eb_m", "Ef_family_d", "ef_family_m", "Ef_levels_d", "ef_levels_m",
                 "Ef_fiber_d", "ef_fiber_m", "Ef_image_fiber_d", "ef_image_fiber_m",
                 "Es_value_d", "es_value_m", "Es_family_d", "es_family_m", "Es_fiber_d", "es_fiber_m",
                 "Es_pull_d", "es_pull_m", "Es_reindex_d", "es_reindex_m", "Es_coherent_d", "es_coherent_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.FilterZF." + name for name in
                ("Base_d", "base_m", "Field_d", "field_m", "Rel_ultra_d", "rel_ultra_m", "Source_d", "source_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel.Fn0_d." + name for name in ("domain_eq_l", "mono_target_l", "ext_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel." + name for name in ("Cp0_d", "cp0_m", "cp0_unique_l", "cp0_mono_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Wf_rel_d", "wf_rel_m", "Wc_step_d", "wc_step_m", "Wc_graph_d", "wc_graph_m",
                 "Wc_value_d", "wc_value_m", "wf_rel_sat_l", "wc_step_sat_l", "wc_graph_sat_l",
                 "wc_value_sat_l", "wc_union_entry_l")]

CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Qt_equiv_d", "Qt_class_d", "qt_class_m", "Qt_map_d", "Di_order_d", "Di_system_d",
                 "Di_eq_d", "di_eq_m", "Di_rel_d", "di_rel_m", "Di_limit_d", "Di_sigma_d", "Di_wf_d",
                 "Di_system_d.eq_refl_l", "Di_eq_d.symm_l", "Di_system_d.eq_trans_l", "Di_system_d.eq_at_l",
                 "Di_system_d.rel_at_l", "Di_system_d.rel_congr_l", "Di_limit_d.commute_l", "di_sigma_of_top_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Wf_desc_d", "YesMetaZFC.SetTheory.FilterZF.Cc_d",
                "YesMetaZFC.SetTheory.FilterZF.cc_m", "YesMetaZFC.SetTheory.LargeCardinal.Ew_down_d",
                "YesMetaZFC.SetTheory.LargeCardinal.ew_down_m", "YesMetaZFC.SetTheory.LargeCardinal.ed_countable_l",
                "YesMetaZFC.SetTheory.LargeCardinal.ew_down_value_l"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Ec_value_d", "ec_value_m", "Ei_d", "ei_m", "Ei_map_d", "ei_map_m", "Em_family_d",
                 "Ec_ok_d", "ec_ok_m", "Ec_all_d", "ec_all_m", "Ec_level_d", "ec_level_m", "Ec_eval_d", "ec_eval_m",
                 "Ep_space_d", "ep_space_m", "Ep_fun_d", "ep_fun_m", "Ep_pull_d", "ep_pull_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.FilterZF.Mt_d", "YesMetaZFC.SetTheory.FilterZF.mt_m",
                "YesMetaZFC.SetTheory.Internal.Rp_atom_d", "YesMetaZFC.SetTheory.Internal.rp_atom_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.Di_step_d", "YesMetaZFC.SetTheory.Internal.di_step_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Ep_at_d", "ep_at_m", "Ep_rel_d", "ep_rel_m", "Ep_graph_d", "Ep_lift_d", "Ep_system_d",
                 "Ee_constraint_d", "ee_constraint_m", "Ee_hit_d", "ee_hit_m", "Ee_rep_d", "ee_rep_m",
                 "Ee_row_d", "ee_row_m", "Ee_test_d", "ee_test_m")]

CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("En_graph_d", "en_graph_m", "En_normal_d", "en_normal_m", "Ex_value_d", "ex_value_m",
                 "Ex_operator_d", "Ex_derived_d", "Ea_test_d", "ea_test_m", "Ea_part_d", "Ea_atoms_d",
                 "ea_part_m", "ea_atoms_m", "Ex_bp_at_d", "ex_bp_at_m", "Ex_bp_d", "Ex_pre_d", "Ex_short_d",
                 "em_family_m", "ex_complete_m", "ex_principal_m", "ex_nonprincipal_m", "ex_countable_m",
                 "ex_pre_m", "ex_short_m", "ex_pre_sat_l", "ex_short_sat_l", "It_local_d.read_l",
                 "Ex_product_d", "ex_product_at_m", "Ex_value_d.mono_l",
                 "Ex_operator_d.at_l", "Ex_operator_d.total_l", "ex_inter_l", "ea_test_read_l",
                 "ex_value_at_l", "ex_value_type_l", "ex_append_unique_l", "ex_prefix_cp_l")]

SKOLEM_MODULES = [
    'YesMetaZFC.Model.SetTheory.Reflection.RankSkolem',
    'YesMetaZFC.Model.SetTheory.Embedding.ElementaryTrace',
    'YesMetaZFC.SetTheory.FinitaryClub',
    'YesMetaZFC.SetTheory.FinitaryTrace',
    'YesMetaZFC.Model.SetTheory.ClassChoice',
    'YesMetaZFC.SetTheory.Card.Properties.SuccessorRegularity',
    'YesMetaZFC.SetTheory.Card.SmallUnion',
    'YesMetaZFC.SetTheory.HereditaryClosure',
    'YesMetaZFC.SetTheory.HereditaryAlgebra',
    'YesMetaZFC.SetTheory.HereditaryCover',
    'YesMetaZFC.SetTheory.IndexedChoice',
    'YesMetaZFC.SetTheory.CountableDirected',
    'YesMetaZFC.SetTheory.InnerModel.Condensation.Internal',
    'YesMetaZFC.Model.SetTheory.Internal.SeparationHull',
    'YesMetaZFC.Model.SetTheory.Internal.Uniformization',
    'YesMetaZFC.Model.SetTheory.Internal.UniformizationHull',
    'YesMetaZFC.Model.SetTheory.Source.Theory',
    'YesMetaZFC.Model.SetTheory.Source.Presentation',
    'YesMetaZFC.Model.SetTheory.Source.OmegaClosed',
    'YesMetaZFC.Model.SetTheory.Source.CollectionBasis',
    'YesMetaZFC.Model.SetTheory.Source.ClosureSyntax',
    'YesMetaZFC.SetTheory.HereditaryCollapse',
    'YesMetaZFC.SetTheory.InaccessibleEnumeration',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RelativeRankSegment',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemSource',
    'YesMetaZFC.SetTheory.InaccessibleHierarchy',
    'YesMetaZFC.SetTheory.HereditaryFunction',
    'YesMetaZFC.SetTheory.HereditarySequences',
    'YesMetaZFC.Model.SetTheory.Source.RankSizeInitial',
    'YesMetaZFC.SetTheory.Collapse.RegularRank',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptRegular',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableCover',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.ReflectHull',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.NiceReturn',
]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Rk_d", "rk_m", "Tc_d", "tc_m", "Hmem_d", "hmem_m", "H_d", "h_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Wc_ext_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("num0_m", "sop0_m", "Fb_node_d", "fb_node_m", "Fb_program_d", "fb_program_m",
                 "Se_update0_d", "se_update0_m", "Fv_arg_d", "fv_arg_m", "Fv_node_d", "fv_node_m",
                 "Fv_eval_d", "fv_eval_m", "Fv_space_d", "fv_space_m", "Fv_at_d", "fv_at_m",
                 "At_coherent_d", "At_prescribed_d", "At_elementary_d", "At_node_d", "at_coherent_m",
                 "at_prescribed_m", "At_test_d", "at_test_m", "At_cert_d", "at_cert_m", "at_witness_m",
                 "at_elementary_m", "at_node_m", "At_relative_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Fw_env_d", "fw_env_m", "Fw_cert_d", "fw_cert_m", "fw_witness_m", "Fw_source_d",
                 "sh_product_m", "sh_bijection_m", "sh_value_m", "sh_closed_m", "sh_codes_m", "sh_sequences_m",
                 "sh_choice_m", "sh_select_m", "sh_skolem_m", "Sh_hull_d", "sh_hull_m", "sh_input_m",
                 "Sh_data_d", "Sh_source_d", "sh_output_m", "sh_source_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in ("Wc_iso_d", "wc_iso_m", "wc_ext_m", "Wc_map_d", "wc_map_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in ("Sc_wf_d", "Sc_collapse_d", "sc_collapse_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Sc_branch_d", "Sc_hierarchy_d", "sc_hierarchy_m", "Sc_algebra_d", "sc_algebra_m", "sc_total0_m",
                 "Sc_index_d", "sc_index_m", "Sc_small_d", "sc_small_m", "Sc_uniform_d", "Sc_collection_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Descriptive.Tb_step_d", "YesMetaZFC.SetTheory.Descriptive.tb_step_m",
                "YesMetaZFC.SetTheory.LargeCardinal.Er_level_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.ep_binary_pair_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Sc_regular_d", "sc_seq_index_m", "sr_pair_env_l", "Sb_chain_d", "sb_chain_m",
                 "Sb_edge_d", "sb_edge_m", "Sb_bad_d", "sb_bad_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.Sc_omega_bound_d", "YesMetaZFC.SetTheory.Internal.sc_omega_bound_m",
                "YesMetaZFC.SetTheory.LargeCardinal.ec_count_value_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Di_stage_d", "di_stage_m", "Di_elementary_d", "Di_row_d", "di_row_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.Ee_value_d", "YesMetaZFC.SetTheory.LargeCardinal.ee_value_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Vr_d", "YesMetaZFC.SetTheory.KPair_d.mem_l"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Ep_comparison_d", "Ep_length_d", "Su0_d", "su0_m", "Er_enum_d", "er_enum_m",
                 "Er_stage_d", "er_stage_m", "Er_hit_d", "er_hit_m", "Er_hit_d.bound_l", "Eb_collapse_d", "Eb_trace_d")]
ZFC_BASELINE = BASELINE
CHOICE_FREE += ["YesMetaZFC.SetTheory.Rr_d", "YesMetaZFC.SetTheory.rr_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("It_embedding_d", "It_return_at_d", "It_return_d", "It_hull_return_d", "Ja_enum_d", "Ja_rows_d", "Ja_commute_d", "Ja_node_d",
                 "Ja_extend_d", "ja_elementary_m", "ja_rows_m", "ja_commute_m", "ja_node_m", "ja_extend_m",
                 "Ja_value_d", "ja_value_m", "Ja_cell_d", "ja_cell_m", "Ja_space_d", "Ja_seen_d", "ja_seen_m",
                 "Ja_path_d", "Ja_observe_d", "ja_observe_m", "Ja_leg_d", "ja_leg_m")]
# 全背景见证选择及商赋值代表选择允许对象 AC；给定源理论后的源内部 Łoś 按 ZF 审计。
LOS_MODULES = [
    'YesMetaZFC.Model.SetTheory.ReducedPower.Los',
    'YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel',
    'YesMetaZFC.Model.SetTheory.ReducedPower.Projection',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.SourceProjection',
    'YesMetaZFC.Model.SetTheory.Source.Relation',
    'YesMetaZFC.Model.SetTheory.Relations.CollectCode',
    'YesMetaZFC.Model.SetTheory.Relations.FunctionFamily',
    'YesMetaZFC.Model.SetTheory.ReducedPower.DeltaImage',
    'YesMetaZFC.Model.SetTheory.Relations.Separation',
    'YesMetaZFC.Model.SetTheory.Source.CollectionBasis',
    'YesMetaZFC.Model.SetTheory.Relations.Collection',
    'YesMetaZFC.Model.SetTheory.Relations.Constant',
    'YesMetaZFC.Model.SetTheory.Relations.Ultrafilter',
    'YesMetaZFC.Model.SetTheory.Relations.PointwiseWitness',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationNormalize',
    'YesMetaZFC.Model.SetTheory.Relations.SeparationSource',
    'YesMetaZFC.Model.SetTheory.Relations.Small',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationRestriction',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationSuccessor',
    'YesMetaZFC.Model.SetTheory.Relations.Composition',
    'YesMetaZFC.Model.SetTheory.Relations.Parity',
    'YesMetaZFC.Model.SetTheory.Relations.Hierarchy',
    'YesMetaZFC.Model.SetTheory.Relations.FunctionCapture',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationProjection',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationTrace',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationMeasure',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull',
    'YesMetaZFC.SetTheory.Collapse.RelationRealization',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.FunctionValue',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SeedCollapse',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedRaw',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedRealization',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyClass',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawProjection',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRank',
    'YesMetaZFC.Model.SetTheory.Game.NodeEmbedding',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Trace',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Limit',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.DerivedLimit',
    'YesMetaZFC.Model.SetTheory.ReducedPower.FullElementary',
    'YesMetaZFC.Model.SetTheory.ReducedPower.FullEmbedding',
    'YesMetaZFC.Model.SetTheory.ReducedPower.Copy',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.CopyApplication',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Value',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.TupleValue',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.ValueBound',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SuccessorApplication',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.CopySuccessor',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraSupport',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.Fork',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.TreeSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RankCover',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinTypeStep',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Strength',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawExactHistory',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.SubtypeStretch',
    'YesMetaZFC.SetTheory.LargeCardinal.Types.OneStep',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.Branch',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalRead',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceLimit',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceNode',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.LocalAgreement',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceTrace',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceSubsets',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceSuccessors',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RankAgreement',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.CopySubsets',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.OmegaClosed',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.ValueApply',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SetInclusion',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.SetCopy',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.Descent',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.Reflection',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.InitialPull',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyRow',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyHistory',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyExtend',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyPadding',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyTree',
    'YesMetaZFC.SetTheory.CumulativeRegularCover',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.NiceReturn',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraCertificate',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.HullReturn',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableLimit',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.WeakAnswer',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.Weak',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.RelativeStart',
    'YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer',
    'YesMetaZFC.Model.SetTheory.Source.BinaryRelation',
    'YesMetaZFC.Model.SetTheory.Relations.OmegaCut',
    'YesMetaZFC.Model.SetTheory.Relations.LayerSeparation',
    'YesMetaZFC.Model.SetTheory.Relations.RecordImage',
    'YesMetaZFC.Model.SetTheory.Internal.MembershipSlice',
    'YesMetaZFC.Model.SetTheory.Relations.LayerMeasure',
    'YesMetaZFC.Model.SetTheory.Relations.LayerComposition',
    'YesMetaZFC.Model.SetTheory.Relations.NativeRank',
    'YesMetaZFC.Model.SetTheory.Relations.CrossMeasure',
    'YesMetaZFC.Model.SetTheory.Relations.CrossProjection',
    'YesMetaZFC.Model.SetTheory.Relations.CrossCapture',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationCrossBounded',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Continue',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.RunMove',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.PastEvents',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.TreeStep',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.EvenLimit',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.ShiftedStrategy',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.ReturnBranch',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawPresent',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawStrength',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedIdentity',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.LevelTransfer',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawGraphSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawColimit',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawEvaluation',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawConstant',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationFormulaImage',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationApplication',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawApplication',
    'YesMetaZFC.Model.SetTheory.Relations.OmegaEvaluation',
    'YesMetaZFC.Model.SetTheory.Source.ClosureSyntax',
    'YesMetaZFC.SetTheory.KP.TransitiveInduction',
    'YesMetaZFC.SetTheory.CumulativeComparison',
    'YesMetaZFC.Model.SetTheory.Relations.RankImage',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.ActivityRead',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyQuality',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAgreementRead',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawMembershipSystem',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Padding',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCountable',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableCover',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptRegular',
    'YesMetaZFC.SetTheory.LargeCardinal.Cardinals.EmbeddingSetImage',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptCoordinates',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyNice',
]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("eb_pool_m", "ep_indices0_m", "eb_collapse_m", "es_strength0_m", "ex_strength0_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.Pn_agree_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.rr_rel_m", "YesMetaZFC.SetTheory.Internal.Sr_sep_d"]
RELATION_CODES = ["YesMetaZFC.SetTheory.Internal." + name for name in
                  ("Rf_ext_d", "rf_ext_m", "Rf_val_d", "rf_val_m", "Rf_fun_d", "rf_fun_m", "Rf_const_d", "rf_const_m",
                   "Rt_trace_d", "rt_trace_m", "Rt_source_d", "Rc_graph_d", "rc_graph_m",
                   "Rc_eval_d", "rc_eval_m", "Rc_holds_d", "rc_holds_m", "Rc_los_d", "rc_los_m", "Rf_pull_d", "rf_pull_m", "Rc_family_d", "rc_family_m",
                   "Rr_closed_d", "Rf_small_d", "Rr_small_d", "rr_closed_m", "rr_small_m", "Rr_rank_d")]
CHOICE_FREE += RELATION_CODES
RAW_EXTENDER_CODES = ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                      ("Eg_graph_d", "Eg_transition_d", "Er_component_d", "er_component_m", "Er_system_d",
                       "Er_value_d", "er_value_m")]
CHOICE_FREE += RAW_EXTENDER_CODES
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.Fs_read_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("ep_source_m", "Pn_model_d", "pn_model_m", "Pn_row_d", "pn_row_m", "pn_agree_m",
                 "Pn_cell_d", "pn_cell_m", "Pn_past_d", "pn_past_m", "Pn_history_d", "pn_history_m", "It_nice_d", "It_cut_d",
                 "Ic_model_d", "ic_model_m", "ic_core0_m", "ic_core_m", "Ic_row_d", "ic_row_m", "Ic_cell_d", "ic_cell_m", "Ic_at_d", "ic_at_m",
                 "Ic_edge_d", "ic_edge_m", "Ic_past_d", "ic_past_m", "Ic_operation_d", "ic_operation_m", "Ic_history_d", "ic_history_m", "Ic_state_d", "ic_state_m",
                 "Ic_extend_d", "ic_extend_m", "Ic_move_d", "ic_move_m", "it_pred_m", "it_order_m", "it_diagram_m",
                 "ea_agree_m", "ep_graph_m", "ep_lift_m", "ep_system_m", "ep_constants_m", "it_ultra_m", "it_source_m", "it_payload_m",
                 "Ja_lift_d", "ja_lift_m", "Jr_value_d", "jr_value_m", "It_ladder_d", "it_ladder_m", "Tg_odd_node_d", "Tg_odd_cofinal_d",
                 "Tg_odd_edge_d", "Tg_odd_tail_d", "It_pull_subset_d", "Tg_return_node_d", "Tg_return_growth_d", "Tg_odd_compatible_d", "Tg_odd_limit_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("Tg_return_model_d", "Tg_shifted_d", "It_critical_bound_d", "it_critical_bound_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in ("di_order_m", "di_system_m", "di_limit_m")]
LOS_CHOICE_FREE = ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                   ("Ep_source_d", "Ep_component_d", "ep_component_m", "Ep_arrow_d", "ep_arrow_m", "Ep_limit_d",
                    "Ep_collapse_d", "Ee_node_d", "ee_node_m", "ee_node_pair_l", "Ee_factor_d", "Ep_derived_limit_d")]
LOS_CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                   ("Ep_constants_d", "Ep_realizer_d", "Ep_strength_d", "Ep_strong_limit_d", "Es_strength_d", "es_strength_m", "Ex_strength_d")]
LOS_CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.rp_change_filter_l", "YesMetaZFC.SetTheory.Internal.rp_lift_unique_l"]
LOS_CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.rr_rel_m", "YesMetaZFC.SetTheory.Internal.Sr_sep_d", *RELATION_CODES, *RAW_EXTENDER_CODES]
LOS_ZF_BOUNDS = {"YesMetaZFC.SetTheory.LargeCardinal.ep_branch_reflection_l": BASELINE, "YesMetaZFC.SetTheory.Internal.rp_lift_exists_l": BASELINE}
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("sfm_template_l", "sfm_total_raw_l", "sfm_function_raw_l", "sfm_uniform_raw_l",
                      "Sc_uniform_d.raw_l", "Sc_uniform_d.on_l", "sfm_sep_test_raw_l", "sfm_sep_raw_l", "sc_separation_raw_l",
                      "sc_constant_raw_l", "Smap_d.pe_context_l", "pe_compile_bound_l", "pe_value_exists_l",
                      "Smap_d.pe_trace_raw_l", "rt_source_exists_l", "sc_pe_witness_raw_l", "rc_los_l", "rc_satisfies_l",
                      "sc_separate_raw_l", "sc_cut_raw_l", "Smap_d.subsets_raw_l", "Rt_source_d.recover_l",
                      "Rt_source_d.field_l", "Smap_d.small_raw_l", "rc_atom_trace_l", "rc_restrict_model_l",
                      "rc_code_constants_l", "rc_constant_embedding_l", "sc_compose_raw_l", "rf_pull_exists_l",
                      "rr_realize_delta_l", "rr_realize_function_l", "rr_realize_product_l", "rr_realize_rank_l",
                      "rr_capture_l", "rr_capture_function_l", "rr_power_l",
                      "rr_bounded_functions_l", "Rc_graph_d.pull_l", "rc_pullback_family_l", "rc_full_trace_l",
                      "Rt_source_d.pull_l", "sc_bound_raw_l", "rc_bounded_representative_l", "Rp_model_d.low_cover_raw_l",
                      "rc_successor_l", "Rp_model_d.unique_l", "Smap_d.measure_raw_l",
                      "Rf_small_d.index_l", "Smap_d.rr_closed_l", "Smap_d.rr_small_l", "rr_rank_low_l") })
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("Ep_strength_d.above_l", "Ep_strong_limit_d.type_image_l", "ec_raw_push_l",
                      "eg_graphs_l", "Eg_graph_d.system_l", "Eg_graph_d.elementary_l", "er_components_l",
                      "er_component_exists_l", "Er_component_d.unique_l", "Er_system_d.model_l",
                      "Er_system_d.bounded_l", "Er_system_d.bound_mem_l", "Er_system_d.bounded_value_l",
                      "Er_system_d.reindex_l", "Er_system_d.constant_l", "er_repr_atoms_l", "er_edge_iff_l", "Eb_collapse_d.next_raw_l")})
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("Em_family_d.rank_mem_l", "es_strength_relative_l", "es_strength_map_l", "Ex_strength_d.map_l", "Ex_strength_d.realize_l",
                      "Ep_strong_limit_d.rank_l")})
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("Ep_source_d.space_l", "Ep_source_d.space_mem_l", "Ep_source_d.function_l", "Ep_source_d.uniform_l",
                      "Ep_source_d.projection_l", "Ep_source_d.family_l", "Ep_source_d.model_l", "Ep_source_d.successor_l",
                      "Ep_source_d.finite_index_l", "ep_constant_limit_l", "ep_collapse_l",
                      "es_source_push_l", "Ep_limit_d.factor_l", "ep_representatives_l", "ep_relation_l", "ep_arrow_id_l")})
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.ep_support_cover_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.It_local_d.closed_wf_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.It_local_d.function_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.ep_value_constant_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.ep_value_support_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.Internal.rp_matrix_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.ep_copy_identity_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.Ep_source_d.rebase_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.it_apply_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.er_stage_l"] = BASELINE
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("em_family_relative_l", "ec_coherent_relative_l", "It_local_d.measures_l",
                      "It_local_d.coherent_l", "It_local_d.bounded_model_l", "ea_atoms_relative_l", "en_normal_relative_l",
                      "It_local_d.atoms_l", "It_local_d.normal_l")})
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("Wi_history_d.last_keep_l", "wi_answer_root_l", "Wi_selector_d.answer_l",
                      "Wi_input_d.unique_l", "Wi_drive_d.unique_l", "Wi_public_d.unique_l")})
ZF_BOUNDS = {"YesMetaZFC.SetTheory.Internal.Ssk_d." + name: BASELINE for name in
             ("value_l", "closed_l", "point_mem_l")}
ZF_BOUNDS["YesMetaZFC.SetTheory.InnerModel.jc_internal_l"] = BASELINE
ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                  ("sc_separation_raw_l", "Sc_theory_d.pull_l", "Sc_collection_d.pull_l", "smap_uniform_l", "sc_collection_iff_l", "Sc_collection_d.map_l", "Sc_theory_d.map_l",
                   "sc_wf_relative_l", "sc_collapse_sat_l", "sc_collapse_iff_l", "Sc_collapse_d.collapse_l",
                   "sc_v_collapse_l", "sc_v_branch_l", "sc_sequences_iff_l", "sc_v_sequences_l",
                   "sc_total0_delta_l", "sc_total0_sat_l", "sc_algebra_sat_l", "sc_algebra_iff_l", "sc_v_pair_l",
                   "Sc_algebra_d.kpair_l", "Sc_algebra_d.insert_l", "Sc_algebra_d.envelope_l",
                   "sc_index_delta_l", "sc_index_sat_l", "Sc_index_d.of_injection_l", "Sc_index_d.bound_l", "Sc_index_d.mono_l",
                   "Sc_small_d.mono_l", "sc_small_sat_l", "Smap_d.small_l", "sc_ordinal_small_l", "sc_small_image_l", "sc_index_image_l", "Sc_index_d.restrict_l", "sc_infinite_index_l",
                   "Sc_sequences_d.small_l", "sc_seq_index_sat_l", "sc_small_pull_l")})
ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal.Er_level_d." + name: BASELINE for name in
                 ("map_l", "rank_l", "restriction_l")})
ZF_BOUNDS["YesMetaZFC.SetTheory.ZF.h_collapse_image_l"] = BASELINE
ZF_BOUNDS["YesMetaZFC.SetTheory.Internal.scode_rank_mem_l"] = BASELINE
ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.ep_rank_restriction_l"] = BASELINE
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Senv_tail_d", "senv_tail_m", "Sall_d", "sall_m", "Sc_theory_d", "Sc_sequences_d", "Sc_power_d", "sc_power_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Sc_cover_d", "sc_cover_m", "Sb_hull_d", "sb_hull_m", "smem_formula_l", "rt_pair_l",
                 "Sc_inaccessible_d", "sc_inaccessible_m", "Sc_rank_size_d", "sc_rank_size_m",
                 "Sc_inaccessible_closure_d", "sc_inaccessible_closure_m", "Sc_omega_closed_d", "sc_omega_closed_m",
                 "Sc_bounded_omega_closed_d", "sc_bounded_omega_closed_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Eb_space_d", "eb_space_m", "Eb_node_d", "eb_node_m", "Eb_point_d", "eb_point_m",
                 "Eb_constraint_d", "eb_constraint_m", "Eb_edge_d", "eb_edge_m", "Eb_link_d", "eb_link_m",
                 "Eb_pool_d", "Eb_value_d", "eb_value_m", "Ec_ok0_d", "ec_ok0_m", "Ec_all0_d", "ec_all0_m",
                 "Ec_level_at_d", "ec_level_at_m", "Eb_witness_d", "eb_witness_m", "Eb_eval_d", "eb_eval_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.Pe_context_d", "YesMetaZFC.SetTheory.Internal.pe_context_m",
                "YesMetaZFC.SetTheory.FilterZF.Sf_ultra_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Em_source_d", "Ec_source_d", "Ea_agree_d", "Ea_subset_d", "Ea_maps_d", "Ec_class_d", "ec_class_m",
                 "Ec_node_d", "ec_node_m", "Ec_limit_d")]
LOS_CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.Ec_ultrapowers_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("En_source_d", "Ep_repr_d", "ep_repr_m", "Ep_coord_d", "ep_coord_m", "Ep_seed_d", "ep_seed_m", "ep_pair_at_m")]
LOS_CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                    ("Ep_value_d", "ep_value_m", "ep_subspace_m", "Ep_successor_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("It_pred_d", "It_order_d", "It_map_d", "it_map_m", "It_comp_d", "it_comp_m", "It_diagram_d",
                 "It_next_d", "it_next_m", "It_source_d", "It_local_d", "It_ultra_d", "It_payload_d", "It_active_d",
                 "It_step_d", "It_limit_d", "It_tree_d", "It_extension_d", "It_image_d", "it_image_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("It_branch_d", "It_tag_d", "It_arrow_d", "it_arrow_m", "It_system_d",
                 "It_project_d", "it_project_m", "It_cone_d", "It_finish_d", "it_finish_m",
                 "It_wf_branch_d", "It_ill_branch_d", "It_realizer_d", "It_value_d", "it_value_m", "It_limit_extension_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.InnerModel.Rd_quad_d", "YesMetaZFC.SetTheory.InnerModel.rd_quad_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("it_branch_m", "it_tag_m", "it_system_m", "it_embedding_m", "it_cone_m", "wi_limit_m",
                 "Wi_state_d", "Wi_extension_d", "Wi_limit_d", "Wi_keep_d", "Wi_at_d", "Wi_history_d",
                 "Wi_tree_d", "Wi_past_d", "Wi_success_d", "Wi_continuous_d", "Wi_answer_d",
                 "wi_state_m", "wi_keep_m", "wi_at_m", "wi_past_m", "wi_history_m", "wi_tree_m",
                 "wi_success_m", "wi_continuous_m", "wi_answer_m", "Wi_request_d", "wi_request_m",
                 "Wi_selector_d", "wi_select_m", "Wi_input_d", "wi_input_m", "Wi_drive_d", "wi_drive_m",
                 "wi_drive_schema", "Wi_run_d", "wi_run_m", "Wi_legal_d", "Wi_reply_d",
                 "Wi_position_d", "wi_position_m", "Wi_public_d", "wi_public_m", "Wi_strategy_d", "Wi_play_d")]
LOS_CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.Wi_winning_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Tn_name_d", "tn_name_m", "Tn_names_d", "Tn_value_d", "tn_value_m", "Tn_assign_d", "tn_assign_m",
                 "Tt_query_d", "tt_query_m", "Tt_pool_d", "Tt_truth_d", "Tt_realized_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
                ("Fp_shift_d", "fp_shift0_m", "Fp_tag_d", "fp_tag0_m", "Fp_pair_d", "fp_pair0_m", "Fp_d",
                 "Fs_trace_d", "fs_trace_m", "Fs_code_d", "fs_code_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Ft_arg_d", "ft_arg_m", "Ft_node_d", "ft_node_m", "Ft_eval_d", "ft_eval_m",
                 "Ft_sat_d", "ft_sat_m", "ft_local_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Sref_d", "Sr_at_d", "sr_at_m", "Sr_rule_d", "sr_rule_m",
                 "Sr_context_d", "sr_context_m", "Sr_row_d", "sr_row_m", "Sr_state_d", "sr_state_m",
                 "Sr_and_d", "sr_and_m", "Sr_top_d", "Sr_top_code_d", "sr_top_code_m",
                 "Sr_minus_d", "sr_minus_m", "Tm_code_d", "tm_code_m", "Tm_query_d", "tm_query_m",
                 "Tm_minus_d", "tm_minus_m", "Tt_slots_d", "tt_slots_m", "Tm_table_d", "tm_link0_m", "tm_cut0_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Sv_max_d", "sv_max_m", "sv_last_m", "Ft_prev_d", "ft_prev_m", "ft_prev_local_m", "Sg_all_d", "sg_all_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Sx_node_d", "sx_node_m", "Sx_program_d", "sx_program_m", "Sx_graph_d", "sx_graph_m",
                 "Sx_row_d", "sx_row_m", "Sc_flat_d", "sc_flat_m", "sc_flat_local_m", "sc_num_local_m",
                 "Tr_tag_d", "tr_tag_m", "Tr_zero_d", "Tr_step_d", "tr_zero_m", "tr_step_m",
                 "Tr_roles_d", "tr_roles_m", "Tr_prog_d", "tr_prog_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("lp_rel_m", "ft_lower_m", "sc_lower_s", "sc_lower_m", "fp_entry0_m", "Tf_value_d", "tf_value0_m",
                 "Tf_fill_d", "tf_fill0_m", "Tf_dom_d", "tf_dom0_m", "tf_query_s", "tf_query_m",
                 "tf_prev_s", "tf_prev_m", "tf_type_m", "tf_type_local_m", "St_pack_d", "st_pack_m", "st_unpack_s")]
LOS_CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.Et_stretch_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("fs_space0_m", "tn_names0_m", "tt_pool0_m", "tt_constants0_m", "tf_kappa_s", "tf_kappa_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Eb_const_d", "eb_const_m", "ex_local_m", "ex_inaccessible_m", "ex_strength_m", "ex_quality_m",
                 "Eb_stretch_d", "et_stretch0_m", "et_stretch_m", "et_quality_m", "Ee_step_d", "ee_step_s", "ee_step_m",
                 "Ee_realized_d", "ee_realized_s", "ee_realized_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("Ee_queries_d", "Ee_defined_d", "Ee_elastic_d", "Ee_minus_d", "ee_elastic_m", "Ee_language_d")]
# 完整实现及编译证书含已有平坦配对的 Prop 证明，适用通用公理边界；纯查询和关系数据另禁选择。
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
                ("Tp_perm_d", "tp_perm0_m", "ts_guard_m", "ts_below_s",
                 "ts_below_m", "ts_template_m",
                 "Ts_names_d", "Ts_query_d", "Ts_subtype_d", "Ts_up_d", "ts_up0_m")]
LOS_CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.Ee_one_step_d"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Li_type_d", "li_type_m", "Tt_realized_d.point_env_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Tm_assign_d", "tm_assign0_m", "tm_type_m", "tm_type_f", "tm_params_l", "Tm_move_d", "Tm_quote_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("Li_pair_d", "li_pair_m", "Li_least_d", "li_least_m", "Li_finite_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Sg_any_d", "sg_any_m", "Sg_set_d", "sg_set_m", "Tg_graph_d", "tg_graph_m",
                "Tg_join_d", "tg_join_m", "Tg_node_d", "tg_node_m", "Tg_node_query_d",
                "Tg_root_query_d", "tg_root_m", "Tg_max_query_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Td_name_d", "td_name_m", "Td_column_d", "td_column_m", "Td_query_d", "td_query_m",
                "Td_project_d", "td_project_m", "Td_dcp_d", "td_dcp_m", "Tg_bound_d", "tg_bound_m",
                "Tg_bound_query_d", "Tg_height_d", "tg_height_m", "Tg_height_query_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("Tg_elastic_d", "tg_elastic_m", "Tg_reply_queries_d", "Tg_reply_d", "Tg_reply_language_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("tt_pool_m", "tt_truth_m", "tt_realized_m", "sr_rel_m", "sc_inaccessible_raw_m",
                "ts_values_m", "ts_compile_m", "ts_columns_m", "ts_program_m", "tg_node_query_m",
                "tg_root_query_m", "tg_max_query_m", "tg_bound_raw_m", "tg_height_raw_m", "tg_bound_query_m",
                "tg_height_query_m", "tp_perm_raw_m", "ts_at_m", "tx_exceeds_m", "ts_names_m", "ts_query_m", "ts_subtype_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("et_stretch_raw_m", "ee_step0_m", "ee_read_m", "ee_successor_m", "ee_domain_m", "ee_inacc_m",
                "ee_language_m", "ee_packet_m", "tg_program_packet_m", "tg_reply_language_m", "tg_query_request_m",
                "tg_query_packet_m", "tg_query_key_m", "tg_aux_data_m", "tg_ee_data_m", "tg_query_data_m",
                "tg_program_data_m", "tg_event_m", "tg_digits_m", "tg_reset_m", "tg_growth_m", "tg_continue_m",
                "tg_aux_m", "tg_aux0_m", "tg_continue0_m", "tg_issued_aux0_m", "tg_issued0_m",
                "tg_context_data_m", "tg_saved_record0_m", "Tg_saved_d", "Tg_saved_code_d", "tg_saved_code0_m", "tg_saved_code_m", "tg_saved_m",
                "tg_past_cell_m", "tg_past_at_m", "tg_past_links_m", "tg_past_m", "Tg_past_fixed_d", "Tg_past_update_d",
                "tg_index_m", "Tg_round_event_d", "tg_round_event_m", "tg_round_event0_m", "tg_event_in0_m",
                "tg_trace0_m", "Tg_trace_d", "tg_trace_m", "Tg_saved_trace_d", "tg_saved_trace0_m",
                "tg_saved_trace_m", "Tg_past_events_d", "tg_past_events_m",
                "Tg_request_d", "Tg_saved_high_d", "tg_saved_high0_m", "tg_saved_high_m", "tg_anchor_m",
                "Tg_past_roots_d", "tg_past_roots_m", "Tg_tree_step_d", "Tg_run_d", "Tg_run_next_d",
                "Tg_saved_branch_d", "tg_saved_branch0_m", "tg_saved_branch_m", "Tg_odd_d", "tg_odd_m",
                "it_strength_m", "it_active_m", "it_tree_m", "it_pnice_m", "it_extension_m",
                "tg_run_m", "Tg_run_code_d", "tg_run_code0_m", "tg_run_code_m", "tg_run_next_m",
                "Tg_run_edge_d", "tg_run_edge0_m", "tg_run_edge_m",
                "Tg_tree_keep_d", "tg_tree_keep_m", "Tg_run_keep_d", "tg_run_keep0_m", "tg_run_keep_m",
                "Tg_run_value_d", "tg_run_value0_m", "Tg_sequence_d", "Tg_even_d", "tg_even0_m",
                "Tg_limit_value_d", "tg_limit_value0_m", "tg_limit_value_m",
                "tg_reply_m", "tg_answer_m", "tg_step_m", "tg_check_m", "Tg_aux_data_d",
                "Tg_ee_data_d", "Tg_query_data_d", "Tg_program_data_d", "Tg_params_d", "Tg_params_d.map_l", "Tg_params_d.closed_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Descriptive." + name for name in
               ("Cg_first_d", "cg_first_m", "Cg_bad_d", "Cg_safe_d", "Cg_payoff_d", "Cg_legal_d",
                "Cg_follows_d", "Cg_win_d", "cg_follows_m", "cg_win_m",
                "Cg_tail_follows_d", "cg_tail_follows_m", "Cg_tail_win_d", "cg_tail_win_m", "Cg_ii_d",
                "Cg_splice_d", "cg_splice_m", "Cg_avoid_d", "cg_avoid_m", "Cg_det_d", "cg_det_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("woodin0_m", "tg_low0_m", "tg_low_m", "tg_image_m", "tg_seed_m", "tg_seed0_m", "tg_successor_m", "tg_successor0_m",
                "tg_renewal_m", "tg_context_m", "Tg_context_d", "tg_reply0_m", "Tg_reply_in_d",
                "tg_round_m", "tg_witness0_m", "tg_round0_m", "tg_round_env_d", "tg_kernel_m",
                "ti_image_m", "tc_image_m", "tc_seed0_m", "tc_result0_m", "tc_transfer_m",
                "Tg_query_base_d", "tg_query_base_m", "Ee_numeric_d", "Ee_stretch_read_d", "Ee_stretch_program_d",
                "Ee_stretch_code_d", "Ee_largest_program_d", "Ee_inacc_program_d", "ee_numeric0_m", "ee_numeric_m",
                "ee_largest_program0_m", "ee_largest_program_m", "ee_inacc_program0_m", "ee_inacc_program_m",
                "ee_stretch_program0_m", "ee_stretch_program_m", "ee_stretch_code_m", "ee_stretch_read_m",
                "ee_realized0_m", "ee_language0_m", "ee_rebuild_seed_m", "ee_rebuild_m",
                "tg_candidate0_m", "tg_subtype0_m", "Tg_subtype_in_d", "Tg_realized_in_d",
                "tc_realize_seed0_m", "tc_realize_result0_m", "tc_realize_m", "Tg_anchor_d",
                "Tg_reply_base_d", "tg_reply_base0_m", "tg_reply_base_m", "tq_basis_m", "tg_query_base0_m", "tg_query_row0_m",
                "ee_domain_pack0_m", "ee_domain_pack_m", "tc_rigid_seed0_m", "tc_rigid_m",
                "tc_recover_seed0_m", "tc_recovered_m", "tc_recovered0_m", "tc_recover_result0_m", "tc_recover_m",
                "tg_restart_env_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Descriptive." + name for name in
               ("Cg_rank_d", "cg_rank0_m", "cg_rank_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Ts_column_d", "ts_column_m", "Ts_rebound_d", "ts_rebound_m", "Tt_program_d", "Tt_code_d",
                "Tg_guard_program_d", "Tg_guard_code_d", "tt_code0_m", "tt_code2_m", "tg_guard_code_m",
                "tg_guard_program0_m", "tg_guard_program_m", "ts_program0_m", "ts_numeric0_m", "ts_numeric_m",
                "Ts_program_in_d", "tt_realized0_m", "ts_at0_m", "tx_exceeds0_m")]
# HOD 的对象 AC 定理保持原背景假设；选择句子的闭合性证书由内核检查。
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in ("Rt_coord_d", "rt_coord0_m", "rt_coord_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("Tg_root_tree_d", "tg_root_tree_m", "Tg_common_tree_d", "tg_common_tree_m",
                "Tg_run_name_d", "tg_run_name0_m", "tg_run_name_m", "tg_play_body0_m", "tg_play0_m", "Tg_play_d", "tg_play_m",
                "Tg_saved_play_d", "tg_saved_play0_m", "tg_saved_play_m", "Tg_past_play_d", "tg_past_play_m",
                "tg_return_node0_m", "tg_return_node_m", "Tg_return_row_d", "tg_return_row_m", "Tg_return_sequence_d",
                "Tg_return_union_d", "Tg_return_tree_d", "Tg_cofinal_branch_d",
                "Tg_real_d", "tg_real_m", "Tg_turn_move_d", "tg_turn_move_m",
                "Tg_run_real_d", "tg_run_real_m", "Tg_run_move_d", "tg_run_move_m", "Tg_run_choice_d",
                "Tg_response_d", "tg_response_m", "Tg_archive_play_d", "Tg_projection_d", "tg_projection_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Descriptive." + name for name in ("Gi_input_d", "gi_input_m", "Gi_d", "gi_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in ("Fseq_recode_d", "fseq_recode_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("Tg_level_d", "tg_level_m", "Tg_level_key_d", "tg_level_key_m", "Tg_level_table_d",
                "Tg_tracked_d", "tg_tracked_m", "Tg_projection_win_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Descriptive." + name for name in ("Tr_pull_d", "tr_pull_m", "Tr_shift_d", "tr_shift_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("Tv_drop_value_d", "tv_drop_value_m", "Tv_drop_d", "Tp_projection_d", "tp_projection_m", "Tp_win_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("Tp_left_d", "Tp_filter_d", "Td_cover_d", "td_cover_m", "tp_win_m", "td_cover0_m",
                "td_checks_m", "td_order_m", "td_parameters_m", "td_names_m", "td_input_m", "Td_input_d",
                "td_output_m", "Tp_certificate_d", "Td_winner_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Pe_d"]
RELATIVE_INITIAL_MODULES = [
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.RelativeStart',
]
ZFC_CODE_MODULES = [
    'YesMetaZFC.Model.SetTheory.Reflection.ZfcTransfer',
    'YesMetaZFC.Model.SetTheory.Source.BinaryRelation',
    'YesMetaZFC.Model.SetTheory.Relations.CollectCode',
]
LAYER_MODULES = [
    'YesMetaZFC.Model.SetTheory.Relations.Parity',
    'YesMetaZFC.Model.SetTheory.Relations.OmegaCut',
    'YesMetaZFC.Model.SetTheory.Relations.LayerSeparation',
    'YesMetaZFC.Model.SetTheory.Relations.CollectCode',
    'YesMetaZFC.Model.SetTheory.Relations.RecordImage',
    'YesMetaZFC.Model.SetTheory.Internal.MembershipSlice',
    'YesMetaZFC.Model.SetTheory.Relations.Ultrafilter',
    'YesMetaZFC.Model.SetTheory.Relations.LayerMeasure',
    'YesMetaZFC.Model.SetTheory.Relations.LayerComposition',
    'YesMetaZFC.Model.SetTheory.Relations.NativeRank',
    'YesMetaZFC.Model.SetTheory.Relations.CrossMeasure',
    'YesMetaZFC.Model.SetTheory.Relations.CrossProjection',
    'YesMetaZFC.Model.SetTheory.Relations.CrossCapture',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationCrossBounded',
    'YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel',
]
# 前缀证书及其生产搬运使用与原关系记录相同的公理界。
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("Tg_play_d.map_l", "Tg_past_play_d.map_l")})
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("Tg_play_d.member_l", "Tg_play_d.mem_l", "Tg_run_real_d.read_l", "Tg_run_real_d.function_l")]
# 历史事件使用原关系真值；逐坐标搬运仍保持 ZF 公理界。
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("Tg_trace_d.map_l", "Tg_past_events_d.map_l")})
# 工作模型的四项结构条件由同一个原关系核读取。
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("ic_core_sat_l", "ic_core_mem_l", "ic_model_sat_l", "Ic_model_d.read_l", "Ic_model_d.rebase_l")})
# 原关系记录的实际递归、初值及分支末端调用也进入同一公理审计。
RAW_POOL_MODULES = [
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawPresent',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawStrength',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedIdentity',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.LevelTransfer',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawGraphSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyClass',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawColimit',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawEvaluation',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawConstant',
]
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.rr_span_realize_l"] = BASELINE
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Zc_schemas_d", "Zc_model_d", "zc_base_m", "zc_separation_m", "zc_collection_m", "zc_model_m", "Rr_layer_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in ("fs_read0_m", "fs_read_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Rr_truth_d", "Rf_record_d", "Rf_tuple_d", "rr_params_m", "rr_truth_m", "rf_record_m", "rf_tuple_m",
                "Rr_finite_d", "rr_finite_m", "Rf_pair_d", "rf_pair_m", "Smem_d.slice_env_d", "Smem_d.native_env_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("Tg_kernel_d", "it_local_m", "Er_measure_d", "er_measure_m", "Er_code_d", "er_code_m",
                "Er_native_d", "er_native_m", "Er_coord_d", "er_coord_m", "Er_arrow_d", "er_arrow_m", "Er_graph_d",
                "Er_eval_d", "er_eval_m", "Er_constants_d", "er_constants_m", "eo_seed0_m", "eo_result0_m", "eo_kernel_m",
                "Ec_source_d", "ec_source_m", "ec_source_sat_l", "En_source_d", "en_source_m", "en_source_sat_l",
                "Ep_positive_d", "ep_positive_m", "ep_positive_sat_l", "Eo_image_d", "eo_image_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
               ("v_transitive_l", "v_subset_mem_l", "v_power_exists_l", "v_power_mem_l", "v_joint_bound_l",
                "v_relation_cover_l", "v_relation_mem_l", "v_relations_mem_l", "v_fspace_exists_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.sc_finite_function_l", "YesMetaZFC.SetTheory.Internal.sc_v_power_l"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Sc_bound_d", "sc_bound_m", "sc_bound_sat_l", "Sc_bound_d.models_l",
                "sc_v_pair_l", "sc_rank_cover_l", "Sc_power_d.rank_l",
                "Sc_bounded_omega_closed_d.rank_l", "Sc_branch_d.rank_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory." + name for name in
               ("vc_transitive_l", "Vr_d.transitive_l", "Vr_d.relation_mem_l", "Vr_d.union_mem_l", "Vr_d.of_rank_l", "Vr_d.transitive_cover_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("Eb_pool_d.of_rank_l", "Eb_collapse_d.of_rank_l")]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("sc_v_bound_l", "sc_v_inaccessible_up_l")})
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("Eb_pool_d.read_l", "Eb_pool_d.node_l")})
CHOICE_FREE += ["YesMetaZFC.SetTheory.FilterZF." + name for name in
               ("adjoin_m", "adjoin_exists_d", "maximal_of_decides_d", "Rel_ultra_d.full_l")]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.FilterZF." + name: BASELINE for name in
                     ("maximal_decides_d", "maximal_relative_l", "Maximal_d.source_l")})
CHOICE_FREE += ["YesMetaZFC.SetTheory.FilterZF.sf_ultra_m", "YesMetaZFC.SetTheory.FilterZF.sf_ultra_sat_l",
                "YesMetaZFC.SetTheory.LargeCardinal.em_source_m", "YesMetaZFC.SetTheory.LargeCardinal.em_source_sat_l"]
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.InnerModel.fn0_identity_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.formula_image_l"] = BASELINE
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("it_local_mem_l", "it_local_sat_l", "ex_local_sat_l", "it_local_short_l", "It_local_d.read_l",
                      "It_local_d.map_l", "It_local_d.pull_l", "It_local_d.rank_l", "It_local_d.of_rank_l",
                      "it_active_sat_l", "it_tree_sat_l", "ec_join_l", "ei_order_l",
                      "er_measure_sat_l", "Er_measure_d.unique_l", "Er_measure_d.trace_l", "It_local_d.raw_measure_l",
                      "It_local_d.raw_family_l", "It_local_d.raw_reduced_l", "It_local_d.raw_coherent_l",
                      "It_local_d.raw_ultrapower_l", "er_ultrapower_l", "er_components_l",
                      "er_component_map_l", "ep_raw_map_l", "It_local_d.raw_present_l",
                      "It_local_d.raw_strength_l", "It_ultra_d.strength_rank_l", "It_ultra_d.owned_rank_l", "It_ultra_d.critical_pre_l",
                      "It_ultra_d.critical_source_l", "Em_family_d.source_l", "eo_image_sat_l",
                      "eo_kernel_true_l", "eo_owned_l", "ep_source_sat_l", "it_ultra_sat_l",
                      "ex_strength0_sat_l", "ex_strength_sat_l", "ex_quality_sat_l",
                      "It_local_d.raw_rank_cut_l", "It_local_d.rank_absolute_l", "er_cut_closure_l", "er_cross_push_l", "It_local_d.raw_projection_l",
                      "er_code_sat_l", "Er_code_d.unique_l", "Er_code_d.base_l", "Er_code_d.read_l", "Er_code_d.constant_l", "It_local_d.code_table_l",
                      "er_projection_identity_l", "er_projection_composition_l", "er_native_sat_l", "er_coord_sat_l",
                      "Er_coord_d.of_native_l", "Er_coord_d.read_l", "Er_coord_d.unique_l", "Er_coord_d.refl_l", "Er_coord_d.comp_l",
                      "er_arrow_sat_l", "Er_code_d.arrow_refl_l", "It_local_d.code_map_l", "It_local_d.code_graphs_l",
                      "It_local_d.code_system_l", "Er_graph_d.elementary_l", "Er_graph_d.stage_l", "It_local_d.code_limit_l",
                      "Er_graph_d.lift_l", "Er_graph_d.bounded_l", "Er_graph_d.bound_mem_l", "Er_graph_d.bounded_value_l",
                      "er_index_decode_l", "er_support_factor_l", "Er_coord_d.native_l", "Er_coord_d.pull_l", "eb_point_pull_l",
                      "Er_graph_d.repr_atoms_l", "Er_graph_d.reindex_l", "It_local_d.code_edge_l",
                      "er_eval_sat_l", "Er_eval_d.read_l", "Er_eval_d.write_l", "er_constants_sat_l", "Er_graph_d.constant_l")})
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                      ("fs_omega_relative_l", "fs_read_relative_l", "fs_rank_relative_l", "Fs_read_d.rank_l",
                       "fs_read0_sat_l", "fs_read0_relative_l", "Fs_read_d.map_layer_l", "fs_read_sat_l", "Fs_read_d.source_l",
                       "ec_coherent_relative_l", "ea_atoms_relative_l", "en_normal_relative_l",
                       "sf_finite_power_l", "em_family_relative_l", "It_local_d.measures_l", "It_local_d.bounded_model_l",
                       "Tg_context_d.kernel_l", "Tg_context_d.finite_l", "Tg_context_d.of_mem_l", "Tg_context_d.kernel_mem_l",
                       "tg_context_data_sat_l", "tg_kernel_relation_l", "Tg_context_d.map_l",
                       "Tg_run_d.read_l", "Tg_run_d.advance_l", "Tg_saved_d.read_l", "Tg_saved_d.membership_l",
                       "Tg_saved_d.rank_l", "Tg_saved_d.limit_l", "Tg_saved_d.node_l", "Tg_saved_d.answer_fixed_l",
                       "Tg_sequence_d.branch_limit_l", "Tg_sequence_d.return_unique_l", "Tg_context_d.save_l", "Tg_context_d.save_round_l",
                       "tg_saved_code_read_l", "tg_saved_code_sat_l", "Tg_saved_code_d.inj_l", "Tg_saved_code_d.values_l", "tg_saved_sat_l",
                       "Tg_game_d.zero_relative_l", "Tg_game_d.run_start_l", "Tg_sequence_d.even_illfounded_l",
                       "Tg_kernel_d.renew_l", "Tg_kernel_d.owned_l", "Tg_context_d.root_relative_l",
                       "Tg_kernel_d.continue_l", "Tg_kernel_d.language_l", "Tg_kernel_d.realize_seed_l",
                       "Tg_kernel_d.rigid_seed_l", "Tg_kernel_d.recover_seed_l", "Tg_kernel_d.reply_queries_l",
                       "tg_image_omega_l", "tg_successor_omega_l", "fs_sequences_relative_l", "fs_collapse_relative_l")})
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("sc_finite_function_l", "sc_relative_sat_l", "rt_record_in_read_l", "rt_record_in_save_l",
                      "rr_truth_sat_l", "Rr_truth_d.map_l", "rr_truth_mem_l",
                      "rr_truth_native_l", "rf_record_native_l", "rf_tuple_native_l", "Rf_tuple_d.inj_l", "rf_record_read_l",
                      "rf_record_save_l", "Rf_record_d.values_l", "Smap_d.record_image_l",
                      "Smem_d.slice_transitive_l", "Smem_d.slice_formula_l", "Smem_d.native_formula_l",
                      "Smem_d.slice_pair_l", "Smem_d.slice_tuple_l",
                      "zc_model_sat_l", "Zc_model_d.separate_l",
                      "Zc_model_d.collect_l", "Zc_model_d.native_l", "Zc_model_d.membership_l",
                      "sc_binary_relation_l", "Zc_model_d.theory_l", "Zc_model_d.power_l", "Zc_model_d.collection_l",
                      "Zc_model_d.source_l", "sfm_collect_raw_l", "Zc_model_d.map_l", "rr_layer_mem_l",
                      "Rr_layer_d.restrict_l", "Rr_layer_d.image_l", "Rr_layer_d.relative_l", "rr_program_l", "rr_separation_l",
                      "Smap_d.layer_map_l", "Smap_d.relative_image_l", "rr_native_delta_l", "rr_native_function_l", "rr_native_rank_l",
                      "rr_cut_formula_l", "rr_cut_models_l", "rr_cross_measure_l", "rr_cross_projection_l",
                      "rr_cross_capture_l", "rr_cross_functions_l", "rr_cross_closed_l", "rr_cross_relation_l", "rr_cross_pull_l",
                      "smdl_graph_identity_l", "smdl_graph_composition_l",
                      "rt_measure_exists_l", "rt_base_l", "rt_ultra_l", "Rr_layer_d.trace_l", "Rr_layer_d.measure_l", "rt_measure_read_l",
                      "Rr_layer_d.measure_capture_l", "Rr_layer_d.entry_l", "Rr_layer_d.low_composition_l",
                      "Rr_layer_d.composition_l",
                      "Rr_layer_d.function_space_l", "Rr_layer_d.finite_function_l", "Rr_layer_d.factor_l",
                      "Rr_layer_d.function_range_l", "Rr_layer_d.function_unique_l",
                      "smdl_function_l", "Rr_layer_d.function_decode_l", "Rr_layer_d.function_injective_l",
                      "rr_finite_sat_l", "Rr_finite_d.unique_l", "Rr_finite_d.input_unique_l", "Rr_layer_d.finite_codes_l",
                      "smdl_graph_l", "rf_pair_sat_l", "Rf_pair_d.bounds_l", "rf_pair_native_l")})
# 源理论在原关系中双向传递；字面接口只在实际隶属实例中解读。
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("sc_algebra_closed_l", "sc_algebra_mem_l", "Sc_theory_d.algebra_l", "Sc_theory_d.separation_l", "ssep_relation_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.Ep_source_d.algebra_l"]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("Sc_theory_d.map_l", "Sc_theory_d.pull_l", "sc_algebra_mem_l",
                      "Sc_theory_d.algebra_l", "Sc_theory_d.separation_l")})
# 原关系收集保留任意子集、全部内部程序和实际统一函数。
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.sc_uniform_mem_l"]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("sc_collection_iff_l", "Sc_collection_d.map_l", "Sc_collection_d.pull_l",
                      "sc_uniform_mem_l", "sc_collection_mem_l", "sc_collection0_sat_l")})
# 内部自然数对象与有限列空间共同沿原根图传输；实际初值和秩段接口同步审计。
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("sc_seq0_m", "sc_seq0_closed_l", "sc_sequences0_m", "sc_sequences0_closed_l", "sc_sequences0_sat_l",
                "Rr_layer_d.successor_l", "Rr_layer_d.omega_l")]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("sc_sequences_mem_l", "sc_sequences_iff_l", "sc_sequences0_sat_l",
                      "Rr_layer_d.successor_l", "Rr_layer_d.omega_l", "Smap_d.omega_chart_l")})
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("Ep_source_d.sequences_l", "Ep_source_d.rank_sequence_l", "Ep_source_d.rank_sequences_l")})
# 外部可数闭性保留原关系函数和同一自然数图；切片及其高层像进入实际后继。
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("rr_layer_m", "rr_layer_sat_l", "Rr_layer_d.omega_unique_l",
                "sc_omega_closed_mem_l", "sc_bounded_omega_closed_mem_l", "Sc_omega_closed_d.bounded_l",
                "Sc_bound_d.function_l", "Sc_bounded_omega_closed_d.capture_l")]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("rr_layer_sat_l", "Rr_layer_d.omega_unique_l", "sc_omega_closed_sat_l",
                      "sc_bounded_omega_closed_sat_l", "Sc_omega_closed_d.at_l", "Sc_bounded_omega_closed_d.at_l",
                      "sc_omega_closed_mem_l", "sc_bounded_omega_closed_mem_l", "Sc_bounded_omega_closed_d.branch_l",
                      "sc_v_bounded_omega_closed_l", "sc_v_omega_closed_l", "Sc_bound_d.function_l",
                      "Sc_bounded_omega_closed_d.capture_l", "Sc_bounded_omega_closed_d.cut_l", "Sc_bounded_omega_closed_d.image_l")})
# 固定定义域统一化、唯一商赋值、原关系应用及其实际秩后继实例。
RAW_APPLICATION_MODULES = [
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationCopyPull',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationFormulaImage',
    'YesMetaZFC.Model.SetTheory.ReducedPower.RelationApplication',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawApplication',
]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.Rc_graph_d.unique_l", "YesMetaZFC.SetTheory.Internal.Sc_uniform_d.raw_l"]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("Rc_graph_d.unique_l", "rc_eval_exists_l", "rc_formula_image_l", "rc_coordinate_l", "rc_application_l",
                      "sc_identity_l", "sc_identity_raw_l", "rs_formula_image_l")})
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.Er_graph_d.application_l"] = BASELINE
# 同一有界池的恒等代表先在实际超幂中证明，再进入已有反射规则。
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.Eb_collapse_d.identity_l"] = BASELINE
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.KP.v_ordinal_subset_l"] = BASELINE
# 原关系逐点求值闭性及两处实际旧调用共享同一公理界。
OMEGA_EVALUATION_MODULES = [
    'YesMetaZFC.Model.SetTheory.Relations.OmegaEvaluation',
    'YesMetaZFC.Model.SetTheory.Relations.CollectCode',
]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("Sc_uniform_d.formula_l", "Rf_fun_d.map_l", "Rf_val_d.map_l",
                      "Sc_omega_closed_d.evaluation_l", "Smap_d.sfun_l")})
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.It_ultra_d.closed_l"] = BASELINE
# 小关系坍塌在现用源与实际后继中统一使用原关系解释。
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.sc_collapse_closed_l"]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("sc_collapse_closed_l", "sc_collapse_mem_l", "sc_h_collapse_l")})
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("ep_closure_free_closed_l", "Ep_source_d.rank_collapse_l")})
# 指定有限空间、弱有限实现及其原后继实例共享既有公理边界。
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("sc_pair_union_l", "sc_fseq0_m", "Sc_fseq_d", "Sc_fseq_d.bounds_l", "Sc_fseq_d.mem_l",
                "sc_fseq_m", "sc_fseq_closed_l", "Sc_sequences_d.space_l")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.Ep_source_d.rebase_l"]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("sc_pair_union_l", "sc_fseq_native_l", "sc_fseq_mem_l", "sc_fseq_sat_l", "Sc_sequences_d.space_l")})
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.Ep_source_d.finite_l"] = BASELINE
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("sc_sequences_models_l", "sc_collapse_models_l")})
# 源小性与原关系低层共用同一编号；限制和收集入口均保持构造性。
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Rf_small_d.mem_l", "rf_small_native_l", "Rf_small_d.mono_l", "Rf_small_d.mono_mem_l",
                "rf_small_m", "rf_small_closed_l", "rf_small_sat_l", "Sc_collection_d.uniform_l")]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("rf_small_mem_l", "Rf_small_d.mono_l", "Rf_small_d.mono_mem_l", "Sc_collection_d.uniform_l")})
LOS_ZF_BOUNDS["YesMetaZFC.SetTheory.LargeCardinal.Ep_source_d.cardinal_small_l"] = BASELINE
# 原关系源分开保存背景程序自然数与模型自然数对象，现用源直接继承。
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal.Rf_small_d.of_index_l",
                "YesMetaZFC.SetTheory.Internal.sc_collection0_sat_l",
                "YesMetaZFC.SetTheory.LargeCardinal.Er_source_d.rebase_l",
                "YesMetaZFC.SetTheory.LargeCardinal.er_source_sat_l"]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                     ("Er_source_d.of_mem_l", "Er_source_d.of_layer_l", "Er_source_d.rebase_l", "er_source_sat_l")})
# 原生锚点使用 KP 有界归纳和实际秩历史，不向所属模型添加完整 ZFC。
ANCHOR_MODULES = [
    'YesMetaZFC.SetTheory.KP.TransitiveInduction',
    'YesMetaZFC.SetTheory.CumulativeComparison',
    'YesMetaZFC.Model.SetTheory.Relations.Parity',
    'YesMetaZFC.Model.SetTheory.Relations.NativeRank',
    'YesMetaZFC.Model.SetTheory.Relations.RankImage',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.RunMove',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.TreeStep',
]
# 原生活动边及其精确编码一并进入常驻审计，覆盖此前迁移新增的生产模块。
ACTIVITY_MODULES = [
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopyClass',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawGraphSyntax',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.ActivityRead',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyQuality',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawAgreementRead',
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawMembershipSystem',
    'YesMetaZFC.SetTheory.LargeCardinal.Game.Padding',
]
# 原关系可数像及已有公共覆盖、失败尝试入口一并核验。
COUNTABLE_MODULES = [
    'YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCountable',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.CountableCover',
    'YesMetaZFC.SetTheory.LargeCardinal.Iteration.AttemptRegular',
]
# 模型列的实际像及有限尝试坐标换算取代旧的逐点固定层。
HOD_CHOICE_MODULES = [
    'YesMetaZFC.SetTheory.InnerModel.HOD.Choice',
    'YesMetaZFC.SetTheory.InnerModel.HOD.BracketChoice',
]
HOD_ZF_BOUNDS = {"YesMetaZFC.SetTheory.InnerModel." + name: BASELINE for name in
                 ("hod_choice_set_l", "hod_model_l", "hod_model_ext_l")}
HOD_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.InnerModel." + name: BASELINE for name in
                      ("hb_pick_exists_l", "hb_pick_unique_l", "hb_choice_set_l")})

# 完整复制历史的实际原关系 nice 树；独立检查其活动边构造。

# 原关系代表复制直接供现有完整超幂复制调用。

if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    result = main(MODULES, CHOICE_FREE, BASELINE, "INTERNAL_MODEL_GUARD_PASS")
    if not result:
        result = main(HOD_CHOICE_MODULES, [], ZFC_BASELINE, "HOD_CHOICE_GUARD_PASS", HOD_ZF_BOUNDS)
    if not result:
        result = main(SKOLEM_MODULES, [], ZFC_BASELINE, "INTERNAL_SKOLEM_GUARD_PASS", ZF_BOUNDS)
    if not result:
        result = main(LOS_MODULES, LOS_CHOICE_FREE, ZFC_BASELINE, "INTERNAL_LOS_GUARD_PASS", LOS_ZF_BOUNDS)
    sys.exit(result)
