"""审计内部模型、公式编译、司寇伦闭包、有限反射及 OD/HOD。

各切片仅允许既有标准 Lean 公理，不再放行原生句法闭合性公理。
编码和解码数据排除经典选择，司寇伦模块的 ZF 端点另逐项收紧。
复用实际声明审计，不生成常驻测试模块。
"""
import sys

from check_filters import BASELINE, main

MODULES = ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
           ("Numeral", "Structure", "Assignment", "Syntax", "TruthSyntax", "Truth",
            "TruthRules", "FormulaCode", "Satisfaction", "Theory", "Prefix", "Source",
            "Builder", "CompileSemantics", "Compiler", "Countable", "FiniteAssignment", "FiniteSource", "SkolemSyntax",
            "CanonicalRows", "CanonicalCode", "CanonicalSatisfaction",
            "PredicateTrace", "TypeNames", "TypeTruth", "TypeSource", "TypeRank", "TypeEmbedding",
            "SupportSyntax", "SupportBound", "Support", "Induction", "TarskiVaughtSyntax",
            "FullWitness", "ElementarySyntax", "TarskiVaught", "Elementary", "SourceElementary", "Membership", "MembershipSkolem", "Hereditary")]
MODULES += ["YesMetaZFC.Model.SetTheory.LevyReflection." + name for name in
            ("Parameters", "WitnessSyntax", "Collection", "Step", "Chain", "Closure", "Relativization", "Decode", "Bounded")]
MODULES += ["YesMetaZFC.Model.SetTheory.LevyReflection", "YesMetaZFC.SetTheory.CumulativeUnion"]
MODULES += ["YesMetaZFC.Model.SetTheory.ProjectEmbedding", "YesMetaZFC.Model.SetTheory.Internal.EmbeddingProject"]
MODULES += ["YesMetaZFC.SetTheory.RelationChain", "YesMetaZFC.Model.SetTheory.ClassResponse"]
MODULES += ["YesMetaZFC.SetTheory.FlatPairing"]
MODULES += ["YesMetaZFC.SetTheory.FlatPairing." + name for name in
            ("Shift", "Tag", "Pair", "Rank", "Source", "Sequence", "Finite", "RankObjects",
             "Functions", "SequenceSource", "AssignmentSource")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("FlatProgram", "FlatTruthSyntax", "FlatTruth", "FlatTruthSource", "FlatSatisfaction", "RankSatisfaction")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("RelativizationRule", "RelativizationSyntax", "InstructionAppend", "RelativizationSteps",
             "Relativization", "RelativizationCorrect", "LargestSetCode", "LargestSet",
             "TypeMinusCode", "TypeMinusSemantics", "TypeMinusSyntax", "TypeQueryClosure",
             "TypeMinus", "TypeMinusMatrix", "TypeMinusEmbedding")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.TypeMinusStretch"]
MODULES += ["YesMetaZFC.SetTheory.FunctionRecoding", "YesMetaZFC.SetTheory.CumulativePairing"]
MODULES += ["YesMetaZFC.SetTheory.FlatPairing." + name for name in
            ("RecursionSource", "CumulativeSource", "StructureSource")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("RankLargest", "FlatPredecessor", "FiniteConjunction", "TypeGuardCode", "TypeGuardColumn", "TypeGuard")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("TransitiveRecursion", "TransitiveOrderCollapse", "OrdinalPairOrderSource", "OrdinalPairSource",
             "TransitiveSequence", "OrdinalFoldStepSource", "OrdinalFoldSource", "SyntaxSource",
             "CanonicalNodeSource", "CanonicalSource", "CanonicalLocal", "ProgramRecode",
             "ProgramRecodeSemantics", "ProgramRecodeSource", "CanonicalFlat",
             "TypeRolesSyntax", "TypeRolesCode", "TypeRoles")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("PowerRelativization", "LowerSatisfaction", "CanonicalRank", "FlatTypeNames", "FlatTypeQuery",
             "FlatTypePredecessor", "FlatTypeRead")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("TuplePackSyntax", "TuplePackStep", "TuplePackCode", "TupleUnpack", "TupleCode", "TypePredecessorCode")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("FiniteSpaceBounded", "TypePoolBounded", "TypeDomain", "TypeKappaSource", "TypeKappaCode")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderBoundedConst", "ExtenderLocalFormula", "ExtenderQuality", "TypeStretch",
             "TypeStretchCode", "TypeStretchBounded", "TypeStretchFormula", "TypeStretchSource",
             "TypeStretchQuality", "TypeElasticStep", "TypeElasticSource", "TypeElasticCode")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("TypeElasticColumn", "TypeElasticQuery", "TypeElasticClauses", "TypeElastic", "TypeElasticRead")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("TuplePackBinder", "TypeColumn", "TypePackedQuery", "TypeLowerSource", "TypePermutation",
             "SubtypeClause", "SubtypeWitness", "SubtypeQuery", "SubtypeCode", "Subtype",
             "SubtypeUp", "SubtypeClosure", "SubtypeEmbedding", "SubtypeLift", "TypeExceeds")]
MODULES += ["YesMetaZFC.SetTheory.Card.Cofinality.OmegaAddition"]
MODULES += ["YesMetaZFC.SetTheory.Ord.UnboundedFiber"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in ("LocalType", "LocalTypeRead")]
MODULES += ["YesMetaZFC.SetTheory.CumulativeFinite"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("OrdinalAdditionSource", "TypeMove", "TypeMoveSource", "TypeMoveRead", "TypeMoveQuote")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("LocalIndiscernibles", "LocalIndiscerniblesLeast", "LocalTypeTransport", "LocalTypeTransportTuple")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("FiniteEnumeration", "FiniteSetCode", "TypeGameNode", "TypeGameNodeSource", "TypeGameNodeCode",
             "TypeGameNodeQuery", "TypeGameRoot", "TypeGameMax", "TypeGameGraph")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in ("TypeGameDecoding", "TypeGameReset")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("TypeDropNames", "TypeDropSyntax", "TypeDropRead", "TypeDrop", "TypeDropAppend", "TypeGameBound", "TypeGameHeight")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("TypeElasticDomain", "TypeGameElastic", "TypeGameRigidity", "TypeGameReply", "TypeGameReplyBuild")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("TypeTruthSyntax", "SourceRelative", "SourceInaccessibleSyntax", "SubtypeProgramMatrix",
             "SubtypeProgramSyntax", "TypeGameQuerySyntax", "TypeExceedsSyntax", "SubtypeSyntax")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("TypeElasticSyntax", "TypeElasticReadSyntax", "TypeElasticLanguageSyntax", "TypeElasticCatalog",
             "TypeGameProgramCatalog", "TypeGameQueryPacket", "TypeGameQueryCatalog", "TypeGameData",
             "TypeGameCatalogRead", "TypeGameClock", "TypeGameParameters", "TypeGameHistoryRules",
             "TypeGameAuxiliary", "TypeGameAnswer", "TypeGameHistory", "TypeGameSetup", "TypeGame", "TypeGameStages", "TypeGameDeterminacy")]
MODULES += ["YesMetaZFC.SetTheory.Ord.FiniteTail"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("FiniteTailSource", "SubtypeColumn", "SubtypeRebound", "TypePoolImage", "SubtypeReboundImage",
             "TypeDropSource", "TypeDropEmbedding", "SubtypeSource")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("LocalIndiscerniblesGap", "TypeRenewal", "TypeGameRenewal", "ExtenderCriticalPoint", "IterationCriticalBound",
             "TypeOneStepImage", "TypeGameStepImage", "IterationWorkingApply",
             "TypeGameTreeStep", "TypeGameIssuedAnswer", "TypeGameAnswerHistory",
             "TypeGameControlMove", "TypeGamePositionIssue", "TypeGamePositionNext", "TypeGameRank",
             "TypeGameIssuedReset", "TypeGameIssuedQuery", "TypeGameIssuedLow",
             "TypeGameSaved", "TypeGamePast", "TypeGamePastStep",
             "TypeGameEventHistory", "TypeGameTrace", "TypeGamePastEvents", "TypeGameHistorySelect",
             "TypeGameContinueSeed", "TypeGameContinueAuto", "TypeGameControlCard", "TypeGamePastRoots",
             "TypeGameStepResult", "TypeGameHistoryContinue", "TypeGameHistoryStep", "IterationTreeSyntax",
             "TypeGameRunState", "TypeGameRunAdvance", "TypeGameRunSyntax", "TypeGameRunNext", "TypeGameRunSequence", "TypeGameOdd",
             "TypeGameRunOrder", "TypeGameRunUnion", "TypeGameEvenBranch", "TypeGameOddBranch", "TypeGameOddRecords",
             "TypeGameOddCompatibility", "TypeGameOddLimit", "TypeGameLimitValues", "TypeGameLimitControl", "TypeGameEvenLimit",
             "IterationConeFixed", "TypeGameBranchFixed", "TypeGameBranchLimit", "TypeGameBranchTree",
             "TypeGameBranchProjection", "TypeGameShiftedStrategy",
             "IterationBranchSequence", "TypeGameRootTree", "TypeGameRunRoot", "TypeGamePlayTrace", "TypeGamePastPlay",
             "TypeGameReturnSyntax", "TypeGameReturnSequence", "TypeGameReturnTree", "TypeGameReturnUnion", "TypeGameReturnBranch",
             "FiniteArithmeticSource", "TypeGameRealPrefix", "TypeGameRunMove", "TypeGameRunChoice",
             "TypeGameStrategy", "TypeGameStrategyPlay", "TypeGameArchivePlay", "TypeGameTransfer",
             "TypeGameReplyDescent", "TypeGameGenericExtension", "TypeGameGenericMove", "TypeGameGenericDense",
             "TypeGameGenericTarget", "TypeGameGenericMeet", "TypeGameGenericCapture", "TypeGameResetMove",
             "TypeGameReady", "TypeGameReadyStep", "TypeGameRoundSet", "TypeGameGenericStep", "TypeGameGenericRun", "TypeGameGenericIndices",
             "TypeGameProjection", "TypeGameGenericPlay", "TypeGameGenericCatch", "TypeGameGenericBranch",
             "TypeGameLevel", "TypeGameLevelReply", "TypeGameTracked", "TypeGameGenericAvoid", "TypeGameGenericTransfer", "TypeGameCollapse",
             "TypeGameVacuous", "TypeGameCorollary67", "TypeGameShiftProjection", "TypeGameCorollary610",
             "TreeProjection", "TreeProjectionTransfer", "TwinTreeDichotomy", "TwinTreeSyntax", "TwinTreeGround",
             "TwinTreeRank", "TwinTreeCertificate", "TwinTreeOutward",
             "TypeGameImageSyntax", "TypeGameRenewalSyntax", "TypeGameContext",
             "TypeGameReplySource", "TypeGameImageRead")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("FiniteRecordCoordinate", "TypeGameGraphUnion", "SubtypeInsertion", "TypeGameNodeRank")]
MODULES += ["YesMetaZFC.SetTheory.Descriptive." + name for name in
            ("InputIteration", "Path", "TreeDependentChoice", "TreePullback", "GameAttemptRank", "TreeRankPrefix",
             "TreeTail", "SequenceCons", "GameParity", "GameShift", "TreeShift", "TreeRank", "HistoryTree", "GameBattle",
             "LeastLegalMove", "LegalMoveBounded", "ScanResponse", "ScanStrategy", "GameCompletion", "GameLegalStep", "GameControl",
             "FirstViolation", "FirstViolationRead", "FirstViolationMinimum", "LegalHistory", "ScheduledGame",
             "GameContinuation", "GameSplice", "GameGlue", "GameWinningPositions", "GameAvoid", "GameAvoidRun", "ClosedDeterminacy")]
MODULES += ["YesMetaZFC.SetTheory.IndexedIteration"]
MODULES += ["YesMetaZFC.SetTheory.Ord.FirstCrossing"]
MODULES += ["YesMetaZFC.SetTheory." + name for name in
            ("FinitaryTraceSyntax", "FinitaryFamily", "Card.FiniteParameters")]
MODULES += ["YesMetaZFC.SetTheory.Card." + name for name in
            ("FiniteSequenceSyntax", "FiniteSequenceRecursion", "FiniteSequenceNumbering",
             "FiniteSequenceCountable", "FiniteSequenceLift", "FiniteSequenceEnd", "FiniteSequenceRecode", "OrdinalImage")]
MODULES += ["YesMetaZFC.SetTheory." + name for name in
            ("CountableChain", "FinitaryHullSyntax", "FinitaryHullStep", "FinitaryHull")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal", "YesMetaZFC.Model.SetTheory.Internal.ReducedPower"]
MODULES += ["YesMetaZFC.SetTheory." + name for name in
            ("Rank", "TransitiveClosure", "RankImage", "Hereditary", "Card.SmallBound", "FunctionRetraction", "FinitarySlice")]
MODULES += ["YesMetaZFC.SetTheory.Ord.Code." + name for name in
            ("Transport", "Pair", "Natural", "Fold", "Prefix", "Sequence")]
MODULES += ["YesMetaZFC.SetTheory.Ord.Code", "YesMetaZFC.SetTheory.InnerModel.OD"]
MODULES += ["YesMetaZFC.SetTheory.InnerModel.OD." + name for name in
            ("Syntax", "Source", "Code", "Definition", "Complexity", "Minimum", "Order", "Choice")]
MODULES += ["YesMetaZFC.SetTheory." + name for name in
            ("CumulativeCertificate", "Ord.DefinableMinimum", "Definitional.Project.Hierarchy.Levy",
             "InnerModel.HOD.Definition", "InnerModel.HOD")]
MODULES += ["YesMetaZFC.SetTheory.InnerModel.OD." + name for name in
            ("Graph", "Brackets", "Parameters", "Relative", "RelativeClosure", "Separation", "Relations")]
MODULES += ["YesMetaZFC.SetTheory.InnerModel.HOD." + name for name in
            ("Relative", "Relativization", "Closure", "Schemas", "Models", "Parameters", "Coding", "Presentation")]
MODULES += ["YesMetaZFC.SetTheory.Collapse." + name for name in
            ("RelationSyntax", "RelationRecursion", "RelationExistence", "RelationIso", "RelationBounded", "RelationMap")]
MODULES += ["YesMetaZFC.SetTheory.Collapse"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in ("ExtenderRelationCode", "ExtenderModelCode")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedEvaluation"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRank"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrengthRank"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrengthAgreement"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.RelativeRankAgreement"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.RelativeRankEnumeration"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.ExtenderUltraSupport"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.IterationCoherence"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.IterationNice"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("IterationAttempt", "IterationAttemptNode", "IterationAttemptSpace", "IterationAttemptRelative",
             "IterationAttemptImage", "IterationAttemptMember", "IterationAttemptLift", "IterationAttemptPath",
             "IterationAttemptRow", "IterationAttemptDecode", "IterationAttemptRank", "IterationEnumeration", "IterationEmbedding",
             "ExtenderCountable", "IterationCountable")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.SourceClosureSyntax", "YesMetaZFC.Model.SetTheory.Internal.SourceOmegaClosed"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.ExtenderClosedFiber", "YesMetaZFC.SetTheory.LargeCardinal.ExtenderSupportRank"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiniteMatrix"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in ("ExtenderSourceSyntax", "IterationHistorySyntax", "IterationHistory")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("EmbeddingSmallRestriction", "EmbeddingCountableBound", "ExtenderCopyRestriction", "EmbeddingSetRestriction", "ExtenderSourceInclusion", "ExtenderRankLocal", "ExtenderSuccessorUnique")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in ("EmbeddingOrdinal", "SourceOmegaBound", "SourceHierarchy")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("TransitiveSource", "TransitiveFunctionFormula", "TransitiveCofinalFormula", "TransitiveCardinal",
             "SourceInaccessible", "SourceInaccessibleRead", "SourceInaccessibleRank", "SourceInaccessibleUp")]
MODULES += ["YesMetaZFC.SetTheory.Card.Syntax", "YesMetaZFC.SetTheory.Card.Properties.Syntax",
            "YesMetaZFC.SetTheory.LargeCardinal.ExtenderInitial"]
MODULES += ["YesMetaZFC.SetTheory.CumulativeRelativeAlgebra", "YesMetaZFC.SetTheory.LargeCardinal.ExtenderTreeBranch"]
MODULES += ["YesMetaZFC.SetTheory.CumulativeRelativeRestriction"]
MODULES += ["YesMetaZFC.SetTheory.CumulativeRelativeComparison"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.SourceRankSize"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.SourceRankStage"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.SourceInaccessibleClosure"]
MODULES += ["YesMetaZFC.SetTheory.Descriptive." + name for name in ("TreeCons", "TreeBounded", "TreeWellFounded")]
MODULES += ["YesMetaZFC.SetTheory.Descriptive"]
MODULES += ["YesMetaZFC.SetTheory.Card.FiniteSequenceJoin"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.PredicateEmbedding",
            "YesMetaZFC.SetTheory.LargeCardinal.Woodin",
            "YesMetaZFC.SetTheory.Descriptive.Game", "YesMetaZFC.SetTheory.Descriptive.Determinacy"]
MODULES += ["YesMetaZFC.SetTheory.InnerModel.Relative." + name for name in
            ("Operator", "Hierarchy", "Class", "Structure", "Relativization", "Reflection",
             "Schemas", "Model", "Reals", "LReal", "Determinacy")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("EmbeddingSource", "PredicateSource", "Isomorphism", "Collapse", "SeparationCode", "Separation",
             "BinaryTruth", "CollectionCode", "DeltaCode", "UniformizationCode", "FunctionCode",
             "PointwiseAssignment", "PointwiseSyntax", "PointwiseSteps", "PointwiseValue", "PointwiseTruth",
             "SeparationSource", "SourceField")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower." + name for name in
            ("Relation", "Classes", "Model", "Truth", "Update", "Assignment", "Atomic", "LosSyntax",
             "SourceSyntax", "SourceTruth", "SourceAssignment", "SourceProjection", "PullbackKernel", "ProjectionLaws")]
MODULES += ["YesMetaZFC.SetTheory.CumulativeFunction", "YesMetaZFC.SetTheory.KP.Ordinal", "YesMetaZFC.SetTheory.CumulativeClosure", "YesMetaZFC.SetTheory.InnerModel.Recursion.Graph",
            "YesMetaZFC.SetTheory.InnerModel.Recursion.Composition"]
MODULES += ["YesMetaZFC.SetTheory.Filter." + name for name in ("Relative", "Source", "Projection")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("DerivedFilter", "SourceMeasure", "CriticalMeasure", "CriticalOrdinal", "MeasureCompleteness", "Measurable", "MeasurePower", "MeasureRegularity",
             "TreeReflection", "MeasureFamily", "FiberCompleteness", "FiniteSupport", "SupportCompleteness",
             "SupportProjection", "Coherence", "SupportConstruction")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.Quotient",
            "YesMetaZFC.Model.SetTheory.Internal.DirectedSystem"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.DirectedSystem." + name for name in
            ("Basic", "Limit", "WellFounded", "Cone", "Union", "Stages", "ElementarySyntax", "Elementary", "Factor")]
MODULES += ["YesMetaZFC.SetTheory.Collapse.RelationSequence", "YesMetaZFC.SetTheory.Filter.Countable",
            "YesMetaZFC.SetTheory.LargeCardinal.ComponentWellFounded",
            "YesMetaZFC.SetTheory.LargeCardinal.WellFoundedComponents"]
MODULES += ["YesMetaZFC.SetTheory.CountableChoice", "YesMetaZFC.SetTheory.Filter.Finite",
            "YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullProjection"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("CountableSupport", "SupportIndex", "MeasureConstraints", "ConstraintLevels", "JointFiber", "ExtenderFunctions")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.AscendingDescent"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.DirectedSystem." + name for name in ("FiniteCover", "ElementaryFactor")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("EmbeddingFinite", "PointwiseContext", "SeparationTransport", "SourceTransport")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower." + name for name in ("CopyKernel", "CopyConstant")]
MODULES += ["YesMetaZFC.SetTheory.Filter.SourceUltrafilter"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderRelative", "ExtenderTransport", "ExtenderCopyPull", "ExtenderCopySyntax")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower." + name for name in ("Bounded", "FormulaImage", "DeltaImage")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("SourceApplication", "RelationRelative", "RelationFunction", "RelationFunctionFamily",
             "RelationSeparation", "RelationUniformCode", "SourceCollectionBasis", "RelationCollection",
             "RelationEvaluation", "RelationConstant", "RelationTraceFamily", "RelationPointwiseWitness",
             "ReducedPower.RelationSyntax", "ReducedPower.RelationLos",
             "RelationSeparationSource", "RelationSubset", "RelationSmall",
             "ReducedPower.RelationRestriction", "ReducedPower.RelationConstant",
             "RelationComposition", "RelationRealization", "RelationPower", "RelationLow", "RelationHierarchy", "RelationFunctionCapture",
             "ReducedPower.RelationPullback", "ReducedPower.RelationAssignment", "ReducedPower.RelationTrace",
             "ReducedPower.RelationProjection", "ReducedPower.RelationMeasure", "ReducedPower.RelationSuccessor",
             "ReducedPower.RelationBounded", "ReducedPower.RelationNormalize", "ReducedPower.RelationFamily")]
MODULES += ["YesMetaZFC.SetTheory.Collapse.RelationRealization"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderFiniteRepresentative", "ExtenderFunctionValue", "ExtenderSeedSegment",
             "ExtenderBoundedRaw", "ExtenderBoundedRealization", "ExtenderRawMeasure", "ExtenderRawReduced", "ExtenderRawProjection",
             "ExtenderRawComponent", "ExtenderRawAssembly", "ExtenderRawLimit", "ExtenderRawBounded",
             "ExtenderRawValue", "ExtenderRawRelation", "ExtenderRawLow", "ExtenderRawRank")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderFunctionCode", "ExtenderNormalSource", "ExtenderRepresentative", "ExtenderCoordinateSource",
             "ExtenderSeed", "ExtenderSeedNormal", "ExtenderSeedCollapse", "ExtenderCopySeed", "ExtenderCopyCollapse",
             "ExtenderTuple", "ExtenderSetCode")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("IterationOrder", "IterationDiagram", "IterationNextMaps", "IterationDiagramExtend", "IterationStep",
             "IterationTree", "IterationTreeExtend", "IterationRoot", "IterationLimit", "Iteration")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Isomorphism"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("IterationBranch", "IterationTag", "IterationTagIso", "IterationSystem", "IterationDirectLimit",
             "IterationProjection", "IterationLimitModel", "IterationLimitOrder", "IterationLimitMaps",
             "IterationLimitDiagram", "IterationLimitExtend", "IterationWellFounded", "IterationCofinal",
             "IterationRealizer", "IterationBranchExtend", "IterationPadding")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderSystemSyntax", "ExtenderEdge", "ExtenderDescentSyntax", "ExtenderWellFounded")]
MODULES += ["YesMetaZFC.SetTheory.OrdinalChoice"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("EmbeddingComposition", "Extensionality", "RelationCollapse")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("UniversalSyntax", "UniversalClosure", "EmbeddingOmega", "SourceFinite", "SourceFinitePartial", "SourceFamily",
             "UniformizationSource", "PointwiseQuantifier", "Pointwise", "PointwiseTrace",
             "PointwiseDiagonal", "PointwiseWitness", "SourceReindex")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower." + name for name in
            ("SourceLos", "SourceSatisfaction", "Constant", "SourceComposition", "SourceTrace", "Restriction")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderComponents", "ExtenderEvaluation", "ExtenderEvaluationPull", "ExtenderFactor",
             "ExtenderRepresent", "RankLookup")]
MODULES += ["YesMetaZFC.SetTheory.Card.PowerBound", "YesMetaZFC.SetTheory.LargeCardinal.ExtenderTag",
            "YesMetaZFC.SetTheory.LargeCardinal.DerivedEvaluation"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("DerivedSeparation", "ExtenderNormalSyntax", "ExtenderNormal", "ExtenderOperator", "ExtenderAlgebra",
             "ExtenderSeeds", "ExtenderRestriction", "ExtenderPrefix", "ExtenderBoundedSyntax", "ExtenderBounded",
             "ExtenderShort", "ExtenderSyntax", "WoodinExtender", "ExtenderTruncation", "ExtenderProduct", "Extender")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.EmbeddingRange",
            "YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.RelationChange"]
MODULES += ["YesMetaZFC.SetTheory." + name for name in
            ("Kuratowski", "Card.SmallEnumeration", "Collapse.EmbeddingFixed", "CumulativeRelative")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderComparison", "ExtenderCoordinates", "ExtenderLength", "DerivedPredicate",
             "RankTransport", "RankEnumerationSyntax", "RankLookupSyntax")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("FiniteTruth", "FiniteSyntax", "FiniteEvaluationSyntax", "FiniteEvaluation", "FiniteEmbedding",
             "EmbeddingAttempt", "EmbeddingAttemptSyntax", "EmbeddingAttemptCertificate", "EmbeddingAttemptRelative", "EmbeddingAttemptDecode")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderFiniteSyntax", "ExtenderFiniteEvaluation", "ExtenderEmbeddingTree", "ExtenderEmbeddingCountable")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in ("FiniteWitness", "SmallSkolemSyntax")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("EmbeddingCountable", "EmbeddingFixed", "EmbeddingRankFixed", "RegularRankImage", "CollapseCountable", "SourceEnumeration", "SourceFunctionSize", "RelativeCountable")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("IterationCountableFixed", "IterationCopyAttempt", "IterationAttemptShift", "IterationRankValue",
             "IterationCopyRank", "IterationCopyCut")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderFiniteWitness", "ExtenderSkolemCode", "ExtenderSkolemRead", "ExtenderSkolemSource", "ExtenderSkolemCollapse", "ExtenderSkolemStep")]


MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("FormulaRelation", "ReducedPower.SourceFormula", "SourceBranchSyntax", "SourceBranchRelation",
             "SourceBranchPull", "SourceRankClosure", "Sigma1Substructure")]
MODULES += ["YesMetaZFC.SetTheory.CumulativeRelativeClosure", "YesMetaZFC.SetTheory.InnerModel.Rudimentary.Closure"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderFormulaSystem", "ExtenderRankTheory", "ExtenderRankClosure", "ExtenderSkolemRank")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("SourcePower", "SourceUltrafilter", "ReducedPower.SourceModel")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderFiberBranch", "ExtenderFiberRelative", "ExtenderLevelTransfer")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("SourceCover", "SourceCantor", "SourceRelation", "SourceBranchBound", "SourcePresentation")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderBoundedRepresentative", "ExtenderBoundedDescent", "ExtenderBoundedRelationSyntax",
             "ExtenderBoundedNodes", "ExtenderBoundedRelation", "ExtenderBoundedGraph", "ExtenderSourceDescent",
             "ExtenderSourceSupport", "ExtenderSourceConstraintSyntax", "ExtenderSourceLevels",
             "ExtenderSourceJointFiber", "ExtenderSourceConstraints", "ExtenderConstraintDescent",
             "ExtenderSourceWellFounded", "ExtenderBranchBound", "ExtenderSourceBranch", "ExtenderBoundedCollapse",
             "ExtenderBoundedTransport", "ExtenderBoundedValue", "ExtenderFunctionMap", "ExtenderCopyBounded",
             "ExtenderTrace", "ExtenderTraceMap", "ExtenderModelMap", "ExtenderProductIndex", "ExtenderPresentation", "ExtenderRankLift",
             "ExtenderSystemCode", "IterationDiagramSyntax", "IterationStepSyntax")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Syntax"]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("TransitiveStructure", "TransitiveCollapse", "ReducedPower.Relative", "DirectedSystem.Relative")]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderReadSource", "ExtenderComponentRead", "ExtenderRepresentativeRead", "ExtenderSystemRead")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal.EmbeddingRelative"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("ExtenderSetPull", "ExtenderBoundedCode", "ExtenderStrengthPull", "IterationColumnPull",
             "IterationDiagramPull", "IterationOwnerPull", "IterationCutPull")]
MODULES += ["YesMetaZFC.SetTheory.Ord.Recursion", "YesMetaZFC.SetTheory.InnerModel.Rudimentary.Tuple"]
MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("IterationEmbeddingLaws", "IterationLinearOrder", "IterationLimitSyntax", "IterationWeakState",
             "IterationWeakAppend", "IterationWeakHistory", "IterationWeakUnion", "IterationWeakSyntax",
             "IterationWeakAnswerSyntax", "IterationWeakReplay", "IterationWeakPublicWinning")]

MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
            ("TypeGameCrossImage", "TypeGameReplyReflect", "TypeGameRoundScope", "TypeGameRound",
             "TypeImageSyntax", "TypeImageRead", "TypeContinueSyntax", "TypeGameContinue", "TypeGameQueryBase",
             "TypeElasticProgramSyntax", "TypeElasticCodeTransfer", "TypeElasticNumericTransfer",
             "TypePoolRead", "TypeGameLanguageTransfer", "TypeGameCandidate", "TypeGameSubtype",
             "TypeContinueRealizeSyntax", "TypeGameRealization", "TypeGameReplyBase", "TypeGameAnchor",
             "TypeGameQueryTransfer", "TypeGameRigidRead", "TypeGameRecoverySyntax", "TypeGameRecovery",
             "TypeGameRestart")]
MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
            ("TypeNamesSource", "SubtypeReflect", "TypeGameQueryScope",
             "TypeProgramSyntax", "TypeProgramSource", "TypeProgramReflect", "SubtypeProgramTransfer")]

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
                 "ex_pre_m", "ex_short_m", "Ex_product_d", "ex_product_at_m", "Ex_value_d.mono_l",
                 "Ex_operator_d.at_l", "Ex_operator_d.total_l", "ex_inter_l", "ea_test_read_l",
                 "ex_value_at_l", "ex_value_type_l", "ex_append_unique_l", "ex_prefix_cp_l")]

SKOLEM_MODULES = ["YesMetaZFC.Model.SetTheory.Internal." + name for name in ("Skolem", "ElementaryHull", "ElementaryClub")]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.FinitaryClub"]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.FinitaryTrace", "YesMetaZFC.Model.SetTheory.Internal.ElementaryTrace"]
SKOLEM_MODULES += ["YesMetaZFC.Model.SetTheory.ClassChoice"]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory." + name for name in
                   ("Card.Properties.SuccessorRegularity", "Card.SmallUnion", "HereditaryClosure", "HereditaryAlgebra",
                    "HereditaryCover", "IndexedChoice", "CountableDirected")]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.InnerModel.Condensation.Internal"]
SKOLEM_MODULES += ["YesMetaZFC.Model.SetTheory.Internal.SeparationHull"]
SKOLEM_MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
                   ("Collection", "Uniformization", "UniformizationHull", "SourceTheory", "SourceCollapse", "SourceBranch",
                    "SourceAlgebra", "SourceSmall", "SourceCollection", "SourceSequences")]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.HereditaryCollapse"]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.InaccessibleEnumeration", "YesMetaZFC.SetTheory.LargeCardinal.EmbeddingRankRestriction"]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.RelativeRankSegment"]
SKOLEM_MODULES += ["YesMetaZFC.Model.SetTheory.Internal.RankSkolem", "YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemInitial"]
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
SKOLEM_MODULES += ["YesMetaZFC.SetTheory." + name for name in
                   ("InaccessibleHierarchy", "HereditaryFunction", "HereditarySequences")]
ZFC_BASELINE = BASELINE
SKOLEM_MODULES += ["YesMetaZFC.Model.SetTheory.Internal.SourceRankSizeInitial"]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.Collapse.RegularRank", "YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptRegular",
                   "YesMetaZFC.SetTheory.LargeCardinal.IterationCountableCover"]
SKOLEM_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.ExtenderReflectHull", "YesMetaZFC.SetTheory.LargeCardinal.IterationDiagramHull"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Rr_d", "YesMetaZFC.SetTheory.rr_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                ("It_embedding_d", "It_return_at_d", "It_return_d", "It_hull_return_d", "Ja_enum_d", "Ja_rows_d", "Ja_commute_d", "Ja_node_d",
                 "Ja_extend_d", "ja_elementary_m", "ja_rows_m", "ja_commute_m", "ja_node_m", "ja_extend_m",
                 "Ja_value_d", "ja_value_m", "Ja_cell_d", "ja_cell_m", "Ja_space_d", "Ja_seen_d", "ja_seen_m",
                 "Ja_path_d", "Ja_observe_d", "ja_observe_m", "Ja_leg_d", "ja_leg_m")]
# 全背景见证选择及商赋值代表选择允许对象 AC；给定源理论后的源内部 Łoś 按 ZF 审计。
LOS_MODULES = ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower." + name for name in
               ("Witness", "Los", "Lift", "Projection")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.SourceProjection"]
LOS_MODULES += ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
               ("SourceApplication", "RelationRelative", "RelationFunction", "RelationFunctionFamily", "ReducedPower.FormulaImage",
                "RelationSeparation", "RelationUniformCode", "SourceCollectionBasis", "RelationCollection",
             "RelationEvaluation", "RelationConstant", "RelationTraceFamily", "RelationPointwiseWitness",
             "ReducedPower.RelationSyntax", "ReducedPower.RelationLos",
             "RelationSeparationSource", "RelationSubset", "RelationSmall",
             "ReducedPower.RelationRestriction", "ReducedPower.RelationConstant",
             "RelationComposition", "RelationRealization", "RelationPower", "RelationLow", "RelationHierarchy", "RelationFunctionCapture",
             "ReducedPower.RelationPullback", "ReducedPower.RelationAssignment", "ReducedPower.RelationTrace",
             "ReducedPower.RelationProjection", "ReducedPower.RelationMeasure", "ReducedPower.RelationSuccessor",
             "ReducedPower.RelationBounded", "ReducedPower.RelationNormalize", "ReducedPower.RelationFamily")]
LOS_MODULES += ["YesMetaZFC.SetTheory.Collapse.RelationRealization"]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("ExtenderFiniteRepresentative", "ExtenderFunctionValue", "ExtenderSeedSegment",
                "ExtenderBoundedRaw", "ExtenderBoundedRealization", "ExtenderRawMeasure", "ExtenderRawReduced", "ExtenderRawProjection",
             "ExtenderRawComponent", "ExtenderRawAssembly", "ExtenderRawLimit", "ExtenderRawBounded",
             "ExtenderRawValue", "ExtenderRawRelation", "ExtenderRawLow", "ExtenderRawRank")]
LOS_MODULES += ["YesMetaZFC.Model.SetTheory.Internal.TypeGameNodeEmbedding", "YesMetaZFC.SetTheory.LargeCardinal.IterationConePull"]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("ExtenderSource", "ExtenderArrows", "ExtenderLaws",
                "ExtenderGraphs", "ExtenderSystem", "ExtenderLimit", "ExtenderElementary", "ExtenderConstant",
                "ExtenderCollapse", "ExtenderRankSource", "ExtenderDerivedLimit")]
LOS_MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullElementary"]
LOS_MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FullEmbedding"]
LOS_MODULES += ["YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Copy"]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("ExtenderUltrapower", "ExtenderCopyComponent", "ExtenderCopy", "ExtenderCopyApplication")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("ExtenderValue", "ExtenderTupleValue", "ExtenderValueAgreement", "ExtenderValueBound",
                "ExtenderSetTransfer", "ExtenderSuccessor", "ExtenderSuccessorApplication", "ExtenderCopySuccessor", "ExtenderSupportBound")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in ("IterationApply", "IterationAgreement", "IterationFork")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("RankEnumeration", "RankCover", "RankLength", "MeasurableInaccessible",
                "ExtenderPredicateComponent", "ExtenderPredicateLimit", "ExtenderStrengthBound", "ExtenderExactStrength", "ExtenderStrength", "WoodinStrength", "WoodinTrace", "WoodinTypes")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("SubtypeStretch", "TypeOneStep", "WoodinTypeStep")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in ("WoodinGameTypes", "WoodinGameReset")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in ("ExtenderBranch", "ExtenderLocalRead")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("ExtenderSourceLimit", "ExtenderSourceNode", "IterationLocalApply", "IterationLocalAgreement",
                "ExtenderSourceTrace", "ExtenderSourceSubsets", "ExtenderSourceSuccessors", "ExtenderRankImage", "ExtenderRankAgreement",
                "ExtenderCopySubsets")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("ExtenderStrengthReturn", "ExtenderClosedLimit", "ExtenderValueApply", "ExtenderOmegaClosed", "ExtenderSetValue",
                "ExtenderMatrixValue", "ExtenderSetComponent", "ExtenderSetInclusion", "ExtenderSetCopy")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.IterationDescentStep"]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal.IterationCutStep"]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in ("IterationCutHistory", "IterationCutNormalize", "IterationDescent")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("IterationModel", "IterationInitial", "IterationCopyModel", "IterationCopyApply", "IterationCopyStep",
                "IterationCopyRow", "IterationCopyPast", "IterationCopyHistory", "IterationCopyExtend", "IterationCopyPadding", "IterationCopySequence", "IterationCopyUnion", "IterationCopyTree")]
LOS_MODULES += ["YesMetaZFC.SetTheory.CumulativeRegularCover", "YesMetaZFC.SetTheory.LargeCardinal.IterationFailureCopy"]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("ExtenderUltraCertificate", "IterationUltraRead")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("IterationUltraPull", "IterationInitialPull", "IterationPartialColumn", "IterationNicePull", "IterationNiceReturn",
                "IterationLadder", "IterationLadderCone", "IterationHullReturn")]
LOS_MODULES += ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
               ("IterationCountableLimit", "IterationWeakLimit", "IterationWeakSuccessor", "IterationWeakAnswer",
                "IterationWeakBound", "IterationWeakChoice", "IterationWeakRun", "IterationWeakWinning",
                "IterationWeakPublic", "IterationWeak")]
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
                 "Ic_model_d", "ic_model_m", "Ic_row_d", "ic_row_m", "Ic_cell_d", "ic_cell_m", "Ic_at_d", "ic_at_m",
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
                      "sc_collection_raw_l", "sc_collection_on_raw_l", "sfm_sep_test_raw_l", "sfm_sep_raw_l", "sc_separation_raw_l",
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
                  ("sc_separation_forward_l", "Sc_theory_d.pull_l", "Sc_collection_d.pull_l", "smap_uniform_l", "sc_collection_forward_l", "Sc_collection_d.map_l", "Sc_theory_d.map_l",
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
                "tg_context_data_m", "tg_saved_record0_m", "Tg_saved_code_d", "tg_saved_m",
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
RELATIVE_INITIAL_MODULES = ["YesMetaZFC.SetTheory.LargeCardinal." + name for name in
                          ("ExtenderReadRelative", "ExtenderReadLayer", "TypeGameSeedBound", "TypeGameRelativeContext",
                           "TypeGameRelativeRoot", "TypeGameRelativeStart", "ExtenderSourceRelative")]
MODULES += RELATIVE_INITIAL_MODULES
LOS_MODULES += RELATIVE_INITIAL_MODULES
ZFC_CODE_MODULES = ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
                    ("ZfcCode", "ZfcDecode", "ZfcRank", "SourceBinaryRelation", "ZfcSource",
                     "RelationCollectCode", "ZfcTransfer")]
MODULES += ZFC_CODE_MODULES
LOS_MODULES += ZFC_CODE_MODULES
LAYER_MODULES = ["YesMetaZFC.Model.SetTheory.Internal." + name for name in
                 ("RelationLayer", "RelationProgram", "RelationLayerSeparation", "RelationRecord")]
MODULES += LAYER_MODULES
LOS_MODULES += LAYER_MODULES
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Zc_schemas_d", "Zc_model_d", "zc_base_m", "zc_separation_m", "zc_collection_m", "zc_model_m", "Rr_layer_d")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.fs_read0_m"]
CHOICE_FREE += ["YesMetaZFC.SetTheory.Internal." + name for name in
               ("Rr_truth_d", "Rf_record_d", "Rf_tuple_d", "rr_params_m", "rr_truth_m", "rf_record_m", "rf_tuple_m")]
CHOICE_FREE += ["YesMetaZFC.SetTheory.LargeCardinal.Tg_kernel_d"]
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.LargeCardinal." + name: BASELINE for name in
                      ("fs_omega_relative_l", "fs_read_relative_l", "fs_rank_relative_l", "Fs_read_d.rank_l",
                       "fs_read0_sat_l", "fs_read0_relative_l", "Fs_read_d.map_layer_l",
                       "ec_coherent_relative_l", "ea_atoms_relative_l", "en_normal_relative_l",
                       "sf_finite_power_l", "em_family_relative_l", "It_local_d.measures_l", "It_local_d.bounded_model_l",
                       "Tg_context_d.kernel_l", "Tg_kernel_d.renew_l", "Tg_context_d.root_relative_l",
                       "Tg_kernel_d.continue_l", "Tg_kernel_d.language_l", "Tg_kernel_d.realize_seed_l",
                       "Tg_kernel_d.rigid_seed_l", "Tg_kernel_d.recover_seed_l", "Tg_kernel_d.reply_queries_l",
                       "tg_image_omega_l", "tg_successor_omega_l", "fs_sequences_relative_l", "fs_collapse_relative_l")})
LOS_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.Internal." + name: BASELINE for name in
                     ("sc_finite_function_l", "sc_relative_sat_l", "rt_record_in_read_l", "rt_record_in_save_l",
                      "rr_truth_sat_l", "Rr_truth_d.map_l", "rr_truth_mem_l", "rf_record_mem_l", "rf_tuple_mem_l",
                      "zc_model_sat_l", "Zc_model_d.separate_l",
                      "Zc_model_d.collect_l", "Zc_model_d.native_l", "Zc_model_d.membership_l",
                      "sc_binary_relation_l", "Zc_model_d.theory_l", "Zc_model_d.power_l", "Zc_model_d.collection_l",
                      "Zc_model_d.source_l", "sfm_collect_raw_l", "Zc_model_d.map_l", "rr_layer_mem_l",
                      "Rr_layer_d.restrict_l", "Rr_layer_d.relative_l", "Rr_layer_d.program_l", "Rr_layer_d.separation_l",
                      "Smap_d.layer_map_l", "Smap_d.relative_image_l")})
HOD_CHOICE_MODULES = ["YesMetaZFC.SetTheory.InnerModel.HOD." + name for name in ("Choice", "BracketChoice")]
HOD_ZF_BOUNDS = {"YesMetaZFC.SetTheory.InnerModel." + name: BASELINE for name in
                 ("hod_choice_set_l", "hod_model_l", "hod_model_ext_l")}
HOD_ZF_BOUNDS.update({"YesMetaZFC.SetTheory.InnerModel." + name: BASELINE for name in
                      ("hb_pick_exists_l", "hb_pick_unique_l", "hb_choice_set_l")})

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
