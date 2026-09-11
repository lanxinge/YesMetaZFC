import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRosserDelta0
import YesMetaZFC.Model.ZFC.Pure.PureCompletedStage
import YesMetaZFC.Model.ZFC.Pure.PureStageTwoSemantics
import YesMetaZFC.Model.ZFC.Pure.PureRoundOneSpecifications
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.DefinitionContracts
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormalSystem
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.Project
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.SyntaxCoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.SyntaxNumeralCoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.StructuralCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.WeakenBoundStructuralCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormulaStructuralCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.AbstractFreeTopFormulaCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.OccurrenceStructuralCorrectness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CodeDomain
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ProofSequenceCodeConstruction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hierarchy
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceGraph
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceDomain
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceBounds
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SuccessorCodeDomain
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta0Support
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSchemaClosure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicForallPrefix
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FixedAxiomTable
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCertificateTable
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFixedTable
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalCertificate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicSchemaCertificate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicSchemaLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicRosserAssembly
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicGraph
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicProofCertificate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscript
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta1ProofPresentation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceConditionInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatSequenceInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceDomainSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceSupportTheory
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSyntaxSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSyntaxCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuineCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuineFormulaCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofRows
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofTerminal
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicProofSupport
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.PairingInversionDirect
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuredCertificateCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuralSequenceConditionInversion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicTheoryLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicForallGeneralization
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFirstOrderLogicalLine
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFixedRows
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicCheckedWitness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuredWitness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Rosser
import YesMetaZFC.SetTheory.Ord.PrimePowerSequence
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.NatDecode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.NatEncode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaConclusion
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaQuotationAudit
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaEnvelope
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaTerm
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaBody
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaRenameInstances
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaBodyDerives
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaRenameDerives
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaTemplateDerives
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaClosure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.NatPacketLink
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaJoinInstances
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaPacketSpec
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaKernelInstances
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.BaseAxiomPacketSpec
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SupportParameterDerives
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SupportRealization
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedAxiomPacket
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofPresentation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedRosser
import YesMetaZFC.Model.ZFC.Pure.PureRelationFunctions
import YesMetaZFC.Model.ZFC.Pure.PureMappingSpecifications
import YesMetaZFC.Model.ZFC.Pure.PureCoordinateSpecifications
import YesMetaZFC.Model.ZFC.Pure.PureMappingOperations
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureRosserTransfer
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedDerivability
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedProofReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralOrderReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalQuotationEvaluation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalVerificationTrace
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralTraceDecision
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalProjectionReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalSyntaxReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalTransformReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalSchemaQueries
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalCheckedStepReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedIntrospection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedLoeb
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedSecondIncompleteness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSecondIncompleteness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedTarski
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.ReducedTarskiParameters
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureTarskiSource
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureTarski

/-!
# 一阶形式系统编码元理论入口

当前普通可证明性及对象一致性句子见 `ReducedProvability`；
`necessitation`、`distribution`、`introspection` 已分别证明 D1、D2、D3。
D2 使用原有内部自然数证明图，实际轨迹合成见 `ReducedProofComposition`。
`InternalNumeralSubstitution` 提供整个内部 ω 上的合法数码及固定公式代入总性。
`ReducedProofComposition` 与 `ReducedProofLogicalConstruction` 支持内部结论码上的节点装配、MP 与存在引入。
`InternalNumeralProof.exists_introduction` 已消去数码实例的全部语法和模式 2 变换义务。
`InternalNumeralReflection.natural`、`zero`、`nonzero` 已构造自然数 guard 和零测试的内部证明。
`natural_derives` 给出统一闭句子；内部归纳使用实际反射公式及最终阶段对应。
`InternalNumeralProof.specialize_finite` 覆盖任意有限参数数目的数码特化；单参数入口复用它的构造。
`InternalNumeralReflection.equal`、`unequal` 已证明任意两个内部自然数的数码相等／不等反射。
`InternalNumeralReflection.order`、`weak_order` 提供序关系的正负反射；`arithmetic_evaluation` 给出加乘幂求值。
`InternalCodingEvaluation` 将求值扩展到 Gödel 配对、复合项、节点、字段列和参数化 AST 码项；
`InternalQuotationEvaluation` 保留既有结构 quotation，所有结果均生成原证明图接受的等式证明。
`atomic_reflection` 与 `boolean_reflection` 组合原子判断及逻辑联结词；
`bounded_term_reflection` 覆盖自然数复合界项的全称／存在正负反射。
`finite_verification` 保留给定有限骨架的装配接口。
`proof_trace_positive` 已反射原证明树的任意内部 checked 轨迹，消去有限骨架及连边证明输入。
`verification_reflection`、`proof_matrix_reflection` 精确接回原验证矩阵与自然数 guard；
`ReducedProvability.introspection` 已完成当前原可证明性谓词的 D3。
`ReducedProvability.loeb_axiom_m` 和 `loeb_m` 给出同一谓词的内部 Löb 公式及普通 Löb 规则；
固定点由 `ObjectLoeb.fixedPoint_m` 使用原对角构造实际生成。
`second_incompleteness_m` 只假定原理论一致，排除已有一致性句子的普通推导；
`second_incompleteness_internal_m` 给出同一句子的内部第二不完备公式。
`PureSentenceTransfer` 提供纯句子的嵌入往返及双向推导接口。
`PureProvability` 使用嵌入后的原 quotation 与检查器，在 `PureModel.theory` 中
证明 D1–D3、实际固定点、Löb 和第二不完备定理；`checked_iff_m` 精确表示裸 ZFC 推导。
`consistency_translation_m` 确认纯一致性句子等于原一致性句子的消元翻译。
`ReducedTarski` 为任意候选一元真谓词实际构造 `liarSentence_m`，
`liar_refutes_m` 在原支撑理论中否定相应真值等价式；
`undefinable_syntax_m` 只假定原理论一致，`undefinable_semantics_m` 覆盖任意原模型。
`ReducedTarski.Parameters` 进一步保留任意有限参数上下文，构造实际 `liarFormula_m`，
并在每个模型参数赋值下排除正确判定全部相应开放公式的谓词。
`PureTarskiSource` 将候选、反例和推导落到裸 ZFC 的纯语言中，
`predicate_satisfies_m` 保留原纯候选及每组参数赋值，`undefinable_source_at_m`
排除对规范扩张中全部源公式真值的定义。其编码仍指向源公式。
`PureQuotation` 与 `PureFixedPoint` 进一步给出最终纯公式自身完整 AST 编码的带参数固定点；
`PureTarski` 仅量化纯公式，并在每组任意有限参数赋值下排除纯真值定义。

该入口导出内在 quotation、结构语法正确性、对象证明图及抽象 Rosser 终局。
`AxiomPresentation` 与 `ProofCertificate` 已在完整支撑公理理论上实例化，
提供显式公理证书及与普通 Hilbert 推导等价的结构证书。
`intrinsic_zfc_nat_decode` 已提供实际可计算的自然数正向解码，
`intrinsic_zfc_nat_check_sound` 将接受结果重放为原理论中的普通 `Derives`。

`intrinsic_zfc_nat_encode` 与 `intrinsic_zfc_nat_decode_encode` 已完成逆向编码和
完整证书往返；`intrinsic_zfc_derives_iff_nat_certificate` 给出自然数入口的完备性。
完整等价公理基的对象表示已由下述 ReducedAxiomPacket 完成；整棵证明树的对象图
及其正负表示合同由 `ReducedProofPresentation` 完成。旧 ZFC 对象 verifier
只装配 ZFC 固定公理和 schema，不能据其名称推断其已覆盖整个支撑理论。

`IntrinsicQuotation.quote` 保留当前全部公式构造子，并有宿主往返、单射及对象码不等
证明。公共 `Delta1ProofPresentation` 与 `RosserPresentation` 使用此码。
旧 Hilbert quotation 与当前自然数检查器不相容，具体反例见 `SchemaQuotationAudit`。
`SchemaConclusion` 已完成分离、收集、替换三类已解析实例的结论比较正负表示；
`SchemaEnvelope` 已表示任意原始树的模式外壳，`SchemaTerm` 已表示正文项的
作用域检查，二者均有真实正负对象推导。`SchemaBody` 已证明整个正文识别的
可靠性、完备性与拒绝判准；`SchemaRename` 已证明有限表递归和类型化重命名
对成功与失败结果的交换律，并连接实际六个模式位置和新 quotation。
`SchemaBodyDerives`、`SchemaRenameDerives` 进一步给出统一 Delta0 对象图的真实正负推导，
覆盖任意原始树、任意候选输出和六个实际模式位置。`SchemaTemplateDerives` 已完成
三类固定装配模板的同一带标签 Delta0 公式及正负推导，并逐节点连接实际核心构造。
`SchemaClosure` 已完成任意层数的新码全称闭合图；`NatPacketLink` 已将实际版本一
包解码器连接到对象树码，两者均有统一 Delta0 公式及正负普通推导。`SchemaTable`
已表示六个重命名位置的参数表生成；`SchemaJoin` 的四元图在对象层量化七个中间码，
从任意原始正文直接连接三类实际 Project 闭句，并给出正负推导。
`KernelQuotation` 已完成 Project 树码到当前内核 quotation 的转换，`SchemaPacket`
已把模式外壳、传输包和内部四元图连接成固定二元图。`BaseAxiomPacket` 进一步并入
八条固定公理，给出任意包和候选自然数的正负普通推导，其 `presentation` 是
`Delta1AxiomPresentation intrinsic_zfc_theory intrinsic_zfc_axiom_theory` 的具体实例。
基础公理成员关系的可靠性、完备性与正负表示均已填入。
`SupportParameterDerives` 已完成十一类参数化支撑公理的证书合法性正负表示，
包含当前内核全部函数项及 indexed 外壳，并精确对齐原公理分支的接受、拒绝结果。
`SupportRealization` 已完成十一类固定模板的完整项代入、任意自由上下文的全称闭合，
原始码装配逐节点等于原证书的实际结论，并连接当前 quotation 和内层参数外壳的版本一包。
任意成功装配的闭句均在对应原族理论中有普通 Hilbert 推导。

`SupportAssembly.sentence_of_closedTemplate` 证明每类参数公理均由一份闭模板导出。
`SupportAxiomBasis` 沿完整原理论结构证明
有限生成性，`ReducedAxioms.basis` 去重后含 119 条原公理。
`ReducedAxioms.derives_iff` 对任意上下文证明等价公理基与原理论具有同一普通推导。
`ReducedAxiomPacket.presentation` 已给出整个等价公理基的具体 Delta1AxiomPresentation，
包含原 ZFC 基础分支、支撑有限表、实际自然数包解码以及当前 quotation 上的正负推导。
它表示等价公理基的成员关系，不声称表示原参数证书逐字装配关系；后者不再阻塞本路线。
`ReducedProofPresentation.presentation` 已通过 `ReducedAxioms.liftProofPresentation`
恢复原目标理论的完整证明表示。

`Delta0ProofGraph` 记录对象图的量词分类，`RosserPresentation` 在证明表示、
有限比较装配和给定的固定点证明上推出抽象不完备结论。`ReducedRosser` 已有具体
固定点构造，`PureRosserComplete` 完成任意原模型对应与裸 ZFC Rosser 不完备终点。
-/
