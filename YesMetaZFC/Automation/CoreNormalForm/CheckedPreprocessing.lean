import YesMetaZFC.Automation.CoreNormalForm.LocalSkolemSoundness
import YesMetaZFC.Automation.CoreNormalForm.DefinitionalCnfSoundness
import YesMetaZFC.Automation.CoreNormalForm.NormalizationSoundness

/-!
# Core normal form checked preprocessing

本模块把当前新预处理主线串成一个 checked payload：

1. core normalizer trace；
2. dependency-driven anti-prenex / mini-scoping；
3. local Skolem trace；
4. equality-visible definitional CNF。

这里的 `CheckedPreprocessing.sound` 先给出结构 soundness 骨架：checked 总证书确实钉住
每个阶段的 checker 和相邻阶段的输入输出。真正的语义等价、Skolem 保守性和定义性
CNF 保守性将后续作为各 phase 的 theorem 接入。
-/

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax
namespace NormalForm

namespace CheckedPreprocessing

universe x

/-- checked preprocessing 的执行配置。 -/
structure Settings where
  normalForm : _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Config := {}
  antiPrenex : AntiPrenex.Config := {}
  localSkolem : LocalSkolem.Config := {}
  definitionalCnf : DefinitionalCnf.Config := {}
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr

/-- 逐字段比较公共 stats。 -/
def statsEq (left right : Certificate.Stats) : Bool :=
  left.steps == right.steps &&
    left.clauses == right.clauses &&
      left.literals == right.literals &&
        left.generated == right.generated &&
          left.retained == right.retained &&
            left.verified == right.verified &&
              left.residuals == right.residuals &&
                left.fuel == right.fuel

/-- 汇总四个预处理阶段的审计摘要。 -/
def statsOf (settings : Settings) (source : Formula) (normalizationTrace : Trace)
    (antiPrenex : AntiPrenexPayload) (localSkolem : LocalSkolemPayload)
    (cnf : DefinitionalCnfPayload) : Certificate.Stats :=
  {
    steps :=
      normalizationTrace.steps.size +
        antiPrenex.steps +
          localSkolem.steps +
            cnf.definitionCount
    clauses := cnf.clauseCount
    literals := cnf.literalCount
    generated := source.size
    retained := cnf.clauseCount
    verified :=
      normalizationTrace.steps.size +
        antiPrenex.steps +
          localSkolem.steps +
            cnf.definitionCount
    residuals :=
      (if antiPrenex.fuelExhausted then 1 else 0) +
        (if localSkolem.budgetSatisfied then 0 else 1) +
          (if cnf.budgetSatisfied then 0 else 1)
    fuel :=
      settings.normalForm.fuel +
        settings.antiPrenex.maxSteps +
          settings.localSkolem.maxSteps +
            settings.definitionalCnf.maxDefinitions
  }

/-- 整条 checked preprocessing 的可检查 payload。 -/
structure Payload where
  settings : Settings
  source : Formula
  normalized : Formula
  normalizationTrace : Trace
  initialNnf : Nnf
  antiPrenex : AntiPrenexPayload
  localSkolem : LocalSkolemPayload
  definitionalCnf : DefinitionalCnfPayload
  clauses : ClauseSet
  stats : Certificate.Stats
  deriving Repr, Lean.ToExpr

namespace Payload

/-- 运行四段预处理，构造总 payload。 -/
def build (settings : Settings) (source : Formula) : Payload :=
  let normalized := normalizeFormula source (config := settings.normalForm)
  let normalizationTrace := Trace.ofFormula source (config := settings.normalForm)
  let initialNnf := toNnfWith Polarity.positive normalized
  let antiPrenex := AntiPrenexPayload.build settings.antiPrenex initialNnf
  let localSkolem := LocalSkolemPayload.build settings.localSkolem antiPrenex.result
  let definitionalCnf :=
    DefinitionalCnfPayload.build settings.definitionalCnf [] localSkolem.result
  {
    settings := settings
    source := source
    normalized := normalized
    normalizationTrace := normalizationTrace
    initialNnf := initialNnf
    antiPrenex := antiPrenex
    localSkolem := localSkolem
    definitionalCnf := definitionalCnf
    clauses := definitionalCnf.clauses
    stats := statsOf settings source normalizationTrace antiPrenex localSkolem definitionalCnf
  }

/-- 各阶段自身 checker 是否通过。 -/
def phaseCheck (payload : Payload) : Bool :=
  payload.source.check? &&
    payload.normalized.check? &&
      Trace.check payload.settings.normalForm payload.normalizationTrace &&
        AntiPrenexPayload.check payload.antiPrenex &&
          LocalSkolemPayload.check payload.localSkolem &&
            DefinitionalCnfPayload.check payload.definitionalCnf

/-- 总 payload 是否正确串起相邻阶段。 -/
def linkCheck (payload : Payload) : Bool :=
  TraceExpr.eq payload.normalizationTrace.source (TraceExpr.formula payload.source) &&
    TraceExpr.eq payload.normalizationTrace.target (TraceExpr.formula payload.normalized) &&
      SyntaxEq.nnfEq payload.initialNnf
        (toNnfWith Polarity.positive payload.normalized) &&
        SyntaxEq.nnfEq payload.antiPrenex.source payload.initialNnf &&
          SyntaxEq.nnfEq payload.localSkolem.source payload.antiPrenex.result &&
            SyntaxEq.nnfEq payload.definitionalCnf.source payload.localSkolem.result &&
              ClauseSet.eq payload.clauses payload.definitionalCnf.clauses

/-- 七条相邻阶段链接的独立证明合成总 link checker。 -/
theorem linkCheck_eq_true_of_components
    (payload : Payload)
    (hTraceSource :
      TraceExpr.eq payload.normalizationTrace.source
        (TraceExpr.formula payload.source) = true)
    (hTraceTarget :
      TraceExpr.eq payload.normalizationTrace.target
        (TraceExpr.formula payload.normalized) = true)
    (hInitialNnf :
      SyntaxEq.nnfEq payload.initialNnf
        (toNnfWith Polarity.positive payload.normalized) = true)
    (hAntiPrenex :
      SyntaxEq.nnfEq payload.antiPrenex.source payload.initialNnf = true)
    (hLocalSkolem :
      SyntaxEq.nnfEq payload.localSkolem.source payload.antiPrenex.result = true)
    (hDefinitionalCnf :
      SyntaxEq.nnfEq payload.definitionalCnf.source payload.localSkolem.result = true)
    (hClauses :
      ClauseSet.eq payload.clauses payload.definitionalCnf.clauses = true) :
    linkCheck payload = true :=
  Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr
        ⟨Bool.and_eq_true_iff.mpr
          ⟨Bool.and_eq_true_iff.mpr
            ⟨Bool.and_eq_true_iff.mpr
              ⟨hTraceSource, hTraceTarget⟩,
              hInitialNnf⟩,
            hAntiPrenex⟩,
          hLocalSkolem⟩,
        hDefinitionalCnf⟩,
      hClauses⟩

/-- 总 payload 的计数摘要是否由阶段数据复算得到。 -/
def metricCheck (payload : Payload) : Bool :=
  statsEq payload.stats
    (statsOf payload.settings payload.source payload.normalizationTrace
      payload.antiPrenex payload.localSkolem payload.definitionalCnf)

/-- checked preprocessing 的 kernel-facing 语义 checker。 -/
def check (payload : Payload) : Bool :=
  phaseCheck payload && linkCheck payload

/--
checked preprocessing 的完整构造审计。

计数复算和定义性 CNF 的非语义审计不进入 soundness 边界。
-/
def auditCheck (payload : Payload) : Bool :=
  check payload &&
    (metricCheck payload &&
      AntiPrenexPayload.auditCheck payload.antiPrenex &&
        DefinitionalCnfPayload.auditCheck payload.definitionalCnf)

/-- 构造已通过 checker 的总预处理 payload。 -/
def mk? (settings : Settings) (source : Formula) :
    Option (Certificate.Checked Payload Payload.check) :=
  Certificate.Checked.mk? (check := Payload.check) (build settings source)

end Payload

/-- 已检查的预处理证书。 -/
abbrev Checked := Certificate.Checked Payload Payload.check

/-- 总 checker 通过后得到的结构 soundness 骨架。 -/
structure Sound (payload : Payload) : Prop where
  checked : Payload.check payload = true
  phasesChecked : Payload.phaseCheck payload = true
  linksChecked : Payload.linkCheck payload = true

/-- checker 通过时，各阶段 checker 与阶段链接都已固定。 -/
theorem sound_of_check {payload : Payload} (h : Payload.check payload = true) :
    Sound payload := by
  unfold Payload.check at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hPhase, hLink⟩
  exact {
    checked := h
    phasesChecked := hPhase
    linksChecked := hLink
  }

/-- checked preprocessing 的公开 soundness 骨架。 -/
def sound (checked : Checked) : Sound checked.payload :=
  sound_of_check checked.checked

/-- checked normalization trace 在同一合同模型和环境中保持 source 公式语义。 -/
theorem satisfies_source_iff_normalized (checked : Checked)
    {M : Semantics.Model} (contract : Semantics.FoolLambdaContract M)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) :
    Semantics.Formula.Satisfies env checked.payload.source ↔
      Semantics.Formula.Satisfies env checked.payload.normalized := by
  have hSound := sound checked
  have hPhases := hSound.phasesChecked
  have hLinks := hSound.linksChecked
  simp only [Payload.phaseCheck, Bool.and_eq_true_iff] at hPhases
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  have hTrace :
      Trace.check checked.payload.settings.normalForm
        checked.payload.normalizationTrace = true :=
    hPhases.1.1.1.2
  have hSourceLink :
      TraceExpr.eq checked.payload.normalizationTrace.source
        (TraceExpr.formula checked.payload.source) = true :=
    hLinks.1.1.1.1.1.1
  have hTargetLink :
      TraceExpr.eq checked.payload.normalizationTrace.target
        (TraceExpr.formula checked.payload.normalized) = true :=
    hLinks.1.1.1.1.1.2
  have hTraceSem :=
    Semantics.Trace.sound_of_check contract
      checked.payload.settings.normalForm env hFree
        checked.payload.normalizationTrace hTrace
  have hSourceEq :
      checked.payload.normalizationTrace.source =
        TraceExpr.formula checked.payload.source :=
    Semantics.TraceExpr.eq_eq_true.mp hSourceLink
  have hTargetEq :
      checked.payload.normalizationTrace.target =
        TraceExpr.formula checked.payload.normalized :=
    Semantics.TraceExpr.eq_eq_true.mp hTargetLink
  rw [hSourceEq, hTargetEq] at hTraceSem
  exact hTraceSem

/-- checked positive-NNF 链接把 normalized 公式语义等价地搬到 initial NNF。 -/
theorem satisfies_normalized_iff_initialNnf (checked : Checked)
    {M : Semantics.Model} (env : Semantics.Env M) :
    Semantics.Formula.Satisfies env checked.payload.normalized ↔
      Semantics.Nnf.Satisfies env checked.payload.initialNnf := by
  have hLinks := (sound checked).linksChecked
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  have hInitialNnf :
      SyntaxEq.nnfEq checked.payload.initialNnf
        (toNnfWith Polarity.positive checked.payload.normalized) = true :=
    hLinks.1.1.1.1.2
  have hInitialNnfEq :
      checked.payload.initialNnf =
        toNnfWith Polarity.positive checked.payload.normalized :=
    SyntaxEq.nnfEq_eq_true.mp hInitialNnf
  rw [hInitialNnfEq]
  exact
    (Semantics.Nnf.satisfies_toNnfWith_positive env
      checked.payload.normalized).symm

/-- checked anti-prenex trace 保持 initial NNF 的逐环境语义。 -/
theorem satisfies_initialNnf_iff_antiPrenexResult (checked : Checked)
    {M : Semantics.Model} (env : Semantics.Env M) :
    Semantics.Nnf.Satisfies env checked.payload.initialNnf ↔
      Semantics.Nnf.Satisfies env checked.payload.antiPrenex.result := by
  have hSound := sound checked
  have hPhases := hSound.phasesChecked
  have hLinks := hSound.linksChecked
  simp only [Payload.phaseCheck, Bool.and_eq_true_iff] at hPhases
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  have hAntiPrenex :
      AntiPrenexPayload.check checked.payload.antiPrenex = true :=
    hPhases.1.1.2
  have hAntiPrenexSource :
      SyntaxEq.nnfEq checked.payload.antiPrenex.source
        checked.payload.initialNnf = true :=
    hLinks.1.1.1.2
  have hAntiPrenexSourceEq :
      checked.payload.antiPrenex.source = checked.payload.initialNnf :=
    SyntaxEq.nnfEq_eq_true.mp hAntiPrenexSource
  rw [← hAntiPrenexSourceEq]
  exact AntiPrenexPayload.semanticEquivalent_of_check hAntiPrenex env

/-- normalization、positive NNF 与 anti-prenex 的整段逐环境语义等价。 -/
theorem satisfies_source_iff_antiPrenexResult (checked : Checked)
    {M : Semantics.Model} (contract : Semantics.FoolLambdaContract M)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) :
    Semantics.Formula.Satisfies env checked.payload.source ↔
      Semantics.Nnf.Satisfies env checked.payload.antiPrenex.result :=
  (satisfies_source_iff_normalized checked contract env hFree).trans
    ((satisfies_normalized_iff_initialNnf checked env).trans
      (satisfies_initialNnf_iff_antiPrenexResult checked env))

/--
纯一阶入口把 normalization 固定为恒等变换后，source 到 anti-prenex 的语义链不需要
FOOL/lambda 合同。
-/
theorem satisfies_source_iff_antiPrenexResult_of_normalized_eq
    (checked : Checked)
    (hNormalized :
      checked.payload.normalized = checked.payload.source)
    {M : Semantics.Model} (env : Semantics.Env M) :
    Semantics.Formula.Satisfies env checked.payload.source ↔
      Semantics.Nnf.Satisfies env checked.payload.antiPrenex.result := by
  rw [← hNormalized]
  exact
    (satisfies_normalized_iff_initialNnf checked env).trans
      (satisfies_initialNnf_iff_antiPrenexResult checked env)

/-- checked 总证书中的 Local Skolem payload 已通过自己的完整 checker。 -/
theorem localSkolem_checked (checked : Checked) :
    LocalSkolemPayload.check checked.payload.localSkolem = true := by
  have hPhases := (sound checked).phasesChecked
  simp only [Payload.phaseCheck, Bool.and_eq_true_iff] at hPhases
  exact hPhases.1.2

/-- Local Skolem 的 source 是整问题 anti-prenex 输出，而不是单独某个 premise。 -/
theorem localSkolem_source_eq_antiPrenexResult (checked : Checked) :
    checked.payload.localSkolem.source =
      checked.payload.antiPrenex.result := by
  have hLinks := (sound checked).linksChecked
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  exact SyntaxEq.nnfEq_eq_true.mp hLinks.1.1.2

/-- checked Local Skolem payload 的共享 freshness 与依赖参数不变量。 -/
theorem localSkolem_sharedStateSound (checked : Checked) :
    LocalSkolemPayload.SharedStateSound checked.payload.localSkolem :=
  LocalSkolemPayload.sharedStateSound_of_check (localSkolem_checked checked)

/--
anti-prenex 反模型可以扩张为满足 Local Skolem 输出的新模型，并保留旧 frame。
-/
theorem localSkolem_soundExtension_of_antiPrenexResult
    (checked : Checked) {M : Semantics.Model} (env : Semantics.Env M)
    (hAntiPrenex :
      Semantics.Nnf.Satisfies env checked.payload.antiPrenex.result) :
    Nonempty
      (Semantics.LocalSkolemSoundness.SoundExtension
        (LocalSkolem.initialState checked.payload.antiPrenex.result)
        checked.payload.localSkolem.result M env) := by
  have hSourceEq := localSkolem_source_eq_antiPrenexResult checked
  have hLocalSource :
      Semantics.Nnf.Satisfies env checked.payload.localSkolem.source := by
    simpa [hSourceEq] using hAntiPrenex
  have hExtension :=
    LocalSkolemPayload.soundExtension_of_check
      (localSkolem_checked checked) env hLocalSource
  simpa [hSourceEq] using hExtension

/--
原始 source 反模型沿 normalization、NNF、anti-prenex 后扩张到 Local Skolem 模型。
-/
theorem localSkolem_soundExtension_of_source (checked : Checked)
    {M : Semantics.Model} (contract : Semantics.FoolLambdaContract M)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (hSource : Semantics.Formula.Satisfies env checked.payload.source) :
    Nonempty
      (Semantics.LocalSkolemSoundness.SoundExtension
        (LocalSkolem.initialState checked.payload.antiPrenex.result)
        checked.payload.localSkolem.result M env) :=
  localSkolem_soundExtension_of_antiPrenexResult checked env
    ((satisfies_source_iff_antiPrenexResult checked contract env hFree).mp hSource)

/-- checked 总证书中的定义性 CNF payload 已通过自己的完整 checker。 -/
theorem definitionalCnf_checked (checked : Checked) :
    DefinitionalCnfPayload.check checked.payload.definitionalCnf = true := by
  have hPhases := (sound checked).phasesChecked
  simp only [Payload.phaseCheck, Bool.and_eq_true_iff] at hPhases
  exact hPhases.2

/-- 定义性 CNF 的 source 是批量 Local Skolem 的唯一输出。 -/
theorem definitionalCnf_source_eq_localSkolemResult (checked : Checked) :
    checked.payload.definitionalCnf.source =
      checked.payload.localSkolem.result := by
  have hLinks := (sound checked).linksChecked
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  exact SyntaxEq.nnfEq_eq_true.mp hLinks.1.2

/-- 总 payload 的最终字句集就是定义性 CNF payload 的字句集。 -/
theorem clauses_eq_definitionalCnfClauses (checked : Checked) :
    checked.payload.clauses =
      checked.payload.definitionalCnf.clauses := by
  have hLinks := (sound checked).linksChecked
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  exact Semantics.ClauseSet.eq_eq_true.mp hLinks.2

/--
整条批量预处理的统一环境族扩张：固定一次 Skolem 模型和定义谓词模型，随后把任意
well-sorted、共享 bound stack 的环境机械搬到最终模型。
-/
structure ModelExtension (checked : Checked)
    (M : Semantics.Model) (base : Semantics.Env M) where
  sourceSupported :
    Semantics.FreeSupport.NnfSupportedBy []
      checked.payload.antiPrenex.result
  localSkolem :
    Semantics.LocalSkolemSoundness.UniformSoundExtension
      (LocalSkolem.initialState checked.payload.antiPrenex.result)
      checked.payload.antiPrenex.result
      checked.payload.localSkolem.result M base
  definitionalCnf :
    Semantics.DefinitionalCnf.UniformSoundExtension
      checked.payload.definitionalCnf.contextSorts
      checked.payload.definitionalCnf.source
      checked.payload.definitionalCnf.root
      checked.payload.definitionalCnf.clauses
      checked.payload.definitionalCnf.definitions
      localSkolem.extension.target
      (localSkolem.extension.rebase base)

namespace ModelExtension

/-- 组合扩张的固定最终模型。 -/
def target {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base) :
    Semantics.Model :=
  Semantics.Model.overrideDefinitions
    extension.localSkolem.extension.target
    (extension.localSkolem.extension.rebase base)
    checked.payload.definitionalCnf.definitions

/-- 把任意源环境依次搬过 Skolem 扩张和定义谓词扩张。 -/
def rebase {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    (env : Semantics.Env M) : Semantics.Env extension.target :=
  Semantics.Env.rebaseOverrideDefinitions
    (extension.localSkolem.extension.rebase base)
    checked.payload.definitionalCnf.definitions
    (extension.localSkolem.extension.rebase env)

/-- 把最终模型环境依次回拉过定义谓词覆盖和 Skolem 函数覆盖。 -/
def unbase {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    (env : Semantics.Env extension.target) : Semantics.Env M :=
  extension.localSkolem.extension.unbase <|
    Semantics.Env.unbaseOverrideDefinitions env

/-- 组合环境搬运与回拉互为右逆。 -/
theorem rebase_unbase {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    (env : Semantics.Env extension.target) :
    extension.rebase (extension.unbase env) = env := by
  unfold rebase unbase
  rw [extension.localSkolem.extension.rebase_unbase,
    Semantics.Env.rebaseOverrideDefinitions_unbaseOverrideDefinitions]

/-- 组合环境回拉与搬运互为左逆。 -/
theorem unbase_rebase {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    (env : Semantics.Env M) :
    extension.unbase (extension.rebase env) = env := by
  unfold rebase unbase
  rw [Semantics.Env.unbaseOverrideDefinitions_rebaseOverrideDefinitions,
    extension.localSkolem.extension.unbase_rebase]

/-- 组合环境回拉保持 typed 自由变量 sort。 -/
theorem unbaseRespectsFree {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    {env : Semantics.Env extension.target}
    (hFree : Semantics.Env.RespectsFree env) :
    Semantics.Env.RespectsFree (extension.unbase env) :=
  extension.localSkolem.extension.unbaseRespectsFree _ <|
    Semantics.Env.respectsFree_unbaseOverrideDefinitions hFree

/-- 组合环境回拉保持 bound-stack 关系。 -/
theorem unbaseSameBound {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    {left right : Semantics.Env extension.target}
    (hBound : Semantics.LocalSkolemChoice.SameBoundStack left right) :
    Semantics.LocalSkolemChoice.SameBoundStack
      (extension.unbase left) (extension.unbase right) :=
  extension.localSkolem.extension.unbaseSameBound <|
    Semantics.Env.sameBoundStack_unbaseOverrideDefinitions hBound

/-- 组合扩张保持所有一阶函数解释的 codomain sort。 -/
theorem functionSort {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    (contract : Semantics.FoolLambdaContract M) :
    ∀ symbol arguments,
      extension.target.sortInterp symbol.outputSort
        (extension.target.functionInterp symbol arguments) := by
  intro symbol arguments
  exact
    extension.localSkolem.extension.functionSort contract.function_sort
      symbol arguments

/-- 纯一阶模型只需显式提供函数 codomain sort，不需要携带完整 FOOL/lambda 合同。 -/
theorem functionSort_of {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    (hFunctionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort
          (M.functionInterp symbol arguments)) :
    ∀ symbol arguments,
      extension.target.sortInterp symbol.outputSort
        (extension.target.functionInterp symbol arguments) := by
  intro symbol arguments
  exact
    extension.localSkolem.extension.functionSort hFunctionSort
      symbol arguments

/-- 组合扩张保持 FOOL/lambda 的全部语义合同。 -/
def contract {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    (source : Semantics.FoolLambdaContract M) :
    Semantics.FoolLambdaContract extension.target :=
  Semantics.FoolLambdaContract.overrideDefinitions
    (extension.localSkolem.extension.contract source)
    (extension.localSkolem.extension.rebase base)
    checked.payload.definitionalCnf.definitions

/-- 组合搬运保持 typed 自由变量的 sort 不变量。 -/
theorem respectsFree {checked : Checked} {M : Semantics.Model}
    {base env : Semantics.Env M} (extension : ModelExtension checked M base)
    (hFree : Semantics.Env.RespectsFree env) :
    Semantics.Env.RespectsFree (extension.rebase env) := by
  apply Semantics.Env.respectsFree_rebaseOverrideDefinitions
  exact extension.localSkolem.extension.respectsFree env hFree

/-- 组合搬运保持 locally-nameless bound stack。 -/
theorem sameBound {checked : Checked} {M : Semantics.Model}
    {base left right : Semantics.Env M}
    (extension : ModelExtension checked M base)
    (hBound : Semantics.LocalSkolemChoice.SameBoundStack left right) :
    Semantics.LocalSkolemChoice.SameBoundStack
      (extension.rebase left) (extension.rebase right) := by
  apply Semantics.Env.sameBoundStack_rebaseOverrideDefinitions
  exact extension.localSkolem.extension.sameBound hBound

/--
任意满足原 source 的 well-sorted、共享 bound-stack 环境，搬到固定最终模型后都满足
总 payload 暴露的字句集。
-/
theorem clausesSatisfied {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    (contract : Semantics.FoolLambdaContract M)
    (hBaseFree : Semantics.Env.RespectsFree base)
    (hSource : Semantics.Formula.Satisfies base checked.payload.source)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (hBound : Semantics.LocalSkolemChoice.SameBoundStack env base)
    :
    Semantics.ClauseSet.Satisfies
      (extension.rebase env)
      checked.payload.clauses := by
  have hAntiPrenex :
      Semantics.Nnf.Satisfies base checked.payload.antiPrenex.result :=
    (satisfies_source_iff_antiPrenexResult
      checked contract base hBaseFree).mp hSource
  have hLocalResult :
      Semantics.Nnf.Satisfies
        (extension.localSkolem.extension.rebase env)
        checked.payload.localSkolem.result :=
    extension.localSkolem.resultSat_of_source
      extension.sourceSupported hAntiPrenex env hFree hBound
  have hCnfSource :
      Semantics.Nnf.Satisfies
        (extension.localSkolem.extension.rebase env)
        checked.payload.definitionalCnf.source := by
    rw [definitionalCnf_source_eq_localSkolemResult checked]
    exact hLocalResult
  rw [clauses_eq_definitionalCnfClauses checked]
  exact extension.definitionalCnf.clausesSatisfied
    (extension.localSkolem.extension.rebase env) hCnfSource

/--
纯一阶恒等 normalization 下，任意满足 source 的环境都可沿共享 Skolem/CNF 扩张得到
最终字句集，不消费 FOOL/lambda 合同。
-/
theorem clausesSatisfied_of_normalized_eq
    {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    (hNormalized :
      checked.payload.normalized = checked.payload.source)
    (hSource : Semantics.Formula.Satisfies base checked.payload.source)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (hBound : Semantics.LocalSkolemChoice.SameBoundStack env base) :
    Semantics.ClauseSet.Satisfies
      (extension.rebase env)
      checked.payload.clauses := by
  have hAntiPrenex :
      Semantics.Nnf.Satisfies base checked.payload.antiPrenex.result :=
    (satisfies_source_iff_antiPrenexResult_of_normalized_eq
      checked hNormalized base).mp hSource
  have hLocalResult :
      Semantics.Nnf.Satisfies
        (extension.localSkolem.extension.rebase env)
        checked.payload.localSkolem.result :=
    extension.localSkolem.resultSat_of_source
      extension.sourceSupported hAntiPrenex env hFree hBound
  have hCnfSource :
      Semantics.Nnf.Satisfies
        (extension.localSkolem.extension.rebase env)
        checked.payload.definitionalCnf.source := by
    rw [definitionalCnf_source_eq_localSkolemResult checked]
    exact hLocalResult
  rw [clauses_eq_definitionalCnfClauses checked]
  exact extension.definitionalCnf.clausesSatisfied
    (extension.localSkolem.extension.rebase env) hCnfSource

/--
最终模型中的任意 well-sorted 环境，只要与基础搬运环境共享 bound stack，就满足总字句集。
-/
theorem clausesSatisfiedTarget {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    (contract : Semantics.FoolLambdaContract M)
    (hBaseFree : Semantics.Env.RespectsFree base)
    (hSource : Semantics.Formula.Satisfies base checked.payload.source)
    (env : Semantics.Env extension.target)
    (hFree : Semantics.Env.RespectsFree env)
    (hBound :
      Semantics.LocalSkolemChoice.SameBoundStack
        env (extension.rebase base)) :
    Semantics.ClauseSet.Satisfies env checked.payload.clauses := by
  let sourceEnv := extension.unbase env
  have hSourceFree : Semantics.Env.RespectsFree sourceEnv :=
    extension.unbaseRespectsFree hFree
  have hSourceBound :
      Semantics.LocalSkolemChoice.SameBoundStack sourceEnv base := by
    have hPulled := extension.unbaseSameBound hBound
    simpa [sourceEnv, extension.unbase_rebase] using hPulled
  have hClauses :=
    extension.clausesSatisfied contract hBaseFree hSource
      sourceEnv hSourceFree hSourceBound
  simpa [sourceEnv, extension.rebase_unbase] using hClauses

/--
纯一阶恒等 normalization 的最终模型版本；用于一阶投影证明 canonical clause problem
对所有目标自由变量环境都有效。
-/
theorem clausesSatisfiedTarget_of_normalized_eq
    {checked : Checked} {M : Semantics.Model}
    {base : Semantics.Env M} (extension : ModelExtension checked M base)
    (hNormalized :
      checked.payload.normalized = checked.payload.source)
    (hSource : Semantics.Formula.Satisfies base checked.payload.source)
    (env : Semantics.Env extension.target)
    (hFree : Semantics.Env.RespectsFree env)
    (hBound :
      Semantics.LocalSkolemChoice.SameBoundStack
        env (extension.rebase base)) :
    Semantics.ClauseSet.Satisfies env checked.payload.clauses := by
  let sourceEnv := extension.unbase env
  have hSourceFree : Semantics.Env.RespectsFree sourceEnv :=
    extension.unbaseRespectsFree hFree
  have hSourceBound :
      Semantics.LocalSkolemChoice.SameBoundStack sourceEnv base := by
    have hPulled := extension.unbaseSameBound hBound
    simpa [sourceEnv, extension.unbase_rebase] using hPulled
  have hClauses :=
    extension.clausesSatisfied_of_normalized_eq
      hNormalized hSource sourceEnv hSourceFree hSourceBound
  simpa [sourceEnv, extension.rebase_unbase] using hClauses

end ModelExtension

/--
闭合 anti-prenex source 沿整条 checked preprocessing 构造统一环境族模型扩张。
-/
theorem modelExtension (checked : Checked)
    (hSupported :
      Semantics.FreeSupport.NnfSupportedBy []
        checked.payload.antiPrenex.result)
    (M : Semantics.Model) (base : Semantics.Env M) :
    Nonempty (ModelExtension checked M base) := by
  have hLocalSourceEq := localSkolem_source_eq_antiPrenexResult checked
  have hLocalSupported :
      Semantics.FreeSupport.NnfSupportedBy []
        checked.payload.localSkolem.source := by
    simpa [hLocalSourceEq] using hSupported
  rcases LocalSkolemPayload.uniformSoundExtension_of_check
      (localSkolem_checked checked) hLocalSupported M base with ⟨localSkolem⟩
  have localSkolem' :
      Semantics.LocalSkolemSoundness.UniformSoundExtension
        (LocalSkolem.initialState checked.payload.antiPrenex.result)
        checked.payload.antiPrenex.result
        checked.payload.localSkolem.result M base := by
    simpa [hLocalSourceEq] using localSkolem
  exact ⟨{
    sourceSupported := hSupported
    localSkolem := localSkolem'
    definitionalCnf :=
      Semantics.DefinitionalCnfPayload.uniformSoundExtension_of_check
        (definitionalCnf_checked checked)
        (localSkolem'.extension.rebase base)
  }⟩

/--
总 checker 通过后，从初始 NNF 的可满足性依次穿过 anti-prenex、局部 Skolem 与
定义性 CNF，得到最终字句集的可满足性。
-/
theorem clauses_satisfiable_of_initialNnf (checked : Checked)
    (hInitial : Semantics.Nnf.Satisfiable.{x} checked.payload.initialNnf) :
    Semantics.ClauseSet.Satisfiable.{x} checked.payload.clauses := by
  have hSound := sound checked
  have hPhases := hSound.phasesChecked
  have hLinks := hSound.linksChecked
  simp only [Payload.phaseCheck, Bool.and_eq_true_iff] at hPhases
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  have hAntiPrenex :
      AntiPrenexPayload.check checked.payload.antiPrenex = true :=
    hPhases.1.1.2
  have hLocalSkolem :
      LocalSkolemPayload.check checked.payload.localSkolem = true :=
    hPhases.1.2
  have hDefinitionalCnf :
      DefinitionalCnfPayload.check checked.payload.definitionalCnf = true :=
    hPhases.2
  have hAntiPrenexSource :
      SyntaxEq.nnfEq checked.payload.antiPrenex.source
        checked.payload.initialNnf = true :=
    hLinks.1.1.1.2
  have hLocalSkolemSource :
      SyntaxEq.nnfEq checked.payload.localSkolem.source
        checked.payload.antiPrenex.result = true :=
    hLinks.1.1.2
  have hDefinitionalCnfSource :
      SyntaxEq.nnfEq checked.payload.definitionalCnf.source
        checked.payload.localSkolem.result = true :=
    hLinks.1.2
  have hClauses :
      ClauseSet.eq checked.payload.clauses
        checked.payload.definitionalCnf.clauses = true :=
    hLinks.2
  have hAntiPrenexSourceEq :
      checked.payload.antiPrenex.source = checked.payload.initialNnf :=
    SyntaxEq.nnfEq_eq_true.mp hAntiPrenexSource
  have hAntiPrenexInput :
      Semantics.Nnf.Satisfiable.{x} checked.payload.antiPrenex.source := by
    simpa [hAntiPrenexSourceEq] using hInitial
  have hAntiPrenexResult :
      Semantics.Nnf.Satisfiable.{x} checked.payload.antiPrenex.result := by
    rcases hAntiPrenexInput with ⟨M, env, hSource⟩
    exact ⟨M, env,
      (AntiPrenexPayload.semanticEquivalent_of_check hAntiPrenex env).mp hSource⟩
  have hLocalSkolemSourceEq :
      checked.payload.localSkolem.source = checked.payload.antiPrenex.result :=
    SyntaxEq.nnfEq_eq_true.mp hLocalSkolemSource
  have hLocalSkolemInput :
      Semantics.Nnf.Satisfiable.{x} checked.payload.localSkolem.source := by
    simpa [hLocalSkolemSourceEq] using hAntiPrenexResult
  have hLocalSkolemResult :
      Semantics.Nnf.Satisfiable.{x} checked.payload.localSkolem.result :=
    LocalSkolemPayload.satisfiable_of_check hLocalSkolem hLocalSkolemInput
  have hDefinitionalCnfSourceEq :
      checked.payload.definitionalCnf.source = checked.payload.localSkolem.result :=
    SyntaxEq.nnfEq_eq_true.mp hDefinitionalCnfSource
  have hDefinitionalCnfInput :
      Semantics.Nnf.Satisfiable.{x} checked.payload.definitionalCnf.source := by
    simpa [hDefinitionalCnfSourceEq] using hLocalSkolemResult
  have hDefinitionalCnfResult :
      Semantics.ClauseSet.Satisfiable.{x} checked.payload.definitionalCnf.clauses :=
    Semantics.DefinitionalCnfPayload.satisfiable_of_check
      hDefinitionalCnf hDefinitionalCnfInput
  have hClausesEq :
      checked.payload.clauses = checked.payload.definitionalCnf.clauses :=
    Semantics.ClauseSet.eq_eq_true.mp hClauses
  simpa [hClausesEq] using hDefinitionalCnfResult

/--
正极性 NNF 转换与源公式等价，因此已检查预处理可以直接消费 normalized 公式模型。
normalization 本身的语义合同由独立定理提供，不在此处对任意模型作隐含假设。
-/
theorem clauses_satisfiable_of_normalized (checked : Checked)
    (hNormalized :
      Semantics.Formula.Satisfiable.{x} checked.payload.normalized) :
    Semantics.ClauseSet.Satisfiable.{x} checked.payload.clauses := by
  have hLinks := (sound checked).linksChecked
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  have hInitialNnf :
      SyntaxEq.nnfEq checked.payload.initialNnf
        (toNnfWith Polarity.positive checked.payload.normalized) = true :=
    hLinks.1.1.1.1.2
  have hInitialNnfEq :
      checked.payload.initialNnf =
        toNnfWith Polarity.positive checked.payload.normalized :=
    SyntaxEq.nnfEq_eq_true.mp hInitialNnf
  apply clauses_satisfiable_of_initialNnf checked
  rw [hInitialNnfEq]
  exact
    (Semantics.Nnf.satisfiable_toNnfWith_positive
      checked.payload.normalized).mpr hNormalized

/-- checked normalization trace 将同一合同模型中的 source 搬到 normalized。 -/
theorem normalized_satisfiable_of_source_model (checked : Checked)
    {M : Semantics.Model.{x}} (contract : Semantics.FoolLambdaContract M)
    (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env)
    (hSource : Semantics.Formula.Satisfies env checked.payload.source) :
    Semantics.Formula.Satisfiable.{x} checked.payload.normalized :=
  ⟨M, env,
    (satisfies_source_iff_normalized checked contract env hFree).mp hSource⟩

/-- 从带合同的 source 可满足性贯穿全部预处理阶段到最终字句集。 -/
theorem clauses_satisfiable_of_source (checked : Checked)
    (hSource :
      Semantics.Formula.FoolLambdaSatisfiable.{x} checked.payload.source) :
    Semantics.ClauseSet.Satisfiable.{x} checked.payload.clauses := by
  rcases hSource with ⟨M, env, ⟨contract⟩, hFree, hSource⟩
  exact clauses_satisfiable_of_normalized checked
    (normalized_satisfiable_of_source_model checked contract env hFree hSource)

end CheckedPreprocessing

end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
