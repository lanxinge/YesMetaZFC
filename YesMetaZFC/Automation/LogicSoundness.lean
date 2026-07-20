import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Logic.Shallow.Soundness

/-!
# 新语义核自动化 soundness 边界

本文件是新 `Logic` 语义核和自动化层之间的第一层可信合同。它不导入旧
`Automation.Core` / `LCF` replay，也不复用旧 MF1 soundness。搜索器后续只需要把
自己的可检查证书落到这里的 `SemanticCertificate` / `DeepProblem` 合同上。自动化主线
保持 `SetLevel` 语法与可计算 payload 位于 `Type 0`，同时允许 provider 与语义证书消费
任意 universe 的模型载体；无后缀 API 仅是现有 tactic 使用的 `x = 0` 特化。
-/

namespace YesMetaZFC
namespace Automation
namespace LogicSoundness

universe u v w x

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder
open _root_.YesMetaZFC.Logic.Shallow.FirstOrder

/--
自动化搜索器进入可信边界后必须交出的最小语义合同。

注意：这里故意只说“前提语义蕴涵目标”，不提旧 Hilbert/LCF replay。DAG、
CDCL residual、叠加演算和后续二阶/Henkin checker 都应各自证明能产生这个合同。
-/
structure SemanticCertificate {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (premises : Theory σ) (target : Formula σ) where
  entails : Theory.SemanticallyEntails.{u, v, w, x} premises target

namespace SemanticCertificate

/-- 提取证书的语义 soundness。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {premises : Theory σ} {target : Formula σ}
    (cert : SemanticCertificate.{u, v, w, x} premises target) :
    Theory.SemanticallyEntails.{u, v, w, x} premises target :=
  cert.entails

/-- 前提理论增强时，语义证书可单调弱化。 -/
def weaken {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {strong weak : Theory σ} {target : Formula σ}
    (hSub : ∀ φ, weak φ → strong φ)
    (cert : SemanticCertificate.{u, v, w, x} weak target) :
    SemanticCertificate.{u, v, w, x} strong target where
  entails := Theory.entails_weaken hSub cert.entails

end SemanticCertificate

/-- 自动化后端实际消费的深嵌入问题：有限前提列表和一个目标公式。 -/
structure DeepProblem (σ : Signature.{u, v, w}) where
  premises : List (Formula σ) := []
  target : Formula σ

namespace DeepProblem

/-- 有限前提列表诱导出的语义理论。 -/
def theory {σ : Signature.{u, v, w}} (problem : DeepProblem σ) : Theory σ :=
  fun φ => φ ∈ problem.premises

/-- 把全部有限前提与目标否定组装成单个反证源公式。 -/
def refutationFormula {σ : Signature.{u, v, w}}
    (problem : DeepProblem σ) : Formula σ :=
  Formula.conjunctionList
    (problem.premises ++ [Formula.neg problem.target])

/-- 问题的反例环境恰好满足整问题反证公式。 -/
theorem satisfies_refutationFormula_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (problem : DeepProblem σ) (env : Env M) :
    Theory.Models problem.theory env ∧
        ¬ Formula.satisfies env problem.target ↔
      Formula.satisfies env problem.refutationFormula := by
  unfold refutationFormula
  rw [Formula.satisfies_conjunctionList_iff]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hModels, hTarget⟩ formula (hPremise | hTargetFormula)
    · exact hModels formula hPremise
    · subst formula
      simpa [Formula.satisfies] using hTarget
  · intro h
    constructor
    · intro formula hPremise
      exact h formula (Or.inl hPremise)
    · have hNeg := h (Formula.neg problem.target) (Or.inr rfl)
      simpa [Formula.satisfies] using hNeg

/-- 空前提深嵌入问题。 -/
def empty {σ : Signature.{u, v, w}} (target : Formula σ) : DeepProblem σ where
  premises := []
  target := target

/-- 深嵌入问题的已检查语义证书。 -/
abbrev Certificate {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) :=
  SemanticCertificate.{u, v, w, x} problem.theory problem.target

/-- 单个前提可以直接作为该有限理论的语义后果。 -/
def premiseCertificate {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) {φ : Formula σ} (hMem : φ ∈ problem.premises) :
    SemanticCertificate.{u, v, w, x} problem.theory φ where
  entails := Theory.entails_of_mem hMem

end DeepProblem

/-- 泛 universe 深嵌入证书对象；自动化主线应优先产出 `SetLevel.CheckedCertificate`。 -/
structure CheckedCertificate {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] where
  problem : DeepProblem σ
  cert : DeepProblem.Certificate.{u, v, w, x} problem

namespace CheckedCertificate

/-- 深嵌入证书的公开 soundness。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (checked : CheckedCertificate.{u, v, w, x} (σ := σ)) :
    Theory.SemanticallyEntails.{u, v, w, x} checked.problem.theory checked.problem.target :=
  checked.cert.entails

end CheckedCertificate

/-- 空理论目标的深嵌入证书对象。 -/
structure CheckedValidCertificate {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] where
  target : Formula σ
  cert : SemanticCertificate.{u, v, w, x} Theory.empty target

namespace CheckedValidCertificate

/-- 空理论目标证书的公开 soundness。 -/
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (checked : CheckedValidCertificate.{u, v, w, x} (σ := σ)) :
    Theory.SemanticallyEntails.{u, v, w, x} Theory.empty checked.target :=
  checked.cert.entails

end CheckedValidCertificate

/- 集合层语法固定在 `Type 0`；模型载体可独立处于任意 universe。 -/
namespace SetLevel

abbrev Signature := Logic.Signature.{0, 0, 0}
abbrev Term (σ : Signature) := Logic.FirstOrder.Term σ
abbrev Formula (σ : Signature) := Logic.FirstOrder.Formula σ
abbrev Theory (σ : Signature) := Logic.FirstOrder.Theory σ

/-- 固定集合层语法在 universe `x` 的模型解释。 -/
abbrev StructureAt (σ : Signature) :=
  Logic.FirstOrder.Structure.{0, 0, 0, x} σ

/-- universe `x` 模型上的 typed 环境。 -/
abbrev EnvAt {σ : Signature} (M : StructureAt.{x} σ) :=
  Logic.FirstOrder.Env M

/-- 固定集合层语法相对于 universe `x` 模型的语义蕴涵。 -/
abbrev SemanticallyEntailsAt
    {σ : Signature} [DecidableEq σ.SortSymbol]
    (T : Theory σ) (φ : Formula σ) :=
  Logic.FirstOrder.Theory.SemanticallyEntails.{0, 0, 0, x} T φ

/-- 现有自动化搜索接口使用的零 universe 模型特化。 -/
abbrev Structure (σ : Signature) := StructureAt.{0} σ

/-- 现有自动化搜索接口使用的零 universe 环境特化。 -/
abbrev Env {σ : Signature} (M : Structure σ) := EnvAt.{0} M

/-- 现有自动化搜索接口使用的零 universe 语义蕴涵。 -/
abbrev SemanticallyEntails {σ : Signature} [DecidableEq σ.SortSymbol]
    (T : Theory σ) (φ : Formula σ) :=
  SemanticallyEntailsAt.{0} T φ

namespace Theory

/-- 零层级空理论。 -/
def empty {σ : Signature} : Theory σ :=
  Logic.FirstOrder.Theory.empty

/-- 零层级单公式理论。 -/
def singleton {σ : Signature} (φ : Formula σ) : Theory σ :=
  Logic.FirstOrder.Theory.singleton φ

/-- 零层级理论插入。 -/
def insert {σ : Signature} (φ : Formula σ) (T : Theory σ) : Theory σ :=
  Logic.FirstOrder.Theory.insert φ T

/-- 零层级理论并。 -/
def union {σ : Signature} (T U : Theory σ) : Theory σ :=
  Logic.FirstOrder.Theory.union T U

end Theory

/-- 固定集合层语法在 universe `x` 模型上的语义证书。 -/
abbrev SemanticCertificateAt
    {σ : Signature} [DecidableEq σ.SortSymbol]
    (premises : Theory σ) (target : Formula σ) :=
  LogicSoundness.SemanticCertificate.{0, 0, 0, x} premises target

/-- 现有自动化搜索接口使用的零 universe 语义证书。 -/
abbrev SemanticCertificate {σ : Signature} [DecidableEq σ.SortSymbol]
    (premises : Theory σ) (target : Formula σ) :=
  SemanticCertificateAt.{0} premises target

namespace SemanticCertificate

/-- universe-polymorphic 语义证书的公开 soundness。 -/
theorem soundAt {σ : Signature} [DecidableEq σ.SortSymbol]
    {premises : Theory σ} {target : Formula σ}
    (cert : SemanticCertificateAt.{x} premises target) :
    SemanticallyEntailsAt.{x} premises target :=
  cert.entails

theorem sound {σ : Signature} [DecidableEq σ.SortSymbol]
    {premises : Theory σ} {target : Formula σ}
    (cert : SemanticCertificate premises target) :
    SemanticallyEntails premises target :=
  cert.entails

/-- universe-polymorphic 语义证书在理论增强下保持有效。 -/
def weakenAt {σ : Signature} [DecidableEq σ.SortSymbol]
    {strong weak : Theory σ} {target : Formula σ}
    (hSub : ∀ φ, weak φ → strong φ)
    (cert : SemanticCertificateAt.{x} weak target) :
    SemanticCertificateAt.{x} strong target :=
  LogicSoundness.SemanticCertificate.weaken hSub cert

def weaken {σ : Signature} [DecidableEq σ.SortSymbol]
    {strong weak : Theory σ} {target : Formula σ}
    (hSub : ∀ φ, weak φ → strong φ)
    (cert : SemanticCertificate weak target) :
    SemanticCertificate strong target :=
  weakenAt hSub cert

end SemanticCertificate

/-- 零层级深嵌入问题。 -/
structure DeepProblem (σ : Signature) where
  premises : List (Formula σ) := []
  target : Formula σ

namespace DeepProblem

def theory {σ : Signature} (problem : DeepProblem σ) : Theory σ :=
  fun φ => φ ∈ problem.premises

/-- 把零层级问题的全部有限前提与目标否定组装成单个反证源公式。 -/
def refutationFormula {σ : Signature} (problem : DeepProblem σ) : Formula σ :=
  Formula.conjunctionList
    (problem.premises ++ [Formula.neg problem.target])

/-- universe `x` 模型中的反例环境恰好满足整问题反证公式。 -/
theorem satisfies_refutationFormula_iff_at {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : StructureAt.{x} σ}
    (problem : DeepProblem σ) (env : EnvAt.{x} M) :
    Logic.FirstOrder.Theory.Models problem.theory env ∧
        ¬ Logic.FirstOrder.Formula.satisfies env problem.target ↔
      Logic.FirstOrder.Formula.satisfies env problem.refutationFormula := by
  unfold refutationFormula
  rw [Logic.FirstOrder.Formula.satisfies_conjunctionList_iff]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hModels, hTarget⟩ formula (hPremise | hTargetFormula)
    · exact hModels formula hPremise
    · subst formula
      simpa [Logic.FirstOrder.Formula.satisfies] using hTarget
  · intro h
    constructor
    · intro formula hPremise
      exact h formula (Or.inl hPremise)
    · have hNeg := h (Formula.neg problem.target) (Or.inr rfl)
      simpa [Logic.FirstOrder.Formula.satisfies] using hNeg

/-- 零 universe 特化的整问题反证公式语义。 -/
theorem satisfies_refutationFormula_iff {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : Structure σ}
    (problem : DeepProblem σ) (env : Env M) :
    Logic.FirstOrder.Theory.Models problem.theory env ∧
        ¬ Logic.FirstOrder.Formula.satisfies env problem.target ↔
      Logic.FirstOrder.Formula.satisfies env problem.refutationFormula :=
  satisfies_refutationFormula_iff_at problem env

def empty {σ : Signature} (target : Formula σ) : DeepProblem σ where
  premises := []
  target := target

/-- 固定集合层问题在 universe `x` 模型上的语义证书。 -/
abbrev CertificateAt {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) :=
  SemanticCertificateAt.{x} problem.theory problem.target

abbrev Certificate {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) :=
  CertificateAt.{0} problem

/-- 问题前提在任意模型 universe 上都是语义后果。 -/
def premiseCertificateAt {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) {φ : Formula σ} (hMem : φ ∈ problem.premises) :
    SemanticCertificateAt.{x} problem.theory φ where
  entails := Logic.FirstOrder.Theory.entails_of_mem hMem

def premiseCertificate {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) {φ : Formula σ} (hMem : φ ∈ problem.premises) :
    SemanticCertificate problem.theory φ :=
  premiseCertificateAt problem hMem

end DeepProblem

/-- 固定集合层问题在 universe `x` 模型上的 checked 语义证书。 -/
structure CheckedCertificateAt
    {σ : Signature} [DecidableEq σ.SortSymbol] where
  problem : DeepProblem σ
  cert : DeepProblem.CertificateAt.{x} problem

/-- 自动化主线默认消费的零 universe checked 证书。 -/
abbrev CheckedCertificate {σ : Signature} [DecidableEq σ.SortSymbol] :=
  CheckedCertificateAt.{0} (σ := σ)

namespace CheckedCertificate

/-- universe-polymorphic checked 证书的公开 soundness。 -/
theorem soundAt {σ : Signature} [DecidableEq σ.SortSymbol]
    (checked : CheckedCertificateAt.{x} (σ := σ)) :
    SemanticallyEntailsAt.{x}
      checked.problem.theory checked.problem.target :=
  checked.cert.entails

theorem sound {σ : Signature} [DecidableEq σ.SortSymbol]
    (checked : CheckedCertificate (σ := σ)) :
    SemanticallyEntails checked.problem.theory checked.problem.target :=
  soundAt checked

end CheckedCertificate

/-! ### 自动化后端消费协议 -/

/--
已经在可信边界内闭合的一个自动化后端结果。

搜索器本身仍是不可信的；它只能通过自己的 checker/soundness 定理构造这里的
`cert` 字段。`audit?` 只保存压缩证书图和统计信息，不参与 soundness。
-/
structure BackendSuccessAt {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) where
  backend : Certificate.Backend
  phase : Certificate.Phase := .replay
  cert : DeepProblem.CertificateAt.{x} problem
  audit? : Option Certificate.Composite := none
  note : String := ""

/-- 现有自动化 provider 使用的零 universe 后端成功对象。 -/
abbrev BackendSuccess {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) :=
  BackendSuccessAt.{0} problem

namespace BackendSuccessAt

/-- universe-polymorphic 后端成功结果的公开 soundness。 -/
theorem sound {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (success : BackendSuccessAt.{x} problem) :
    SemanticallyEntailsAt.{x} problem.theory problem.target :=
  success.cert.entails

/-- 成功结果可直接降为同 universe 的 checked certificate。 -/
def toCheckedCertificate {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (success : BackendSuccessAt.{x} problem) :
    CheckedCertificateAt.{x} (σ := σ) where
  problem := problem
  cert := success.cert

/-- 成功结果的审计摘要。 -/
def summary {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (success : BackendSuccessAt.{x} problem) : String :=
  let note := if success.note.isEmpty then "" else s!"; note={success.note}"
  let audit :=
    match success.audit? with
    | some cert => s!"; auditNodes={cert.nodes.size}; root={cert.root}"
    | none => ""
  s!"{success.backend.label}/{success.phase.label}: closed{audit}{note}"

/-- 从裸 universe-polymorphic 语义证书构造后端成功结果。 -/
def ofCertificate {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (backend : Certificate.Backend)
    (phase : Certificate.Phase) (cert : DeepProblem.CertificateAt.{x} problem)
    (audit? : Option Certificate.Composite := none) (note : String := "") :
    BackendSuccessAt.{x} problem where
  backend := backend
  phase := phase
  cert := cert
  audit? := audit?
  note := note

end BackendSuccessAt

namespace BackendSuccess

/-- 零 universe 后端成功结果的兼容 soundness。 -/
theorem sound {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (success : BackendSuccess problem) :
    SemanticallyEntails problem.theory problem.target :=
  BackendSuccessAt.sound success

/-- 零 universe 成功结果降为 tactic 当前消费的 checked certificate。 -/
def toCheckedCertificate {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (success : BackendSuccess problem) :
    CheckedCertificate (σ := σ) :=
  BackendSuccessAt.toCheckedCertificate success

/-- 零 universe 成功结果的审计摘要。 -/
def summary {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (success : BackendSuccess problem) : String :=
  BackendSuccessAt.summary success

/-- 从零 universe 裸语义证书构造后端成功结果。 -/
def ofCertificate {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (backend : Certificate.Backend)
    (phase : Certificate.Phase) (cert : DeepProblem.Certificate problem)
    (audit? : Option Certificate.Composite := none) (note : String := "") :
    BackendSuccess problem :=
  BackendSuccessAt.ofCertificate backend phase cert audit? note

end BackendSuccess

/-- 自动化后端的一次尝试结果。 -/
inductive BackendAttemptAt {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) where
  | success (success : BackendSuccessAt.{x} problem)
  | failure (diagnostic : Certificate.Diagnostic)

/-- 现有自动化 provider 使用的零 universe 尝试结果。 -/
abbrev BackendAttempt {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) :=
  BackendAttemptAt.{0} problem

namespace BackendAttemptAt

/-- 尝试是否闭合。 -/
def closed {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} : BackendAttemptAt.{x} problem → Bool
  | .success _ => true
  | .failure _ => false

/-- 成功时提取后端结果。 -/
def success? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} :
    BackendAttemptAt.{x} problem → Option (BackendSuccessAt.{x} problem)
  | .success result => some result
  | .failure _ => none

/-- 失败时提取诊断。 -/
def diagnostic? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} :
    BackendAttemptAt.{x} problem → Option Certificate.Diagnostic
  | .success _ => none
  | .failure diagnostic => some diagnostic

/-- 尝试结果摘要。 -/
def summary {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} : BackendAttemptAt.{x} problem → String
  | .success result => BackendSuccessAt.summary result
  | .failure diagnostic => diagnostic.label

/-- 成功尝试给出语义蕴涵。 -/
theorem sound_of_success {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} {attempt : BackendAttemptAt.{x} problem}
    {success : BackendSuccessAt.{x} problem}
    (_hSuccess : success? attempt = some success) :
    SemanticallyEntailsAt.{x} problem.theory problem.target :=
  BackendSuccessAt.sound success

end BackendAttemptAt

namespace BackendAttempt

/-- 零 universe 尝试是否闭合。 -/
def closed {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (attempt : BackendAttempt problem) : Bool :=
  BackendAttemptAt.closed attempt

/-- 零 universe 尝试成功时提取后端结果。 -/
def success? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (attempt : BackendAttempt problem) :
    Option (BackendSuccess problem) :=
  BackendAttemptAt.success? attempt

/-- 零 universe 尝试失败时提取诊断。 -/
def diagnostic? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (attempt : BackendAttempt problem) :
    Option Certificate.Diagnostic :=
  BackendAttemptAt.diagnostic? attempt

/-- 零 universe 尝试结果摘要。 -/
def summary {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (attempt : BackendAttempt problem) : String :=
  BackendAttemptAt.summary attempt

/-- 零 universe 成功尝试给出语义蕴涵。 -/
theorem sound_of_success {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} {attempt : BackendAttempt problem}
    {success : BackendSuccess problem}
    (hSuccess : BackendAttempt.success? attempt = some success) :
    SemanticallyEntails problem.theory problem.target :=
  BackendAttemptAt.sound_of_success hSuccess

end BackendAttempt

/-- 同一问题下的多后端候选组合。 -/
structure PortfolioAt {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) where
  attempts : Array (BackendAttemptAt.{x} problem) := #[]

/-- 现有自动化主线使用的零 universe provider 组合。 -/
abbrev Portfolio {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) :=
  PortfolioAt.{0} problem

namespace PortfolioAt

/-- 空组合。 -/
def empty {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) : PortfolioAt.{x} problem where
  attempts := #[]

/-- 追加一次后端尝试。 -/
def push {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem)
    (attempt : BackendAttemptAt.{x} problem) : PortfolioAt.{x} problem where
  attempts := portfolio.attempts.push attempt

/-- 从候选组合中取第一个成功后端。 -/
def firstSuccess? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) :
    Option (BackendSuccessAt.{x} problem) := Id.run do
  for attempt in portfolio.attempts do
    match BackendAttemptAt.success? attempt with
    | some success => return some success
    | none => pure ()
  return none

/-- 收集所有失败诊断，供 tactic 层报告真实缺口。 -/
def diagnostics {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) :
    Array Certificate.Diagnostic := Id.run do
  let mut out := #[]
  for attempt in portfolio.attempts do
    match BackendAttemptAt.diagnostic? attempt with
    | some diagnostic => out := out.push diagnostic
    | none => pure ()
  return out

/-- 候选组合是否已有闭合后端。 -/
def closed {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) : Bool :=
  (firstSuccess? portfolio).isSome

/-- 成功组合可直接交给 tactic 消费。 -/
def checkedCertificate? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) :
    Option (CheckedCertificateAt.{x} (σ := σ)) := do
  let success ← firstSuccess? portfolio
  pure (BackendSuccessAt.toCheckedCertificate success)

/-- 候选组合闭合时给出语义蕴涵。 -/
theorem sound_of_firstSuccess {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} {portfolio : PortfolioAt.{x} problem}
    {success : BackendSuccessAt.{x} problem}
    (_hSuccess : firstSuccess? portfolio = some success) :
    SemanticallyEntailsAt.{x} problem.theory problem.target :=
  BackendSuccessAt.sound success

end PortfolioAt

namespace Portfolio

/-- 零 universe 空组合。 -/
def empty {σ : Signature} [DecidableEq σ.SortSymbol]
    (problem : DeepProblem σ) : Portfolio problem :=
  PortfolioAt.empty problem

/-- 零 universe 追加后端尝试。 -/
def push {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : Portfolio problem)
    (attempt : BackendAttempt problem) : Portfolio problem :=
  PortfolioAt.push portfolio attempt

/-- 零 universe 组合中的第一个成功后端。 -/
def firstSuccess? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : Portfolio problem) :
    Option (BackendSuccess problem) :=
  PortfolioAt.firstSuccess? portfolio

/-- 零 universe 组合的失败诊断。 -/
def diagnostics {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : Portfolio problem) :
    Array Certificate.Diagnostic :=
  PortfolioAt.diagnostics portfolio

/-- 零 universe 组合是否闭合。 -/
def closed {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : Portfolio problem) : Bool :=
  PortfolioAt.closed portfolio

/-- 零 universe 组合降为 tactic 当前消费的 checked certificate。 -/
def checkedCertificate? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : Portfolio problem) :
    Option (CheckedCertificate (σ := σ)) :=
  PortfolioAt.checkedCertificate? portfolio

/-- 零 universe 成功组合给出语义蕴涵。 -/
theorem sound_of_firstSuccess {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} {portfolio : Portfolio problem}
    {success : BackendSuccess problem}
    (hSuccess : Portfolio.firstSuccess? portfolio = some success) :
    SemanticallyEntails problem.theory problem.target :=
  PortfolioAt.sound_of_firstSuccess hSuccess

end Portfolio

/--
自动化搜索器的 proof-carrying provider 接口。

`run` 可以做任意搜索，但返回 `.success` 时必须已经携带 `BackendSuccess`，因此可信边界
仍然只依赖语义证书本身。
-/
structure ProviderAt (σ : Signature) [DecidableEq σ.SortSymbol] where
  name : String
  backend : Certificate.Backend
  run : (problem : DeepProblem σ) → BackendAttemptAt.{x} problem

/-- 现有自动化主线使用的零 universe provider。 -/
abbrev Provider (σ : Signature) [DecidableEq σ.SortSymbol] :=
  ProviderAt.{0} σ

namespace ProviderAt

/-- 运行单个 provider 并取成功结果。 -/
def solve? {σ : Signature} [DecidableEq σ.SortSymbol] (provider : ProviderAt.{x} σ)
    (problem : DeepProblem σ) : Option (BackendSuccessAt.{x} problem) :=
  BackendAttemptAt.success? (provider.run problem)

/-- 运行一组 provider，形成同一问题下的候选组合。 -/
def runAll {σ : Signature} [DecidableEq σ.SortSymbol]
    (providers : Array (ProviderAt.{x} σ)) (problem : DeepProblem σ) :
    PortfolioAt.{x} problem := Id.run do
  let mut attempts := #[]
  for provider in providers do
    attempts := attempts.push (provider.run problem)
  return { attempts := attempts }

end ProviderAt

namespace Provider

/-- 运行零 universe provider 并取成功结果。 -/
def solve? {σ : Signature} [DecidableEq σ.SortSymbol] (provider : Provider σ)
    (problem : DeepProblem σ) : Option (BackendSuccess problem) :=
  ProviderAt.solve? provider problem

/-- 运行一组零 universe provider。 -/
def runAll {σ : Signature} [DecidableEq σ.SortSymbol]
    (providers : Array (Provider σ)) (problem : DeepProblem σ) :
    Portfolio problem :=
  ProviderAt.runAll providers problem

end Provider

/-- 固定集合层目标在 universe `x` 模型上的 checked 空理论证书。 -/
structure CheckedValidCertificateAt
    {σ : Signature} [DecidableEq σ.SortSymbol] where
  target : Formula σ
  cert : SemanticCertificateAt.{x} Theory.empty target

/-- 现有自动化入口使用的零 universe checked 空理论证书。 -/
abbrev CheckedValidCertificate
    {σ : Signature} [DecidableEq σ.SortSymbol] :=
  CheckedValidCertificateAt.{0} (σ := σ)

namespace CheckedValidCertificate

/-- universe-polymorphic checked 空理论证书的公开 soundness。 -/
theorem soundAt {σ : Signature} [DecidableEq σ.SortSymbol]
    (checked : CheckedValidCertificateAt.{x} (σ := σ)) :
    SemanticallyEntailsAt.{x} Theory.empty checked.target :=
  checked.cert.entails

theorem sound {σ : Signature} [DecidableEq σ.SortSymbol]
    (checked : CheckedValidCertificate (σ := σ)) :
    SemanticallyEntails Theory.empty checked.target :=
  soundAt checked

end CheckedValidCertificate

end SetLevel

/-- 浅嵌入桥接出的自动化问题。所有前提和目标共享同一个模型解释。 -/
structure BridgeProblem {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (M : Structure.{u, v, w, x} σ) where
  premises : List (BridgeResult M) := []
  target : BridgeResult M

namespace BridgeProblem

/-- 把浅嵌入 problem 投影成搜索器消费的深嵌入 problem。 -/
def toDeep {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M) :
    DeepProblem σ where
  premises := problem.premises.map (fun premise => premise.deep)
  target := problem.target.deep

/-- 浅层前提在某个环境下全部成立。 -/
def ShallowModels {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M)
    (env : Env M) : Prop :=
  ∀ premise, premise ∈ problem.premises → premise.prop env

/-- 浅层前提成立时，深层前提理论在同一环境下成立。 -/
theorem models_of_shallowModels {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M)
    {env : Env M} (hPremises : problem.ShallowModels env) :
    Theory.Models problem.toDeep.theory env := by
  intro φ hφ
  rcases List.mem_map.mp hφ with ⟨premise, hMem, hDeep⟩
  rw [← hDeep]
  exact (premise.sound env).mp (hPremises premise hMem)

/-- 深层证书推出深嵌入目标在当前环境满足。 -/
theorem target_satisfies_of_certificate {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (problem : BridgeProblem M)
    (cert : DeepProblem.Certificate.{u, v, w, x} problem.toDeep)
    {env : Env M} (hPremises : problem.ShallowModels env) :
    Formula.satisfies env problem.target.deep :=
  cert.entails env (problem.models_of_shallowModels hPremises)

/-- 深层证书最终回到浅嵌入目标。 -/
theorem target_prop_of_certificate {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (problem : BridgeProblem M)
    (cert : DeepProblem.Certificate.{u, v, w, x} problem.toDeep)
    {env : Env M} (hPremises : problem.ShallowModels env) :
    problem.target.prop env :=
  (problem.target.sound env).mpr
    (problem.target_satisfies_of_certificate cert hPremises)

/-- 一个桥接问题被证书闭合后，得到浅层语义蕴涵。 -/
theorem shallow_entails_of_certificate {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (problem : BridgeProblem M)
    (cert : DeepProblem.Certificate.{u, v, w, x} problem.toDeep) :
    ∀ env : Env M, problem.ShallowModels env → problem.target.prop env :=
  fun _ hPremises => problem.target_prop_of_certificate cert hPremises

/-- 无前提目标的常用入口：深层空理论证书推出浅层全局有效性。 -/
theorem target_valid_of_empty_certificate {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (target : BridgeResult M)
    (cert : SemanticCertificate.{u, v, w, x} Theory.empty target.deep) :
    ∀ env : Env M, target.prop env := by
  intro env
  exact (target.sound env).mpr (cert.entails env (Theory.models_empty env))

end BridgeProblem

end LogicSoundness
end Automation
end YesMetaZFC
