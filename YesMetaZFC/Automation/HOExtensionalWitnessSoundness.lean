import YesMetaZFC.Automation.HOExtensionalWitnessRegistry
import YesMetaZFC.Automation.CoreNormalForm.HigherOrderProjectionSoundness

/-!
# 高阶外延见证的多符号模型扩张

这里把签名中所有标记为 `diff` 的函数符号一次性解释成区分函数。
扩张只改函数解释，保留 sort、关系、apply、lambda 与 FOOL/lambda 的语义设施；
因此原始 witness-free source clause 的解释不变。
-/

namespace YesMetaZFC
namespace Automation
namespace HOExtensionalWitnessSoundness

open HODAGCertificate
open HOExtensionalWitnessRegistry
open Logic.HigherOrder

universe u v w x

noncomputable local instance classicalPropDecidable
    (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Signature := HODAGCertificate.Signature
abbrev SimpleType (σ : Signature) := HODAGCertificate.SimpleType σ
abbrev Term (σ : Signature) := HODAGCertificate.Term σ
abbrev Literal (σ : Signature) := HODAGCertificate.Literal σ
abbrev Clause (σ : Signature) := HODAGCertificate.Clause σ
abbrev Problem (σ : Signature) := HODAGCertificate.Problem σ
abbrev Structure (σ : Signature) := Logic.HigherOrder.Structure σ
abbrev Env (σ : Signature) (M : Structure σ) := Logic.HigherOrder.Env M

section Choice

variable {σ : Signature.{u, v, w}}

/-- 在指定 sort 中选择一个默认值。 -/
noncomputable def defaultValue (M : Structure σ) (sort : SimpleType σ) : M.Domain :=
  Classical.choose (M.sortNonempty sort)

theorem defaultValue_sort (M : Structure σ) (sort : SimpleType σ) :
    M.sortInterp sort (defaultValue M sort) :=
  Classical.choose_spec (M.sortNonempty sort)

/-- 函数不相等时，由外延性得到一个区分实参。 -/
theorem exists_distinguishing_argument
    {M : Structure σ} (contract : ExtensionalContract M)
    (domain codomain : SimpleType σ) (left right : M.Domain)
    (hLeft : M.sortInterp (.arrow domain codomain) left)
    (hRight : M.sortInterp (.arrow domain codomain) right)
    (hNe : left ≠ right) :
    ∃ argument, M.sortInterp domain argument ∧
      M.applyInterp left argument ≠ M.applyInterp right argument := by
  apply Classical.byContradiction
  intro hExists
  have hPointwise :
      ∀ argument, M.sortInterp domain argument →
        M.applyInterp left argument = M.applyInterp right argument := by
    intro argument hArgument
    apply Classical.byContradiction
    intro hDifferent
    exact hExists ⟨argument, hArgument, hDifferent⟩
  exact hNe
    ((contract.functionExtensionality domain codomain left right hLeft hRight).2
      hPointwise)

/-- 对一对函数值选择区分实参；未满足前提时退回 domain 中的默认值。 -/
noncomputable def differenceValue
    {M : Structure σ} (contract : ExtensionalContract M)
    (domain codomain : SimpleType σ) (left right : M.Domain) : M.Domain :=
  dite
    (M.sortInterp (.arrow domain codomain) left ∧
      M.sortInterp (.arrow domain codomain) right ∧ left ≠ right)
    (fun h =>
      Classical.choose (exists_distinguishing_argument contract domain codomain left right
        h.1 h.2.1 h.2.2))
    (fun _ => defaultValue M domain)

theorem differenceValue_sort
    {M : Structure σ} (contract : ExtensionalContract M)
    (domain codomain : SimpleType σ) (left right : M.Domain) :
    M.sortInterp domain (differenceValue contract domain codomain left right) := by
  unfold differenceValue
  by_cases h :
      M.sortInterp (.arrow domain codomain) left ∧
        M.sortInterp (.arrow domain codomain) right ∧ left ≠ right
  · simp only [dif_pos h]
    exact (Classical.choose_spec
      (exists_distinguishing_argument contract domain codomain left right
        h.1 h.2.1 h.2.2)).1
  · simp only [dif_neg h]
    exact defaultValue_sort M domain

theorem differenceValue_distinguishes
    {M : Structure σ} (contract : ExtensionalContract M)
    (domain codomain : SimpleType σ) (left right : M.Domain)
    (hLeft : M.sortInterp (.arrow domain codomain) left)
    (hRight : M.sortInterp (.arrow domain codomain) right)
    (hNe : left ≠ right) :
    M.applyInterp left (differenceValue contract domain codomain left right) ≠
      M.applyInterp right (differenceValue contract domain codomain left right) := by
  unfold differenceValue
  have h :
      M.sortInterp (.arrow domain codomain) left ∧
        M.sortInterp (.arrow domain codomain) right ∧ left ≠ right :=
    ⟨hLeft, hRight, hNe⟩
  simp only [dif_pos h]
  exact (Classical.choose_spec
    (exists_distinguishing_argument contract domain codomain left right
      h.1 h.2.1 h.2.2)).2

end Choice

section WitnessInterpretation

variable {σ : Signature.{u, v, w}}

/-- 从 witness 符号的声明中提取候选 domain sort。 -/
def inferredDomain (symbol : σ.FuncSymbol) : SimpleType σ :=
  match σ.funcDomain symbol with
  | .arrow domain _ :: _ => domain
  | _ => σ.funcCodomain symbol

/-- 从 witness 符号的声明中提取候选 codomain sort。 -/
def inferredCodomain (symbol : σ.FuncSymbol) : SimpleType σ :=
  match σ.funcDomain symbol with
  | .arrow _ codomain :: _ => codomain
  | _ => σ.funcCodomain symbol

/-- 声明是否正好是 `diff : (a -> b) -> (a -> b) -> a`。 -/
def WitnessShape (symbol : σ.FuncSymbol) : Prop :=
  σ.funcDomain symbol =
      [.arrow (inferredDomain symbol) (inferredCodomain symbol),
        .arrow (inferredDomain symbol) (inferredCodomain symbol)] ∧
    σ.funcCodomain symbol = inferredDomain symbol

/-- 对单个函数符号批量处理任意参数列表。 -/
noncomputable def witnessValue
    {M : Structure σ} (contract : ExtensionalContract M)
    (symbol : σ.FuncSymbol) (arguments : List M.Domain) : M.Domain :=
  if WitnessShape symbol then
    match arguments with
    | [left, right] =>
        differenceValue contract (inferredDomain symbol) (inferredCodomain symbol) left right
    | _ =>
        defaultValue M (σ.funcCodomain symbol)
  else
    defaultValue M (σ.funcCodomain symbol)

theorem witnessValue_sort
    {M : Structure σ} (contract : ExtensionalContract M)
    (symbol : σ.FuncSymbol) (arguments : List M.Domain) :
    M.sortInterp (σ.funcCodomain symbol) (witnessValue contract symbol arguments) := by
  unfold witnessValue
  by_cases hShape : WitnessShape symbol
  · simp only [if_pos hShape]
    cases arguments with
    | nil =>
        exact defaultValue_sort M (σ.funcCodomain symbol)
    | cons left rest =>
        cases rest with
        | nil =>
            exact defaultValue_sort M (σ.funcCodomain symbol)
        | cons right tail =>
            cases tail with
            | nil =>
                simpa [hShape.2] using
                  differenceValue_sort contract (inferredDomain symbol)
                    (inferredCodomain symbol) left right
            | cons extra tail =>
                exact defaultValue_sort M (σ.funcCodomain symbol)
  · simp only [if_neg hShape]
    exact defaultValue_sort M (σ.funcCodomain symbol)

theorem witnessValue_distinguishes
    {M : Structure σ} (contract : ExtensionalContract M)
    (symbol : σ.FuncSymbol) (domain codomain : SimpleType σ)
    (left right : M.Domain)
    (hDomain :
      σ.funcDomain symbol =
        [.arrow domain codomain, .arrow domain codomain])
    (hCodomain : σ.funcCodomain symbol = domain)
    (hLeft : M.sortInterp (.arrow domain codomain) left)
    (hRight : M.sortInterp (.arrow domain codomain) right)
    (hNe : left ≠ right) :
    M.applyInterp left (witnessValue contract symbol [left, right]) ≠
      M.applyInterp right (witnessValue contract symbol [left, right]) := by
  have hInferredDomain : inferredDomain symbol = domain := by
    simp [inferredDomain, hDomain]
  have hInferredCodomain : inferredCodomain symbol = codomain := by
    simp [inferredCodomain, hDomain]
  have hShape : WitnessShape symbol := by
    simp [WitnessShape, hInferredDomain, hInferredCodomain, hDomain, hCodomain]
  rw [show
    witnessValue contract symbol [left, right] =
      differenceValue contract (inferredDomain symbol) (inferredCodomain symbol)
        left right by
      simp [witnessValue, hShape]]
  rw [hInferredDomain, hInferredCodomain]
  exact differenceValue_distinguishes contract domain codomain left right
    hLeft hRight hNe

end WitnessInterpretation

section Model

variable {σ : Signature.{u, v, w}}

/-- 一次性覆盖签名中所有标记为外延见证的函数符号。 -/
noncomputable def Structure.overrideExtensionalWitnesses
    (M : Structure σ) (contract : ExtensionalContract M) : Structure σ where
  Domain := M.Domain
  nonempty := M.nonempty
  sortInterp := M.sortInterp
  sortNonempty := M.sortNonempty
  funcInterp := fun symbol arguments =>
    if σ.isFunctionExtensionalityWitness symbol = true then
      witnessValue contract symbol arguments
    else
      M.funcInterp symbol arguments
  funcSort := by
    intro symbol arguments hArguments
    by_cases hWitness : σ.isFunctionExtensionalityWitness symbol = true
    · change
        M.sortInterp (σ.funcCodomain symbol)
          (if σ.isFunctionExtensionalityWitness symbol = true then
            witnessValue contract symbol arguments
          else
            M.funcInterp symbol arguments)
      rw [if_pos hWitness]
      exact witnessValue_sort contract symbol arguments
    · change
        M.sortInterp (σ.funcCodomain symbol)
          (if σ.isFunctionExtensionalityWitness symbol = true then
            witnessValue contract symbol arguments
          else
            M.funcInterp symbol arguments)
      rw [if_neg hWitness]
      exact M.funcSort symbol arguments hArguments
  relInterp := M.relInterp
  applyInterp := M.applyInterp
  applySort := M.applySort
  lambdaInterp := M.lambdaInterp
  lambdaSort := M.lambdaSort

@[simp]
theorem Structure.overrideExtensionalWitnesses_funcInterp_witness
    {M : Structure σ} (contract : ExtensionalContract M)
    {symbol : σ.FuncSymbol} (hWitness :
      σ.isFunctionExtensionalityWitness symbol = true) (arguments : List M.Domain) :
    (Structure.overrideExtensionalWitnesses M contract).funcInterp symbol arguments =
      witnessValue contract symbol arguments := by
  simp [Structure.overrideExtensionalWitnesses, hWitness]

@[simp]
theorem Structure.overrideExtensionalWitnesses_funcInterp_nonWitness
    {M : Structure σ} (contract : ExtensionalContract M)
    {symbol : σ.FuncSymbol} (hWitness :
      σ.isFunctionExtensionalityWitness symbol = false) (arguments : List M.Domain) :
    (Structure.overrideExtensionalWitnesses M contract).funcInterp symbol arguments =
      M.funcInterp symbol arguments := by
  simp [Structure.overrideExtensionalWitnesses, hWitness]

/-- 覆盖只修改函数解释，因此所有原有 FOOL/lambda 语义操作保持不变。 -/
def extensionalContractPreserved
    {M : Structure σ} (contract : ExtensionalContract M) :
    ExtensionalContract (Structure.overrideExtensionalWitnesses M contract) where
  lambdaCongr := by
    simpa [Structure.overrideExtensionalWitnesses] using contract.lambdaCongr
  beta := by
    simpa [Structure.overrideExtensionalWitnesses] using contract.beta
  eta := by
    simpa [Structure.overrideExtensionalWitnesses] using contract.eta
  functionExtensionality := by
    simpa [Structure.overrideExtensionalWitnesses] using contract.functionExtensionality

/-- 覆盖后的模型自动获得全局外延见证合同。 -/
def extensionalWitnessContract
    {M : Structure σ} (contract : ExtensionalContract M) :
    ExtensionalWitnessContract (Structure.overrideExtensionalWitnesses M contract) where
  distinguishes := by
    intro symbol domain codomain left right hWitness hDomain hCodomain hLeft hRight hNe
    simp only [Structure.overrideExtensionalWitnesses, hWitness, ↓reduceIte]
    exact witnessValue_distinguishes contract symbol domain codomain left right
      hDomain hCodomain hLeft hRight hNe

/--
两个 witness 符号独立满足区分合同。

两组函数值可以重复；两组 domain/codomain 也可以完全不同。
-/
theorem twoWitnesses_distinguish_independently
    {M : Structure σ} (contract : ExtensionalContract M)
    (firstSymbol secondSymbol : σ.FuncSymbol)
    (firstDomain firstCodomain secondDomain secondCodomain : SimpleType σ)
    (firstLeft firstRight secondLeft secondRight : M.Domain)
    (hFirstWitness : σ.isFunctionExtensionalityWitness firstSymbol = true)
    (hSecondWitness : σ.isFunctionExtensionalityWitness secondSymbol = true)
    (hFirstDomain :
      σ.funcDomain firstSymbol =
        [.arrow firstDomain firstCodomain, .arrow firstDomain firstCodomain])
    (hSecondDomain :
      σ.funcDomain secondSymbol =
        [.arrow secondDomain secondCodomain, .arrow secondDomain secondCodomain])
    (hFirstCodomain : σ.funcCodomain firstSymbol = firstDomain)
    (hSecondCodomain : σ.funcCodomain secondSymbol = secondDomain)
    (hFirstLeft :
      M.sortInterp (.arrow firstDomain firstCodomain) firstLeft)
    (hFirstRight :
      M.sortInterp (.arrow firstDomain firstCodomain) firstRight)
    (hSecondLeft :
      M.sortInterp (.arrow secondDomain secondCodomain) secondLeft)
    (hSecondRight :
      M.sortInterp (.arrow secondDomain secondCodomain) secondRight)
    (hFirstNe : firstLeft ≠ firstRight)
    (hSecondNe : secondLeft ≠ secondRight) :
    let target := Structure.overrideExtensionalWitnesses M contract
    target.applyInterp firstLeft
        (target.funcInterp firstSymbol [firstLeft, firstRight]) ≠
          target.applyInterp firstRight
            (target.funcInterp firstSymbol [firstLeft, firstRight]) ∧
      target.applyInterp secondLeft
        (target.funcInterp secondSymbol [secondLeft, secondRight]) ≠
          target.applyInterp secondRight
            (target.funcInterp secondSymbol [secondLeft, secondRight]) := by
  let witnessContract := extensionalWitnessContract contract
  exact ⟨
    witnessContract.distinguishes firstSymbol firstDomain firstCodomain
      firstLeft firstRight hFirstWitness hFirstDomain hFirstCodomain
      hFirstLeft hFirstRight hFirstNe,
    witnessContract.distinguishes secondSymbol secondDomain secondCodomain
      secondLeft secondRight hSecondWitness hSecondDomain hSecondCodomain
      hSecondLeft hSecondRight hSecondNe⟩

end Model

section Environment

variable {σ : Signature.{u, v, w}}

/-- 把原模型环境搬到批量覆盖后的模型。 -/
def Env.rebase {M : Structure σ} (contract : ExtensionalContract M)
    (env : Env σ M) : Env σ (Structure.overrideExtensionalWitnesses M contract) where
  boundVal := env.boundVal
  freeVal := env.freeVal

/-- 从覆盖模型环境回拉到原模型。 -/
def Env.unbase {M : Structure σ} (contract : ExtensionalContract M)
    (env : Env σ (Structure.overrideExtensionalWitnesses M contract)) : Env σ M where
  boundVal := env.boundVal
  freeVal := env.freeVal

@[simp]
theorem Env.rebase_unbase {M : Structure σ} (contract : ExtensionalContract M)
    (env : Env σ (Structure.overrideExtensionalWitnesses M contract)) :
    Env.rebase contract (Env.unbase contract env) = env := by
  cases env
  rfl

@[simp]
theorem Env.unbase_rebase {M : Structure σ} (contract : ExtensionalContract M)
    (env : Env σ M) :
    Env.unbase contract (Env.rebase contract env) = env := by
  cases env
  rfl

theorem Env.wellSorted_rebase {M : Structure σ} (contract : ExtensionalContract M)
    {env : Env σ M} (hEnv : env.WellSorted []) :
    (Env.rebase contract env).WellSorted [] := by
  simpa [Env.rebase, Structure.overrideExtensionalWitnesses] using hEnv

theorem Env.wellSorted_unbase
    {M : Structure σ} (contract : ExtensionalContract M)
    {env : Env σ (Structure.overrideExtensionalWitnesses M contract)}
    (hEnv : env.WellSorted []) :
    (Env.unbase contract env).WellSorted [] := by
  simpa [Env.unbase, Structure.overrideExtensionalWitnesses] using hEnv

end Environment

section SourcePreservation

variable {σ : Signature.{u, v, w}}

mutual
  /-- witness-free 项在批量模型扩张前后解释相同。 -/
  theorem Term.eval_rebase_of_witnessFree
      {M : Structure σ} (contract : ExtensionalContract M)
      (env : Env σ M) :
      ∀ term, Syntax.termWitnessFree term = true →
        Term.eval (Env.rebase contract env) term = Term.eval env term
    | .var (.bvar sort index), _ => by
        simp [Term.eval, Env.rebase]
    | .var (.fvar sort id), _ => by
        simp [Term.eval, Env.rebase]
    | .app symbol arguments, hFree => by
        simp only [Syntax.termWitnessFree, Bool.and_eq_true_iff] at hFree
        have hFalse : σ.isFunctionExtensionalityWitness symbol = false := by
          cases hValue : σ.isFunctionExtensionalityWitness symbol with
          | false => rfl
          | true => simp [hValue] at hFree
        simp only [Term.eval, Structure.overrideExtensionalWitnesses, hFalse,
          Bool.false_eq_true, if_false]
        congr 1
        exact Term.evalList_rebase_of_witnessFree contract env arguments hFree.2
    | .apply function argument, hFree => by
        simp only [Syntax.termWitnessFree, Bool.and_eq_true_iff] at hFree
        simp only [Term.eval]
        rw [Term.eval_rebase_of_witnessFree contract env function hFree.1,
          Term.eval_rebase_of_witnessFree contract env argument hFree.2]
        rfl
    | .lam domain codomain body, hFree => by
        simp only [Syntax.termWitnessFree] at hFree
        simp only [Term.eval]
        congr 1
        funext value
        simpa [Env.rebase, Env.push] using
          Term.eval_rebase_of_witnessFree contract (env.push value) body hFree

  /-- witness-free 项列表在批量模型扩张前后逐项解释相同。 -/
  theorem Term.evalList_rebase_of_witnessFree
      {M : Structure σ} (contract : ExtensionalContract M)
      (env : Env σ M) :
      ∀ terms, Syntax.termListWitnessFree terms = true →
        (terms.map (Term.eval (Env.rebase contract env))) =
          terms.map (Term.eval env)
    | [], _ => by
        rfl
    | term :: rest, hFree => by
        simp only [Syntax.termListWitnessFree, Bool.and_eq_true_iff] at hFree
        simp only [List.map_cons]
        rw [Term.eval_rebase_of_witnessFree contract env term hFree.1,
          Term.evalList_rebase_of_witnessFree contract env rest hFree.2]
        rfl
end

theorem Atom.satisfies_rebase_of_witnessFree
    {M : Structure σ} (contract : ExtensionalContract M)
    (env : Env σ M) (atom : Atom σ)
    (hFree : Syntax.atomWitnessFree atom = true) :
    atom.Satisfies (Env.rebase contract env) ↔ atom.Satisfies env := by
  cases atom with
  | rel symbol arguments =>
      change
        (Structure.overrideExtensionalWitnesses M contract).relInterp symbol
            (arguments.map (Term.eval (Env.rebase contract env))) ↔
          M.relInterp symbol (arguments.map (Term.eval env))
      simp only [Structure.overrideExtensionalWitnesses]
      exact iff_of_eq <| congrArg (M.relInterp symbol)
        (Term.evalList_rebase_of_witnessFree contract env arguments hFree)
  | equal sort left right =>
      have hParts := Bool.and_eq_true_iff.mp hFree
      change
        Term.eval (Env.rebase contract env) left =
            Term.eval (Env.rebase contract env) right ↔
          Term.eval env left = Term.eval env right
      rw [Term.eval_rebase_of_witnessFree contract env left hParts.1,
        Term.eval_rebase_of_witnessFree contract env right hParts.2]
      rfl

theorem Literal.satisfies_rebase_of_witnessFree
    {M : Structure σ} (contract : ExtensionalContract M)
    (env : Env σ M) (literal : Literal σ)
    (hFree : Syntax.literalWitnessFree literal = true) :
    literal.Satisfies (Env.rebase contract env) ↔ literal.Satisfies env := by
  cases literal with
  | mk polarity atom =>
      cases polarity with
      | false =>
          change
            (¬ atom.Satisfies (Env.rebase contract env)) ↔
              ¬ atom.Satisfies env
          exact not_congr (Atom.satisfies_rebase_of_witnessFree contract env atom hFree)
      | true =>
          change
            atom.Satisfies (Env.rebase contract env) ↔
              atom.Satisfies env
          exact Atom.satisfies_rebase_of_witnessFree contract env atom hFree

theorem Clause.satisfies_rebase_of_witnessFree
    {M : Structure σ} (contract : ExtensionalContract M)
    (env : Env σ M) (clause : Clause σ)
    (hFree : Syntax.clauseWitnessFree clause = true) :
    clause.Satisfies (Env.rebase contract env) ↔ clause.Satisfies env := by
  constructor
  · rintro ⟨literal, hMember, hSatisfies⟩
    refine ⟨literal, hMember, ?_⟩
    rcases Array.mem_iff_getElem.mp hMember with ⟨index, hIndex, hGet⟩
    have hLiteral : Syntax.literalWitnessFree literal = true := by
      simpa [hGet] using Array.all_eq_true.mp hFree index hIndex
    exact (Literal.satisfies_rebase_of_witnessFree contract env literal hLiteral).mp hSatisfies
  · rintro ⟨literal, hMember, hSatisfies⟩
    refine ⟨literal, hMember, ?_⟩
    rcases Array.mem_iff_getElem.mp hMember with ⟨index, hIndex, hGet⟩
    have hLiteral : Syntax.literalWitnessFree literal = true := by
      simpa [hGet] using Array.all_eq_true.mp hFree index hIndex
    exact (Literal.satisfies_rebase_of_witnessFree contract env literal hLiteral).mpr hSatisfies

theorem Problem.valid_rebase_of_witnessFree
    {M : Structure σ} (contract : ExtensionalContract M)
    {problem : Problem σ} (hFree : SourceProblem.WitnessFree problem)
    (hValid : problem.Valid M) :
    problem.Valid (Structure.overrideExtensionalWitnesses M contract) := by
  intro targetEnv hTargetEnv
  let sourceEnv := Env.unbase contract targetEnv
  have hSourceEnv : sourceEnv.WellSorted [] :=
    Env.wellSorted_unbase contract hTargetEnv
  intro index clause hClause
  have hClauseFree := hFree index clause hClause
  have hSourceSatisfies := hValid sourceEnv hSourceEnv index clause hClause
  rw [← Env.rebase_unbase contract targetEnv]
  exact (Clause.satisfies_rebase_of_witnessFree contract sourceEnv clause hClauseFree).mpr
    hSourceSatisfies

/-- checked registry 携带的 source 合同足以把原问题整体搬到扩张模型。 -/
theorem checkedRegistry_problemValidAfterExpansion
    {σ : Signature.{u, v, w}} [DecidableEq σ.BaseSort]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {cert : HOExtensionalWitnessRegistry.CheckedDAG σ}
    (registry : HOExtensionalWitnessRegistry.CheckedRegistry cert)
    {M : Structure.{u, v, w, x} σ} (contract : ExtensionalContract M)
    (hValid : cert.dag.problem.Valid M) :
    cert.dag.problem.Valid (Structure.overrideExtensionalWitnesses M contract) :=
  Problem.valid_rebase_of_witnessFree contract
    registry.contract.sourceWitnessFree hValid

end SourcePreservation

section CoreProjection

open CoreSyntax
open CoreSyntax.NormalForm
open HOSearchMaterialization
open HOSearchMaterialization.CoreProjectionSoundness

abbrev CoreModel := CoreSyntax.NormalForm.Semantics.Model
abbrev CoreEnv (M : CoreModel) := CoreSyntax.NormalForm.Semantics.Env M
abbrev FoolLambdaContract := CoreSyntax.NormalForm.Semantics.FoolLambdaContract

/-- 同时保存 FOOL/lambda 合同、基础 HO 外延合同和扩张后的两个 HO 合同。 -/
structure Expansion {M : CoreModel}
    (contract : FoolLambdaContract M)
    (functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)) where
  foolLambda : FoolLambdaContract M
  base : Logic.HigherOrder.Structure SearchSignature
  baseExtensional : ExtensionalContract base
  expanded : Logic.HigherOrder.Structure SearchSignature
  expandedExtensional : ExtensionalContract expanded
  witness : ExtensionalWitnessContract expanded

/-- 从一个 FOOL/lambda 模型构造全量外延见证扩张。 -/
noncomputable def expand {M : CoreModel}
    (contract : FoolLambdaContract M)
    (functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)) :
    Expansion contract functionSort where
  foolLambda := contract
  base := searchStructure M contract functionSort
  baseExtensional := extensionalContract M contract functionSort
  expanded := Structure.overrideExtensionalWitnesses
    (searchStructure M contract functionSort)
    (extensionalContract M contract functionSort)
  expandedExtensional := extensionalContractPreserved
    (extensionalContract M contract functionSort)
  witness := extensionalWitnessContract
    (extensionalContract M contract functionSort)

/-- 原始 core source 在外延见证扩张中的可满足性保持。 -/
theorem expandedProblemValid
    {M : CoreModel} (contract : FoolLambdaContract M)
    (functionSort :
      ∀ symbol arguments,
        M.sortInterp symbol.outputSort (M.functionInterp symbol arguments))
    (base : CoreEnv M) (clauses : CoreSyntax.NormalForm.ClauseSet)
    (hNative : Native.clauseSet clauses = true)
    (hChecks :
      (coreProblem clauses).initialClauses.all HODAGCertificate.Clause.check = true)
    (hClauses :
      ∀ env, CoreSyntax.NormalForm.Semantics.Env.RespectsFree env →
        CoreSyntax.NormalForm.Semantics.LocalSkolemChoice.SameBoundStack env base →
          CoreSyntax.NormalForm.Semantics.ClauseSet.Satisfies env clauses)
    (hFree : SourceProblem.WitnessFree (coreProblem clauses)) :
    (coreProblem clauses).Valid
      (Structure.overrideExtensionalWitnesses
        (searchStructure M contract functionSort)
        (extensionalContract M contract functionSort)) := by
  apply Problem.valid_rebase_of_witnessFree
    (extensionalContract M contract functionSort) hFree
  exact coreProblem_valid contract functionSort base clauses hNative hChecks hClauses

end CoreProjection

end HOExtensionalWitnessSoundness
end Automation
end YesMetaZFC
