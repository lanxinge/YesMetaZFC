import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSchema
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSyntaxTransport

/-!
# ProofT 的内在 schema witness 闭包

这里用依赖索引记录每层 bound 上下文与最终矩阵上下文。旧层的
`FreeVarId`、`closeFreeAt`、freshness 和 `Admissible` 参数因此不再进入闭包接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 无界 witness 闭包 -/

/-- 从 `outer` 到 `inner` 的纯存在量词骨架。 -/
inductive WitnessPlan (free : SetContext) :
    SetContext → SetContext → Type where
  | nil (outer : SetContext) : WitnessPlan free outer outer
  | cons {outer inner : SetContext} :
      WitnessPlan free (SetSort.set :: outer) inner →
        WitnessPlan free outer inner

/-- 按依赖索引把最终矩阵封装为纯存在闭包。 -/
def witness_closure
    {free outer inner : SetContext} :
    WitnessPlan free outer inner →
      SetFormula inner free → SetFormula outer free
  | .nil _, body => body
  | .cons rest, body =>
      Formula.existsE SetSort.set
        (witness_closure rest body)

/-- 任意有限存在闭包都是 `Sigma1`。 -/
theorem witness_closure_sigma1
    {free outer inner : SetContext}
    (plan : WitnessPlan free outer inner)
    {body : SetFormula inner free}
    (hBody : Formula.IsSigma1 set_levy_bound body) :
    Formula.IsSigma1 set_levy_bound
      (witness_closure plan body) := by
  induction plan with
  | nil outer =>
      simpa [witness_closure] using hBody
  | cons rest ih =>
      simpa [witness_closure] using
        Formula.IsLevel1.existsE (ℬ := set_levy_bound)
          SetSort.set (ih hBody)

/-! ## 有界 witness 闭包 -/

/-- 每层界项直接处于当前 outer bound/free 上下文。 -/
inductive BoundedWitnessPlan (free : SetContext) :
    SetContext → SetContext → Type where
  | nil (outer : SetContext) : BoundedWitnessPlan free outer outer
  | cons {outer inner : SetContext}
      (bound : SetTerm outer free) :
      BoundedWitnessPlan free (SetSort.set :: outer) inner →
        BoundedWitnessPlan free outer inner

/-- 按依赖索引生成嵌套有界存在式。 -/
def bounded_witness_closure
    {free outer inner : SetContext} :
    BoundedWitnessPlan free outer inner →
      SetFormula inner free → SetFormula outer free
  | .nil _, body => body
  | .cons bound rest, body =>
      Formula.LevyBound.boundedExists set_levy_bound bound
        (bounded_witness_closure rest body)

/-- 有界 witness 闭包保持 `Delta0`，不需要任何 fresh 或良构旁证。 -/
theorem bounded_witness_closure_delta0
    {free outer inner : SetContext}
    (plan : BoundedWitnessPlan free outer inner)
    {body : SetFormula inner free}
    (hBody : Formula.IsDelta0 set_levy_bound body) :
    Formula.IsDelta0 set_levy_bound
      (bounded_witness_closure plan body) := by
  induction plan with
  | nil outer =>
      simpa [bounded_witness_closure] using hBody
  | cons bound rest ih =>
      simpa [bounded_witness_closure] using
        Formula.IsDelta0.bounded_exists bound (ih hBody)

/-! ## 有界闭包的类型化运输 -/

/-- 一个有界闭包计划在替换后的 outer 上下文中的完整运输结果。 -/
structure BoundedWitnessTransport
    (sourceFree sourceOuter sourceInner targetFree targetOuter : SetContext) where
  inner : SetContext
  plan : BoundedWitnessPlan targetFree targetOuter inner
  boundSubstitution :
    VariableSubstitution signature sourceInner inner targetFree
  freeSubstitution :
    VariableSubstitution signature sourceFree inner targetFree

/-- 沿计划递归提升 bound/free 替换，并同步改写每一层界项。 -/
def BoundedWitnessPlan.transport
    {sourceFree sourceOuter sourceInner targetFree targetOuter : SetContext}
    (plan : BoundedWitnessPlan sourceFree sourceOuter sourceInner)
    (boundSubstitution :
      VariableSubstitution signature sourceOuter targetOuter targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetOuter targetFree) :
    BoundedWitnessTransport sourceFree sourceOuter sourceInner
      targetFree targetOuter :=
  match plan with
  | .nil outer =>
      { inner := targetOuter
        plan := .nil targetOuter
        boundSubstitution := boundSubstitution
        freeSubstitution := freeSubstitution }
  | .cons bound rest =>
      let result := BoundedWitnessPlan.transport rest
        (VariableSubstitution.liftBound SetSort.set boundSubstitution)
        (VariableSubstitution.weakenBound SetSort.set freeSubstitution)
      { inner := result.inner
        plan := .cons
          (bound.substituteMapped boundSubstitution freeSubstitution)
          result.plan
        boundSubstitution := result.boundSubstitution
        freeSubstitution := result.freeSubstitution }

/-- 有界闭包与类型化替换交换，并返回同步运输后的计划。 -/
theorem bounded_witness_closure_substituteMapped
    {sourceFree sourceOuter sourceInner targetFree targetOuter : SetContext}
    (plan : BoundedWitnessPlan sourceFree sourceOuter sourceInner)
    (body : SetFormula sourceInner sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceOuter targetOuter targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetOuter targetFree) :
    (bounded_witness_closure plan body).substituteMapped
        boundSubstitution freeSubstitution =
      let result := BoundedWitnessPlan.transport plan
        boundSubstitution freeSubstitution
      bounded_witness_closure result.plan
        (body.substituteMapped result.boundSubstitution result.freeSubstitution) := by
  induction plan generalizing targetOuter with
  | nil outer =>
      rfl
  | cons bound rest ih =>
      simp [bounded_witness_closure, BoundedWitnessPlan.transport,
        Formula.LevyBound.boundedExists, Formula.substituteMapped,
        Formula.LevyBound.membership_substituteMapped,
        Term.substituteMapped, VariableSubstitution.liftBound,
        Term.substituteMapped_weakenBound, ih]

/--
引入最外层有界见证，并把该见证对后续界项与最终矩阵的影响统一交给
`BoundedWitnessPlan.transport`。调用方不再手工维护 binder 位置或新鲜变量。
-/
theorem bounded_witness_closure_cons_intro
    {T : SetTheory}
    {free inner : SetContext}
    {Γ : Context signature free}
    (bound : SetOpenTerm free)
    (rest : BoundedWitnessPlan free [SetSort.set] inner)
    (body : SetFormula inner free)
    (witness : SetOpenTerm free)
    (hBound : Γ ⊢ₘ[T] witness ∈ₘ bound)
    (hTail :
      let result := BoundedWitnessPlan.transport rest
        (VariableSubstitution.instantiateTop witness)
        VariableSubstitution.freeId
      Γ ⊢ₘ[T]
        bounded_witness_closure result.plan
          (body.substituteMapped
            result.boundSubstitution result.freeSubstitution)) :
    Γ ⊢ₘ[T]
      bounded_witness_closure (.cons bound rest) body := by
  apply bounded_exists_intro bound (bounded_witness_closure rest body)
    witness hBound
  change Γ ⊢ₘ[T]
    Formula.substituteMapped
      (VariableSubstitution.instantiateTop witness)
      VariableSubstitution.freeId
      (bounded_witness_closure rest body)
  rw [bounded_witness_closure_substituteMapped]
  exact hTail

/-! ## 有界见证的一次替换赋值 -/

/--
见证赋值沿计划从外向内扩展一份直接 bound 替换。每层界项立即在当前赋值下
解释，最终矩阵因此只执行一次替换，不积累多层 `transport` 复合。
-/
def BoundedWitnessAssignment
    (T : SetTheory)
    {free : SetContext}
    (Γ : Context signature free)
    {outer inner : SetContext}
    (plan : BoundedWitnessPlan free outer inner)
    (outerSubstitution :
      VariableSubstitution signature outer [] free) : Type :=
  match plan with
  | .nil _ => PUnit
  | .cons bound rest =>
      Σ witnessed : { witness : SetOpenTerm free //
        Γ ⊢ₘ[T]
          witness ∈ₘ
            bound.substituteMapped outerSubstitution
              VariableSubstitution.freeId },
        BoundedWitnessAssignment T Γ rest
          (VariableSubstitution.cons witnessed.1 outerSubstitution)

/-- 见证赋值最终得到从完整矩阵 bound 上下文到开放上下文的直接替换。 -/
def BoundedWitnessAssignment.finalSubstitution
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    {outer inner : SetContext}
    {plan : BoundedWitnessPlan free outer inner}
    {outerSubstitution :
      VariableSubstitution signature outer [] free}
    (assignment :
      BoundedWitnessAssignment T Γ plan outerSubstitution) :
    VariableSubstitution signature inner [] free :=
  match plan with
  | .nil _ => outerSubstitution
  | .cons _ rest =>
      BoundedWitnessAssignment.finalSubstitution
        assignment.2

/-- 完整见证赋值把有界闭包直接归约为最终矩阵的一次替换。 -/
theorem bounded_witness_closure_intro_assignment
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    {outer inner : SetContext}
    {plan : BoundedWitnessPlan free outer inner}
    {outerSubstitution :
      VariableSubstitution signature outer [] free}
    (assignment :
      BoundedWitnessAssignment T Γ plan outerSubstitution)
    (body : SetFormula inner free)
    (hBody : Γ ⊢ₘ[T]
      body.substituteMapped assignment.finalSubstitution
        VariableSubstitution.freeId) :
    Γ ⊢ₘ[T]
      (bounded_witness_closure plan body).substituteMapped
        outerSubstitution VariableSubstitution.freeId := by
  induction plan with
  | nil outer =>
      simpa [BoundedWitnessAssignment.finalSubstitution,
        bounded_witness_closure] using hBody
  | @cons outer inner bound rest ih =>
      rcases assignment with ⟨⟨witness, hBound⟩, tail⟩
      let transformedBound : SetOpenTerm free :=
        bound.substituteMapped outerSubstitution
          VariableSubstitution.freeId
      let transformedBody : SetFormula [SetSort.set] free :=
        (bounded_witness_closure rest body).substituteMapped
          (VariableSubstitution.liftBound SetSort.set outerSubstitution)
          (VariableSubstitution.weakenBound SetSort.set
            (VariableSubstitution.freeId :
              VariableSubstitution signature free [] free))
      have hTail : Γ ⊢ₘ[T]
          transformedBody.instantiateTop witness := by
        have hDirect := ih
          (outerSubstitution :=
            VariableSubstitution.cons witness outerSubstitution)
          tail body (by
            simpa [BoundedWitnessAssignment.finalSubstitution] using hBody)
        simpa only [transformedBody,
          Formula.substituteMapped_liftBound_instantiateTop] using hDirect
      have hExists : Γ ⊢ₘ[T]
          Formula.LevyBound.boundedExists set_levy_bound
            transformedBound transformedBody :=
        bounded_exists_intro transformedBound transformedBody witness
          (by simpa [transformedBound] using hBound) hTail
      simpa only [bounded_witness_closure, transformedBound, transformedBody,
        Formula.LevyBound.boundedExists, Formula.substituteMapped,
        Formula.LevyBound.membership_substituteMapped,
        Term.substituteMapped_weakenBound] using! hExists

/-- 有界 witness 闭包同时保持 `Sigma1`。 -/
theorem bounded_witness_closure_sigma1
    {free outer inner : SetContext}
    (plan : BoundedWitnessPlan free outer inner)
    {body : SetFormula inner free}
    (hBody : Formula.IsSigma1 set_levy_bound body) :
    Formula.IsSigma1 set_levy_bound
      (bounded_witness_closure plan body) := by
  induction plan with
  | nil outer =>
      simpa [bounded_witness_closure] using hBody
  | cons bound rest ih =>
      simpa [bounded_witness_closure] using
      Formula.IsLevel1.bounded_exists
          (ℬ := set_levy_bound) bound (ih hBody)

/-! ## 带闭包的 schema 分支 -/

/-- 把开放项提升到给定的 bound 上下文，提升过程由上下文类型决定。 -/
def weaken_bound_context
    {free : SetContext}
    (bound : SetContext)
    (term : SetOpenTerm free) : SetTerm bound free :=
  match bound with
  | [] => term
  | sort :: rest =>
      (weaken_bound_context rest term).weakenBound sort

theorem weaken_bound_context_eq_embedBoundClosed
    {free : SetContext}
    (bound : SetContext)
    (term : SetOpenTerm free) :
    weaken_bound_context bound term = term.embedBoundClosed bound := by
  induction bound with
  | nil =>
      rfl
  | cons sort rest ih =>
      exact congrArg (fun term => term.weakenBound sort) ih

/-- 闭 bound 项进入任意 witness 上下文后，替换只作用于其 free 参数。 -/
@[simp] theorem weaken_bound_context_substituteMapped
    {sourceFree targetFree sourceBound targetBound : SetContext}
    (term : SetOpenTerm sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    (weaken_bound_context sourceBound term).substituteMapped
        boundSubstitution freeSubstitution =
      term.substituteMapped VariableSubstitution.empty freeSubstitution := by
  rw [weaken_bound_context_eq_embedBoundClosed]
  exact Term.embedBoundClosed_substituteMapped
    term boundSubstitution freeSubstitution

/--
带依赖 witness 闭包的三元 schema 分支。

`condition` 的最终 bound 上下文由 `plan` 的索引固定；`condition_closed` 是唯一对外
暴露的开放条件，因此调用方不会再看到闭包内部的变量位置。
-/
structure BoundedTernaryBranch (free : SetContext) where
  tag : Nat
  bound : SetContext
  plan : BoundedWitnessPlan free [] bound
  condition :
    SetTerm bound free → SetTerm bound free → SetTerm bound free →
      SetFormula bound free
  delta0 :
    ∀ (formula certificate base : SetTerm bound free),
      Formula.IsDelta0 set_levy_bound
        (condition formula certificate base)

/-- 关闭一个带依赖 witness 的三元 schema 分支。 -/
def BoundedTernaryBranch.condition_closed
    {free : SetContext}
    (branch : BoundedTernaryBranch free)
    (formula certificate base : SetOpenTerm free) :
    SetOpenFormula free :=
  bounded_witness_closure branch.plan
    (branch.condition
      (weaken_bound_context branch.bound formula)
      (weaken_bound_context branch.bound certificate)
      (weaken_bound_context branch.bound base))

theorem BoundedTernaryBranch.condition_closed_delta0
    {free : SetContext}
    (branch : BoundedTernaryBranch free)
    (formula certificate base : SetOpenTerm free) :
    Formula.IsDelta0 set_levy_bound
      (branch.condition_closed formula certificate base) := by
  simpa [BoundedTernaryBranch.condition_closed] using
    bounded_witness_closure_delta0 branch.plan
      (branch.delta0
        (weaken_bound_context branch.bound formula)
        (weaken_bound_context branch.bound certificate)
        (weaken_bound_context branch.bound base))

theorem BoundedTernaryBranch.condition_closed_sigma1
    {free : SetContext}
    (branch : BoundedTernaryBranch free)
    (formula certificate base : SetOpenTerm free) :
    Formula.IsSigma1 set_levy_bound
      (branch.condition_closed formula certificate base) :=
  (branch.condition_closed_delta0 formula certificate base).to_sigma1

/-! ## 带依赖 witness 闭包的二元证书分支 -/

/-- 固定表与 schema 表共用的二元内在条件分支。 -/
structure BoundedBinaryBranch (free : SetContext) where
  tag : Nat
  bound : SetContext
  plan : BoundedWitnessPlan free [] bound
  condition :
    SetTerm bound free → SetTerm bound free → SetFormula bound free
  delta0 :
    ∀ (formula certificate : SetTerm bound free),
      Formula.IsDelta0 set_levy_bound
        (condition formula certificate)

/-- 关闭一个带依赖 witness 的二元证书分支。 -/
def BoundedBinaryBranch.condition_closed
    {free : SetContext}
    (branch : BoundedBinaryBranch free)
    (formula certificate : SetOpenTerm free) :
    SetOpenFormula free :=
  bounded_witness_closure branch.plan
    (branch.condition
      (weaken_bound_context branch.bound formula)
      (weaken_bound_context branch.bound certificate))

theorem BoundedBinaryBranch.condition_closed_delta0
    {free : SetContext}
    (branch : BoundedBinaryBranch free)
    (formula certificate : SetOpenTerm free) :
    Formula.IsDelta0 set_levy_bound
      (branch.condition_closed formula certificate) := by
  simpa [BoundedBinaryBranch.condition_closed] using
    bounded_witness_closure_delta0 branch.plan
      (branch.delta0
        (weaken_bound_context branch.bound formula)
        (weaken_bound_context branch.bound certificate))

theorem BoundedBinaryBranch.condition_closed_sigma1
    {free : SetContext}
    (branch : BoundedBinaryBranch free)
    (formula certificate : SetOpenTerm free) :
    Formula.IsSigma1 set_levy_bound
      (branch.condition_closed formula certificate) :=
  (branch.condition_closed_delta0 formula certificate).to_sigma1

/-- 二元内在证书分支的统一有限析取。 -/
def bounded_binary_condition_list
    {free : SetContext}
    (branches : List (BoundedBinaryBranch free))
    (formula certificate : SetOpenTerm free) :
    SetOpenFormula free :=
  match branches with
  | [] => Formula.falsum
  | branch :: rest =>
      branch.condition_closed formula certificate ∨ₘ
        bounded_binary_condition_list rest formula certificate

theorem bounded_binary_condition_list_delta0
    {free : SetContext}
    (branches : List (BoundedBinaryBranch free))
    (formula certificate : SetOpenTerm free) :
    Formula.IsDelta0 set_levy_bound
      (bounded_binary_condition_list branches formula certificate) := by
  induction branches with
  | nil =>
      exact Formula.IsDelta0.falsum
  | cons branch rest ih =>
      simpa [bounded_binary_condition_list] using
        Formula.IsDelta0.disj
          (branch.condition_closed_delta0 formula certificate)
          ih

theorem bounded_binary_condition_list_of_mem
    {T : SetTheory}
    {free : SetContext}
    {branches : List (BoundedBinaryBranch free)}
    {branch : BoundedBinaryBranch free}
    (hBranch : branch ∈ branches)
    {Γ : Context signature free}
    {formula certificate : SetOpenTerm free}
    (hCondition :
      Γ ⊢ₘ[T] branch.condition_closed formula certificate) :
    Γ ⊢ₘ[T]
      bounded_binary_condition_list branches formula certificate := by
  induction branches with
  | nil =>
      simp at hBranch
  | cons head rest ih =>
      rcases List.mem_cons.mp hBranch with rfl | hBranch
      · simpa [bounded_binary_condition_list] using
          FirstOrder.Derives.disj_intro_left hCondition
      · simpa [bounded_binary_condition_list] using
          FirstOrder.Derives.disj_intro_right
            (ih hBranch)

theorem bounded_binary_condition_list_neg
    {T : SetTheory}
    {free : SetContext}
    {branches : List (BoundedBinaryBranch free)}
    {Γ : Context signature free}
    {formula certificate : SetOpenTerm free}
    (hReject :
      ∀ branch, branch ∈ branches →
        Γ ⊢ₘ[T] ¬ₘ branch.condition_closed formula certificate) :
    Γ ⊢ₘ[T]
      ¬ₘ(bounded_binary_condition_list branches formula certificate) := by
  induction branches with
  | nil =>
      exact FirstOrder.Derives.neg_intro
        (FirstOrder.Derives.assumption List.mem_cons_self)
  | cons head rest ih =>
      let headCondition : SetOpenFormula free :=
        head.condition_closed formula certificate
      let restCondition : SetOpenFormula free :=
        bounded_binary_condition_list rest formula certificate
      have hHeadNeg : Γ ⊢ₘ[T] ¬ₘ headCondition := by
        exact hReject head (by simp)
      have hRestNeg : Γ ⊢ₘ[T] ¬ₘ restCondition := by
        apply ih
        intro branch hBranch
        exact hReject branch (by simp [hBranch])
      simpa [bounded_binary_condition_list, headCondition, restCondition]
        using IntrinsicSchema.disj_neg hHeadNeg hRestNeg

/-- 带闭包 schema 分支的统一有限析取。 -/
def bounded_condition_list
    {free : SetContext}
    (branches : List (BoundedTernaryBranch free))
    (formula certificate base : SetOpenTerm free) :
    SetOpenFormula free :=
  match branches with
  | [] => Formula.falsum
  | branch :: rest =>
      branch.condition_closed formula certificate base ∨ₘ
        bounded_condition_list rest formula certificate base

theorem bounded_condition_list_delta0
    {free : SetContext}
    (branches : List (BoundedTernaryBranch free))
    (formula certificate base : SetOpenTerm free) :
    Formula.IsDelta0 set_levy_bound
      (bounded_condition_list branches formula certificate base) := by
  induction branches with
  | nil =>
      exact Formula.IsDelta0.falsum
  | cons branch rest ih =>
      simpa [bounded_condition_list] using
        Formula.IsDelta0.disj
          (branch.condition_closed_delta0 formula certificate base)
          ih

theorem bounded_condition_list_of_mem
    {T : SetTheory}
    {free : SetContext}
    {branches : List (BoundedTernaryBranch free)}
    {branch : BoundedTernaryBranch free}
    (hBranch : branch ∈ branches)
    {Γ : Context signature free}
    {formula certificate base : SetOpenTerm free}
    (hCondition :
      Γ ⊢ₘ[T] branch.condition_closed formula certificate base) :
    Γ ⊢ₘ[T] bounded_condition_list branches formula certificate base := by
  induction branches with
  | nil =>
      simp at hBranch
  | cons head rest ih =>
      rcases List.mem_cons.mp hBranch with rfl | hBranch
      · simpa [bounded_condition_list] using
          FirstOrder.Derives.disj_intro_left hCondition
      · simpa [bounded_condition_list] using
          FirstOrder.Derives.disj_intro_right
            (ih hBranch)

theorem bounded_condition_list_neg
    {T : SetTheory}
    {free : SetContext}
    {branches : List (BoundedTernaryBranch free)}
    {Γ : Context signature free}
    {formula certificate base : SetOpenTerm free}
    (hReject :
      ∀ branch, branch ∈ branches →
        Γ ⊢ₘ[T] ¬ₘ branch.condition_closed formula certificate base) :
    Γ ⊢ₘ[T]
      ¬ₘ(bounded_condition_list branches formula certificate base) := by
  induction branches with
  | nil =>
      exact FirstOrder.Derives.neg_intro
        (FirstOrder.Derives.assumption List.mem_cons_self)
  | cons head rest ih =>
      let headCondition : SetOpenFormula free :=
        head.condition_closed formula certificate base
      let restCondition : SetOpenFormula free :=
        bounded_condition_list rest formula certificate base
      have hHeadNeg : Γ ⊢ₘ[T] ¬ₘ headCondition := by
        exact hReject head (by simp)
      have hRestNeg : Γ ⊢ₘ[T] ¬ₘ restCondition := by
        apply ih
        intro branch hBranch
        exact hReject branch (by simp [hBranch])
      simpa [bounded_condition_list, headCondition, restCondition]
        using IntrinsicSchema.disj_neg hHeadNeg hRestNeg

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
