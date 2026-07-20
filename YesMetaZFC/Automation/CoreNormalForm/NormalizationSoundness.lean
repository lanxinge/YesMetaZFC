import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaTraceSoundness

/-!
# Core normalization 与 NNF soundness

本模块证明核心公式进入 NNF 时的语义等价，并明确 normalization 的 βη、FOOL、
外延等规则需要额外的模型合同；NNF 逻辑转换本身不依赖这些合同。
-/

namespace YesMetaZFC
namespace Automation
namespace CoreSyntax
namespace NormalForm
namespace Semantics

universe x

/-
关闭全部归一化规则后，三个互递归 normalizer 只遍历语法树，不改变任何节点。
这个结果是纯一阶 preprocessing 不依赖 FOOL/lambda 合同的关键入口。
-/
mutual
  theorem normalizeTermWith_firstOrderIdentity :
      ∀ fuel term,
        normalizeTermWith Config.firstOrderIdentity fuel term = term
    | 0, _ => rfl
    | _ + 1, .bvar .. => rfl
    | _ + 1, .fvar .. => rfl
    | fuel + 1, .app symbol args => by
        simp only [normalizeTermWith]
        rw [normalizeTermListWith_firstOrderIdentity fuel args]
    | fuel + 1, .apply fn arg => by
        simp only [normalizeTermWith]
        rw [normalizeTermWith_firstOrderIdentity fuel fn,
          normalizeTermWith_firstOrderIdentity fuel arg]
        rfl
    | _ + 1, .bool .. => rfl
    | fuel + 1, .notE body => by
        simp only [normalizeTermWith]
        rw [normalizeTermWith_firstOrderIdentity fuel body]
        rfl
    | fuel + 1, .andE left right => by
        simp only [normalizeTermWith]
        rw [normalizeTermWith_firstOrderIdentity fuel left,
          normalizeTermWith_firstOrderIdentity fuel right]
        rfl
    | fuel + 1, .orE left right => by
        simp only [normalizeTermWith]
        rw [normalizeTermWith_firstOrderIdentity fuel left,
          normalizeTermWith_firstOrderIdentity fuel right]
        rfl
    | fuel + 1, .impE left right => by
        simp only [normalizeTermWith]
        rw [normalizeTermWith_firstOrderIdentity fuel left,
          normalizeTermWith_firstOrderIdentity fuel right]
        rfl
    | fuel + 1, .iffE left right => by
        simp only [normalizeTermWith]
        rw [normalizeTermWith_firstOrderIdentity fuel left,
          normalizeTermWith_firstOrderIdentity fuel right]
        rfl
    | fuel + 1, .quote formula => by
        simp only [normalizeTermWith]
        rw [normalizeFormulaWith_firstOrderIdentity fuel formula]
        rfl
    | fuel + 1, .lam domain codomain body => by
        simp only [normalizeTermWith]
        rw [normalizeTermWith_firstOrderIdentity fuel body]
        rfl
    | fuel + 1, .ite sort condition thenTerm elseTerm => by
        simp only [normalizeTermWith]
        rw [normalizeFormulaWith_firstOrderIdentity fuel condition,
          normalizeTermWith_firstOrderIdentity fuel thenTerm,
          normalizeTermWith_firstOrderIdentity fuel elseTerm]
        rfl

  theorem normalizeFormulaWith_firstOrderIdentity :
      ∀ fuel formula,
        normalizeFormulaWith Config.firstOrderIdentity fuel formula = formula
    | 0, _ => rfl
    | _ + 1, .trueE => rfl
    | _ + 1, .falseE => rfl
    | fuel + 1, .atom predicate args => by
        simp only [normalizeFormulaWith]
        rw [normalizeTermListWith_firstOrderIdentity fuel args]
    | fuel + 1, .equal sort left right => by
        simp only [normalizeFormulaWith]
        rw [normalizeTermWith_firstOrderIdentity fuel left,
          normalizeTermWith_firstOrderIdentity fuel right]
        rfl
    | fuel + 1, .boolTerm term => by
        simp only [normalizeFormulaWith]
        rw [normalizeTermWith_firstOrderIdentity fuel term]
        rfl
    | fuel + 1, .neg body => by
        simp only [normalizeFormulaWith]
        rw [normalizeFormulaWith_firstOrderIdentity fuel body]
        rfl
    | fuel + 1, .imp left right => by
        simp only [normalizeFormulaWith]
        rw [normalizeFormulaWith_firstOrderIdentity fuel left,
          normalizeFormulaWith_firstOrderIdentity fuel right]
        rfl
    | fuel + 1, .conj left right => by
        simp only [normalizeFormulaWith]
        rw [normalizeFormulaWith_firstOrderIdentity fuel left,
          normalizeFormulaWith_firstOrderIdentity fuel right]
        rfl
    | fuel + 1, .disj left right => by
        simp only [normalizeFormulaWith]
        rw [normalizeFormulaWith_firstOrderIdentity fuel left,
          normalizeFormulaWith_firstOrderIdentity fuel right]
        rfl
    | fuel + 1, .iffE left right => by
        simp only [normalizeFormulaWith]
        rw [normalizeFormulaWith_firstOrderIdentity fuel left,
          normalizeFormulaWith_firstOrderIdentity fuel right]
        rfl
    | fuel + 1, .forallE sort body => by
        simp only [normalizeFormulaWith]
        rw [normalizeFormulaWith_firstOrderIdentity fuel body]
        rfl
    | fuel + 1, .existsE sort body => by
        simp only [normalizeFormulaWith]
        rw [normalizeFormulaWith_firstOrderIdentity fuel body]
        rfl

  theorem normalizeTermListWith_firstOrderIdentity :
      ∀ fuel terms,
        normalizeTermListWith Config.firstOrderIdentity fuel terms = terms
    | 0, _ => rfl
    | _ + 1, [] => rfl
    | fuel + 1, term :: rest => by
        simp only [normalizeTermListWith]
        rw [normalizeTermWith_firstOrderIdentity fuel term,
          normalizeTermListWith_firstOrderIdentity fuel rest]
end

/-- 纯一阶恒等配置下，公开公式 normalizer 不改变 source。 -/
theorem normalizeFormula_firstOrderIdentity (formula : Formula) :
    normalizeFormula formula (config := Config.firstOrderIdentity) = formula :=
  normalizeFormulaWith_firstOrderIdentity _ _

/-- 当前极性下公式应满足的语义。 -/
def polaritySatisfiesFormula {M : Model} (env : Env M) : Polarity → Formula → Prop
  | .positive, formula => Formula.Satisfies env formula
  | .negative, formula => ¬ Formula.Satisfies env formula

private theorem imp_iff_not_or (left right : Prop) :
    (left → right) ↔ ¬left ∨ right := by
  classical
  by_cases hLeft : left <;> by_cases hRight : right <;> simp [hLeft, hRight]

private def formulaRecSize : Formula → Nat
  | Formula.trueE
  | Formula.falseE
  | Formula.atom ..
  | Formula.equal ..
  | Formula.boolTerm .. => 0
  | Formula.neg body => formulaRecSize body + 1
  | Formula.imp left right
  | Formula.conj left right
  | Formula.disj left right
  | Formula.iffE left right =>
      formulaRecSize left + formulaRecSize right + 1
  | Formula.forallE _ body
  | Formula.existsE _ body =>
      formulaRecSize body + 1

private theorem formulaRecSize_neg (body : Formula) :
    formulaRecSize body < formulaRecSize (.neg body) := by
  simp [formulaRecSize]

private theorem formulaRecSize_binary_left (left right : Formula)
    (constructor : Formula → Formula → Formula)
    (hConstructor : formulaRecSize (constructor left right) =
      formulaRecSize left + formulaRecSize right + 1) :
    formulaRecSize left < formulaRecSize (constructor left right) := by
  rw [hConstructor]
  omega

private theorem formulaRecSize_binary_right (left right : Formula)
    (constructor : Formula → Formula → Formula)
    (hConstructor : formulaRecSize (constructor left right) =
      formulaRecSize left + formulaRecSize right + 1) :
    formulaRecSize right < formulaRecSize (constructor left right) := by
  rw [hConstructor]
  omega

private theorem formulaRecSize_quantifier (sort : CoreSort) (body : Formula)
    (constructor : CoreSort → Formula → Formula)
    (hConstructor : formulaRecSize (constructor sort body) =
      formulaRecSize body + 1) :
    formulaRecSize body < formulaRecSize (constructor sort body) := by
  rw [hConstructor]
  omega

/-- `toNnfWith` 在正极性保留公式语义，在负极性表达公式否定。 -/
theorem Nnf.satisfies_toNnfWith {M : Model} (env : Env M)
    (polarity : Polarity) (formula : Formula) :
    Nnf.Satisfies env (toNnfWith polarity formula) ↔
      polaritySatisfiesFormula env polarity formula := by
  classical
  cases formula with
  | trueE =>
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Nnf.Satisfies,
          Formula.Satisfies, Formula.eval]
  | falseE =>
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Nnf.Satisfies,
          Formula.Satisfies, Formula.eval]
  | atom predicate args =>
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Polarity.literal,
          Nnf.Satisfies, Literal.Satisfies, Atom.Satisfies,
          Formula.Satisfies, Formula.eval] <;> rfl
  | equal sort left right =>
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Polarity.literal,
          Nnf.Satisfies, Literal.Satisfies, Atom.Satisfies,
          Formula.Satisfies, Formula.eval] <;> rfl
  | boolTerm term =>
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Polarity.literal,
          Nnf.Satisfies, Literal.Satisfies, Atom.Satisfies,
          Formula.Satisfies, Formula.eval] <;> rfl
  | neg body =>
      have hPositive := Nnf.satisfies_toNnfWith env Polarity.positive body
      have hNegative := Nnf.satisfies_toNnfWith env Polarity.negative body
      cases polarity
      · simpa [toNnfWith, polaritySatisfiesFormula, Polarity.flip,
          Formula.Satisfies, Formula.eval] using hNegative
      · simpa [toNnfWith, polaritySatisfiesFormula, Polarity.flip,
          Formula.Satisfies, Formula.eval] using hPositive
  | imp left right =>
      have hLeftPositive := Nnf.satisfies_toNnfWith env Polarity.positive left
      have hLeftNegative := Nnf.satisfies_toNnfWith env Polarity.negative left
      have hRightPositive := Nnf.satisfies_toNnfWith env Polarity.positive right
      have hRightNegative := Nnf.satisfies_toNnfWith env Polarity.negative right
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Nnf.Satisfies,
          Formula.Satisfies, Formula.eval, hLeftPositive, hLeftNegative,
          hRightPositive, hRightNegative, imp_iff_not_or]
  | conj left right =>
      have hLeftPositive := Nnf.satisfies_toNnfWith env Polarity.positive left
      have hLeftNegative := Nnf.satisfies_toNnfWith env Polarity.negative left
      have hRightPositive := Nnf.satisfies_toNnfWith env Polarity.positive right
      have hRightNegative := Nnf.satisfies_toNnfWith env Polarity.negative right
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Nnf.Satisfies,
          Formula.Satisfies, Formula.eval, hLeftPositive, hLeftNegative,
          hRightPositive, hRightNegative, imp_iff_not_or]
  | disj left right =>
      have hLeftPositive := Nnf.satisfies_toNnfWith env Polarity.positive left
      have hLeftNegative := Nnf.satisfies_toNnfWith env Polarity.negative left
      have hRightPositive := Nnf.satisfies_toNnfWith env Polarity.positive right
      have hRightNegative := Nnf.satisfies_toNnfWith env Polarity.negative right
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Nnf.Satisfies,
          Formula.Satisfies, Formula.eval, hLeftPositive, hLeftNegative,
          hRightPositive, hRightNegative]
  | iffE left right =>
      have hLeftPositive := Nnf.satisfies_toNnfWith env Polarity.positive left
      have hLeftNegative := Nnf.satisfies_toNnfWith env Polarity.negative left
      have hRightPositive := Nnf.satisfies_toNnfWith env Polarity.positive right
      have hRightNegative := Nnf.satisfies_toNnfWith env Polarity.negative right
      cases polarity <;>
        by_cases hLeft : (Formula.eval env left).holds <;>
        by_cases hRight : (Formula.eval env right).holds <;>
        simp [toNnfWith, polaritySatisfiesFormula, Nnf.Satisfies,
          Formula.Satisfies, Formula.eval, hLeftPositive, hLeftNegative,
          hRightPositive, hRightNegative, hLeft, hRight]
  | forallE sort body =>
      have hPositive (value : M.Carrier) :=
        Nnf.satisfies_toNnfWith (env.push value) Polarity.positive body
      have hNegative (value : M.Carrier) :=
        Nnf.satisfies_toNnfWith (env.push value) Polarity.negative body
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Nnf.Satisfies,
          Formula.Satisfies, Formula.eval, hPositive, hNegative]
  | existsE sort body =>
      have hPositive (value : M.Carrier) :=
        Nnf.satisfies_toNnfWith (env.push value) Polarity.positive body
      have hNegative (value : M.Carrier) :=
        Nnf.satisfies_toNnfWith (env.push value) Polarity.negative body
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Nnf.Satisfies,
          Formula.Satisfies, Formula.eval, hPositive, hNegative]
termination_by formulaRecSize formula
decreasing_by
  all_goals
    first
    | exact formulaRecSize_neg _
    | apply formulaRecSize_binary_left <;> rfl
    | apply formulaRecSize_binary_right <;> rfl
    | apply formulaRecSize_quantifier <;> rfl

/-- 正极性 NNF 与源公式语义等价。 -/
theorem Nnf.satisfies_toNnfWith_positive {M : Model} (env : Env M)
    (formula : Formula) :
    Nnf.Satisfies env (toNnfWith Polarity.positive formula) ↔
      Formula.Satisfies env formula := by
  simpa [polaritySatisfiesFormula] using
    Nnf.satisfies_toNnfWith env Polarity.positive formula

/- 公式与其正极性 NNF 的可满足性完全等价。 -/
theorem Nnf.satisfiable_toNnfWith_positive (formula : Formula) :
    Nnf.Satisfiable.{x} (toNnfWith Polarity.positive formula) ↔
      Formula.Satisfiable.{x} formula := by
  constructor
  · rintro ⟨M, env, hNnf⟩
    exact ⟨M, env, (Nnf.satisfies_toNnfWith_positive env formula).mp hNnf⟩
  · rintro ⟨M, env, hFormula⟩
    exact ⟨M, env, (Nnf.satisfies_toNnfWith_positive env formula).mpr hFormula⟩

end Semantics
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
