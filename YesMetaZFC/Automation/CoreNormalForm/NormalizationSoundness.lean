import YesMetaZFC.Automation.CoreNormalForm.FoolLambdaTraceSoundness
/-!
# Core normalization 与 NNF soundness
本模块证明核心公式进入 NNF 时的语义等价，并明确 normalization 的 βη、FOOL、
外延等规则需要额外的模型合同；NNF 逻辑转换本身不依赖这些合同。
-/
namespace YesMetaZFC.Automation.CoreSyntax.NormalForm.Semantics
universe x
mutual
  theorem normalizeTermWith_firstOrderIdentity : ∀ fuel term, normalizeTermWith Config.firstOrderIdentity fuel term = term := by
    intro fuel term
    cases fuel with
    | zero => rfl
    | succ fuel =>
        cases term <;> simp only [normalizeTermWith,
          normalizeTermWith_firstOrderIdentity fuel,
          normalizeFormulaWith_firstOrderIdentity fuel,
          normalizeTermListWith_firstOrderIdentity fuel] <;> rfl
  theorem normalizeFormulaWith_firstOrderIdentity : ∀ fuel formula, normalizeFormulaWith Config.firstOrderIdentity fuel formula = formula
    | 0, _ => rfl
    | _ + 1, .trueE => rfl
    | _ + 1, .falseE => rfl
    | fuel + 1, .atom predicate args => by
        simp only [normalizeFormulaWith]
        rw [normalizeTermListWith_firstOrderIdentity fuel args]
    | fuel + 1, .equal sort left right => by
        simp only [normalizeFormulaWith]
        rw [normalizeTermWith_firstOrderIdentity fuel left, normalizeTermWith_firstOrderIdentity fuel right]
        rfl
    | fuel + 1, .boolTerm term => by
        simp only [normalizeFormulaWith]
        rw [normalizeTermWith_firstOrderIdentity fuel term]
        rfl
    | fuel + 1, .neg body => by
        simp only [normalizeFormulaWith]
        rw [normalizeFormulaWith_firstOrderIdentity fuel body]
        rfl
    | fuel + 1, .imp left right
    | fuel + 1, .conj left right
    | fuel + 1, .disj left right
    | fuel + 1, .iffE left right => by
        simp only [normalizeFormulaWith]
        rw [normalizeFormulaWith_firstOrderIdentity fuel left, normalizeFormulaWith_firstOrderIdentity fuel right]
        rfl
    | fuel + 1, .forallE sort body
    | fuel + 1, .existsE sort body => by
        simp only [normalizeFormulaWith]
        rw [normalizeFormulaWith_firstOrderIdentity fuel body]
        rfl
  theorem normalizeTermListWith_firstOrderIdentity : ∀ fuel terms, normalizeTermListWith Config.firstOrderIdentity fuel terms = terms := by
    intro fuel terms
    cases fuel with
    | zero => rfl
    | succ fuel =>
        cases terms <;> simp only [normalizeTermListWith,
          normalizeTermWith_firstOrderIdentity fuel,
          normalizeTermListWith_firstOrderIdentity fuel] <;> rfl

end
theorem normalizeFormula_firstOrderIdentity (formula : Formula) : normalizeFormula formula (config := Config.firstOrderIdentity) = formula :=
  normalizeFormulaWith_firstOrderIdentity _ _
def polaritySatisfiesFormula {M : Model} (env : Env M) : Polarity → Formula → Prop
  | .positive, formula => Formula.Satisfies env formula
  | .negative, formula => ¬ Formula.Satisfies env formula
private theorem imp_iff_not_or (left right : Prop) : (left → right) ↔ ¬left ∨ right := by
  classical
  by_cases hLeft : left <;> by_cases hRight : right <;> simp [hLeft, hRight]
theorem Nnf.satisfies_toNnfWith {M : Model} (env : Env M) (polarity : Polarity) (formula : Formula) : Nnf.Satisfies env (toNnfWith polarity formula) ↔ polaritySatisfiesFormula env polarity formula := by
  classical
  cases formula with
  | trueE | falseE =>
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Nnf.Satisfies, Formula.Satisfies, Formula.eval]
  | atom predicate args | equal sort left right | boolTerm term =>
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Polarity.literal, Nnf.Satisfies,
          Literal.Satisfies, Atom.Satisfies, Formula.Satisfies, Formula.eval] <;> rfl
  | neg body =>
      have hPositive := Nnf.satisfies_toNnfWith env Polarity.positive body
      have hNegative := Nnf.satisfies_toNnfWith env Polarity.negative body
      cases polarity
      · simpa [toNnfWith, polaritySatisfiesFormula, Polarity.flip, Formula.Satisfies, Formula.eval] using hNegative
      · simpa [toNnfWith, polaritySatisfiesFormula, Polarity.flip, Formula.Satisfies, Formula.eval] using hPositive
  | imp left right | conj left right | disj left right =>
      have hLeftPositive := Nnf.satisfies_toNnfWith env Polarity.positive left
      have hLeftNegative := Nnf.satisfies_toNnfWith env Polarity.negative left
      have hRightPositive := Nnf.satisfies_toNnfWith env Polarity.positive right
      have hRightNegative := Nnf.satisfies_toNnfWith env Polarity.negative right
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Nnf.Satisfies, Formula.Satisfies, Formula.eval, hLeftPositive, hLeftNegative, hRightPositive, hRightNegative, imp_iff_not_or]
  | iffE left right =>
      have hLeftPositive := Nnf.satisfies_toNnfWith env Polarity.positive left
      have hLeftNegative := Nnf.satisfies_toNnfWith env Polarity.negative left
      have hRightPositive := Nnf.satisfies_toNnfWith env Polarity.positive right
      have hRightNegative := Nnf.satisfies_toNnfWith env Polarity.negative right
      cases polarity <;>
        by_cases hLeft : (Formula.eval env left).holds <;>
        by_cases hRight : (Formula.eval env right).holds <;>
        simp [toNnfWith, polaritySatisfiesFormula, Nnf.Satisfies, Formula.Satisfies, Formula.eval, hLeftPositive, hLeftNegative, hRightPositive, hRightNegative, hLeft, hRight]
  | forallE sort body | existsE sort body =>
      have hPositive (value : M.Carrier) :=
        Nnf.satisfies_toNnfWith (env.push value) Polarity.positive body
      have hNegative (value : M.Carrier) :=
        Nnf.satisfies_toNnfWith (env.push value) Polarity.negative body
      cases polarity <;>
        simp [toNnfWith, polaritySatisfiesFormula, Nnf.Satisfies, Formula.Satisfies, Formula.eval, hPositive, hNegative]
termination_by structural formula

theorem Nnf.satisfies_toNnfWith_positive {M : Model} (env : Env M) (formula : Formula) : Nnf.Satisfies env (toNnfWith Polarity.positive formula) ↔ Formula.Satisfies env formula := by
  simpa [polaritySatisfiesFormula] using
    Nnf.satisfies_toNnfWith env Polarity.positive formula
theorem Nnf.satisfiable_toNnfWith_positive (formula : Formula) : Nnf.Satisfiable.{x} (toNnfWith Polarity.positive formula) ↔ Formula.Satisfiable.{x} formula := by
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
