import YesMetaZFC.Logic.FirstOrder.Context
import YesMetaZFC.Model.FirstOrder.SubstitutionSemantics

/-!
# 类型正确 Hilbert 内核的语义可靠性

可靠性直接对可信推导树归纳。内在排序语法已经排除非法项与公式，因此本层不再恢复
检查证书，也不携带良构、作用域或 freshness 证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x

namespace HilbertBaseAxiom

/-- 每个基础 Hilbert 模式在任意类型化环境中成立。 -/
theorem sound {σ : Signature.{u, v, w}}
    {free : SortContext σ} {formula : OpenFormula σ free}
    (hAxiom : HilbertBaseAxiom σ formula)
    {M : Structure.{u, v, w, x} σ} (env : Env M [] free) :
    Formula.satisfies env formula := by
  cases hAxiom with
  | implication_distribution antecedent middle consequent =>
      intro hChain hMiddle hAntecedent
      exact hChain hAntecedent (hMiddle hAntecedent)
  | self_implication formula =>
      exact fun hFormula _ => hFormula
  | weakening formula extra =>
      exact fun hFormula _ => hFormula
  | contradiction formula conclusion =>
      intro hFormula hNegation
      exact False.elim (hNegation hFormula)
  | classical formula =>
      intro hReduction
      exact Classical.byContradiction (fun hNegation =>
        hNegation (hReduction hNegation))
  | explosion formula conclusion =>
      intro hNegation hFormula
      exact False.elim (hNegation hFormula)
  | case_analysis formula conclusion =>
      intro hPositive hNegative
      by_cases hFormula : Formula.satisfies env formula
      · exact hPositive hFormula
      · exact hNegative hFormula
  | truth_intro =>
      trivial
  | falsum_elimination conclusion =>
      exact False.elim
  | negation_intro formula =>
      exact fun hRefutation => hRefutation
  | negation_elimination formula =>
      exact fun hFormula hNegation => hNegation hFormula
  | conjunction_intro left right =>
      exact fun hLeft hRight => ⟨hLeft, hRight⟩
  | conjunction_elim_left left right =>
      exact And.left
  | conjunction_elim_right left right =>
      exact And.right
  | disjunction_intro_left left right =>
      exact Or.inl
  | disjunction_intro_right left right =>
      exact Or.inr
  | disjunction_elimination left right conclusion =>
      intro hLeft hRight hDisjunction
      exact hDisjunction.elim hLeft hRight
  | biconditional_intro left right =>
      exact fun hForward hBackward => ⟨hForward, hBackward⟩
  | biconditional_elim_left left right =>
      exact fun hIff => hIff.mp
  | biconditional_elim_right left right =>
      exact fun hIff => hIff.mpr
  | forall_specialization sort body term =>
      intro hUniversal
      have hAtWitness := hUniversal (term.eval env)
      exact
        (Formula.satisfies_instantiateTop env term body).mpr
          hAtWitness
  | forall_distribution sort antecedent consequent =>
      intro hUniversalImplication hUniversalAntecedent
      apply (Formula.satisfies_forallFreeTop env consequent).mpr
      intro value
      have hImplication :=
        (Formula.satisfies_forallFreeTop env
          (Formula.imp antecedent consequent)).mp
          hUniversalImplication value
      have hAntecedent :=
        (Formula.satisfies_forallFreeTop env antecedent).mp
          hUniversalAntecedent value
      exact hImplication hAntecedent
  | vacuous_forall sort formula =>
      intro hFormula
      apply (Formula.satisfies_forallFreeTop env
        (formula.weakenFree sort)).mpr
      intro value
      exact (Formula.satisfies_weakenFree env value formula).mpr hFormula
  | exists_introduction sort body term =>
      intro hInstance
      refine ⟨term.eval env, ?_⟩
      exact
        (Formula.satisfies_instantiateTop env term body).mp hInstance
  | exists_elimination sort body conclusion =>
      intro hUniversalCase hExistential
      rcases (Formula.satisfies_existsFreeTop env body).mp hExistential with
        ⟨value, hBody⟩
      have hCase :=
        (Formula.satisfies_forallFreeTop env
          (Formula.imp body (conclusion.weakenFree sort))).mp
          hUniversalCase value
      exact (Formula.satisfies_weakenFree env value conclusion).mp
        (hCase hBody)
  | equality_substitution sort left right body =>
      intro hEquality hLeftInstance
      have hLeftBody : Formula.satisfies
          (env.pushBound (left.eval env)) body :=
        (Formula.satisfies_instantiateTop env left body).mp
          hLeftInstance
      have hRightBody : Formula.satisfies
          (env.pushBound (right.eval env)) body := by
        rw [← hEquality]
        exact hLeftBody
      exact
        (Formula.satisfies_instantiateTop env right body).mpr
          hRightBody
  | equality_reflexivity term =>
      rfl

end HilbertBaseAxiom

namespace HilbertDerivation

/-- 可信 Hilbert 推导树保持所有模型中的满足关系。 -/
theorem sound {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {formula : OpenFormula σ free}
    (proof : HilbertDerivation T free formula)
    {M : Structure.{u, v, w, x} σ}
    (hModels : Theory.Models M T) (env : Env M [] free) :
    Formula.satisfies env formula := by
  induction proof with
  | logical_axiom hAxiom =>
      exact hAxiom.sound env
  | @theory_axiom free sentence hTheory =>
      exact (Formula.satisfies_fromSentence env sentence).mpr
        (hModels sentence hTheory)
  | modus_ponens hAntecedent hImplication ihAntecedent ihImplication =>
      exact (ihImplication env) (ihAntecedent env)
  | @forall_generalization free sort formula hFormula ih =>
      apply (Formula.satisfies_forallFreeTop env formula).mpr
      intro value
      exact ih (env.pushFree value)
  | @free_strengthening free sort formula hFormula ih =>
      rcases M.nonempty sort with ⟨value⟩
      exact (Formula.satisfies_weakenFree env value formula).mp
        (ih (env.pushFree value))
  | @free_substitution sourceFree targetFree substitution formula
      hFormula ih =>
      apply (Formula.satisfies_substituteFree env substitution formula).mpr
      exact ih
        (env.pullback (Substitution.free_map substitution))

end HilbertDerivation

namespace Provable

/-- 核心可证性蕴含任意模型、任意类型化环境中的成立。 -/
theorem sound {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {formula : OpenFormula σ free}
    (hFormula : Provable T formula)
    {M : Structure.{u, v, w, x} σ}
    (hModels : Theory.Models M T) (env : Env M [] free) :
    Formula.satisfies env formula := by
  rcases hFormula with ⟨proof⟩
  exact proof.sound hModels env

end Provable

namespace Context

/-- 满足局部上下文时，可依次应用其规范蕴含闭包。 -/
theorem satisfies_of_discharge {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {free : SortContext σ}
    (env : Env M [] free) (Γ : Context σ free)
    (formula : OpenFormula σ free)
    (hContext : Satisfied env Γ)
    (hDischarge : Formula.satisfies env (discharge Γ formula)) :
    Formula.satisfies env formula := by
  induction Γ generalizing formula with
  | nil =>
      exact hDischarge
  | cons assumption rest ih =>
      have hRest : Satisfied env rest := by
        intro candidate hMem
        exact hContext candidate
          (List.mem_cons_of_mem assumption hMem)
      have hImplication : Formula.satisfies env
          (Formula.imp assumption formula) :=
        ih (Formula.imp assumption formula) hRest hDischarge
      exact hImplication
        (hContext assumption List.mem_cons_self)

end Context

namespace Derives

/-- 局部上下文推导的公共语义可靠性接口。 -/
theorem sound {σ : Signature.{u, v, w}}
    {T : Theory σ} {free : SortContext σ}
    {Γ : Context σ free} {formula : OpenFormula σ free}
    (hFormula : Derives T Γ formula)
    {M : Structure.{u, v, w, x} σ}
    (hModels : Theory.Models M T) (env : Env M [] free)
    (hContext : Context.Satisfied env Γ) :
    Formula.satisfies env formula :=
  Context.satisfies_of_discharge env Γ formula hContext
    (Provable.sound hFormula hModels env)

/-- 闭句定理给出标准模型论语义后承。 -/
theorem semantically_entails {σ : Signature.{u, v, w}}
    {T : Theory σ} {sentence : Sentence σ}
    (hSentence : Derives T [] sentence) :
    Theory.SemanticallyEntails.{u, v, w, x} T sentence := by
  intro M hModels
  exact hSentence.sound hModels Env.empty (by
    intro formula hMem
    cases hMem)

end Derives
end FirstOrder
end Logic
end YesMetaZFC
