import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureDiagonalGraph
import YesMetaZFC.Automation.FormulaBinderSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureQuotationFaithful

/-! # 裸 ZFC 中带参数的纯公式自身编码固定点

正文采用一个绑定输入槽。数码封闭之后，编码图的输出精确等于所得纯公式本身的码；
候选中的全部自由参数仍按原环境读取。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFixedPoint
open Nonlogical.BasicSetTheory PureOpenTransfer PureQuotation
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature RelationalTranslation.Expansion.model PureCompletedStage.interpretation
universe x
variable {parameters : SetContext}

abbrev Candidate_m (parameters : SetContext) := OpenFormula ℒ (pureContext_m (SetSort.set :: parameters))

noncomputable def body_m (P : Candidate_m parameters) :
    Formula ℒ (pureContext_m [SetSort.set]) (pureContext_m parameters) :=
  .existsE PureModel.setSort (.conj
    (PureDiagonalGraph.apply_m (.bvar (.there .here)) (.bvar .here))
    (Formula.weakenBound (σ := ℒ) (bound := []) (free := pureContext_m (SetSort.set :: parameters)) PureModel.setSort P).abstractFreeTop)

-- 在抽象公式上证明语义外壳，再装入完整纯图，避免内核归约整张图。
attribute [local irreducible] body_m PureDiagonalGraph.apply_m

noncomputable def formula_m (P : Candidate_m parameters) : OpenFormula ℒ (pureContext_m parameters) :=
  specialize_m (free := parameters) (body_m P) (code_m (bound := [SetSort.set]) (free := parameters) (body_m P))

def predicate_m (P : Candidate_m parameters) (φ : OpenFormula ℒ (pureContext_m parameters)) :
    OpenFormula ℒ (pureContext_m parameters) :=
  instance_m P (code_m (bound := []) (free := parameters) φ)

attribute [local irreducible] formula_m number_m code_m diagonalValue_m numeralCode_m zeroCode_m successorCode_m numeralStep_m

theorem body_satisfies_m {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ PureModel.theory)
    (env : Env ℳ [] (pureContext_m parameters)) (P : Candidate_m parameters) (n : Nat) :
    (body_m P).satisfies (env.pushBound (number_m hℳ n)) ↔
      P.satisfies (env.pushFree (number_m hℳ (diagonalValue_m n))) := by
  unfold body_m
  rw [Formula.satisfies_exists_m]
  simp only [Formula.satisfies_conj_m]
  have hg (a : PureModel.Carrier ℳ) := PureDiagonalGraph.satisfies_m hℳ
    ((env.pushBound (number_m hℳ n)).pushBound a) (.bvar (.there .here)) (.bvar .here) n rfl
  have hp (a : PureModel.Carrier ℳ) :
      (Formula.weakenBound (σ := ℒ) (bound := []) (free := pureContext_m (SetSort.set :: parameters)) PureModel.setSort P).abstractFreeTop.satisfies
        ((env.pushBound (number_m hℳ n)).pushBound a) ↔ P.satisfies (env.pushFree a) :=
    (Formula.satisfies_abstractFreeTop (env.pushBound (number_m hℳ n)) a _).trans
      (Formula.satisfies_weakenBound_m (env.pushFree a) (number_m hℳ n) P)
  constructor
  · rintro ⟨a, ha, hb⟩
    have he : a = number_m hℳ (diagonalValue_m n) := (hg a).mp ha
    have hP := (hp a).mp hb
    rwa [he] at hP
  · intro hP
    exact ⟨number_m hℳ (diagonalValue_m n), (hg _).mpr rfl, (hp _).mpr hP⟩

/-- 参数任意赋值下，最终纯公式的真值等于候选在该纯公式自身编码处的真值。 -/
theorem satisfies_m {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ PureModel.theory)
    (env : Env ℳ [] (pureContext_m parameters)) (P : Candidate_m parameters) :
    (formula_m P).satisfies env ↔
      P.satisfies (env.pushFree (number_m hℳ (code_m (bound := []) (free := parameters) (formula_m P)))) := by
  unfold formula_m
  rw [self_code_m]
  exact (specialize_satisfies_m hℳ env (body_m P) _).trans (body_satisfies_m hℳ env P _)

theorem predicate_satisfies_m {ℳ : Structure.{0,0,0,x} ℒ} (hℳ : Theory.Models ℳ PureModel.theory)
    (env : Env ℳ [] (pureContext_m parameters)) (P : Candidate_m parameters)
    (φ : OpenFormula ℒ (pureContext_m parameters)) :
    (predicate_m P φ).satisfies env ↔
      P.satisfies (env.pushFree (number_m hℳ (code_m (bound := []) (free := parameters) φ))) :=
  instance_satisfies_m hℳ env P _

theorem fixed_point_m (P : Candidate_m parameters) :
    Derives PureModel.theory [] (.iff (formula_m P) (predicate_m P (formula_m P))) := by
  apply SemanticTransfer.derives_open_m PureRosserSchedule.target
  intro ℳ hℳ env
  rw [Formula.satisfies_iff_m]
  exact (satisfies_m hℳ env P).trans (predicate_satisfies_m hℳ env P (formula_m P)).symm

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFixedPoint
