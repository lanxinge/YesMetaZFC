import YesMetaZFC.Model.Interpretation.RelationalExpansion

/-! # 按原定义正文消去关系符号

开放公式以参数列表为自由槽翻译。若关系图就是其原定义正文的翻译，则任意实现
这些图的扩张逐参数满足该定义；这里同时覆盖带量词、否定和复合函数项的正文。
-/
namespace YesMetaZFC.Automation.RelationalTranslation
open Logic Logic.FirstOrder
set_option autoImplicit false
attribute [local implicit_reducible] Expansion.model
universe x
variable {σ τ : Signature.{0, 0, 0}}

def mapVariable (I : Interpretation σ τ) {sorts : SortContext σ} {sort : σ.SortSymbol} :
    Variable sorts sort → Variable (sorts.map I.sort) (I.sort sort)
  | .here => .here
  | .there previous => .there (mapVariable I previous)

def openFormula (I : Interpretation σ τ) {free : SortContext σ} (body : Formula σ [] free) :
    Formula τ [] (free.map I.sort) :=
  formula I (fun {sort} (entry : Variable [] sort) => nomatch entry) (fun entry => .fvar (mapVariable I entry)) body

theorem mapVariable_value {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ} (E : Expansion I M)
    {sorts : SortContext σ} (args : Values E.model.Carrier sorts)
    {sort : σ.SortSymbol} (entry : Variable sorts sort) :
    (templateEnv (mapValues I args)).freeVal (mapVariable I entry) = (templateEnv args).freeVal entry := by
  induction args with
  | nil => exact nomatch entry
  | cons head tail ih => cases entry with
    | here => rfl
    | there previous => exact ih previous

theorem openFormula_correct {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (E : Expansion I M) (hE : Realizes E) {free : SortContext σ}
    (body : Formula σ [] free) (args : Values E.model.Carrier free) :
    (openFormula I body).satisfies (templateEnv (mapValues I args)) ↔ body.satisfies (templateEnv args) := by
  unfold openFormula
  rw [formula_correct E hE]
  have hEnv : sourceEnv E (templateEnv (mapValues I args)) (fun {sort} (entry : Variable [] sort) => nomatch entry)
      (fun entry => .fvar (mapVariable I entry)) = templateEnv args := by
    apply Env.ext
    · intro sort entry
      exact nomatch entry
    · intro sort entry
      exact mapVariable_value E args entry
  rw [hEnv]

/-- 关系图方程给出原定义的任意参数语义，不假定原定义公理本身。 -/
theorem realizes_definition {I : Interpretation σ τ} {M : Structure.{0, 0, 0, x} τ}
    (E : Expansion I M) (hE : Realizes E) (symbol : σ.RelSymbol)
    (body : Formula σ [] (σ.relDomain symbol))
    (hGraph : I.relation symbol = openFormula I body) (args : Values E.model.Carrier (σ.relDomain symbol)) :
    E.relation symbol args ↔ body.satisfies (templateEnv args) := by
  rw [← hE.relation symbol args, hGraph]
  exact openFormula_correct E hE body args

/- 定义正文的符号依赖检查；逐一访问项参数和公式构造子。 -/
mutual
def termCovered (functions : σ.FuncSymbol → Bool) {bound free : SortContext σ} {sort : σ.SortSymbol} :
    Term σ bound free sort → Bool
  | .bvar _ | .fvar _ => true
  | .app symbol args => functions symbol && argumentsCovered functions args

def argumentsCovered (functions : σ.FuncSymbol → Bool) {bound free sorts : SortContext σ} :
    Arguments σ bound free sorts → Bool
  | .nil => true
  | .cons head tail => termCovered functions head && argumentsCovered functions tail
end

def formulaCovered (functions : σ.FuncSymbol → Bool) (relations : σ.RelSymbol → Bool)
    {bound free : SortContext σ} : Formula σ bound free → Bool
  | .falsum | .truth => true
  | .rel symbol args => relations symbol && argumentsCovered functions args
  | .equal left right => termCovered functions left && termCovered functions right
  | .neg body => formulaCovered functions relations body
  | .conj left right | .disj left right | .imp left right | .iff left right =>
    formulaCovered functions relations left && formulaCovered functions relations right
  | .forallE _ body | .existsE _ body => formulaCovered functions relations body

end YesMetaZFC.Automation.RelationalTranslation
