import YesMetaZFC.Model.ZFC.Pure.PureSyntaxStage

/-! # 结构语法构造的内部自然数界

使用实际 Gödel 配对、后继与识别不动点的 guard，证明结构码构造保持内部 ω。
这些结论只提供集合收集所需的界，不额外断言任意字段都构成良构公式。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureStructuralCodeBounds
open PureModel PureNaturalInduction PureArithmeticSpecifications
open _root_.YesMetaZFC.Automation.RelationalTranslation
open Nonlogical.BasicSetTheory FormalSystem
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}
noncomputable abbrev E (hℳ : Theory.Models ℳ theory) := PureSyntaxStage.expansion hℳ

theorem pairing (hℳ : Theory.Models ℳ theory) {left right : Carrier ℳ}
    (hLeft : membership ℳ left (omega hℳ)) (hRight : membership ℳ right (omega hℳ)) :
    membership ℳ ((E hℳ).function .godelPairing (.cons left (.cons right .nil))) (omega hℳ) := by
  have hGraph := ((PureSyntaxStage.realizes hℳ).function .godelPairing (.cons left (.cons right .nil)) _).mpr rfl
  have hSpec := (PureGodelPairing.agrees hℳ hLeft hRight _).mp hGraph
  exact ((PureGodelPairing.specification_correct hℳ left right _).mp hSpec).1

theorem numeral (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (number : Nat) :
    membership ℳ ((finite_numeral_term number).eval env) (omega hℳ) := by
  induction number with
  | zero =>
    change membership ℳ ((PureRoundTwoStage.expansion hℳ).function .emptySet .nil) _
    rw [PureSyntaxOperator.zero_eq hℳ]
    exact zero_mem hℳ
  | succ number ih =>
    change membership ℳ ((PureRoundTwoStage.expansion hℳ).function .successor (.cons ((finite_numeral_term number).eval env) .nil)) _
    rw [PureSyntaxOperator.succ_eq hℳ]
    exact succ_mem hℳ ih

theorem raw_node (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (tag : StructuralCodeTag) (payload : SetTerm bound free)
    (hPayload : membership ℳ (payload.eval env) (omega hℳ)) :
    membership ℳ ((structural_raw_node_code_term tag payload).eval env) (omega hℳ) := by
  change membership ℳ ((PureRoundTwoStage.expansion hℳ).function .successor
    (.cons ((E hℳ).function .godelPairing (.cons ((finite_numeral_term (structural_code_tag tag)).eval env) (.cons (payload.eval env) .nil))) .nil)) _
  rw [PureSyntaxOperator.succ_eq hℳ]
  exact succ_mem hℳ (pairing hℳ (numeral hℳ env _) hPayload)

theorem field_list (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (fields : List (SetTerm bound free))
    (hFields : ∀ field ∈ fields, membership ℳ (field.eval env) (omega hℳ)) :
    membership ℳ ((structural_list_code_term fields).eval env) (omega hℳ) := by
  induction fields with
  | nil => exact raw_node hℳ env .listNil ∅ₘ (numeral hℳ env 0)
  | cons head tail ih =>
    apply raw_node hℳ env .listCons
    exact pairing hℳ (hFields head (by simp)) (ih (fun field hField => hFields field (by simp [hField])))

theorem node (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (tag : StructuralCodeTag) (fields : List (SetTerm bound free))
    (hFields : ∀ field ∈ fields, membership ℳ (field.eval env) (omega hℳ)) :
    membership ℳ ((structural_node_code_term tag fields).eval env) (omega hℳ) :=
  raw_node hℳ env tag _ (field_list hℳ env fields hFields)

theorem unary (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (tag : StructuralCodeTag) (body : SetTerm bound free)
    (hBody : membership ℳ (body.eval env) (omega hℳ)) :
    membership ℳ ((structural_node_code_term tag [body]).eval env) (omega hℳ) :=
  node hℳ env tag [body] (by simpa using hBody)

theorem binary (hℳ : Theory.Models ℳ theory) {bound free : SortContext S}
    (env : Env (E hℳ).model bound free) (tag : StructuralCodeTag) (left right : SetTerm bound free)
    (hLeft : membership ℳ (left.eval env) (omega hℳ)) (hRight : membership ℳ (right.eval env) (omega hℳ)) :
    membership ℳ ((structural_node_code_term tag [left,right]).eval env) (omega hℳ) :=
  node hℳ env tag [left,right] (by simpa using And.intro hLeft hRight)

theorem term_at (hℳ : Theory.Models ℳ theory) (depth code : Carrier ℳ)
    (hCode : (E hℳ).relation .isTermCodeAt (.cons depth (.cons code .nil))) :
    membership ℳ code (omega hℳ) :=
  (PureSyntaxOperator.condition_bounded hℳ .term
    ((PureSyntaxFixedPoint.equation hℳ .term depth (zero hℳ) code).mp hCode)).2.2

theorem formula_at (hℳ : Theory.Models ℳ theory) (depth code : Carrier ℳ)
    (hCode : (E hℳ).relation .isFormulaCodeAt (.cons depth (.cons code .nil))) :
    membership ℳ code (omega hℳ) :=
  (PureSyntaxOperator.condition_bounded hℳ .formula
    ((PureSyntaxFixedPoint.equation hℳ .formula depth (zero hℳ) code).mp hCode)).2.2

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureStructuralCodeBounds
