import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectSyntaxTransformSpec
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornLocal
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxTransformInstances

/-! # 局部内核变换的具体对象接口

所有候选输出都是任意自然数。四个实例共用同一公式，参数分别固定模式及替换项或表码。
-/
namespace YesMetaZFC.Automation.ObjectSyntaxTransform
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT IntrinsicQuotation QuineEncoding ObjectHorn
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

theorem checked_weakenFree {free : SetContext} (input : SetOpenFormula free) (output : Nat) :
    checked 0 0 0 (treeValue (SyntaxEncode.formula input)) output = true ↔
      treeValue (SyntaxEncode.formula (input.weakenFree SetSort.set)) = output := by
  rw [checked_iff]
  simp only [decode_treeValue, Option.bind_some, SyntaxTransform.weakenFree_encode, Option.some.injEq]

theorem checked_abstractTop {free : SetContext} (input : SetOpenFormula (SetSort.set :: free)) (output : Nat) :
    checked 1 0 0 (treeValue (SyntaxEncode.formula input)) output = true ↔
      treeValue (SyntaxEncode.formula input.abstractFreeTop) = output := by
  rw [checked_iff]
  simp only [decode_treeValue, Option.bind_some, SyntaxTransform.abstractTop_encode, Option.some.injEq]

theorem checked_instantiateTop {free : SetContext} (input : SetFormula [SetSort.set] free)
    (point : SetOpenTerm free) (output : Nat) :
    checked 2 0 (treeValue (SyntaxEncode.term point)) (treeValue (SyntaxEncode.formula input)) output = true ↔
      treeValue (SyntaxEncode.formula (input.instantiateTop point)) = output := by
  rw [checked_iff]
  simp only [decode_treeValue, Option.bind_some, SyntaxTransform.instantiateTop_encode, Option.some.injEq]

theorem checked_substituteFree {source free : SetContext} (input : SetOpenFormula source)
    (subst : VariableSubstitution signature source [] free) (output : Nat) :
    checked 3 0 (listValue ((SyntaxEncode.argumentsList (SyntaxEncode.substitutionArguments source subst)).map treeValue))
      (treeValue (SyntaxEncode.formula input)) output = true ↔
      treeValue (SyntaxEncode.formula (input.substituteFree subst)) = output := by
  rw [checked_iff]
  simp only [decode_treeValue, Option.bind_some, SyntaxTransform.substituteFree_encode, Option.some.injEq]

/-- 独立计算成功后生成普通对象推导。 -/
theorem positive_of_run {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ) (mode depth parameter input output : Nat)
    (h : (decodeTree input).bind (SyntaxTransform.formula mode depth parameter) = some output) :
    Derives T [] (condition (numₘ(mode)) (numₘ(depth)) (numₘ(parameter)) (numₘ(input)) (numₘ(output) : Code)) :=
  positive C S hPower hInfinity _ _ _ _ _ ((checked_iff _ _ _ _ _).mpr h)

/-- 失败输入或错误输出均生成同一对象公式的否定。 -/
theorem negative_of_run_ne {T : SetTheory} (C : CertificateCore T) (A : ArithmeticSupport T)
    (mode depth parameter input output : Nat)
    (h : (decodeTree input).bind (SyntaxTransform.formula mode depth parameter) ≠ some output) :
    Derives T [] (¬ₘ condition (numₘ(mode)) (numₘ(depth)) (numₘ(parameter)) (numₘ(input)) (numₘ(output) : Code)) :=
  negative C A _ _ _ _ _ ((checked_false_iff _ _ _ _ _).mpr h)

/-- 一元查询封装可直接用于有限局部模式。它只表示语法变换，不冒充整棵证明树测试。 -/
def localTest {T : SetTheory} (C : CertificateCore T) (S : FiniteSequenceGraphSupport T)
    (hPower : ∀ {φ}, power_set_operator_theory φ → T φ)
    (hInfinity : ∀ {φ}, infinity_theory φ → T φ) : ObjectCheckedTrace.LocalTest T :=
  ObjectHorn.localTest C S hPower hInfinity rules rank descending

end YesMetaZFC.Automation.ObjectSyntaxTransform
