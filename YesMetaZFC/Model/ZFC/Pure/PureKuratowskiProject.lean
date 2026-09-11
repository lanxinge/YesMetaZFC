import YesMetaZFC.Model.ZFC.Pure.PureKuratowski
import YesMetaZFC.SetTheory.SetConstruction

/-! # 将纯语言 Kuratowski 编码接入集合构造库

约定只包含语法；其模型解释显式接收裸 ZFC 模型证明。由此复用 Project 层的
分离、替换及函数构造，而无需另加有序对存在性或编码正确性假设。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureKuratowskiProject
open PureModel
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
universe x

def code {depth : Nat} (output left right : Project.Term depth) : Project.Formula 1 depth :=
  .existsE <| .existsE <|
    .conj (Project.Formula.isSingleton (.bound 1) left.weaken.weaken)
      (.conj (Project.Formula.isUnorderedPair (.bound 0) left.weaken.weaken right.weaken.weaken)
        (Project.Formula.isUnorderedPair output.weaken.weaken (.bound 1) (.bound 0)))

def convention : Project.OrderedPairConvention where
  code := code
  freeClosed_code := by
    intro depth output left right hOutput hLeft hRight
    simp [code, Project.Formula.isSingleton, Project.Formula.isUnorderedPair,
      _root_.YesMetaZFC.SetTheory.Definitional.Formula.FreeClosed,
      _root_.YesMetaZFC.SetTheory.Definitional.Term.newest,
      Project.Formula.extensionalEq_freeClosed_iff, hOutput, hLeft, hRight]

/-- Project 编码公式与纯语言编码在同一模型对象上逐值一致。 -/
theorem code_correct {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory)
    {depth : Nat} (env : _root_.YesMetaZFC.SetTheory.Env (Project.FirstOrderSemantics.reduct ℳ) depth)
    (output left right : Project.Term depth) :
    Project.Formula.satisfies env (code output left right) ↔
      PureKuratowski.Code ℳ (output.eval env) (left.eval env) (right.eval env) := by
  simp only [code, Project.Formula.isSingleton, Project.Formula.isUnorderedPair,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (project_models hℳ).1, or_self,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.eval_newest,
    _root_.YesMetaZFC.SetTheory.Definitional.Term.eval_weaken,
    Project.Term.eval_bound_zero_push, Project.Term.eval_bound_one_push]
  rfl

/-- 编码实现的四个字段均为已有纯 ZFC 定理，不引入新的模型合同。 -/
def interpretation {ℳ : Structure.{0, 0, 0, x} ℒ} (hℳ : Theory.Models ℳ theory) :
    convention.Interpretation (Project.FirstOrderSemantics.reduct ℳ) where
  Codes := PureKuratowski.Code ℳ
  realizes := code_correct hℳ
  total := PureKuratowski.exists_code hℳ
  unique := PureKuratowski.code_unique hℳ
  injective := PureKuratowski.code_injective

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureKuratowskiProject
