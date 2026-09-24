import YesMetaZFC.Logic.Arithmetic.Syntax
import YesMetaZFC.Logic.Arithmetic.Robinson
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-! # Robinson 算术 Q

七条公理先给开放模板，再用公共全称闭包封闭。模板的参数列表就是槽位合同，
实例化共用 `forall_close_elim`，不按一元／二元复制 binder 消去证明。
-/
namespace YesMetaZFC.Logic.Arithmetic.Q
open FirstOrder
set_option autoImplicit false

abbrev parameters_m : Robinson.base_m → SortContext signature_m :=
  Robinson.parameters_m sort_m.num

/-- 参数槽依次为 x、y；全称闭包按上游的规范次序生成。 -/
def template_m (k : Robinson.base_m) : Formula signature_m [] (parameters_m k) :=
  Robinson.template_m (σ := signature_m) sort_m.num zero_m succ_m add_m mul_m k

def sentence_m (k : Robinson.base_m) : Sentence signature_m :=
  Metatheory.Formula.forall_close (template_m k)

/-- 对象理论的公理谓词；不是 Lean 的新公理。 -/
inductive axiom_m : Sentence signature_m → Prop where
  | base (k : Robinson.base_m) : axiom_m (sentence_m k)

def theory_m : Theory signature_m := axiom_m

/-- 任意扩张 Q 的理论都可按项替换实例化其公理，保留全部局部假设。 -/
theorem derives_m {T : Theory signature_m} (hQ : Theory.Extends T theory_m)
    {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (k : Robinson.base_m) (ρ : VariableSubstitution signature_m (parameters_m k) [] Δ) :
    Derives T Γ ((template_m k).substituteFree ρ) :=
  Metatheory.Derives.forall_close_elim (template_m k) ρ
    (Derives.theory_axiom (hQ (.base k)))

end YesMetaZFC.Logic.Arithmetic.Q
