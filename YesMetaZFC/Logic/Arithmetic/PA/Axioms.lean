import YesMetaZFC.Logic.Arithmetic.Q.Axioms

/-! # Peano 算术与带参数归纳模式

PA 是 Q 加全体算术公式的归纳闭包。归纳正文只来自实际对象公式，
允许任意有限数目参数；不以宿主谓词或标准模型真值代替公理模式。
-/
namespace YesMetaZFC.Logic.Arithmetic.PA
open FirstOrder
set_option autoImplicit false

/-- 只把首个自由变量替为其后继，其他参数不动。 -/
def next_m {Δ : SortContext signature_m} :
    VariableSubstitution signature_m (.num :: Δ) [] (.num :: Δ) :=
  VariableSubstitution.cons (succ_m (.fvar .here))
    (VariableSubstitution.of_renaming (VariableRenaming.weaken sort_m.num))

def induction_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) : Formula signature_m [] Δ :=
  .imp (.conj (φ.instantiateFreeTop zero_m)
    ((Formula.imp φ (φ.substituteFree next_m)).forallFreeTop sort_m.num))
    (φ.forallFreeTop sort_m.num)

inductive axiom_m : Sentence signature_m → Prop where
  | robinson {φ : Sentence signature_m} (h : Q.theory_m φ) : axiom_m φ
  | induction {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ)) :
      axiom_m (Metatheory.Formula.forall_close (induction_m φ))

def theory_m : Theory signature_m := axiom_m

theorem extends_q_m : Theory.Extends theory_m Q.theory_m := axiom_m.robinson

/-- 将归纳公理的参数闭包重新打开，不引入额外归纳原则。 -/
theorem induction_derives_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) : Derives theory_m [] (induction_m φ) :=
  Metatheory.Derives.forall_close_open (induction_m φ)
    (Derives.theory_axiom (axiom_m.induction φ))

/-- 局部假设一起弱化，故归纳步的新变量不会捕获原上下文中的参数。 -/
theorem induction_rule_m {T : Theory signature_m} (hPA : Theory.Extends T theory_m)
    {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    {φ : Formula signature_m [] (.num :: Δ)}
    (h₀ : Derives T Γ (φ.instantiateFreeTop zero_m))
    (h₁ : Derives T (FreshVariable.extendContext sort_m.num Γ)
      (.imp φ (φ.substituteFree next_m))) :
    Derives T Γ (φ.forallFreeTop sort_m.num) :=
  Derives.imp_elim
    (Derives.of_provable (Derives.theory_weaken hPA (induction_derives_m φ)))
    (Derives.conj_intro h₀ (Derives.forall_intro h₁))

end YesMetaZFC.Logic.Arithmetic.PA
