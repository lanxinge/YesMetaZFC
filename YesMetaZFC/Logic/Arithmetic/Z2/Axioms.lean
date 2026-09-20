import YesMetaZFC.Logic.Arithmetic.Z2.Syntax
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-! # Z₂ 的公理模式

数目公理与 Q 共用模板；另加集合外延、集合归纳和完整理解。
理解正文可含任意数集量词及混合参数，见证集合由新槽位引入。
-/
namespace YesMetaZFC.Logic.Arithmetic.Z2
open FirstOrder
set_option autoImplicit false

def number_m (k : Robinson.base_m) : Sentence signature_m :=
  Metatheory.Formula.forall_close
    (Robinson.template_m (σ := signature_m) sort_m.num zero_m succ_m add_m mul_m k)

def extensionality_m : Sentence signature_m :=
  .forallE .set (.forallE .set
    (.imp (.forallE .num (.iff (mem_m (.bvar .here) (.bvar (.there (.there .here))))
      (mem_m (.bvar .here) (.bvar (.there .here)))))
      (.equal (.bvar (.there .here)) (.bvar .here))))

def set_induction_m : Sentence signature_m :=
  (induction_m (mem_m (.fvar .here) (.fvar (.there .here)))).forallFreeTop sort_m.set

def comprehension_m {Δ : SortContext signature_m}
    (φ : Formula signature_m [] (.num :: Δ)) : Formula signature_m [] Δ :=
  ((Formula.iff (mem_m (.fvar .here) (.fvar (.there .here))) (insert_m φ)).forallFreeTop
    sort_m.num).existsFreeTop sort_m.set

/-- 全公式归纳不另列为公理；它是以下模式的推论。 -/
inductive axiom_m : Sentence signature_m → Prop where
  | number (k : Robinson.base_m) : axiom_m (number_m k)
  | extensionality : axiom_m extensionality_m
  | set_induction : axiom_m set_induction_m
  | comprehension {Δ : SortContext signature_m} (φ : Formula signature_m [] (.num :: Δ)) :
      axiom_m (Metatheory.Formula.forall_close (comprehension_m φ))

def theory_m : Theory signature_m := axiom_m

theorem comprehension_derives_m {T : Theory signature_m} (hZ₂ : Theory.Extends T theory_m)
    {Δ : SortContext signature_m} {Γ : Context signature_m Δ}
    (φ : Formula signature_m [] (.num :: Δ)) : Derives T Γ (comprehension_m φ) :=
  Derives.of_provable (Metatheory.Derives.forall_close_open _
    (Derives.theory_axiom (hZ₂ (axiom_m.comprehension φ))))

end YesMetaZFC.Logic.Arithmetic.Z2
