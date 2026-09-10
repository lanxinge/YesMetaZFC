import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralQuotation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceTransformConstruction

/-! # 非标准数码在语法变换下保持不变

性质使用实际变换轨迹公式。模式、深度和参数均可为内部自然数；
这里只要求模式小于四，不把数码解码为宿主项。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceNumeralSyntax
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity PureSourceCoding
open PureSourceHornConstruction
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

theorem zero_transform (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {mode depth parameter : 𝒩.Carrier .set} (hm : mem 𝒩 mode (w 𝒩))
    (hd : mem 𝒩 depth (w 𝒩)) (hp : mem 𝒩 parameter (w 𝒩)) (hSmall : mem 𝒩 mode (numeral 𝒩 4)) :
    PureSourceTransformConstruction.Graph 1 mode depth parameter
      (numeral 𝒩 ObjectNumeralSyntax.zeroCode) (numeral 𝒩 ObjectNumeralSyntax.zeroCode) := by
  have h := PureSourceTransformConstruction.application h𝒩 1 FunctionSymbol.emptySet.ctorIdx (Or.inl rfl)
    hm hd hp [] [] (by simp) (by simp) (PureSourceTransformConstruction.nil_arguments h𝒩 hm hd hp hSmall)
  have hSymbol : node 𝒩 FunctionSymbol.emptySet.ctorIdx [] =
      numeral 𝒩 (ObjectHorn.nodeValue FunctionSymbol.emptySet.ctorIdx []) := node_numerals h𝒩 _ []
  rw [hSymbol] at h
  have hCode := node_numerals h𝒩 2 [ObjectHorn.nodeValue FunctionSymbol.emptySet.ctorIdx []]
  change node 𝒩 2 [numeral 𝒩 (ObjectHorn.nodeValue FunctionSymbol.emptySet.ctorIdx [])] =
    numeral 𝒩 ObjectNumeralSyntax.zeroCode at hCode
  rwa [hCode] at h

theorem successor_transform (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {mode depth parameter output : 𝒩.Carrier .set} (hm : mem 𝒩 mode (w 𝒩))
    (hd : mem 𝒩 depth (w 𝒩)) (hp : mem 𝒩 parameter (w 𝒩)) (ho : mem 𝒩 output (w 𝒩))
    (hSmall : mem 𝒩 mode (numeral 𝒩 4))
    (hTransform : PureSourceTransformConstruction.Graph 1 mode depth parameter output output) :
    PureSourceTransformConstruction.Graph 1 mode depth parameter (next 𝒩 output) (next 𝒩 output) := by
  have hNil := fields_natural h𝒩 (fields := []) (by simp)
  have hArgs := PureSourceTransformConstruction.cons_arguments h𝒩 hm hd hp ho hNil ho hNil hTransform
    (PureSourceTransformConstruction.nil_arguments h𝒩 hm hd hp hSmall)
  have h := PureSourceTransformConstruction.application h𝒩 1 FunctionSymbol.successor.ctorIdx (Or.inl rfl)
    hm hd hp [output] [output] (by simp [ho]) (by simp [ho]) hArgs
  have hSymbol : node 𝒩 FunctionSymbol.successor.ctorIdx [] = numeral 𝒩 ObjectNumeralSyntax.successorSymbol :=
    node_numerals h𝒩 _ []
  rwa [hSymbol] at h

theorem invariantAt_satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (input mode depth parameter : SetTerm bound free) :
    (ObjectNumeralSyntax.invariantAtCondition input mode depth parameter).satisfies env ↔
      ∀ output, mem 𝒩 output (w 𝒩) → Graph 𝒩 (input.eval env) output →
        PureSourceTransformConstruction.Graph 1 (mode.eval env) (depth.eval env) (parameter.eval env) output output := by
  simp only [ObjectNumeralSyntax.invariantAtCondition, Formula.satisfies_forallFreeTop, Formula.satisfies,
    satisfies, ObjectHorn.condition, ObjectTrace.condition_satisfies, node_eval,
    List.map_cons, List.map_nil, Term.eval_weakenFree, and_imp]
  rfl

/-- 此归纳对任意内部深度及替换参数成立，供连续多参数特化使用。 -/
theorem graph_transform (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {mode depth parameter input output : 𝒩.Carrier .set}
    (hm : mem 𝒩 mode (w 𝒩)) (hd : mem 𝒩 depth (w 𝒩)) (hp : mem 𝒩 parameter (w 𝒩))
    (hSmall : mem 𝒩 mode (numeral 𝒩 4)) (hi : mem 𝒩 input (w 𝒩)) (ho : mem 𝒩 output (w 𝒩))
    (hGraph : Graph 𝒩 input output) : PureSourceTransformConstruction.Graph 1 mode depth parameter output output := by
  have hAll := PureSourceInduction.induction h𝒩
    (ObjectNumeralSyntax.invariantAtCondition (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))))
    (.cons mode (.cons depth (.cons parameter .nil))) (by
      intro input hi
      rw [invariantAt_satisfies, invariantAt_satisfies]
      apply forall_congr'
      intro output
      change (mem 𝒩 output (w 𝒩) → _) ↔ (mem 𝒩 output (w (canonical h𝒩)) → _)
      rw [← omega_agrees h𝒩]
      apply imp_congr_right
      intro ho
      exact imp_congr (agrees h𝒩 hi ho) (PureSourceTransformConstruction.graph_agrees h𝒩 1 hm hd hp ho ho)) (by
      apply (invariantAt_satisfies _ _ _ _ _).mpr
      intro output ho hg
      rw [(zero_iff h𝒩 ho).mp hg]
      exact zero_transform h𝒩 hm hd hp hSmall) (by
      intro input hi hProperty
      apply (invariantAt_satisfies _ _ _ _ _).mpr
      intro output ho hg
      obtain ⟨previous, hv, hPrevious, rfl⟩ := (successor_iff h𝒩 hi ho).mp hg
      exact successor_transform h𝒩 hm hd hp hv hSmall
        ((invariantAt_satisfies _ _ _ _ _).mp hProperty previous hv hPrevious))
  exact (invariantAt_satisfies _ _ _ _ _).mp (hAll input hi) output ho hGraph

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceNumeralSyntax
