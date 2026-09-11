import YesMetaZFC.Automation.ObjectNumeralSyntax
import YesMetaZFC.Model.ZFC.Pure.PureSourceProjection
import YesMetaZFC.Model.ZFC.Pure.PureSourceCodingInversion

/-! # 当前 AST 数码图的内部构造与反演

输入和输出均为模型对象。零与后继规则直接消费内部集合轨迹；反演只读取根行，
不将轨迹转换成宿主列表，也不对轨迹作外部良基归纳。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceNumeralSyntax
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceNumerals PureSourceInfinity PureSourceCoding
open PureSourceHorn PureSourceHornConstruction PureSourceTraceComposition PureSourceCodingInversion
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def Graph (𝒩 : Structure.{0,0,0,x} signature) (input output : 𝒩.Carrier .set) : Prop :=
  Witness (ObjectHorn.step ObjectNumeralSyntax.rules) (node 𝒩 0 [input, output])

def next (𝒩 : Structure.{0,0,0,x} signature) (output : 𝒩.Carrier .set) : 𝒩.Carrier .set :=
  node 𝒩 2 [numeral 𝒩 ObjectNumeralSyntax.successorSymbol, output]

theorem satisfies {bound free : SetContext} (env : Env 𝒩 bound free)
    (input output : SetTerm bound free) :
    (ObjectNumeralSyntax.condition input output).satisfies env ↔ Graph 𝒩 (input.eval env) (output.eval env) := by
  simp only [ObjectNumeralSyntax.condition, ObjectHorn.condition, ObjectTrace.condition_satisfies,
    node_eval, List.map_cons, List.map_nil]
  rfl

theorem next_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {output : 𝒩.Carrier .set} (hOutput : mem 𝒩 output (w 𝒩)) : mem 𝒩 (next 𝒩 output) (w 𝒩) :=
  node_natural h𝒩 2 (by simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] using! And.intro (numeral_natural h𝒩 ObjectNumeralSyntax.successorSymbol) hOutput)

theorem zero (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) :
    Graph 𝒩 (z 𝒩) (numeral 𝒩 ObjectNumeralSyntax.zeroCode) := by
  have h := rule_intro h𝒩 ObjectNumeralSyntax.rules ObjectNumeralSyntax.zeroRule
    (by simp [ObjectNumeralSyntax.rules]) Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (by intro guard hg; cases hg) (by intro premise hp; cases hp)
  simpa [ObjectNumeralSyntax.zeroRule, expr_node, exprValue, Graph, numeral] using! h

theorem successor (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input output : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) (hOutput : mem 𝒩 output (w 𝒩))
    (hGraph : Graph 𝒩 input output) : Graph 𝒩 (suc 𝒩 input) (next 𝒩 output) := by
  have h := rule_intro h𝒩 ObjectNumeralSyntax.rules ObjectNumeralSyntax.successorRule
    (by simp [ObjectNumeralSyntax.rules]) (fun i : Fin 2 => [input, output][i])
    (PureSourceProjection.values_natural (fields := [input, output]) (by simp [hInput, hOutput]))
    (by decide +kernel) (by intro guard hg; cases hg) (by
      intro premise hp
      obtain rfl := List.mem_singleton.mp hp
      simpa [ObjectNumeralSyntax.successorRule, expr_node, exprValue, Graph] using! hGraph)
  simpa [ObjectNumeralSyntax.successorRule, expr_node, exprValue, Graph, next] using! h

/-- 内部图在标准输入上与既有完整 AST 编码算法一致。 -/
theorem standard_graph (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (number : Nat) :
    Graph 𝒩 (numeral 𝒩 number) (numeral 𝒩 (ObjectNumeralSyntax.value number)) := by
  induction number with
  | zero => exact zero h𝒩
  | succ number ih =>
    have h := successor h𝒩 (numeral_natural h𝒩 number)
      (numeral_natural h𝒩 (ObjectNumeralSyntax.value number)) ih
    have hValue : next 𝒩 (numeral 𝒩 (ObjectNumeralSyntax.value number)) =
        numeral 𝒩 (ObjectNumeralSyntax.value (number + 1)) :=
      node_numerals h𝒩 2 [ObjectNumeralSyntax.successorSymbol, ObjectNumeralSyntax.value number]
    exact hValue ▸ h

/-- 任意接受轨迹的根恰为零行或带有前驱证书的后继行。 -/
theorem cases_graph (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input output : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) (hOutput : mem 𝒩 output (w 𝒩))
    (hGraph : Graph 𝒩 input output) :
    (input = z 𝒩 ∧ output = numeral 𝒩 ObjectNumeralSyntax.zeroCode) ∨
      ∃ predecessor previous, mem 𝒩 predecessor (w 𝒩) ∧ mem 𝒩 previous (w 𝒩) ∧
        input = suc 𝒩 predecessor ∧ output = next 𝒩 previous ∧ Graph 𝒩 predecessor previous := by
  obtain ⟨trace, hTrace, hRoot, hClosed⟩ := hGraph
  obtain ⟨rule, hRule, hStep⟩ := (step_satisfies _ _ _).mp (hClosed _ hRoot)
  obtain ⟨values, hBounds, hHead, _, hPremises⟩ := (rule_satisfies rule _ _).mp hStep
  have hNatural i := member_natural h𝒩
    ((omega_closed h𝒩).2 _ (node_natural h𝒩 0 (by simp [hInput, hOutput]))) (hBounds i)
  simp only [ObjectNumeralSyntax.rules, List.mem_cons, List.not_mem_nil, or_false] at hRule
  rcases hRule with rfl | rfl
  · have hEqual : node 𝒩 0 [input, output] =
        node 𝒩 0 [z 𝒩, numeral 𝒩 ObjectNumeralSyntax.zeroCode] := by
      simpa [ObjectNumeralSyntax.zeroRule, expr_node, exprValue] using! hHead
    have hFields := (node_injective h𝒩 (by simp [hInput, hOutput])
      (by simp [(omega_closed h𝒩).1, numeral_natural h𝒩]) hEqual).2
    simpa only [List.cons.injEq, and_true] using! Or.inl hFields
  · have hEqual : node 𝒩 0 [input, output] =
        node 𝒩 0 [suc 𝒩 (values 0), next 𝒩 (values 1)] := by
      simpa [ObjectNumeralSyntax.successorRule, expr_node, exprValue, next] using! hHead
    have hFields := (node_injective h𝒩 (by simp [hInput, hOutput])
      (by simp [(omega_closed h𝒩).2 _ (hNatural 0), next_natural h𝒩 (hNatural 1)]) hEqual).2
    have hParts : input = suc 𝒩 (values 0) ∧ output = next 𝒩 (values 1) := by
      simpa only [List.cons.injEq, and_true] using hFields
    have hPrevious : mem 𝒩 (node 𝒩 0 [values 0, values 1]) trace := by
      simpa [ObjectNumeralSyntax.successorRule, expr_node, exprValue] using!
        hPremises _ List.mem_cons_self
    exact Or.inr ⟨values 0, values 1, hNatural 0, hNatural 1, hParts.1, hParts.2,
      trace, hTrace, hPrevious, hClosed⟩

theorem successor_ne_zero (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (input : 𝒩.Carrier .set) :
    suc 𝒩 input ≠ z 𝒩 := by
  intro h
  exact empty_spec h𝒩 input (h ▸ (successor_spec h𝒩 input input).mpr (Or.inr rfl))

theorem zero_iff (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {output : 𝒩.Carrier .set} (hOutput : mem 𝒩 output (w 𝒩)) :
    Graph 𝒩 (z 𝒩) output ↔ output = numeral 𝒩 ObjectNumeralSyntax.zeroCode := by
  constructor
  · intro h
    rcases cases_graph h𝒩 (omega_closed h𝒩).1 hOutput h with h | ⟨predecessor, _, _, _, h, _⟩
    · exact h.2
    · exact False.elim (successor_ne_zero h𝒩 predecessor h.symm)
  · rintro rfl
    exact zero h𝒩

theorem successor_iff (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input output : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) (hOutput : mem 𝒩 output (w 𝒩)) :
    Graph 𝒩 (suc 𝒩 input) output ↔
      ∃ previous, mem 𝒩 previous (w 𝒩) ∧ Graph 𝒩 input previous ∧ output = next 𝒩 previous := by
  constructor
  · intro h
    rcases cases_graph h𝒩 ((omega_closed h𝒩).2 input hInput) hOutput h with h | h
    · exact False.elim (successor_ne_zero h𝒩 input h.1)
    · obtain ⟨predecessor, previous, _, hp, hInputEq, hOutputEq, hPrevious⟩ := h
      have hEq := successor_injective h𝒩 hInput hInputEq
      subst predecessor
      exact ⟨previous, hp, hPrevious, hOutputEq⟩
  · rintro ⟨previous, hp, hPrevious, rfl⟩
    exact successor h𝒩 hInput hp hPrevious

theorem agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input output : 𝒩.Carrier .set} (hInput : mem 𝒩 input (w 𝒩)) (hOutput : mem 𝒩 output (w 𝒩)) :
    Graph 𝒩 input output ↔ Graph (canonical h𝒩) input output := by
  let env : Env 𝒩 [] [.set,.set] := templateEnv (.cons input (.cons output .nil))
  let other : Env (canonical h𝒩) [] [.set,.set] := templateEnv (.cons input (.cons output .nil))
  have h := condition_agrees h𝒩 ObjectNumeralSyntax.rules env other
    (IntrinsicQuotation.node 0 [.fvar .here, .fvar (.there .here)]) (by
      simp only [node_eval, List.map_cons, List.map_nil, Term.eval]
      change node 𝒩 0 [input, output] = node (canonical h𝒩) 0 [input, output]
      exact node_agrees h𝒩 0 (by simp [hInput, hOutput]))
  exact (satisfies env (.fvar .here) (.fvar (.there .here))).symm.trans
    (h.trans (satisfies other (.fvar .here) (.fvar (.there .here))))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceNumeralSyntax
