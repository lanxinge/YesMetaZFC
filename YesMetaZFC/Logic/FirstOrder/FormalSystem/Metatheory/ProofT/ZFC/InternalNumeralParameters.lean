import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalNumeralTransform
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourcePointInstantiation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceInstantiationSyntax

/-! # 多参数数码环境与连续点实例化

已经代入的数码跨量词和后续点替换保持不变。自由上下文仍为任意有限长度，
每个槽位可由不同的内部自然数命名。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInstantiation
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInfinity
open PureSourceTransformConstruction
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def NumeralValues (𝒩 : Structure.{0,0,0,x} signature) (values : Nat → 𝒩.Carrier .set) : Prop :=
  ∀ i, mem 𝒩 (values i) (w 𝒩) ∧ ∃ input, mem 𝒩 input (w 𝒩) ∧ PureSourceNumeralSyntax.Graph 𝒩 input (values i)

theorem numeralValues_natural {values : Nat → 𝒩.Carrier .set} (hValues : NumeralValues 𝒩 values) :
    ∀ i, mem 𝒩 (values i) (w 𝒩) := fun i => (hValues i).1

theorem numeralValues_prepend {values : Nat → 𝒩.Carrier .set} (hValues : NumeralValues 𝒩 values)
    {input named : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) (hn : mem 𝒩 named (w 𝒩))
    (hg : PureSourceNumeralSyntax.Graph 𝒩 input named) :
    NumeralValues 𝒩 (ObjectCodeInstantiation.prepend named values) := by
  intro i
  cases i with
  | zero => exact ⟨hn, input, hi, hg⟩
  | succ i => exact hValues i

theorem numeral_wellFormed (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {values : Nat → 𝒩.Carrier .set} (hValues : NumeralValues 𝒩 values)
    {bound free : SetContext} (body : SetFormula bound free) :
    PureSourceFormulaConstruction.FormulaGraph (numeral 𝒩 bound.length) (z 𝒩) (formula 𝒩 values body) :=
  formula_wellFormed h𝒩 (numeralValues_natural hValues) (omega_closed h𝒩).1 (by
    intro depth i _
    obtain ⟨input, hi, hg⟩ := (hValues i).2
    exact PureSourceNumeralSyntax.graph_term h𝒩 (numeral_natural h𝒩 depth) (omega_closed h𝒩).1
      hi (hValues i).1 hg) body

/-- 抽象顶部变量后再以数码点实例化；尾部数码已代入且保持不变。 -/
theorem numeral_point (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (body : SetOpenFormula (.set :: free))
    {values : Nat → 𝒩.Carrier .set} (hValues : NumeralValues 𝒩 values)
    {named : 𝒩.Carrier .set} (hNamed : mem 𝒩 named (w 𝒩)) :
    Graph 3 (numeral 𝒩 2) (z 𝒩) named (formula 𝒩 values body.abstractFreeTop)
      (formula 𝒩 (ObjectCodeInstantiation.prepend named values) body) := by
  have hTarget : ∀ i, mem 𝒩 (ObjectCodeInstantiation.prepend named values i) (w 𝒩) := by
    intro i; cases i with
    | zero => exact hNamed
    | succ i => exact (hValues i).1
  exact formula_mapped_transform h𝒩 (numeralValues_natural hValues) hTarget 2 0 hNamed
    (numeral_lt h𝒩 (by decide))
    (fun {sort} (entry : Variable [] sort) =>
      VariableSubstitution.abstractBound (σ := signature) (free := free) SetSort.set entry)
    (VariableSubstitution.abstractFreeTop (σ := signature) (bound := []) (free := free)) (by
      intro depth sort entry
      have hIndex : entry.index < depth := by
        have h := entry.index_lt_length
        have hLength : (SyntaxTransform.extend [] depth).length = depth := by
          rw [SyntaxTransform.extend_length]; rfl
        rw [hLength] at h
        exact h
      have hCode := ObjectCodeInstantiation.variable_of_encode (node 𝒩) values false entry.index _
        (SyntaxTransform.boundLift_empty
          (fun {sort} (entry : Variable [] sort) =>
            VariableSubstitution.abstractBound (σ := signature) (free := free) SetSort.set entry) depth entry)
      simpa only [PureSourceInstantiation.term, hCode, Bool.false_eq_true, if_false, Nat.zero_add] using!
        bound_identity h𝒩 2 true (by simp [ObjectSyntaxTransform.rules])
          (numeral_natural h𝒩 depth) hNamed (numeral_natural h𝒩 entry.index) (fun _ => numeral_lt h𝒩 hIndex)) (by
      intro depth sort entry
      cases entry with
      | here =>
        have hCode := ObjectCodeInstantiation.variable_of_encode (node 𝒩) values false depth _
          (SyntaxTransform.freeLift_abstract (free := free) depth Variable.here)
        simpa only [PureSourceInstantiation.term, hCode, Bool.false_eq_true, if_false, Nat.zero_add] using!
          bound_point h𝒩 (numeral_natural h𝒩 depth) hNamed
      | there previous =>
        have hCode := ObjectCodeInstantiation.variable_of_encode (node 𝒩) values true previous.index _
          (SyntaxTransform.freeLift_abstract (free := free) depth (.there previous))
        obtain ⟨input, hi, hg⟩ := (hValues previous.index).2
        simpa only [PureSourceInstantiation.term, hCode, if_true, Nat.zero_add] using!
          PureSourceNumeralSyntax.graph_transform h𝒩 (numeral_natural h𝒩 2) (numeral_natural h𝒩 depth)
            hNamed (numeral_lt h𝒩 (by decide)) hi (hValues previous.index).1 hg) 0 body

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInstantiation
