import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalAtomicReflection

/-! # 数码实例反射的逻辑闭包

双向反射按固定公式骨架组合；四个二元联结词共用经内核检查的真值规则。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureSourceInstantiation ReducedProofCodeSemantics InternalNumeralProof
open _root_.YesMetaZFC.Automation
set_option autoImplicit false
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
universe x
variable {𝒩 : Structure.{0,0,0,x} signature} {free : SetContext}

theorem reflection_choice {env : Env 𝒩 [] free} {values : Nat → 𝒩.Carrier .set}
    {body : SetOpenFormula free} (h : FormulaReflects env values body) :
    ∃ positive, (polarity positive body).satisfies env ∧ ProvableCode 𝒩 (formula 𝒩 values (polarity positive body)) := by
  classical
  by_cases ht : body.satisfies env
  · exact ⟨true, ht, h.1 ht⟩
  · exact ⟨false, ht, h.2 ht⟩

theorem reflects_of_signed {env : Env 𝒩 [] free} {values : Nat → 𝒩.Carrier .set}
    {body : SetOpenFormula free} (positive : Bool)
    (ht : (polarity positive body).satisfies env)
    (hp : ProvableCode 𝒩 (formula 𝒩 values (polarity positive body))) : FormulaReflects env values body := by
  cases positive with
  | false => exact ⟨fun h => False.elim (ht h), fun _ => hp⟩
  | true => exact ⟨fun _ => hp, fun h => False.elim (h ht)⟩

theorem reflection_rule (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {left right : SetOpenFormula free} (hRule : Derives intrinsic_zfc_theory [] (.imp left right))
    (hp : ProvableCode 𝒩 (formula 𝒩 values left)) : ProvableCode 𝒩 (formula 𝒩 values right) :=
  values_modus_ponens (values := values) h𝒩 left right hv hp (specialize_values h𝒩 _ hRule hv)

theorem truth_reflection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values) :
    FormulaReflects env values .truth :=
  reflects_of_signed true True.intro (specialize_values h𝒩 _ (source_complete (.truth : SetOpenFormula free) (fun _ _ _ => True.intro)) hv)

theorem falsum_reflection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values) :
    FormulaReflects env values .falsum :=
  reflects_of_signed false (fun h => h) (specialize_values h𝒩 _ (source_complete (.neg (.falsum : SetOpenFormula free)) (fun _ _ _ h => h)) hv)

theorem negation_reflection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {body : SetOpenFormula free} (h : FormulaReflects env values body) : FormulaReflects env values (.neg body) := by
  classical
  constructor
  · exact h.2
  · intro hn
    exact reflection_rule h𝒩 values hv (source_complete (.imp body (.neg (.neg body))) (fun _ _ _ hp hn => hn hp))
      (h.1 (Classical.byContradiction hn))

inductive BooleanConnective where
  | conj | disj | imp | iff

def BooleanConnective.apply (operation : BooleanConnective) (left right : SetOpenFormula free) : SetOpenFormula free :=
  match operation with
  | .conj => .conj left right
  | .disj => .disj left right
  | .imp => .imp left right
  | .iff => .iff left right

def BooleanConnective.value (operation : BooleanConnective) (left right : Bool) : Bool :=
  match operation with
  | .conj => left && right
  | .disj => left || right
  | .imp => !left || right
  | .iff => left == right

theorem boolean_signed_satisfies (operation : BooleanConnective) (first second : Bool)
    (left right : SetOpenFormula free) (env : Env 𝒩 [] free) :
    (polarity first left).satisfies env → (polarity second right).satisfies env →
      (polarity (operation.value first second) (operation.apply left right)).satisfies env := by
  cases operation <;> cases first <;> cases second <;>
    simp [BooleanConnective.value, BooleanConnective.apply, polarity, Formula.satisfies]
  all_goals intro hl hr; simp_all

theorem boolean_rule_derives (operation : BooleanConnective) (first second : Bool)
    (left right : SetOpenFormula free) :
    Derives intrinsic_zfc_theory [] (.imp (polarity first left) (.imp (polarity second right)
      (polarity (operation.value first second) (operation.apply left right)))) :=
  source_complete _ (fun _ _ env => boolean_signed_satisfies operation first second left right env)

/-- 合取、析取、蕴含与双条件都保持正负反射。 -/
theorem boolean_reflection (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (operation : BooleanConnective) {left right : SetOpenFormula free}
    (hl : FormulaReflects env values left) (hr : FormulaReflects env values right) :
    FormulaReflects env values (operation.apply left right) := by
  obtain ⟨first, hFirst, hp⟩ := reflection_choice hl
  obtain ⟨second, hSecond, hq⟩ := reflection_choice hr
  apply reflects_of_signed (operation.value first second)
    (boolean_signed_satisfies operation first second left right env hFirst hSecond)
  exact values_modus_ponens (values := values) h𝒩 _ _ hv hq
    (reflection_rule h𝒩 values hv (boolean_rule_derives operation first second left right) hp)

/-- 已证明的逻辑等价同时传输正负反射，保留目标公式原来的 AST。 -/
theorem reflection_of_iff (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    {left right : SetOpenFormula free} (hIff : Derives intrinsic_zfc_theory [] (.iff left right))
    (hLeft : FormulaReflects env values left) : FormulaReflects env values right := by
  have hs := hIff.sound h𝒩 env (by intro φ h; cases h)
  constructor
  · intro hr
    exact reflection_rule h𝒩 values hv (source_complete (.imp left right) (by
      intro 𝒩 h𝒩 env
      exact (hIff.sound h𝒩 env (by intro φ h; cases h)).mp)) (hLeft.1 (hs.mpr hr))
  · intro hr
    exact reflection_rule h𝒩 values hv (source_complete (.imp (.neg left) (.neg right)) (by
      intro 𝒩 h𝒩 env hn ht
      exact hn ((hIff.sound h𝒩 env (by intro φ h; cases h)).mpr ht)))
      (hLeft.2 (fun hl => hr (hs.mp hl)))

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
