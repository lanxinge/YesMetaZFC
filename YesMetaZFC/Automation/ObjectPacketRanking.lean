import YesMetaZFC.Automation.ObjectHornRanking
import YesMetaZFC.Automation.ObjectPacketGraph

/-! # 传输包解码的阶段与仿射边界公式 -/
namespace YesMetaZFC.Automation.ObjectPacketRanking
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem Logic.FirstOrder.Nonlogical.BasicSetTheory
open ObjectHorn ObjectHornRanking ObjectNumeralReflection
open scoped Logic.FirstOrder.Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def plan : Plan where
  tags := [0, 1, 2, 3, 4, 5]
  width := fun tag => if tag = 4 then 4 else if tag = 5 then 2 else 3
  slot := fun tag => if h : tag = 0 ∨ tag = 1 then ⟨1, by rcases h with rfl | rfl <;> decide⟩
    else ⟨0, by
      by_cases h4 : tag = 4
      · simp [h4]
      · by_cases h5 : tag = 5 <;> simp [h4, h5]⟩
  phase := fun tag => match tag with
    | 0 | 1 => 0
    | 2 => 1
    | 3 | 4 => 2
    | _ => 3

theorem shapes : Shapes plan ObjectPacket.rules := checkShapes_sound _ _ (by decide +kernel)

def affineBounds {bound free : SetContext} (tail : SetTerm bound free) : SetFormula bound free :=
  let t := (tail.weakenFree SetSort.set).weakenFree SetSort.set
  let digit : SetTerm bound (.set :: .set :: free) := .fvar (.there .here)
  let output : SetTerm bound (.set :: .set :: free) := .fvar .here
  forallNatural (forallNatural (ObjectHorn.condition ObjectPacket.rules (ProofT.IntrinsicQuotation.node 0 [digit, t, output]) ⟶ₘ
    ((t ∈ₘ Sₘ(output)) ∧ₘ ((¬ₘ (t ≐ₘ ∅ₘ)) ⟶ₘ (t ∈ₘ output)))))

end YesMetaZFC.Automation.ObjectPacketRanking
