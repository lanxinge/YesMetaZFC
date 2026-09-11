import YesMetaZFC.Model.ZFC.Pure.PureArithmeticBounds

/-! # 内部自然数算术的消去律与平方次序

复用已由模型内部归纳证明的序数算术，不将内部自然数解释为宿主 Nat。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureArithmeticOrder
open PureModel PureNaturalInduction PureArithmeticStage PureArithmeticSpecifications PureArithmeticBounds
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false
set_option maxRecDepth 32768
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature
universe x
variable {ℳ : Structure.{0,0,0,x} ℒ}

theorem lt_irrefl (hℳ : Theory.Models ℳ theory) {a : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) : ¬ membership ℳ a a := by
  intro h
  exact (ordinal hℳ ha).wellOrder.linear.irrefl a h h

theorem add_comm (hℳ : Theory.Models ℳ theory) {a b : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ)) :
    add hℳ a b = add hℳ b a :=
  _root_.YesMetaZFC.SetTheory.Structure.natural_add_comm (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) (omega_project hℳ) ha hb
    (arithmetic_correct hℳ .addition ha hb) (arithmetic_correct hℳ .addition hb ha)

theorem add_succ (hℳ : Theory.Models ℳ theory) {a b : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ)) :
    add hℳ a (succ hℳ b) = succ hℳ (add hℳ a b) :=
  ordinal_step_value hℳ .addition ha hb
    (arithmetic_correct hℳ .addition ha hb)
    (arithmetic_correct hℳ .addition ha (succ_mem hℳ hb))

theorem add_cancel (hℳ : Theory.Models ℳ theory) {a b c : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ))
    (hc : membership ℳ c (omega hℳ)) (h : add hℳ a b = add hℳ a c) : b = c := by
  apply _root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_right_injective (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) (ordinal hℳ ha) (ordinal hℳ hb) (ordinal hℳ hc)
    (arithmetic_correct hℳ .addition ha hb)
  change PureOrdinalArithmetic.OrdinalValue hℳ .addition (add hℳ a b) a c
  rw [h]
  exact arithmetic_correct hℳ .addition ha hc

theorem add_lt (hℳ : Theory.Models ℳ theory) {a b c : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ))
    (hc : membership ℳ c (omega hℳ)) (h : membership ℳ b c) :
    membership ℳ (add hℳ a b) (add hℳ a c) :=
  (_root_.YesMetaZFC.SetTheory.ZF.ordinalAddition_values_mem_iff (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) (ordinal hℳ ha) (ordinal hℳ hb) (ordinal hℳ hc)
    (arithmetic_correct hℳ .addition ha hb) (arithmetic_correct hℳ .addition ha hc)).mpr h

theorem add_le (hℳ : Theory.Models ℳ theory) {a b c : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ))
    (hc : membership ℳ c (omega hℳ)) (h : Le b c) : Le (add hℳ a b) (add hℳ a c) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (add_lt hℳ ha hb hc h)

theorem mul_comm (hℳ : Theory.Models ℳ theory) {a b : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ)) :
    mul hℳ a b = mul hℳ b a :=
  _root_.YesMetaZFC.SetTheory.Structure.natural_mul_comm (project_modelsZF hℳ)
    (PureKuratowskiProject.interpretation hℳ) (omega_project hℳ) ha hb
    (arithmetic_correct hℳ .multiplication ha hb) (arithmetic_correct hℳ .multiplication hb ha)

theorem mul_succ (hℳ : Theory.Models ℳ theory) {a b : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ)) :
    mul hℳ a (succ hℳ b) = add hℳ (mul hℳ a b) a :=
  ordinal_step_value hℳ .multiplication ha hb
    (arithmetic_correct hℳ .multiplication ha hb)
    (arithmetic_correct hℳ .multiplication ha (succ_mem hℳ hb))

theorem mul_le (hℳ : Theory.Models ℳ theory) {a b c : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ))
    (hc : membership ℳ c (omega hℳ)) (h : Le b c) : Le (mul hℳ a b) (mul hℳ a c) := by
  classical
  rcases h with rfl | h
  · exact Or.inl rfl
  by_cases hPositive : ∃ point, membership ℳ point a
  · exact Or.inr (_root_.YesMetaZFC.SetTheory.ZF.ordinalMultiplication_isIncreasingOnOrdinals
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) (ordinal hℳ ha) hPositive
      b c (ordinal hℳ hb) (ordinal hℳ hc) h _ _
      (arithmetic_correct hℳ .multiplication ha hb) (arithmetic_correct hℳ .multiplication ha hc))
  · have hEmpty : ∀ point, ¬ membership ℳ point a := fun point hp => hPositive ⟨point,hp⟩
    have hFirst := _root_.YesMetaZFC.SetTheory.ZF.ordinalMultiplication_empty_left
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) hEmpty
      b (ordinal hℳ hb) _ (arithmetic_correct hℳ .multiplication ha hb)
    have hSecond := _root_.YesMetaZFC.SetTheory.ZF.ordinalMultiplication_empty_left
      (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) hEmpty
      c (ordinal hℳ hc) _ (arithmetic_correct hℳ .multiplication ha hc)
    exact Or.inl (extensionality hℳ _ _ (fun point => iff_of_false (hFirst point) (hSecond point)))

theorem square_value (hℳ : Theory.Models ℳ theory) {a : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) :
    power hℳ a (PureGodelPairing.two hℳ) = mul hℳ a a := by
  have hz := zero_mem hℳ
  have ho := succ_mem hℳ hz
  have hSeed := ordinal_zero_value hℳ .exponentiation ha (arithmetic_correct hℳ .exponentiation ha hz)
  have hOne := ordinal_step_value hℳ .exponentiation ha hz
    (arithmetic_correct hℳ .exponentiation ha hz) (arithmetic_correct hℳ .exponentiation ha ho)
  change power hℳ a (zero hℳ) = succ hℳ (zero hℳ) at hSeed
  change power hℳ a (succ hℳ (zero hℳ)) = mul hℳ (power hℳ a (zero hℳ)) a at hOne
  rw [hSeed, mul_comm hℳ ho ha] at hOne
  have hIdentity := _root_.YesMetaZFC.SetTheory.ZF.ordinalMultiplication_one_right
    (project_modelsZF hℳ) (PureKuratowskiProject.interpretation hℳ) (ordinal hℳ ha)
    ⟨zero hℳ, zero_spec hℳ, succ_project hℳ _⟩ (arithmetic_correct hℳ .multiplication ha ho)
  have hTwo := ordinal_step_value hℳ .exponentiation ha ho
    (arithmetic_correct hℳ .exponentiation ha ho)
    (arithmetic_correct hℳ .exponentiation ha (succ_mem hℳ ho))
  change power hℳ a (PureGodelPairing.two hℳ) = mul hℳ (power hℳ a (succ hℳ (zero hℳ))) a at hTwo
  exact hTwo.trans (congrArg (fun value => mul hℳ value a) (hOne.trans hIdentity))

theorem square_succ (hℳ : Theory.Models ℳ theory) {a : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) :
    mul hℳ (succ hℳ a) (succ hℳ a) = succ hℳ (add hℳ (add hℳ (mul hℳ a a) a) a) := by
  rw [mul_succ hℳ (succ_mem hℳ ha) ha, mul_comm hℳ (succ_mem hℳ ha) ha,
    mul_succ hℳ ha ha,
    add_succ hℳ (arithmetic_closed hℳ .addition (arithmetic_closed hℳ .multiplication ha ha) ha) ha]

theorem square_le (hℳ : Theory.Models ℳ theory) {a b : Carrier ℳ}
    (ha : membership ℳ a (omega hℳ)) (hb : membership ℳ b (omega hℳ)) (h : Le a b) :
    Le (mul hℳ a a) (mul hℳ b b) := by
  apply le_trans hℳ (arithmetic_closed hℳ .multiplication hb hb) (mul_le hℳ ha ha hb h)
  rw [mul_comm hℳ ha hb]
  exact mul_le hℳ hb ha hb h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureArithmeticOrder
