import YesMetaZFC.Model.Interpretation.ModelClosure
import YesMetaZFC.Model.ZFC.Pure.PureFinalTransfer
import YesMetaZFC.Model.ZFC.Pure.PureArithmeticBounds

/-! # 最终纯扩张中的六条原算术增长公理

先在抽象源模型读取原实例，再用逐图唯一性连接实际算术值；最后关闭自由变量。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalArithmetic
open PureModel Nonlogical.BasicSetTheory PureFinalTransfer
open _root_.YesMetaZFC.Automation.RelationalTranslation
open _root_.YesMetaZFC.Automation.ModelClosure
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x
abbrev S := Nonlogical.BasicSetTheory.signature
abbrev s := SetSort.set
variable {ℳ : Structure.{0,0,0,x} ℒ}

abbrev mem (𝒩 : Structure.{0,0,0,x} S) (left right : 𝒩.Carrier s) :=
  𝒩.relInterp .membership (.cons left (.cons right .nil))
abbrev z (𝒩 : Structure.{0,0,0,x} S) := 𝒩.funcInterp .emptySet .nil
abbrev w (𝒩 : Structure.{0,0,0,x} S) := 𝒩.funcInterp .omega .nil
abbrev suc (𝒩 : Structure.{0,0,0,x} S) (a : 𝒩.Carrier s) := 𝒩.funcInterp .successor (.cons a .nil)
abbrev sum (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) := 𝒩.funcInterp .naturalAddition (.cons a (.cons b .nil))
abbrev product (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) := 𝒩.funcInterp .naturalMultiplication (.cons a (.cons b .nil))
abbrev power (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) := 𝒩.funcInterp .naturalExponentiation (.cons a (.cons b .nil))
abbrev pair (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) := 𝒩.funcInterp .godelPairing (.cons a (.cons b .nil))

theorem addition_upper_correct (𝒩 : Structure.{0,0,0,x} S) (a b c : 𝒩.Carrier s) :
    (natural_addition_upper_bound_instance (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons c (.cons b (.cons a .nil))) : Env 𝒩 [] [s,s,s]) ↔
      ((mem 𝒩 a (w 𝒩) ∧ mem 𝒩 b (w 𝒩) ∧ mem 𝒩 c (w 𝒩) ∧ (mem 𝒩 a (suc 𝒩 b) ∨ mem 𝒩 a (suc 𝒩 c))) → mem 𝒩 a (suc 𝒩 (sum 𝒩 b c))) := by rfl

theorem positive_addition_correct (𝒩 : Structure.{0,0,0,x} S) (a b c : 𝒩.Carrier s) :
    (natural_positive_left_addition_strict_bound_instance (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons c (.cons b (.cons a .nil))) : Env 𝒩 [] [s,s,s]) ↔
      ((mem 𝒩 a (w 𝒩) ∧ mem 𝒩 b (w 𝒩) ∧ mem 𝒩 c (w 𝒩) ∧ mem 𝒩 (z 𝒩) b ∧ mem 𝒩 a (suc 𝒩 c)) → mem 𝒩 a (sum 𝒩 b c)) := by rfl

theorem transitivity_correct (𝒩 : Structure.{0,0,0,x} S) (a b c : 𝒩.Carrier s) :
    (natural_le_lt_transitivity_instance (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons c (.cons b (.cons a .nil))) : Env 𝒩 [] [s,s,s]) ↔
      ((mem 𝒩 b (w 𝒩) ∧ mem 𝒩 c (w 𝒩) ∧ mem 𝒩 a (suc 𝒩 b) ∧ mem 𝒩 b c) → mem 𝒩 a c) := by rfl

theorem pairing_correct (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) :
    (natural_godel_pairing_coordinate_bound_instance (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons b (.cons a .nil)) : Env 𝒩 [] [s,s]) ↔
      ((mem 𝒩 a (w 𝒩) ∧ mem 𝒩 b (w 𝒩)) → (mem 𝒩 a (suc 𝒩 (pair 𝒩 a b)) ∧ mem 𝒩 b (suc 𝒩 (pair 𝒩 a b)))) := by rfl

theorem exponent_correct (𝒩 : Structure.{0,0,0,x} S) (a b : 𝒩.Carrier s) :
    (natural_exponentiation_index_bound_instance (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons b (.cons a .nil)) : Env 𝒩 [] [s,s]) ↔
      ((mem 𝒩 a (w 𝒩) ∧ mem 𝒩 b (w 𝒩) ∧ mem 𝒩 (suc 𝒩 (z 𝒩)) a) → mem 𝒩 b (power 𝒩 a (suc 𝒩 b))) := by rfl

theorem exponent_product_correct (𝒩 : Structure.{0,0,0,x} S) (a b c d : 𝒩.Carrier s) :
    (natural_exponent_product_index_bound_instance (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons d (.cons c (.cons b (.cons a .nil)))) : Env 𝒩 [] [s,s,s,s]) ↔
      ((mem 𝒩 a (w 𝒩) ∧ mem 𝒩 b (w 𝒩) ∧ mem 𝒩 (suc 𝒩 (z 𝒩)) a ∧ mem 𝒩 c (w 𝒩) ∧ mem 𝒩 d (w 𝒩) ∧ mem 𝒩 (suc 𝒩 (z 𝒩)) c) → (mem 𝒩 b (product 𝒩 (power 𝒩 a (suc 𝒩 b)) (power 𝒩 c (suc 𝒩 d))) ∧ mem 𝒩 d (product 𝒩 (power 𝒩 a (suc 𝒩 b)) (power 𝒩 c (suc 𝒩 d))))) := by rfl

@[simp] theorem mem_final (hℳ : Theory.Models ℳ theory) (a b : Carrier ℳ) :
    mem (E hℳ).model a b ↔ membership ℳ a b := Iff.rfl
@[simp] theorem zero_final (hℳ : Theory.Models ℳ theory) :
    z (E hℳ).model = PureNaturalInduction.zero hℳ := functionFromDifference hℳ _ rfl _
@[simp] theorem omega_final (hℳ : Theory.Models ℳ theory) :
    w (E hℳ).model = PureNaturalInduction.omega hℳ := functionFromDifference hℳ _ rfl _
@[simp] theorem succ_final (hℳ : Theory.Models ℳ theory) (a : Carrier ℳ) :
    suc (E hℳ).model a = PureNaturalInduction.succ hℳ a := functionFromDifference hℳ _ rfl _
@[simp] theorem add_final (hℳ : Theory.Models ℳ theory) (a b : Carrier ℳ) :
    sum (E hℳ).model a b = PureArithmeticBounds.add hℳ a b := functionFromArithmetic hℳ _ rfl _
@[simp] theorem mul_final (hℳ : Theory.Models ℳ theory) (a b : Carrier ℳ) :
    product (E hℳ).model a b = PureArithmeticBounds.mul hℳ a b := functionFromArithmetic hℳ _ rfl _
@[simp] theorem pow_final (hℳ : Theory.Models ℳ theory) (a b : Carrier ℳ) :
    power (E hℳ).model a b = PureArithmeticBounds.power hℳ a b := functionFromArithmetic hℳ _ rfl _

theorem addition_upper_instance (hℳ : Theory.Models ℳ theory) (a b c : Carrier ℳ) :
    (natural_addition_upper_bound_instance (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons c (.cons b (.cons a .nil))) : Env (E hℳ).model [] [s,s,s]) := by
  apply (addition_upper_correct (E hℳ).model a b c).mpr
  simp only [mem_final, omega_final, succ_final, add_final]
  rintro ⟨_, hLeft, hRight, hPoint⟩
  exact PureArithmeticBounds.addition_upper_bound hℳ hLeft hRight hPoint

theorem addition_upper_axiom (hℳ : Theory.Models ℳ theory) :
    natural_addition_upper_bound_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro c b a
  exact addition_upper_instance hℳ a b c

theorem positive_addition_instance (hℳ : Theory.Models ℳ theory) (a b c : Carrier ℳ) :
    (natural_positive_left_addition_strict_bound_instance (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons c (.cons b (.cons a .nil))) : Env (E hℳ).model [] [s,s,s]) := by
  apply (positive_addition_correct (E hℳ).model a b c).mpr
  simp only [mem_final, omega_final, succ_final, zero_final, add_final]
  rintro ⟨_, hLeft, hRight, hPositive, hPoint⟩
  exact PureArithmeticBounds.positive_left_addition hℳ hLeft hRight hPositive hPoint

theorem positive_addition_axiom (hℳ : Theory.Models ℳ theory) :
    natural_positive_left_addition_strict_bound_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro c b a
  exact positive_addition_instance hℳ a b c

theorem transitivity_instance (hℳ : Theory.Models ℳ theory) (a b c : Carrier ℳ) :
    (natural_le_lt_transitivity_instance (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons c (.cons b (.cons a .nil))) : Env (E hℳ).model [] [s,s,s]) := by
  apply (transitivity_correct (E hℳ).model a b c).mpr
  simp only [mem_final, omega_final, succ_final]
  rintro ⟨_, hUpper, hPoint, hMiddle⟩
  exact PureArithmeticBounds.le_lt_transitivity hℳ hUpper hPoint hMiddle

theorem transitivity_axiom (hℳ : Theory.Models ℳ theory) :
    natural_le_lt_transitivity_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro c b a
  exact transitivity_instance hℳ a b c

theorem pairing_instance (hℳ : Theory.Models ℳ theory) (a b : Carrier ℳ) :
    (natural_godel_pairing_coordinate_bound_instance (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons b (.cons a .nil)) : Env (E hℳ).model [] [s,s]) := by
  apply (pairing_correct (E hℳ).model a b).mpr
  simp only [mem_final, omega_final, succ_final]
  rintro ⟨hLeft, hRight⟩
  apply PureArithmeticBounds.pairing_coordinates hℳ hLeft hRight
  exact ((PureCompletedStage.realizes hℳ).function .godelPairing (.cons a (.cons b .nil)) _).mpr rfl

theorem pairing_axiom (hℳ : Theory.Models ℳ theory) :
    natural_godel_pairing_coordinate_bound_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro b a
  exact pairing_instance hℳ a b

theorem exponent_instance (hℳ : Theory.Models ℳ theory) (a b : Carrier ℳ) :
    (natural_exponentiation_index_bound_instance (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons b (.cons a .nil)) : Env (E hℳ).model [] [s,s]) := by
  apply (exponent_correct (E hℳ).model a b).mpr
  simp only [mem_final, omega_final, succ_final, zero_final, pow_final]
  rintro ⟨hBase, hIndex, hLarge⟩
  exact PureArithmeticBounds.exponent_index hℳ hBase hIndex hLarge

theorem exponent_axiom (hℳ : Theory.Models ℳ theory) :
    natural_exponentiation_index_bound_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro b a
  exact exponent_instance hℳ a b

theorem exponent_product_instance (hℳ : Theory.Models ℳ theory) (a b c d : Carrier ℳ) :
    (natural_exponent_product_index_bound_instance (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)).satisfies
      (templateEnv (.cons d (.cons c (.cons b (.cons a .nil)))) : Env (E hℳ).model [] [s,s,s,s]) := by
  apply (exponent_product_correct (E hℳ).model a b c d).mpr
  simp only [mem_final, omega_final, succ_final, zero_final, mul_final, pow_final]
  rintro ⟨hBase, hIndex, hLarge, hBase2, hIndex2, hLarge2⟩
  exact PureArithmeticBounds.exponent_product_indices hℳ hBase hIndex hLarge hBase2 hIndex2 hLarge2

theorem exponent_product_axiom (hℳ : Theory.Models ℳ theory) :
    natural_exponent_product_index_bound_axiom.satisfies (Env.empty : Env (E hℳ).model [] []) := by
  apply close_of_curried
  intro d c b a
  exact exponent_product_instance hℳ a b c d

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureFinalArithmetic
