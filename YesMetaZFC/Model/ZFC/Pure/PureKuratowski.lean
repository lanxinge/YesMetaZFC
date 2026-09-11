import YesMetaZFC.Model.ZFC.Pure.PureModel

/-! # 纯 ZFC 模型中的 Kuratowski 有序对

编码严格采用原支撑理论的 {{left}, {left, right}}。存在、唯一、坐标单射均从
裸 ZFC 模型的配对与外延性得到，后续投影及函数图共用这些性质。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureKuratowski
open PureModel
set_option autoImplicit false
universe x
variable {ℳ : Structure.{0, 0, 0, x} ℒ}

def Single (ℳ : Structure.{0, 0, 0, x} ℒ) (output element : Carrier ℳ) : Prop :=
  ∀ member, membership ℳ member output ↔ member = element

def Pair (ℳ : Structure.{0, 0, 0, x} ℒ) (output left right : Carrier ℳ) : Prop :=
  ∀ member, membership ℳ member output ↔ member = left ∨ member = right

def Code (ℳ : Structure.{0, 0, 0, x} ℒ) (output left right : Carrier ℳ) : Prop :=
  ∃ single pair, Single ℳ single left ∧ Pair ℳ pair left right ∧ Pair ℳ output single pair

theorem single_unique (hℳ : Theory.Models ℳ theory) {first second element : Carrier ℳ}
    (hFirst : Single ℳ first element) (hSecond : Single ℳ second element) : first = second :=
  extensionality hℳ first second (fun member => (hFirst member).trans (hSecond member).symm)

theorem pair_unique (hℳ : Theory.Models ℳ theory) {first second left right : Carrier ℳ}
    (hFirst : Pair ℳ first left right) (hSecond : Pair ℳ second left right) : first = second :=
  extensionality hℳ first second (fun member => (hFirst member).trans (hSecond member).symm)

theorem exists_code (hℳ : Theory.Models ℳ theory) (left right : Carrier ℳ) :
    ∃ output, Code ℳ output left right := by
  obtain ⟨single, hSingle⟩ := singleton hℳ left
  obtain ⟨pair, hPair⟩ := PureModel.pair hℳ left right
  obtain ⟨output, hOutput⟩ := PureModel.pair hℳ single pair
  exact ⟨output, single, pair, hSingle, hPair, hOutput⟩

theorem code_unique (hℳ : Theory.Models ℳ theory) {first second left right : Carrier ℳ}
    (hFirst : Code ℳ first left right) (hSecond : Code ℳ second left right) : first = second := by
  obtain ⟨single, pair, hSingle, hPair, hFirst⟩ := hFirst
  obtain ⟨single', pair', hSingle', hPair', hSecond⟩ := hSecond
  have hS := single_unique hℳ hSingle hSingle'
  have hP := pair_unique hℳ hPair hPair'
  subst single'
  subst pair'
  exact pair_unique hℳ hFirst hSecond

/-- 有序对各成员的交恰好是左坐标的单元素集。 -/
theorem code_intersection {output left right : Carrier ℳ} (hCode : Code ℳ output left right)
    (element : Carrier ℳ) :
    (∀ member, membership ℳ member output → membership ℳ element member) ↔ element = left := by
  obtain ⟨single, pair, hSingle, hPair, hOutput⟩ := hCode
  constructor
  · intro h
    exact (hSingle element).mp (h single ((hOutput single).mpr (Or.inl rfl)))
  · intro h member hMember
    rcases (hOutput member).mp hMember with rfl | rfl
    · exact (hSingle element).mpr h
    · exact (hPair element).mpr (Or.inl h)

theorem code_union {output left right : Carrier ℳ} (hCode : Code ℳ output left right)
    (element : Carrier ℳ) :
    (∃ member, membership ℳ member output ∧ membership ℳ element member) ↔
      element = left ∨ element = right := by
  obtain ⟨single, pair, hSingle, hPair, hOutput⟩ := hCode
  constructor
  · rintro ⟨member, hMember, hElement⟩
    rcases (hOutput member).mp hMember with rfl | rfl
    · exact Or.inl ((hSingle element).mp hElement)
    · exact (hPair element).mp hElement
  · intro h
    exact ⟨pair, (hOutput pair).mpr (Or.inr rfl), (hPair element).mpr h⟩

theorem code_injective {output left right left' right' : Carrier ℳ}
    (hFirst : Code ℳ output left right) (hSecond : Code ℳ output left' right') :
    left = left' ∧ right = right' := by
  have hLeft : left = left' :=
    (code_intersection hSecond left).mp ((code_intersection hFirst left).mpr rfl)
  subst left'
  have hRight := (code_union hSecond right).mp ((code_union hFirst right).mpr (Or.inr rfl))
  have hRight' := (code_union hFirst right').mp ((code_union hSecond right').mpr (Or.inr rfl))
  refine ⟨rfl, ?_⟩
  rcases hRight with h | h
  · exact hRight'.elim (fun h' => h.trans h'.symm) Eq.symm
  · exact h

def Left (ℳ : Structure.{0, 0, 0, x} ℒ) (output pair : Carrier ℳ) : Prop :=
  ∃ right, Code ℳ pair output right

def Right (ℳ : Structure.{0, 0, 0, x} ℒ) (output pair : Carrier ℳ) : Prop :=
  ∃ left, Code ℳ pair left output

theorem left_unique {first second pair : Carrier ℳ}
    (hFirst : Left ℳ first pair) (hSecond : Left ℳ second pair) : first = second := by
  obtain ⟨right, hFirst⟩ := hFirst
  obtain ⟨right', hSecond⟩ := hSecond
  exact (code_injective hFirst hSecond).1

theorem right_unique {first second pair : Carrier ℳ}
    (hFirst : Right ℳ first pair) (hSecond : Right ℳ second pair) : first = second := by
  obtain ⟨left, hFirst⟩ := hFirst
  obtain ⟨left', hSecond⟩ := hSecond
  exact (code_injective hFirst hSecond).2

def PairMember (ℳ : Structure.{0, 0, 0, x} ℒ) (left right relation : Carrier ℳ) : Prop :=
  ∃ pair, Code ℳ pair left right ∧ membership ℳ pair relation

def IsRelation (ℳ : Structure.{0, 0, 0, x} ℒ) (relation : Carrier ℳ) : Prop :=
  ∀ pair, membership ℳ pair relation → ∃ left right, Code ℳ pair left right

def IsFunction (ℳ : Structure.{0, 0, 0, x} ℒ) (function : Carrier ℳ) : Prop :=
  IsRelation ℳ function ∧ ∀ input first second,
    PairMember ℳ input first function → PairMember ℳ input second function → first = second

def Application (ℳ : Structure.{0, 0, 0, x} ℒ) (output function input : Carrier ℳ) : Prop :=
  IsFunction ℳ function ∧ PairMember ℳ input output function

theorem application_unique {first second function input : Carrier ℳ}
    (hFirst : Application ℳ first function input) (hSecond : Application ℳ second function input) :
    first = second := hFirst.1.2 input first second hFirst.2 hSecond.2

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureKuratowski
