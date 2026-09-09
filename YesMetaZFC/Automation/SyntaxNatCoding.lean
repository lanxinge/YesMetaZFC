import YesMetaZFC.Logic.FirstOrder.Completeness.Schedule

/-! # 有可数符号编码的一阶语法及公平调度

从排序、函数和关系的单射编码构造内在良构语法的单射编码，再提升到 Henkin
签名。编码只用于强完备性的固定公平调度，不参与对象理论的 quotation 或证明检查。
-/
namespace YesMetaZFC.Automation.SyntaxNatCoding
open Logic Logic.FirstOrder Logic.FirstOrder.HenkinSignature
open Logic.FirstOrder.Completeness.Henkin
set_option autoImplicit false
variable {σ : Signature.{0, 0, 0}}

/-- 符号表的可数性；函数元数和排序仍由原签名决定。 -/
structure SymbolCoding (σ : Signature.{0, 0, 0}) where
  sort : NatCoding σ.SortSymbol
  function : NatCoding σ.FuncSymbol
  relation : NatCoding σ.RelSymbol

private abbrev pair := NatPairing.pair
variable (coding : SymbolCoding σ)

/-- Henkin 见证以排序和自然数序号编码，与原函数分支区分。 -/
def henkin_function_encode : HenkinFunc σ → Nat
  | .base function => pair 0 (coding.function.encode function)
  | .witness sort index => pair 1 (pair (coding.sort.encode sort) index)

theorem henkin_function_encode_injective :
    Function.Injective (henkin_function_encode coding) := by
  intro left right hCode
  cases left <;> cases right
  · simp [henkin_function_encode, NatPairing.pair_eq_pair_iff,
      coding.function.injective.eq_iff] at hCode ⊢
    exact hCode
  · simp [henkin_function_encode, NatPairing.pair_eq_pair_iff] at hCode
  · simp [henkin_function_encode, NatPairing.pair_eq_pair_iff] at hCode
  · simp [henkin_function_encode, NatPairing.pair_eq_pair_iff,
      coding.sort.injective.eq_iff] at hCode ⊢
    exact hCode

def SymbolCoding.henkin : SymbolCoding (HSignature σ) where
  sort := coding.sort
  function := ⟨henkin_function_encode coding, henkin_function_encode_injective coding⟩
  relation := coding.relation

private theorem variable_index_injective {S : Type}
    {context : List S} {sort : S} :
    Function.Injective (@Variable.index S context sort) := by
  intro left right hIndex
  induction left with
  | here =>
      cases right with
      | here => rfl
      | there previous => cases hIndex
  | there previous ih =>
      cases right with
      | here => cases hIndex
      | there previous' =>
          apply congrArg Variable.there
          apply ih
          simp [Variable.index] at hIndex
          omega

mutual

def term_encode (coding : SymbolCoding σ)
    {bound free : SortContext σ}
    {sort : σ.SortSymbol}
    (term : Term σ bound free sort) : Nat :=
  match term with
  | .bvar entry =>
      pair (coding.sort.encode sort) (pair 0 entry.index)
  | .fvar entry =>
      pair (coding.sort.encode sort) (pair 1 entry.index)
  | .app function arguments =>
      pair (coding.sort.encode sort)
        (pair 2
          (pair (coding.function.encode function)
            (arguments_encode coding arguments)))

def arguments_encode (coding : SymbolCoding σ)
    {bound free : SortContext σ}
    {sorts : List σ.SortSymbol}
    (arguments : Arguments σ bound free sorts) : Nat :=
  match arguments with
  | .nil => 0
  | .cons head tail =>
      pair (term_encode coding head) (arguments_encode coding tail) + 1

end

mutual

private theorem term_encode_eq_core (coding : SymbolCoding σ)
    {bound free : SortContext σ} :
    {leftSort rightSort : σ.SortSymbol} →
      (left : Term σ bound free leftSort) →
      (right : Term σ bound free rightSort) →
      term_encode coding left = term_encode coding right →
      (⟨leftSort, left⟩ :
        Σ sort, Term σ bound free sort) =
      ⟨rightSort, right⟩
  | _, _, .bvar leftEntry, .bvar rightEntry, hCode => by
      simp only [term_encode] at hCode
      rcases NatPairing.pair_eq_pair_iff.mp hCode with
        ⟨hSort, hNode⟩
      cases coding.sort.injective hSort
      have hIndex := (NatPairing.pair_eq_pair_iff.mp hNode).2
      cases variable_index_injective hIndex
      rfl
  | _, _, .bvar leftEntry, .fvar rightEntry, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hTag := (NatPairing.pair_eq_pair_iff.mp hNode).1
      omega
  | _, _, .bvar leftEntry, .app rightFunction rightArguments, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hTag := (NatPairing.pair_eq_pair_iff.mp hNode).1
      omega
  | _, _, .fvar leftEntry, .bvar rightEntry, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hTag := (NatPairing.pair_eq_pair_iff.mp hNode).1
      omega
  | _, _, .fvar leftEntry, .fvar rightEntry, hCode => by
      simp only [term_encode] at hCode
      rcases NatPairing.pair_eq_pair_iff.mp hCode with
        ⟨hSort, hNode⟩
      cases coding.sort.injective hSort
      have hIndex := (NatPairing.pair_eq_pair_iff.mp hNode).2
      cases variable_index_injective hIndex
      rfl
  | _, _, .fvar leftEntry, .app rightFunction rightArguments, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hTag := (NatPairing.pair_eq_pair_iff.mp hNode).1
      omega
  | _, _, .app leftFunction leftArguments, .bvar rightEntry, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hTag := (NatPairing.pair_eq_pair_iff.mp hNode).1
      omega
  | _, _, .app leftFunction leftArguments, .fvar rightEntry, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hTag := (NatPairing.pair_eq_pair_iff.mp hNode).1
      omega
  | _, _, .app leftFunction leftArguments,
      .app rightFunction rightArguments, hCode => by
      simp only [term_encode] at hCode
      have hNode := (NatPairing.pair_eq_pair_iff.mp hCode).2
      have hPayload := (NatPairing.pair_eq_pair_iff.mp hNode).2
      rcases NatPairing.pair_eq_pair_iff.mp hPayload with
        ⟨hFunction, hArguments⟩
      cases coding.function.injective hFunction
      cases arguments_encode_eq_core coding leftArguments
        rightArguments hArguments
      rfl

private theorem arguments_encode_eq_core (coding : SymbolCoding σ)
    {bound free : SortContext σ} :
    {leftSorts rightSorts : List σ.SortSymbol} →
      (left : Arguments σ bound free leftSorts) →
      (right : Arguments σ bound free rightSorts) →
      arguments_encode coding left = arguments_encode coding right →
      (⟨leftSorts, left⟩ :
        Σ sorts, Arguments σ bound free sorts) =
      ⟨rightSorts, right⟩
  | _, _, .nil, .nil, _ => rfl
  | _, _, .nil, .cons rightHead rightTail, hCode => by
      simp [arguments_encode] at hCode
  | _, _, .cons leftHead leftTail, .nil, hCode => by
      simp [arguments_encode] at hCode
  | _, _, .cons leftHead leftTail,
      .cons rightHead rightTail, hCode => by
      simp only [arguments_encode] at hCode
      have hPair := Nat.add_right_cancel hCode
      rcases NatPairing.pair_eq_pair_iff.mp hPair with
        ⟨hHead, hTail⟩
      cases term_encode_eq_core coding leftHead rightHead hHead
      cases arguments_encode_eq_core coding leftTail rightTail hTail
      rfl

end

theorem term_encode_eq
    {bound free : SortContext σ}
    {sort : σ.SortSymbol}
    {left right : Term σ bound free sort}
    (hCode : term_encode coding left = term_encode coding right) : left = right :=
  by
    cases term_encode_eq_core coding left right hCode
    rfl

theorem arguments_encode_eq
    {bound free : SortContext σ}
    {sorts : List σ.SortSymbol}
    {left right : Arguments σ bound free sorts}
    (hCode : arguments_encode coding left = arguments_encode coding right) : left = right :=
  by
    cases arguments_encode_eq_core coding left right hCode
    rfl

private theorem equality_formula_eq_of_codes
    {bound free : SortContext σ}
    {leftSort rightSort : σ.SortSymbol}
    {left₁ left₂ :
      Term σ bound free leftSort}
    {right₁ right₂ :
      Term σ bound free rightSort}
    (hLeft : term_encode coding left₁ = term_encode coding right₁)
    (hRight : term_encode coding left₂ = term_encode coding right₂) :
    Formula.equal left₁ left₂ = Formula.equal right₁ right₂ := by
  cases term_encode_eq_core coding left₁ right₁ hLeft
  cases term_encode_eq_core coding left₂ right₂ hRight
  rfl

def formula_encode (coding : SymbolCoding σ)
    {bound free : SortContext σ} :
    Formula σ bound free → Nat
  | .falsum => pair 0 0
  | .truth => pair 1 0
  | .rel relation arguments =>
      pair 2
        (pair (coding.relation.encode relation) (arguments_encode coding arguments))
  | .equal left right =>
      pair 3 (pair (term_encode coding left) (term_encode coding right))
  | .neg body => pair 4 (formula_encode coding body)
  | .conj left right =>
      pair 5 (pair (formula_encode coding left) (formula_encode coding right))
  | .disj left right =>
      pair 6 (pair (formula_encode coding left) (formula_encode coding right))
  | .imp left right =>
      pair 7 (pair (formula_encode coding left) (formula_encode coding right))
  | .iff left right =>
      pair 8 (pair (formula_encode coding left) (formula_encode coding right))
  | .forallE sort body =>
      pair 9 (pair (coding.sort.encode sort) (formula_encode coding body))
  | .existsE sort body =>
      pair 10 (pair (coding.sort.encode sort) (formula_encode coding body))

theorem formula_encode_injective
    {bound free : SortContext σ} :
    Function.Injective (@formula_encode σ coding bound free) := by
  intro left
  induction left <;> intro target hCode <;> cases target <;>
    simp [formula_encode, NatPairing.pair_eq_pair_iff] at hCode
  all_goals first | rfl | skip
  case rel.rel =>
    cases coding.relation.injective hCode.1
    cases arguments_encode_eq coding hCode.2
    rfl
  case equal.equal => exact equality_formula_eq_of_codes coding hCode.1 hCode.2
  case neg.neg =>
    rename_i body ih target
    exact congrArg Formula.neg (ih hCode)
  case conj.conj | disj.disj | imp.imp | iff.iff =>
    rename_i left right ihLeft ihRight left' right'
    cases ihLeft hCode.1
    cases ihRight hCode.2
    rfl
  case forallE.forallE | existsE.existsE =>
    rename_i sort body ih sort' body'
    cases coding.sort.injective hCode.1
    cases ih hCode.2
    rfl


def formula_coding :
    NatCoding (Sentence σ) where
  encode := formula_encode coding
  injective := formula_encode_injective coding

/-- 符号编码给出的固定公平调度，公平性由 `Schedule.of_coding` 正式证明。 -/
noncomputable def schedule : Completeness.Henkin.Schedule σ :=
  Completeness.Henkin.Schedule.of_coding (formula_coding coding.henkin)

end YesMetaZFC.Automation.SyntaxNatCoding
