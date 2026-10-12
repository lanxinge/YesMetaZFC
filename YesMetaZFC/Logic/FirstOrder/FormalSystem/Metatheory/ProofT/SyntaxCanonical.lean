import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SyntaxEncode

/-! # 当前内核项解码的反向规范性 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxDecode
open Nonlogical.BasicSetTheory NatPacket
set_option autoImplicit false

theorem scalar_eq_some (input : Tree) (n : Nat) : scalar input = some n ↔ input = leaf n := by
  cases input with
  | node tag fields => cases fields <;> simp [scalar, leaf, eq_comm]

theorem context_encode_of_decode {input : Tree} {free : SetContext}
    (h : context input = some free) : SyntaxEncode.context free = input := by
  obtain ⟨count, hCount, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [(scalar_eq_some input count).mp hCount]
  simp [SyntaxEncode.context]

theorem variable_index {free : SetContext} {index : Nat} {entry : Variable free SetSort.set}
    (h : decodeVariable free index = some entry) : entry.index = index := by
  induction free generalizing index with
  | nil => cases h
  | cons sort tail ih =>
    cases sort
    cases index with
    | zero => cases h; rfl
    | succ index =>
      change (decodeVariable tail index).map Variable.there = some entry at h
      cases hValue : decodeVariable tail index with
      | none =>
        rw [hValue] at h
        cases h
      | some value =>
        rw [hValue] at h
        cases h
        exact congrArg Nat.succ (ih hValue)

theorem variable_exists (free : SetContext) (index : Nat) (h : index < free.length) :
    ∃ entry, decodeVariable free index = some entry := by
  induction free generalizing index with
  | nil => cases h
  | cons sort tail ih =>
    cases sort
    cases index with
    | zero => exact ⟨.here, rfl⟩
    | succ index =>
      obtain ⟨entry, hEntry⟩ := ih index (by simpa using h)
      exact ⟨.there entry, by simp [decodeVariable, hEntry]⟩

theorem variable_lt {free : SetContext} (entry : Variable free SetSort.set) : entry.index < free.length := by
  induction free with
  | nil => cases entry
  | cons sort tail ih =>
    cases sort
    cases entry with
    | here => simp [Variable.index]
    | there entry => simpa [Variable.index] using ih entry

theorem function_index {index : Nat} {symbol : FunctionSymbol}
    (h : functionSymbols[index]? = some symbol) : symbol.ctorIdx = index := by
  have allIndices : ∀ i : Fin functionSymbols.size, (functionSymbols[i]).ctorIdx = i.val := by decide
  obtain ⟨hIndex, hSymbol⟩ := (getElem?_eq_some_iff).mp h
  rw [← hSymbol]
  exact allIndices ⟨index, hIndex⟩

@[simp] theorem application_encode {bound free : SetContext} (symbol : FunctionSymbol)
    (args : Arguments signature bound free (signature.funcDomain symbol)) :
    SyntaxEncode.term (application symbol args) = .node 2 (leaf symbol.ctorIdx :: SyntaxEncode.argumentsList args) := by
  cases symbol <;> rfl

mutual
theorem term_encode_of_decode (bound free : SetContext) (input : Tree) (result : SetTerm bound free)
    (h : term bound free input = some result) : SyntaxEncode.term result = input := by
  fun_cases term bound free input
  case case1 indexTree | case2 indexTree =>
    rw [term.eq_def] at h
    obtain ⟨index, hIndex, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨entry, hEntry, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    cases hResult
    rw [(scalar_eq_some indexTree index).mp hIndex]
    simp [variable_index hEntry]
  case case3 symbolTree trees =>
    rw [term.eq_def] at h
    obtain ⟨index, hIndex, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨symbol, hSymbol, hRest⟩ := Option.bind_eq_some_iff.mp hRest
    obtain ⟨args, hArgs, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    cases hResult
    rw [application_encode, function_index hSymbol,
      arguments_encode_of_decode bound free _ trees args hArgs, (scalar_eq_some symbolTree index).mp hIndex]
  case case4 =>
    unfold term at h
    split at h <;> simp_all
termination_by sizeOf input

theorem arguments_encode_of_decode (bound free sorts : SetContext) (input : List Tree)
    (result : Arguments signature bound free sorts)
    (h : argumentsList bound free sorts input = some result) : SyntaxEncode.argumentsList result = input := by
  rw [argumentsList.eq_def] at h
  cases sorts with
  | nil => cases input <;> cases h; rfl
  | cons sort sorts =>
    cases sort
    cases input with
    | nil => cases h
    | cons head tail =>
      obtain ⟨headTerm, hHead, hRest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨terms, hTerms, hResult⟩ := Option.bind_eq_some_iff.mp hRest
      cases hResult
      simp only [SyntaxEncode.argumentsList]
      rw [term_encode_of_decode bound free head headTerm hHead,
        arguments_encode_of_decode bound free sorts tail terms hTerms]
termination_by sizeOf input
end

theorem relation_index {index : Nat} {symbol : RelationSymbol}
    (h : relationSymbols[index]? = some symbol) : symbol.ctorIdx = index := by
  have allIndices : ∀ i : Fin relationSymbols.size, (relationSymbols[i]).ctorIdx = i.val := by decide
  obtain ⟨hIndex, hSymbol⟩ := getElem?_eq_some_iff.mp h
  rw [← hSymbol]
  exact allIndices ⟨index, hIndex⟩

/-- 完整公式解码同样只接受规范的当前 AST 编码。 -/
theorem formula_encode_of_decode (bound free : SetContext) (input : Tree) (result : SetFormula bound free)
    (h : formula bound free input = some result) : SyntaxEncode.formula result = input := by
  fun_cases formula bound free input
  case case1 | case2 =>
    rw [formula.eq_def] at h
    cases h
    rfl
  case case3 symbolTree trees =>
    rw [formula.eq_def] at h
    obtain ⟨index, hIndex, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨symbol, hSymbol, hRest⟩ := Option.bind_eq_some_iff.mp hRest
    obtain ⟨args, hArgs, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    cases hResult
    simp only [SyntaxEncode.formula]
    rw [relation_index hSymbol, arguments_encode_of_decode bound free _ trees args hArgs,
      (scalar_eq_some symbolTree index).mp hIndex]
  case case4 left right =>
    rw [formula.eq_def] at h
    obtain ⟨a, hA, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hB, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    cases hResult
    simp only [SyntaxEncode.formula]
    rw [term_encode_of_decode bound free left a hA, term_encode_of_decode bound free right b hB]
  case case5 body | case10 body | case11 body =>
    rw [formula.eq_def] at h
    obtain ⟨a, hA, hResult⟩ := Option.bind_eq_some_iff.mp h
    cases hResult
    simp only [SyntaxEncode.formula]
    rw [formula_encode_of_decode _ free body a hA]
  case case6 left right | case7 left right | case8 left right | case9 left right =>
    rw [formula.eq_def] at h
    obtain ⟨a, hA, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hB, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    cases hResult
    simp only [SyntaxEncode.formula]
    rw [formula_encode_of_decode bound free left a hA, formula_encode_of_decode bound free right b hB]
  case case12 =>
    unfold formula at h
    split at h <;> simp_all
termination_by sizeOf input

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxDecode
