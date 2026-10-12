import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CodePattern
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.AxiomDecode

/-!
# 原始模式证书外壳的正负对象表示

统一识别 `node tag [leaf parameterCount, body]`，正文为任意原始有限树。
本层排除错误标签、字段数和非叶子的参数字段，不假设输入已解析。
正文的公式合法性、作用域、重命名及模式输出由后续层检查；外壳通过不意味着
该输入已经是合法的公理模式实例。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaEnvelope
open Nonlogical.BasicSetTheory QuineEncoding NatPacket ProofCode
open IntrinsicQuotation CodePattern
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
set_option autoImplicit false

def pattern (tag : Nat) : Pattern :=
  nodePattern (.literal tag) [(nodePattern .first []), .second]

/-- 正文保持原始树；这里不调用 `ProjectDecode`。 -/
def decode (tag : Nat) : Tree → Option (Nat × Tree)
  | .node inputTag [(.node count []), body] => if inputTag == tag then some (count, body) else none
  | _ => none

def check (tag : Nat) (input : Tree) : Bool := (decode tag input).isSome

/-- 数值层反演同时固定外壳、参数和正文码，允许候选正文码是任意自然数。 -/
theorem value_iff (tag : Nat) (input : Tree) (count bodyCode : Nat) :
    treeValue input = (pattern tag).eval count bodyCode ↔
      ∃ body, input = .node tag [leaf count, body] ∧ treeValue body = bodyCode := by
  cases input with
  | node inputTag fields =>
    cases fields with
    | nil => simp [pattern, nodePattern, listPattern, Pattern.eval, treeValue,
        forestValue, godel_pair_value_eq_iff, leaf]
    | cons head tail =>
      cases tail with
      | nil => simp [pattern, nodePattern, listPattern, Pattern.eval, treeValue,
          forestValue, godel_pair_value_eq_iff, leaf]
      | cons body tail =>
        cases tail with
        | cons extra rest => simp [pattern, nodePattern, listPattern, Pattern.eval, treeValue,
            forestValue, godel_pair_value_eq_iff, leaf]
        | nil =>
          cases head with
          | node parameter fields =>
            cases fields with
            | nil => simp [pattern, nodePattern, listPattern, Pattern.eval, treeValue,
                forestValue, godel_pair_value_eq_iff, leaf, and_assoc]
            | cons extra rest => simp [pattern, nodePattern, listPattern, Pattern.eval, treeValue,
                forestValue, godel_pair_value_eq_iff, leaf]

theorem decode_eq_some_iff (tag count : Nat) (input body : Tree) :
    decode tag input = some (count, body) ↔ input = .node tag [leaf count, body] := by
  cases input with
  | node inputTag fields =>
    cases fields with
    | nil => constructor <;> intro h <;> cases h
    | cons head tail =>
      cases head with
      | node parameter fields =>
        cases fields with
        | cons _ _ => constructor <;> intro h <;> cases h
        | nil =>
          cases tail with
          | nil => constructor <;> intro h <;> cases h
          | cons candidate tail =>
            cases tail with
            | cons _ _ => constructor <;> intro h <;> cases h
            | nil =>
              by_cases h : inputTag = tag
              · subst inputTag
                change (if decide (tag = tag) then some (parameter, candidate) else none) =
                  some (count, body) ↔ _
                rw [decide_eq_true (rfl : tag = tag)]
                constructor <;> intro h <;> cases h <;> rfl
              · constructor
                · intro hDecoded
                  change (if decide (inputTag = tag) then some (parameter, candidate) else none) =
                    some (count, body) at hDecoded
                  rw [decide_eq_false h] at hDecoded
                  cases hDecoded
                · intro hShape
                  cases hShape
                  exact False.elim (h rfl)

theorem check_eq_true_iff (tag : Nat) (input : Tree) :
    check tag input = true ↔ ∃ count body, input = .node tag [leaf count, body] := by
  unfold check
  cases h : decode tag input with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists]
      intro count body hEq
      have hSome := (decode_eq_some_iff tag count input body).mpr hEq
      rw [h] at hSome
      contradiction
  | some decoded =>
      simp only [Option.isSome_some, true_iff]
      exact ⟨decoded.1, decoded.2, (decode_eq_some_iff tag decoded.1 input decoded.2).mp h⟩

private theorem leaf_bound (count : Nat) : count ≤ treeValue (leaf count) :=
  Nat.le_trans (left_le_godel_pair_value _ _) (Nat.le_succ _)

private theorem head_bound (head : Tree) (tail : List Tree) :
    treeValue head ≤ forestValue (head :: tail) :=
  Nat.le_trans (left_le_godel_pair_value _ _)
    (Nat.le_trans (right_le_godel_pair_value _ _) (Nat.le_succ _))

private theorem tail_bound (head : Tree) (tail : List Tree) :
    forestValue tail ≤ forestValue (head :: tail) :=
  Nat.le_trans (right_le_godel_pair_value _ _)
    (Nat.le_trans (right_le_godel_pair_value _ _) (Nat.le_succ _))

private theorem fields_bound (tag : Nat) (fields : List Tree) :
    forestValue fields ≤ treeValue (.node tag fields) :=
  Nat.le_trans (right_le_godel_pair_value _ _) (Nat.le_succ _)

/-- 图对所有输入使用同一个固定模式，不把已计算的结论放进模板。 -/
def condition {bound free : SetContext} (tag : Nat) (input : SetTerm bound free) :
    SetFormula bound free := CodePattern.graph (pattern tag) input

theorem condition_delta0 {bound free : SetContext} (tag : Nat) (input : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition tag input) := CodePattern.graph_delta0 _ _

theorem positive (tag : Nat) (input : Tree) (h : check tag input = true) :
    Derives intrinsic_zfc_theory [] (condition tag (numₘ(treeValue input) : Code)) := by
  obtain ⟨count, body, rfl⟩ := (check_eq_true_iff tag input).mp h
  apply CodePattern.positive intrinsic_zfc_certificate_core
    intrinsic_zfc_arithmetic_support.contains_successor (pattern tag) _ count (treeValue body)
  · exact Nat.le_trans (leaf_bound count)
      (Nat.le_trans (head_bound _ _) (fields_bound _ _))
  · exact Nat.le_trans (head_bound body [])
      (Nat.le_trans (tail_bound _ _) (fields_bound _ _))
  · exact (value_iff tag _ count (treeValue body)).mpr ⟨body, rfl, rfl⟩

/-- 任何外壳失败的原始树都得到对象否定；不需要理论一致性。 -/
theorem negative (tag : Nat) (input : Tree) (h : check tag input = false) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition tag (numₘ(treeValue input) : Code)) := by
  apply CodePattern.negative intrinsic_zfc_certificate_core
  intro count _ bodyCode _ hEq
  obtain ⟨body, hShape, _⟩ := (value_iff tag input count bodyCode).mp hEq
  have hTrue := (check_eq_true_iff tag input).mpr ⟨count, body, hShape⟩
  rw [h] at hTrue
  contradiction

theorem positive_at_tree (tag : Nat) (input : Tree) (h : check tag input = true) :
    Derives intrinsic_zfc_theory [] (condition tag (IntrinsicQuotation.tree input)) :=
  CodePattern.transport (pattern tag)
    (Metatheory.Derives.equality_symm (tree_evaluate intrinsic_zfc_certificate_core input))
    (positive tag input h)

theorem negative_at_tree (tag : Nat) (input : Tree) (h : check tag input = false) :
    Derives intrinsic_zfc_theory [] (¬ₘ condition tag (IntrinsicQuotation.tree input)) :=
  CodePattern.transport_neg (pattern tag)
    (Metatheory.Derives.equality_symm (tree_evaluate intrinsic_zfc_certificate_core input))
    (negative tag input h)

/-- 当前 ZFC 呈现中的实际两个模式标签；替换不被悄悄加入原公理表。 -/
def zfcCheck (input : Tree) : Bool := check 8 input || check 9 input

def zfcCondition {bound free : SetContext} (input : SetTerm bound free) :
    SetFormula bound free := condition 8 input ∨ₘ condition 9 input

theorem zfcCondition_delta0 {bound free : SetContext} (input : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (zfcCondition input) :=
  Formula.IsDelta0.disj (condition_delta0 8 input) (condition_delta0 9 input)

theorem zfc_positive (input : Tree) (h : zfcCheck input = true) :
    Derives intrinsic_zfc_theory [] (zfcCondition (IntrinsicQuotation.tree input)) := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact FirstOrder.Derives.disj_intro_left (positive_at_tree 8 input h)
  · exact FirstOrder.Derives.disj_intro_right (positive_at_tree 9 input h)

theorem zfc_negative (input : Tree) (h : zfcCheck input = false) :
    Derives intrinsic_zfc_theory [] (¬ₘ zfcCondition (IntrinsicQuotation.tree input)) := by
  have hParts := Bool.or_eq_false_iff.mp h
  apply FirstOrder.Derives.neg_intro
  apply FirstOrder.Derives.disj_elim (FirstOrder.Derives.assumption List.mem_cons_self)
  · exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.assumption List.mem_cons_self)
      (FirstOrder.Derives.context_weaken_cons (FirstOrder.Derives.context_weaken_cons
        (negative_at_tree 8 input hParts.1)))
  · exact FirstOrder.Derives.neg_elim (FirstOrder.Derives.assumption List.mem_cons_self)
      (FirstOrder.Derives.context_weaken_cons (FirstOrder.Derives.context_weaken_cons
        (negative_at_tree 9 input hParts.2)))

private theorem scalar_shape {input : Tree} {n : Nat}
    (h : scalar input = some n) : input = leaf n := by
  cases input with
  | node tag fields =>
      cases fields with
      | nil => simpa only [scalar, Option.some.injEq, leaf, Tree.node.injEq, and_true] using h
      | cons _ _ => cases h

/-- 实际解码器的模式分支保持原始外壳，不要求正文已经规范化。 -/
private theorem decode_schema_shape {input : Tree} {certificate : ZFCAxiomCertificate}
    (h : zfc_base_axiom_decode input = some certificate) :
    (match certificate with
    | .separation _ => check 8 input
    | .collection _ => check 9 input
    | _ => true) = true := by
  fun_cases zfc_base_axiom_decode input
  case case1 => cases h; rfl
  case case2 => cases h; rfl
  case case3 => cases h; rfl
  case case4 => cases h; rfl
  case case5 => cases h; rfl
  case case6 => cases h; rfl
  case case7 => cases h; rfl
  case case8 => cases h; rfl
  case case9 countTree body =>
    change (scalar countTree).bind (fun count =>
      (ProjectDecode.unarySchema count body).bind
        (fun schema => some (ZFCAxiomCertificate.separation schema))) = some certificate at h
    obtain ⟨count, hCount, hBody⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨schema, _, hResult⟩ := Option.bind_eq_some_iff.mp hBody
    cases hResult
    change check 8 (.node 8 [countTree, body]) = true
    rw [scalar_shape hCount]
    rfl
  case case10 countTree body =>
    change (scalar countTree).bind (fun count =>
      (ProjectDecode.binarySchema count body).bind
        (fun schema => some (ZFCAxiomCertificate.collection schema))) = some certificate at h
    obtain ⟨count, hCount, hBody⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨schema, _, hResult⟩ := Option.bind_eq_some_iff.mp hBody
    cases hResult
    change check 9 (.node 9 [countTree, body]) = true
    rw [scalar_shape hCount]
    rfl
  case case11 =>
    have hNone : zfc_base_axiom_decode input = none := by
      unfold zfc_base_axiom_decode
      split <;> simp_all
    rw [hNone] at h
    contradiction

theorem check_of_separation_decode {input : Tree} {n : Nat}
    (schema : _root_.YesMetaZFC.SetTheory.Definitional.Project.UnarySchema n)
    (h : zfc_base_axiom_decode input = some (.separation schema)) :
    check 8 input = true := decode_schema_shape h

theorem check_of_collection_decode {input : Tree} {n : Nat}
    (schema : _root_.YesMetaZFC.SetTheory.Definitional.Project.BinarySchema n)
    (h : zfc_base_axiom_decode input = some (.collection schema)) :
    check 9 input = true := decode_schema_shape h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaEnvelope
