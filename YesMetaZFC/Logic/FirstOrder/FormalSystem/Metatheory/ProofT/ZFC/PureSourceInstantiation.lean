import YesMetaZFC.Automation.ObjectCodeInstantiation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceTransformConstruction

/-! # 固定公式骨架的内部数值代入

原变量码保持完整 AST 格式，替换值可为非标准自然数。
本模块给出码域与 quotation 连接，变换轨迹在后一模块证明。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInstantiation
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def originalValues (𝒩 : Structure.{0,0,0,x} signature) (index : Nat) : 𝒩.Carrier .set :=
  node 𝒩 1 [node 𝒩 index []]

abbrev term (𝒩 : Structure.{0,0,0,x} signature) (values : Nat → 𝒩.Carrier .set)
    {bound free : SetContext} {sort : SetSort} (input : Term signature bound free sort) : 𝒩.Carrier .set :=
  ObjectCodeInstantiation.term (node 𝒩) values input
abbrev arguments (𝒩 : Structure.{0,0,0,x} signature) (values : Nat → 𝒩.Carrier .set)
    {bound free sorts : SetContext} (input : Arguments signature bound free sorts) : List (𝒩.Carrier .set) :=
  ObjectCodeInstantiation.arguments (node 𝒩) values input
abbrev formula (𝒩 : Structure.{0,0,0,x} signature) (values : Nat → 𝒩.Carrier .set)
    {bound free : SetContext} (input : SetFormula bound free) : 𝒩.Carrier .set :=
  ObjectCodeInstantiation.formula (node 𝒩) values input

theorem original_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (index : Nat) :
    mem 𝒩 (originalValues 𝒩 index) (w 𝒩) :=
  node_natural h𝒩 1 (by simp [node_natural h𝒩 index (fields := []) (by simp)])

theorem term_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {values : Nat → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {bound free : SetContext} {sort : SetSort} (input : Term signature bound free sort) :
    mem 𝒩 (term 𝒩 values input) (w 𝒩) :=
  ObjectCodeInstantiation.term_property (node 𝒩) values (fun value => mem 𝒩 value (w 𝒩))
    (fun tag _ hFields => node_natural h𝒩 tag hFields) hValues input

theorem arguments_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {values : Nat → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {bound free sorts : SetContext} (input : Arguments signature bound free sorts) :
    ∀ value ∈ arguments 𝒩 values input, mem 𝒩 value (w 𝒩) :=
  ObjectCodeInstantiation.arguments_property (node 𝒩) values (fun value => mem 𝒩 value (w 𝒩))
    (fun tag _ hFields => node_natural h𝒩 tag hFields) hValues input

theorem formula_natural (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {values : Nat → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {bound free : SetContext} (input : SetFormula bound free) : mem 𝒩 (formula 𝒩 values input) (w 𝒩) :=
  ObjectCodeInstantiation.formula_property (node 𝒩) values (fun value => mem 𝒩 value (w 𝒩))
    (fun tag _ hFields => node_natural h𝒩 tag hFields) hValues input

mutual
theorem tree_eval (input : NatPacket.Tree) : ObjectCodeInstantiation.tree (node 𝒩) input =
    (IntrinsicQuotation.tree input).eval (Env.empty : Env 𝒩 [] []) := by
  cases input with
  | node tag fields =>
    rw [IntrinsicQuotation.tree, node_eval]
    exact congrArg (node 𝒩 tag) (forest_eval fields)
theorem forest_eval (input : List NatPacket.Tree) : ObjectCodeInstantiation.forest (node 𝒩) input =
    (IntrinsicQuotation.forest input).map (fun value => value.eval (Env.empty : Env 𝒩 [] [])) := by
  cases input with
  | nil => rfl
  | cons head tail => simp only [ObjectCodeInstantiation.forest, IntrinsicQuotation.forest, List.map_cons,
      tree_eval head, forest_eval tail]
end

theorem term_original_tree {bound free : SetContext} {sort : SetSort} (input : Term signature bound free sort) :
    term 𝒩 (originalValues 𝒩) input = ObjectCodeInstantiation.tree (node 𝒩) (SyntaxEncode.term input) :=
  ObjectCodeInstantiation.term_original (node 𝒩) input

theorem original_quote {bound free : SetContext} (input : SetFormula bound free) :
    formula 𝒩 (originalValues 𝒩) input =
      (IntrinsicQuotation.quote input).eval (Env.empty : Env 𝒩 [] []) :=
  (ObjectCodeInstantiation.formula_original (node 𝒩) input).trans (tree_eval (SyntaxEncode.formula input))

theorem tree_numeral (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory) (input : NatPacket.Tree) :
    ObjectCodeInstantiation.tree (node 𝒩) input = numeral 𝒩 (IntrinsicQuotation.treeValue input) :=
  (tree_eval input).trans ((IntrinsicQuotation.tree_evaluate intrinsic_zfc_certificate_core input).semantically_entails 𝒩 h𝒩)

/-- 参数化码构造本身是对象项，其求值等于内部节点代数。 -/
theorem formula_eval {bound free sb sf : SetContext} (env : Env 𝒩 bound free)
    (values : Nat → SetTerm bound free) (input : SetFormula sb sf) :
    (ObjectCodeInstantiation.formula IntrinsicQuotation.node values input).eval env =
      formula 𝒩 (fun i => (values i).eval env) input := by
  refine ObjectCodeInstantiation.formula_rel
    (IntrinsicQuotation.node : Nat → List (SetTerm bound free) → SetTerm bound free)
    (node 𝒩) values (fun i => (values i).eval env)
    (fun (term : SetTerm bound free) (value : 𝒩.Carrier .set) => term.eval env = value)
    ?_ (fun _ _ => rfl) input
  · intro tag left right hFields
    rw [node_eval]
    apply congrArg (node 𝒩 tag)
    induction hFields with
    | nil => rfl
    | cons h _ ih => simp only [List.map_cons, h, ih]

/-- 只在实际自然数参数上比较两个节点代数，不要求全域编码函数一致。 -/
theorem formula_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {values : Nat → 𝒩.Carrier .set} (hValues : ∀ i, mem 𝒩 (values i) (w 𝒩))
    {bound free : SetContext} (input : SetFormula bound free) :
    formula 𝒩 values input = formula (PureSourceNumerals.canonical h𝒩) values input := by
  have h := ObjectCodeInstantiation.formula_rel (node 𝒩) (node (PureSourceNumerals.canonical h𝒩))
    values values (fun left right => mem 𝒩 left (w 𝒩) ∧ left = right) (by
      intro tag left right hFields
      have hParts : (∀ value ∈ left, mem 𝒩 value (w 𝒩)) ∧ left = right := by
        induction hFields with
        | nil => exact ⟨(by simp), rfl⟩
        | cons h _ ih =>
          constructor
          · intro value hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact h.1
            · exact ih.1 value hv
          · rw [h.2, ih.2]; rfl
      exact ⟨node_natural h𝒩 tag hParts.1,
        (node_agrees h𝒩 tag hParts.1).trans (congrArg (node (PureSourceNumerals.canonical h𝒩) tag) hParts.2)⟩)
    (fun i _ => ⟨hValues i, rfl⟩) input
  exact h.2

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureSourceInstantiation
