import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaJoinData
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaRenameNumeric
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectFiniteJoin

/-!
# 七个中间数码的真正对象层存在连接

槽位依次是三张重命名表、三个重命名正文及模式核心。所有中间码都在对象公式中
被量化；界只由公开的参数数目和候选结论给出，公式大小不随输入改变。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaJoin
open Nonlogical.BasicSetTheory QuineEncoding NatPacket IntrinsicQuotation
open _root_.YesMetaZFC.Automation ObjectHorn ObjectArithmeticTerm
open scoped Nonlogical.BasicSetTheory.Symbols
set_option autoImplicit false

def tableSlot (i : Fin 3) : Fin 7 := ⟨i.val, by omega⟩
def bodySlot (i : Fin 3) : Fin 7 := ⟨i.val + 3, by omega⟩

def target {bound free : SetContext} (which : SchemaRename.Site) (n : SetTerm bound free) : SetTerm bound free :=
  shift (SchemaTable.entry which).start n

@[simp] theorem target_numeral {bound free : SetContext} (which : SchemaRename.Site) (n : Nat) :
    target which (numₘ(n) : SetTerm bound free) = numₘ(which.targetDepth n) := by
  cases which <;> simp [target, SchemaTable.entry, SchemaRename.Site.targetDepth]

def checks {bound free : SetContext} (kind : SchemaTemplate.Kind) (env : Fin 7 → SetTerm bound free)
    (n input output : SetTerm bound free) : List (SetFormula bound free) :=
  List.ofFn (fun i : Fin 3 => SchemaTable.condition (numₘ((SchemaTable.entry (site kind i)).tag)) n (env (tableSlot i))) ++
  List.ofFn (fun i : Fin 3 => SchemaObjectGraph.Rename.condition (target (site kind i) n)
    (env (tableSlot i)) input (env (bodySlot i))) ++
  [SchemaTemplate.condition (numₘ(kind.tag)) (fun i => env (bodySlot i)) (env 6),
    SchemaClosure.condition n (env 6) output]

def matrix {bound free : SetContext} (kind : SchemaTemplate.Kind) (env : Fin 7 → SetTerm bound free)
    (n input output : SetTerm bound free) : SetFormula bound free := allOf (checks kind env n input output)

theorem matrix_delta0 {bound free : SetContext} (kind : SchemaTemplate.Kind) (env : Fin 7 → SetTerm bound free)
    (n input output : SetTerm bound free) : Formula.IsDelta0 set_levy_bound (matrix kind env n input output) := by
  apply allOf_delta0
  intro φ hφ
  simp only [checks, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with (⟨i, rfl⟩ | ⟨i, rfl⟩) | (rfl | rfl)
  · exact SchemaTable.condition_delta0 _ _ _
  · exact SchemaObjectGraph.Rename.condition_delta0 _ _ _ _
  · exact SchemaTemplate.condition_delta0 _ _ _
  · exact SchemaClosure.condition_delta0 _ _ _

@[simp] theorem matrix_substituteMapped {sb sf tb tf : SetContext} (kind : SchemaTemplate.Kind)
    (env : Fin 7 → SetTerm sb sf) (n input output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (matrix kind env n input output).substituteMapped bs fs =
      matrix kind (fun i => (env i).substituteMapped bs fs)
        (n.substituteMapped bs fs) (input.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [matrix, checks, SchemaObjectGraph.Rename.condition, SchemaClosure.condition,
    ObjectUnaryIteration.condition, target]

/-- 内部的有限界槽位随公开项实例化；不会出现在最终四元公式的接口中。 -/
def boundedTemplate (kind : SchemaTemplate.Kind) : FormulaTemplate (project_bound_context 4) where
  body := quantify 7 (.fvar .here)
    (matrix kind (fun i => .bvar (project_bound_variable i))
      (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here)))))

def arguments {bound free : SetContext} (limit n input output : SetTerm bound free) :
    VariableSubstitution signature (project_bound_context 4) bound free :=
  VariableSubstitution.cons limit (VariableSubstitution.cons n
    (VariableSubstitution.cons input (VariableSubstitution.cons output VariableSubstitution.empty)))

def bounded {bound free : SetContext} (kind : SchemaTemplate.Kind) (limit n input output : SetTerm bound free) :
    SetFormula bound free := (boundedTemplate kind).instantiate (arguments limit n input output)

theorem bounded_delta0 {bound free : SetContext} (kind : SchemaTemplate.Kind) (limit n input output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (bounded kind limit n input output) :=
  FormulaTemplate.instantiate_delta0 _ (quantify_delta0 _ _ _ (matrix_delta0 _ _ _ _ _)) _

@[simp] theorem bounded_substituteMapped {sb sf tb tf : SetContext} (kind : SchemaTemplate.Kind)
    (limit n input output : SetTerm sb sf) (bs : VariableSubstitution signature sb tb tf)
    (fs : VariableSubstitution signature sf tb tf) :
    (bounded kind limit n input output).substituteMapped bs fs =
      bounded kind (limit.substituteMapped bs fs) (n.substituteMapped bs fs)
        (input.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp only [bounded, FormulaTemplate.instantiate_substituteMapped]
  congr 1
  funext sort v
  cases v with
  | here => rfl
  | there v => cases v with
    | here => rfl
    | there v => cases v with
      | here => rfl
      | there v => cases v with
        | here => rfl
        | there v => cases v

def limitTerm {bound free : SetContext} (n output : SetTerm bound free) : SetTerm bound free :=
  Sₘ(godel_pairₘ(tableBound n, output))

def limitValue (n output : Nat) : Nat := ProofCode.godel_pair_value (tableBoundValue n) output + 1

def branch {bound free : SetContext} (kind : SchemaTemplate.Kind) (n input output : SetTerm bound free) : SetFormula bound free :=
  bounded kind (limitTerm n output) n input output

def kinds : List SchemaTemplate.Kind := [.separation, .collection, .replacement]

def condition {bound free : SetContext} (tag n input output : SetTerm bound free) : SetFormula bound free :=
  anyOf (kinds.map (fun kind => (tag ≐ₘ numₘ(kind.tag)) ∧ₘ branch kind n input output))

@[simp] theorem condition_substituteMapped {sb sf tb tf : SetContext} (tag n input output : SetTerm sb sf)
    (bs : VariableSubstitution signature sb tb tf) (fs : VariableSubstitution signature sf tb tf) :
    (condition tag n input output).substituteMapped bs fs =
      condition (tag.substituteMapped bs fs) (n.substituteMapped bs fs)
        (input.substituteMapped bs fs) (output.substituteMapped bs fs) := by
  simp [condition, branch, limitTerm, tableBound, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped, Function.comp_def]

def template : FormulaTemplate.Quaternary where
  body := condition (.fvar .here) (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))

@[simp] theorem template_apply {bound free : SetContext} (tag n input output : SetTerm bound free) :
    template tag n input output = condition tag n input output := by
  simp [template, FormulaTemplate.apply_four, FormulaTemplate.instantiate,
    Term.substituteMapped, VariableSubstitution.cons]

theorem condition_delta0 {bound free : SetContext} (tag n input output : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound (condition tag n input output) := by
  apply anyOf_delta0
  intro φ hφ
  obtain ⟨kind, _, rfl⟩ := List.mem_map.mp hφ
  exact .conj (.equal _ _) (bounded_delta0 _ _ _ _ _)

theorem template_delta0 : Formula.IsDelta0 set_levy_bound template.body := condition_delta0 _ _ _ _

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaJoin
