import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaBody

/-!
# 模式正文的有限表重命名

有限索引表是实际数据，表长固定源作用域。穿过量词时保留最新变量零，旧表的
所有输出加一。递归器只消费原始树；与类型化 `Formula.rename` 的交换律另行证明。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaRename
open Nonlogical.BasicSetTheory NatPacket
open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false

def lift (table : List Nat) : List Nat := 0 :: table.map Nat.succ

def encodeMap {sourceDepth targetDepth : Nat} (indexMap : Fin sourceDepth → Fin targetDepth) :
    List Nat := List.ofFn (fun index => (indexMap index).val)

@[simp] theorem encodeMap_length {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth) : (encodeMap indexMap).length = sourceDepth :=
  List.length_ofFn

@[simp] theorem lift_length (table : List Nat) : (lift table).length = table.length + 1 := by
  simp [lift]

@[simp] theorem lift_encodeMap {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth) :
    lift (encodeMap indexMap) = encodeMap (BoundEmbedding.lift indexMap) := by
  simp [encodeMap, lift, List.ofFn_succ, BoundEmbedding.lift, List.map_ofFn, Function.comp_def]

def term (table : List Nat) : Tree → Option Tree
  | .node 0 [(.node index [])] => (fun target => .node 0 [leaf target]) <$> table[index]?
  | _ => none

def formula (table : List Nat) (input : Tree) : Option Tree :=
  match input with
  | .node 0 [] => some (leaf 0)
  | .node 1 [] => some (leaf 1)
  | .node 2 [left, right] => do return .node 2 [(← term table left), (← term table right)]
  | .node 3 [left, right] => do return .node 3 [(← term table left), (← term table right)]
  | .node 4 [body] => do return .node 4 [← formula table body]
  | .node 5 [left, right] => do return .node 5 [(← formula table left), (← formula table right)]
  | .node 6 [left, right] => do return .node 6 [(← formula table left), (← formula table right)]
  | .node 7 [left, right] => do return .node 7 [(← formula table left), (← formula table right)]
  | .node 8 [left, right] => do return .node 8 [(← formula table left), (← formula table right)]
  | .node 9 [body] => do return .node 9 [← formula (lift table) body]
  | .node 10 [body] => do return .node 10 [← formula (lift table) body]
  | .node 11 [left, right] => do return .node 11 [(← term table left), (← term table right)]
  | _ => none
termination_by sizeOf input

/-- 任意有限表的重命名，恰好要求原项索引落在表长给出的源作用域内。 -/
theorem term_isSome (table : List Nat) (input : Tree) :
    (term table input).isSome = SchemaTerm.check table.length input := by
  cases input with
  | node tag fields =>
    cases tag with
    | succ _ => simp [term, SchemaTerm.check, ProjectDecode.term]
    | zero =>
      cases fields with
      | nil => simp [term, SchemaTerm.check, ProjectDecode.term]
      | cons head tail =>
        cases tail with
        | cons _ _ => simp [term, SchemaTerm.check, ProjectDecode.term]
        | nil =>
          cases head with
          | node index fields =>
            cases fields with
            | cons _ _ => simp [term, SchemaTerm.check, ProjectDecode.term, scalar]
            | nil =>
              by_cases h : index < table.length
              · simp [term, SchemaTerm.check, ProjectDecode.term, scalar, h]
              · simp [term, SchemaTerm.check, ProjectDecode.term, scalar, h]

@[simp] theorem term_encode_rename {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth) (input : Project.Term sourceDepth)
    (hClosed : input.freeSupport = []) :
    term (encodeMap indexMap) (ProjectEncode.term input) =
      some (ProjectEncode.term (input.rename indexMap)) := by
  cases input with
  | bound index =>
      change term (encodeMap indexMap) (.node 0 [leaf index.val]) =
        some (Tree.node 0 [leaf (indexMap index).val])
      simp [term, encodeMap, leaf, index.isLt]
  | free _ => cases hClosed

/-- 原始树递归与类型化重命名逐构造子交换，量词分支使用提升后的同一张表。 -/
theorem formula_encode_rename {sourceDepth targetDepth : Nat}
    (indexMap : Fin sourceDepth → Fin targetDepth) (input : Project.Formula 1 sourceDepth)
    (hClosed : input.FreeClosed) :
    formula (encodeMap indexMap) (ProjectEncode.formula input) =
      some (ProjectEncode.formula (input.rename indexMap)) := by
  induction input generalizing targetDepth with
  | falsum | truth =>
      rw [ProjectEncode.formula, formula.eq_def]
      rfl
  | mem left right =>
      simp only [Formula.FreeClosed] at hClosed
      rw [ProjectEncode.formula, formula.eq_def]
      change (term (encodeMap indexMap) (ProjectEncode.term left)).bind
        (fun l => (term (encodeMap indexMap) (ProjectEncode.term right)).bind
          (fun r => some (Tree.node 2 [l, r]))) = _
      rw [term_encode_rename indexMap left hClosed.1]
      dsimp only [Option.bind_some]
      rw [term_encode_rename indexMap right hClosed.2]
      rfl
  | atom symbol hStage args =>
      simp only [Formula.FreeClosed] at hClosed
      cases symbol <;> rw [ProjectEncode.formula, formula.eq_def]
      all_goals
        change (term (encodeMap indexMap) (ProjectEncode.term (args 0))).bind
          (fun l => (term (encodeMap indexMap) (ProjectEncode.term (args 1))).bind
            (fun r => some (Tree.node _ [l, r]))) = _
        rw [term_encode_rename indexMap (args 0) (hClosed 0)]
        dsimp only [Option.bind_some]
        rw [term_encode_rename indexMap (args 1) (hClosed 1)]
        simp [Definitional.Formula.rename, Definitional.Formula.bind, ProjectEncode.formula,
          Definitional.TermVector.get_bind, Project.Term.rename, Definitional.Term.rename]
  | neg body ih =>
      simp only [Formula.FreeClosed] at hClosed
      rw [ProjectEncode.formula, formula.eq_def]
      change (formula (encodeMap indexMap) (ProjectEncode.formula body)).bind
        (fun b => some (Tree.node 4 [b])) = _
      rw [ih indexMap hClosed]
      rfl
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      simp only [Formula.FreeClosed] at hClosed
      rw [ProjectEncode.formula, formula.eq_def]
      all_goals
        change (formula (encodeMap indexMap) (ProjectEncode.formula left)).bind
          (fun l => (formula (encodeMap indexMap) (ProjectEncode.formula right)).bind
            (fun r => some (Tree.node _ [l, r]))) = _
        rw [ihLeft indexMap hClosed.1]
        dsimp only [Option.bind_some]
        rw [ihRight indexMap hClosed.2]
        rfl
  | forallE body ih | existsE body ih =>
      simp only [Formula.FreeClosed] at hClosed
      rw [ProjectEncode.formula, formula.eq_def, lift_encodeMap]
      all_goals
        change (formula (encodeMap (BoundEmbedding.lift indexMap)) (ProjectEncode.formula body)).bind
          (fun b => some (Tree.node _ [b])) = _
        rw [ih (BoundEmbedding.lift indexMap) hClosed]
        simp only [Option.bind_some, Definitional.Formula.rename, Definitional.Formula.bind,
          QuineEncoding.project_lift_substitution_eq]
        rfl

private theorem unary_isSome {α β : Type} (input : Option α) (build : α → β) :
    (input.bind (fun value => some (build value))).isSome = input.isSome := by
  cases input <;> rfl

private theorem binary_isSome {α β γ : Type}
    (left : Option α) (right : Option β) (build : α → β → γ) :
    (left.bind (fun l => right.bind (fun r => some (build l r)))).isSome =
      (left.isSome && right.isSome) := by
  cases left <;> cases right <;> rfl

/-- 对所有原始输入，重命名成功恰好等价于源正文合法；畸形输入不能被修复后混入。 -/
theorem formula_isSome (table : List Nat) (input : Tree) :
    (formula table input).isSome = SchemaBody.check table.length input := by
  fun_induction formula table input
  all_goals rw [SchemaBody.check, ProjectDecode.formula.eq_def]
  all_goals dsimp only [bind, pure] at *
  all_goals simp_all only [binary_isSome, unary_isSome, Option.isSome_some, Option.isSome_none,
    term_isSome, SchemaTerm.check, SchemaBody.check]
  all_goals
    first
    | rfl
    | rename_i table body ih
      exact congrArg (fun depth => (ProjectDecode.formula depth body).isSome) (lift_length table)

theorem formula_eq_none_iff (table : List Nat) (input : Tree) :
    formula table input = none ↔ ProjectDecode.formula table.length input = none := by
  have h := Iff.of_eq (congrArg (fun value => value = false) (formula_isSome table input))
  simpa only [SchemaBody.check, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] using h

/-- 表中每个目标索引均须落在目标作用域内，即使该位置未在正文中使用。 -/
def valid (targetDepth : Nat) (table : List Nat) : Bool :=
  table.all (fun index => decide (index < targetDepth))

theorem valid_eq_true_iff (targetDepth : Nat) (table : List Nat) :
    valid targetDepth table = true ↔ ∀ index, index ∈ table → index < targetDepth := by
  have and_true : ∀ left right : Bool, (left && right) = true → left = true ∧ right = true := by
    intro left right h
    cases left <;> cases right <;> cases h <;> exact ⟨rfl, rfl⟩
  induction table with
  | nil =>
    constructor
    · intro _ index h
      cases h
    · intro _
      rfl
  | cons head tail ih =>
    constructor
    · intro h index hIndex
      have hParts := and_true _ _ h
      cases hIndex with
      | head => exact of_decide_eq_true hParts.1
      | tail _ hIndex => exact ih.mp hParts.2 index hIndex
    · intro h
      change (decide (head < targetDepth) && valid targetDepth tail) = true
      rw [decide_eq_true (h head (.head _)),
        ih.mpr (fun index hIndex => h index (.tail _ hIndex))]
      rfl

def indexMap (targetDepth : Nat) (table : List Nat) (hValid : valid targetDepth table = true) :
    Fin table.length → Fin targetDepth := fun index =>
  ⟨table[index.val]'index.isLt,
    (valid_eq_true_iff targetDepth table).mp hValid _ (List.getElem_mem index.isLt)⟩

@[simp] theorem encode_indexMap (targetDepth : Nat) (table : List Nat)
    (hValid : valid targetDepth table = true) :
    encodeMap (indexMap targetDepth table hValid) = table := by
  exact List.ofFn_getElem

@[simp] theorem valid_encodeMap {sourceDepth targetDepth : Nat}
    (mapping : Fin sourceDepth → Fin targetDepth) : valid targetDepth (encodeMap mapping) = true := by
  apply (valid_eq_true_iff targetDepth _).mpr
  intro index hIndex
  simp only [encodeMap, List.mem_ofFn] at hIndex
  obtain ⟨position, rfl⟩ := hIndex
  exact (mapping position).isLt

/-- 任意原始输入及候选输出的完整数据层图，含失败分支。 -/
theorem formula_eq_some_iff (targetDepth : Nat) (table : List Nat)
    (hValid : valid targetDepth table = true) (input output : Tree) :
    formula table input = some output ↔
      ∃ body : Project.Formula 1 table.length,
        body.FreeClosed ∧ ProjectEncode.formula body = input ∧
          ProjectEncode.formula (body.rename (indexMap targetDepth table hValid)) = output := by
  constructor
  · intro h
    have hSome : (formula table input).isSome = true := by rw [h]; rfl
    rw [formula_isSome] at hSome
    obtain ⟨body, hClosed, hCode⟩ := (SchemaBody.check_eq_true_iff table.length input).mp hSome
    have hOutput := formula_encode_rename (indexMap targetDepth table hValid) body hClosed
    rw [encode_indexMap, hCode] at hOutput
    exact ⟨body, hClosed, hCode, Option.some.inj (hOutput.symm.trans h)⟩
  · rintro ⟨body, hClosed, hCode, hOutput⟩
    have h := formula_encode_rename (indexMap targetDepth table hValid) body hClosed
    simpa only [encode_indexMap, hCode, hOutput] using h

/-- 解码与重命名对整个 `Option` 结果交换，不以解析成功为假设。 -/
theorem decode_formula (targetDepth : Nat) (table : List Nat)
    (hValid : valid targetDepth table = true) (input : Tree) :
    (formula table input).bind (ProjectDecode.formula targetDepth) =
      (ProjectDecode.formula table.length input).map
        (fun body => body.rename (indexMap targetDepth table hValid)) := by
  cases hInput : ProjectDecode.formula table.length input with
  | none =>
      have hNone := (formula_eq_none_iff table input).mpr hInput
      simp only [hNone, Option.bind_none, Option.map_none]
  | some body =>
      obtain ⟨hClosed, hCode⟩ := SchemaBody.decode_spec table.length input body hInput
      have hOutput := formula_encode_rename (indexMap targetDepth table hValid) body hClosed
      rw [encode_indexMap, hCode] at hOutput
      rw [hOutput]
      simp only [Option.bind_some, Option.map_some]
      exact ProjectEncode.formula_roundtrip _
        ((Definitional.Formula.freeClosed_rename _ body).mpr hClosed)

/-- 完整执行入口先检查目标表，再递归检查和重命名原始正文。 -/
def run (targetDepth : Nat) (table : List Nat) (input : Tree) : Option Tree :=
  if valid targetDepth table then formula table input else none

theorem run_isSome (targetDepth : Nat) (table : List Nat) (input : Tree) :
    (run targetDepth table input).isSome =
      (valid targetDepth table && SchemaBody.check table.length input) := by
  unfold run
  cases valid targetDepth table <;> simp [formula_isSome]

theorem run_reject_iff (targetDepth : Nat) (table : List Nat) (input : Tree) :
    (run targetDepth table input).isSome = false ↔
      valid targetDepth table = false ∨ SchemaBody.check table.length input = false := by
  rw [run_isSome, Bool.and_eq_false_iff]

/-- 加上目标表检查之后，仍然逐构造子得到原类型化重命名结果。 -/
theorem run_encode_rename {sourceDepth targetDepth : Nat}
    (mapping : Fin sourceDepth → Fin targetDepth) (input : Project.Formula 1 sourceDepth)
    (hClosed : input.FreeClosed) :
    run targetDepth (encodeMap mapping) (ProjectEncode.formula input) =
      some (ProjectEncode.formula (input.rename mapping)) := by
  simpa only [run, valid_encodeMap, ↓reduceIte] using formula_encode_rename mapping input hClosed

/-- 对任意候选输出，图的成功判准同时包含目标表合法性和完整正文规格。 -/
theorem run_eq_some_iff (targetDepth : Nat) (table : List Nat) (input output : Tree) :
    run targetDepth table input = some output ↔
      ∃ hValid : valid targetDepth table = true,
        ∃ body : Project.Formula 1 table.length,
          body.FreeClosed ∧ ProjectEncode.formula body = input ∧
            ProjectEncode.formula (body.rename (indexMap targetDepth table hValid)) = output := by
  by_cases hValid : valid targetDepth table = true
  · rw [show run targetDepth table input = formula table input by simp [run, hValid]]
    constructor
    · intro h
      exact ⟨hValid, (formula_eq_some_iff targetDepth table hValid input output).mp h⟩
    · rintro ⟨hValid, h⟩
      exact (formula_eq_some_iff targetDepth table hValid input output).mpr h
  · simp [run, hValid]

/-- 固定合法目标表后，任意错误候选输出的拒绝等价于排除所有可能的源正文。 -/
theorem run_ne_some_iff (targetDepth : Nat) (table : List Nat)
    (hValid : valid targetDepth table = true) (input output : Tree) :
    run targetDepth table input ≠ some output ↔
      ∀ body : Project.Formula 1 table.length, body.FreeClosed → ProjectEncode.formula body = input →
        ProjectEncode.formula (body.rename (indexMap targetDepth table hValid)) ≠ output := by
  have h := not_congr (formula_eq_some_iff targetDepth table hValid input output)
  simpa only [run, hValid, ↓reduceIte, not_exists, not_and] using h

/-- 任意输入的有限表重命名，直接与类型安全内核的 AST 重命名交换。 -/
theorem run_intrinsic (targetDepth : Nat) (table : List Nat)
    (hValid : valid targetDepth table = true) (input : Tree) :
    (run targetDepth table input).bind (SchemaBody.intrinsic targetDepth) =
      (SchemaBody.intrinsic table.length input).map
        (fun body => body.renameMapped
          (QuineEncoding.project_bound_renaming (indexMap targetDepth table hValid))
          VariableRenaming.id) := by
  simp only [run, hValid, ↓reduceIte]
  cases hInput : ProjectDecode.formula table.length input with
  | none =>
      have hNone := (formula_eq_none_iff table input).mpr hInput
      have hIntrinsic := (SchemaBody.intrinsic_eq_none_iff table.length input).mpr hInput
      simp only [hNone, hIntrinsic, Option.bind_none, Option.map_none]
  | some body =>
      obtain ⟨hClosed, hCode⟩ := SchemaBody.decode_spec table.length input body hInput
      have hOutput := formula_encode_rename (indexMap targetDepth table hValid) body hClosed
      rw [encode_indexMap, hCode] at hOutput
      rw [hOutput, Option.bind_some]
      rw [SchemaBody.intrinsic_encode _ _ ((Definitional.Formula.freeClosed_rename _ body).mpr hClosed)]
      have hIntrinsic : SchemaBody.intrinsic table.length input =
          some (QuineEncoding.project_formula body hClosed) := by
        rw [← hCode, SchemaBody.intrinsic_encode _ _ hClosed]
      rw [hIntrinsic, Option.map_some, QuineEncoding.project_formula_rename]

/-- 新 quotation 直接引用上述实际 AST；整个交换律也覆盖解析失败的输入。 -/
theorem run_quotation (targetDepth : Nat) (table : List Nat)
    (hValid : valid targetDepth table = true) (input : Tree) :
    ((run targetDepth table input).bind (SchemaBody.intrinsic targetDepth)).map IntrinsicQuotation.quote =
      (SchemaBody.intrinsic table.length input).map
        (fun body => IntrinsicQuotation.quote (body.renameMapped
          (QuineEncoding.project_bound_renaming (indexMap targetDepth table hValid))
          VariableRenaming.id)) := by
  rw [run_intrinsic targetDepth table hValid]
  simp only [Option.map_map, Function.comp_def]

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaRename
