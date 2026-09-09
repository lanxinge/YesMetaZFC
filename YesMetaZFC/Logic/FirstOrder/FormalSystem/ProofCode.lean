import Lean
/-!
# Hilbert 证明序列的可计算编码
本模块只保留证明序列的外部自然数编码，不定义对象层的理论成员证明谓词。Gödel 配对值严格
复刻对象语言 `godel_pairing_condition` 的两个分支：
`pair(a,b) = b²+a`（`a<b`），否则为 `a²+a+b`。
有限自然数序列从 `0` 开始，按原顺序反复执行
`acc ↦ pair(acc,item)+1`。额外的后继标签保证空序列代码为 `0`，非空序列代码
严格为正，从而可以唯一反向拆出最后一项。证明序列则先逐行编码，再编码所得自然数
列表。
这里证明配对函数、自然数序列编码以及证明序列编码的单射性。对象语言表示正确性
由后续元理论模块把这些可计算值与标准有限序列轨迹连接。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofCode

/-! ## Gödel 配对 -/
/-- 对象语言 Gödel 配对函数在标准自然数上的可计算值。 -/
def godel_pair_value (left right : Nat) :
    Nat :=
  if left < right then
    right ^ 2 + left
  else
    left ^ 2 + left + right
/-- 配对值所在平方壳层的下界。 -/
theorem max_square_le_godel_pair_value (left right : Nat) :
    max left right ^ 2 ≤
      godel_pair_value left right := by
  by_cases hOrder : left < right
  · have hMax : max left right = right := by
      omega
    simp [godel_pair_value, hOrder, hMax]
  · have hMax : max left right = left := by
      omega
    simp [godel_pair_value, hOrder, hMax]
    omega
/-- 配对值严格落在下一平方数之前。 -/
theorem godel_pair_value_lt_max_succ_square (left right : Nat) :
    godel_pair_value left right < (max left right + 1) ^ 2 := by
  by_cases hOrder : left < right
  · have hMax : max left right = right := by
      omega
    simp only [godel_pair_value, hOrder, if_pos, hMax]
    simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
    omega
  · have hReverse : right ≤ left := by
      omega
    have hMax : max left right = left := by
      omega
    simp [godel_pair_value, hOrder, hMax]
    simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
    omega
/-- 相等的配对值必定位于同一个平方壳层。 -/
theorem max_eq_of_godel_pair_value_eq
    {left₁ right₁ left₂ right₂ : Nat} (hCode :
      godel_pair_value left₁ right₁ =
        godel_pair_value left₂ right₂) :
    max left₁ right₁ = max left₂ right₂ := by
  let shell₁ := max left₁ right₁
  let shell₂ := max left₂ right₂
  have hLower₁ :=
    max_square_le_godel_pair_value left₁ right₁
  have hLower₂ :=
    max_square_le_godel_pair_value left₂ right₂
  have hUpper₁ :=
    godel_pair_value_lt_max_succ_square left₁ right₁
  have hUpper₂ :=
    godel_pair_value_lt_max_succ_square left₂ right₂
  by_cases hShell : shell₁ = shell₂
  · exact hShell
  · rcases Nat.lt_or_gt_of_ne hShell with
      hShellLt | hShellGt
    · have hSquares : (shell₁ + 1) ^ 2 ≤ shell₂ ^ 2 := by
        have hSucc : shell₁ + 1 ≤ shell₂ := by
          omega
        simpa [Nat.pow_succ] using
          Nat.mul_le_mul hSucc hSucc
      have hStrict :
          godel_pair_value left₁ right₁ <
            godel_pair_value left₂ right₂ := by
        exact Nat.lt_of_lt_of_le hUpper₁ (Nat.le_trans (by
            simpa [shell₁, shell₂] using hSquares)
            hLower₂)
      exact False.elim ((Nat.ne_of_lt hStrict) hCode)
    · have hSquares : (shell₂ + 1) ^ 2 ≤ shell₁ ^ 2 := by
        have hSucc : shell₂ + 1 ≤ shell₁ := by
          omega
        simpa [Nat.pow_succ] using
          Nat.mul_le_mul hSucc hSucc
      have hStrict :
          godel_pair_value left₂ right₂ <
            godel_pair_value left₁ right₁ := by
        exact Nat.lt_of_lt_of_le hUpper₂ (Nat.le_trans (by
            simpa [shell₁, shell₂] using hSquares)
            hLower₁)
      exact False.elim ((Nat.ne_of_lt hStrict) hCode.symm)
/-- Gödel 配对值相等当且仅当两个坐标分别相等。 -/
theorem godel_pair_value_eq_iff
    {left₁ right₁ left₂ right₂ : Nat} :
    godel_pair_value left₁ right₁ =
        godel_pair_value left₂ right₂ ↔
      left₁ = left₂ ∧ right₁ = right₂ := by
  constructor
  · intro hCode
    have hMax :=
      max_eq_of_godel_pair_value_eq hCode
    by_cases hOrder₁ : left₁ < right₁
    · have hOrder₂ : left₂ < right₂ := by
        by_cases hOrder₂ : left₂ < right₂
        · exact hOrder₂
        · have hReverse₂ : right₂ ≤ left₂ := by
            omega
          have hRight₁ : max left₁ right₁ = right₁ := by
            omega
          have hLeft₂ : max left₂ right₂ = left₂ := by
            omega
          have hShell : right₁ = left₂ := by
            omega
          subst left₂
          simp [godel_pair_value, hOrder₁, hOrder₂] at hCode
          omega
      have hRight₁ : max left₁ right₁ = right₁ := by
        omega
      have hRight₂ : max left₂ right₂ = right₂ := by
        omega
      have hRight : right₁ = right₂ := by
        omega
      subst right₂
      have hLeft : left₁ = left₂ := by
        simp [godel_pair_value, hOrder₁, hOrder₂] at hCode
        omega
      exact ⟨hLeft, rfl⟩
    · have hReverse₁ : right₁ ≤ left₁ := by
        omega
      have hOrder₂ : ¬left₂ < right₂ := by
        intro hOrder₂
        have hLeft₁ : max left₁ right₁ = left₁ := by
          omega
        have hRight₂ : max left₂ right₂ = right₂ := by
          omega
        have hShell : left₁ = right₂ := by
          omega
        subst right₂
        simp [godel_pair_value, hOrder₁, hOrder₂] at hCode
        omega
      have hReverse₂ : right₂ ≤ left₂ := by
        omega
      have hLeft₁ : max left₁ right₁ = left₁ := by
        omega
      have hLeft₂ : max left₂ right₂ = left₂ := by
        omega
      have hLeft : left₁ = left₂ := by
        omega
      subst left₂
      have hRight : right₁ = right₂ := by
        simp [godel_pair_value, hOrder₁, hOrder₂] at hCode
        omega
      exact ⟨rfl, hRight⟩
  · intro hCoordinates
    rcases hCoordinates with ⟨rfl, rfl⟩
    rfl
/-- Gödel 配对是二元自然数上的单射。 -/
theorem godel_pair_value_injective :
    Function.Injective (fun pair : Nat × Nat =>
        godel_pair_value pair.1 pair.2) := by
  rintro ⟨left₁, right₁⟩ ⟨left₂, right₂⟩ hCode
  rcases godel_pair_value_eq_iff.mp hCode with
    ⟨rfl, rfl⟩
  rfl
/--
Gödel 反配对的一步。
坐标严格按配对值的平方壳层顺序推进：先枚举
`(0,k), …, (k-1,k)`，再枚举 `(k,0), …, (k,k)`。
-/
def godel_unpair_next : Nat × Nat → Nat × Nat
  | (left, right) =>
      if left < right then
        if left + 1 < right then
          (left + 1, right)
        else
          (right, 0)
      else if right < left then
        (left, right + 1)
      else
        (0, left + 1)
/--
规范 Gödel 反配对的可计算实现。
从 `(0,0)` 出发逐步遍历平方壳层，因此不使用经典选择，也不依赖平方根。
-/
def godel_unpair_value : Nat → Nat × Nat
  | 0 => (0, 0)
  | code + 1 =>
      godel_unpair_next (godel_unpair_value code)
/-- 规范反配对重新配对后恢复原代码。 -/
theorem godel_unpair_value_spec (code : Nat) :
    godel_pair_value (godel_unpair_value code).1 (godel_unpair_value code).2 =
      code := by
  induction code with
  | zero =>
      simp [godel_unpair_value, godel_pair_value]
  | succ code ih =>
      rcases hPair : godel_unpair_value code with
        ⟨left, right⟩
      have hCode :
          godel_pair_value left right = code := by
        simpa [hPair] using ih
      by_cases hOrder : left < right
      · by_cases hGap : left + 1 < right
        · simp only [godel_unpair_value, godel_unpair_next,
            hPair, hOrder, hGap, if_pos]
          simp only [godel_pair_value, hOrder, if_pos] at hCode
          simp only [godel_pair_value, hGap, if_pos]
          omega
        · have hAdjacent : left + 1 = right := by
            omega
          simp only [godel_unpair_value, godel_unpair_next,
            hPair, hOrder, hGap, if_pos, if_false]
          subst right
          simp only [godel_pair_value,
            Nat.not_lt_zero, if_false]
          simp only [godel_pair_value,
            hOrder, if_pos] at hCode
          simp [Nat.pow_succ, Nat.mul_add,
            Nat.add_mul] at hCode ⊢
          omega
      · have hReverse : right ≤ left := by
          omega
        by_cases hGap : right < left
        · have hNextOrder : ¬left < right + 1 := by
            omega
          simp only [godel_unpair_value, godel_unpair_next,
            hPair, hOrder, hGap, if_false, if_pos]
          simp only [godel_pair_value,
            hOrder, if_false] at hCode
          simp only [godel_pair_value,
            hNextOrder, if_false]
          omega
        · have hEqual : right = left := by
            omega
          simp only [godel_unpair_value, godel_unpair_next,
            hPair, hOrder, hGap, if_false]
          subst right
          simp only [godel_pair_value,
            hOrder, if_false] at hCode
          simp only [godel_pair_value,
            Nat.zero_lt_succ, if_pos]
          simp [Nat.pow_succ, Nat.mul_add,
            Nat.add_mul] at hCode ⊢
          omega
/-- Gödel 配对覆盖全部自然数。 -/
theorem godel_pair_value_surjective :
    Function.Surjective (fun pair : Nat × Nat =>
        godel_pair_value pair.1 pair.2) := by
  intro code
  exact ⟨godel_unpair_value code,
    godel_unpair_value_spec code⟩
/-- 规范反配对是 Gödel 配对的左逆。 -/
theorem godel_unpair_value_pair (left right : Nat) :
    godel_unpair_value (godel_pair_value left right) =
      (left, right) := by
  apply Prod.ext
  · exact (godel_pair_value_eq_iff.mp
      (godel_unpair_value_spec (godel_pair_value left right))).1
  · exact (godel_pair_value_eq_iff.mp
      (godel_unpair_value_spec (godel_pair_value left right))).2
/-- Gödel 配对值不小于左坐标。 -/
theorem left_le_godel_pair_value (left right : Nat) :
    left ≤ godel_pair_value left right := by
  by_cases hOrder : left < right
  · simp [godel_pair_value, hOrder]
  · simp [godel_pair_value, hOrder]
    omega
/-- Gödel 配对值不小于右坐标。 -/
theorem right_le_godel_pair_value (left right : Nat) :
    right ≤ godel_pair_value left right := by
  by_cases hOrder : left < right
  · have hRightPositive : 0 < right := by
      omega
    have hSquare : right ≤ right ^ 2 := by
      calc
        right = right * 1 := by simp
        _ ≤ right * right :=
          Nat.mul_le_mul_left right hRightPositive
        _ = right ^ 2 := by simp [Nat.pow_succ]
    simp only [godel_pair_value, hOrder, if_pos]
    omega
  · simp [godel_pair_value, hOrder]
/-- 规范反配对的左分量不超过原代码。 -/
theorem godel_unpair_value_left_le (code : Nat) : (godel_unpair_value code).1 ≤ code := by
  calc (godel_unpair_value code).1 ≤
        godel_pair_value (godel_unpair_value code).1 (godel_unpair_value code).2 :=
      left_le_godel_pair_value _ _
    _ = code := godel_unpair_value_spec code
/-- 规范反配对的右分量不超过原代码。 -/
theorem godel_unpair_value_right_le (code : Nat) : (godel_unpair_value code).2 ≤ code := by
  calc (godel_unpair_value code).2 ≤
        godel_pair_value (godel_unpair_value code).1 (godel_unpair_value code).2 :=
      right_le_godel_pair_value _ _
    _ = code := godel_unpair_value_spec code
/-! ## 自然数有限序列折叠 -/
/-- 数值序列编码的一步。 -/
def nat_sequence_code_step (accumulator item : Nat) :
    Nat :=
  Nat.succ (godel_pair_value accumulator item)
/-- 每次序列折叠都严格增大当前累积代码。 -/
theorem accumulator_lt_nat_sequence_code_step (accumulator item : Nat) :
    accumulator <
      nat_sequence_code_step accumulator item := by
  exact Nat.lt_succ_of_le (left_le_godel_pair_value accumulator item)
/-- 每次序列折叠后的代码也严格大于本次写入的元素。 -/
theorem item_lt_nat_sequence_code_step (accumulator item : Nat) :
    item < nat_sequence_code_step accumulator item := by
  exact Nat.lt_succ_of_le (right_le_godel_pair_value accumulator item)
/-- 从给定初值开始，按原顺序折叠自然数有限序列。 -/
def nat_sequence_code_from (seed : Nat) (sequence : List Nat) :
    Nat :=
  sequence.foldl nat_sequence_code_step seed
/-- 自然数有限序列的规范证明码值。 -/
def nat_sequence_code_value (sequence : List Nat) :
    Nat :=
  nat_sequence_code_from 0 sequence
/-- 从任意初值开始折叠后，最终代码不小于初值。 -/
theorem seed_le_nat_sequence_code_from (seed : Nat) (sequence : List Nat) :
    seed ≤ nat_sequence_code_from seed sequence := by
  induction sequence generalizing seed with
  | nil =>
      exact Nat.le_refl seed
  | cons item rest ih =>
      change
        seed ≤
          nat_sequence_code_from (nat_sequence_code_step seed item) rest
      exact Nat.le_trans (Nat.le_of_lt (accumulator_lt_nat_sequence_code_step seed item)) (ih (seed := nat_sequence_code_step seed item))
/--
每次折叠至少把累积代码增加一，因此“初值加序列长度”仍不超过最终代码。
-/
theorem seed_add_length_le_nat_sequence_code_from (seed : Nat) (sequence : List Nat) :
    seed + sequence.length ≤
      nat_sequence_code_from seed sequence := by
  induction sequence generalizing seed with
  | nil =>
      simp [nat_sequence_code_from]
  | cons item rest ih =>
      change
        seed + (rest.length + 1) ≤
          nat_sequence_code_from (nat_sequence_code_step seed item) rest
      have hStep :
          seed + 1 ≤
            nat_sequence_code_step seed item := by
        have hStrict :=
          accumulator_lt_nat_sequence_code_step seed item
        omega
      have hRest :=
        ih (seed := nat_sequence_code_step seed item)
      omega
/-- 规范自然数序列代码控制源序列的长度。 -/
theorem nat_sequence_length_le_code (sequence : List Nat) :
    sequence.length ≤ nat_sequence_code_value sequence := by
  simpa [nat_sequence_code_value] using
    seed_add_length_le_nat_sequence_code_from 0 sequence
/-- 源序列中的每个元素都严格小于最终折叠代码。 -/
theorem mem_lt_nat_sequence_code_from
    {seed item : Nat} {sequence : List Nat} (hItem : item ∈ sequence) :
    item < nat_sequence_code_from seed sequence := by
  induction sequence generalizing seed with
  | nil =>
      simp at hItem
  | cons head rest ih =>
      rcases List.mem_cons.mp hItem with
        hHead | hRest
      · subst item
        exact Nat.lt_of_lt_of_le (item_lt_nat_sequence_code_step seed head) (seed_le_nat_sequence_code_from (nat_sequence_code_step seed head) rest)
      · exact ih (seed := nat_sequence_code_step seed head)
          hRest
/-- 规范自然数序列中的每个元素都严格小于其序列代码。 -/
theorem mem_lt_nat_sequence_code_value
    {item : Nat} {sequence : List Nat} (hItem : item ∈ sequence) :
    item < nat_sequence_code_value sequence := by
  exact mem_lt_nat_sequence_code_from (seed := 0) hItem
/-- 为单射证明使用的逆序递归视图。 -/
private def nat_sequence_reverse_code_from (seed : Nat) :
    List Nat → Nat
  | [] => seed
  | item :: rest =>
      nat_sequence_code_step (nat_sequence_reverse_code_from seed rest) item
/-- 逆序递归在尾部追加一项等价于先更新初值。 -/
private theorem nat_sequence_reverse_code_from_append_singleton (seed item : Nat) (sequence : List Nat) :
    nat_sequence_reverse_code_from seed (sequence ++ [item]) =
      nat_sequence_reverse_code_from (nat_sequence_code_step seed item) sequence := by
  induction sequence with
  | nil =>
      rfl
  | cons head tail ih =>
      simp only [List.cons_append,
        nat_sequence_reverse_code_from]
      rw [ih]
/-- 左折叠等于逆序列表上的递归视图。 -/
private theorem nat_sequence_code_from_eq_reverse_code (seed : Nat) (sequence : List Nat) :
    nat_sequence_code_from seed sequence =
      nat_sequence_reverse_code_from seed sequence.reverse := by
  induction sequence generalizing seed with
  | nil =>
      rfl
  | cons head tail ih =>
      change
        nat_sequence_code_from (nat_sequence_code_step seed head) tail =
          nat_sequence_reverse_code_from seed (head :: tail).reverse
      rw [ih]
      simp only [List.reverse_cons]
      rw [nat_sequence_reverse_code_from_append_singleton]
/-- 空序列的规范代码为 `0`。 -/
@[simp]
theorem nat_sequence_code_value_nil :
    nat_sequence_code_value [] = 0 :=
  rfl
/-- 在序列尾部追加一项时的编码递归方程。 -/
@[simp]
theorem nat_sequence_code_value_append_singleton (sequence : List Nat) (item : Nat) :
    nat_sequence_code_value (sequence ++ [item]) =
      nat_sequence_code_step (nat_sequence_code_value sequence) item := by
  simp [nat_sequence_code_value, nat_sequence_code_from,
    List.foldl_append]
/-! ## 自然数序列编码的规范轨迹 -/
/--
从给定初值开始的规范前缀编码轨迹。
轨迹第 `i` 项是源序列前 `i` 项的折叠值，因此轨迹总比源序列多一个位置。
-/
def nat_sequence_code_trace_from (seed : Nat) :
    List Nat → List Nat
  | [] => [seed]
  | item :: rest =>
      seed ::
        nat_sequence_code_trace_from (nat_sequence_code_step seed item) rest
/-- 从初值 `0` 开始的规范自然数序列编码轨迹。 -/
def nat_sequence_code_trace (sequence : List Nat) :
    List Nat :=
  nat_sequence_code_trace_from 0 sequence
/-- 原递归轨迹与通用列表扫描相同，后续结构性质复用扫描代数。 -/
theorem nat_sequence_code_trace_from_eq_scanl (seed : Nat) (sequence : List Nat) :
    nat_sequence_code_trace_from seed sequence =
      sequence.scanl nat_sequence_code_step seed := by
  induction sequence generalizing seed with
  | nil => rfl
  | cons head tail ih =>
      simp only [nat_sequence_code_trace_from, List.scanl_cons, ih]
/-- 规范轨迹的长度恰为源序列长度加一。 -/
@[simp]
theorem nat_sequence_code_trace_from_length (seed : Nat) (sequence : List Nat) : (nat_sequence_code_trace_from seed sequence).length =
      sequence.length + 1 := by
  rw [nat_sequence_code_trace_from_eq_scanl, List.length_scanl]
/-- 初值为零时的规范轨迹长度。 -/
@[simp]
theorem nat_sequence_code_trace_length (sequence : List Nat) : (nat_sequence_code_trace sequence).length =
      sequence.length + 1 := by
  simp [nat_sequence_code_trace]
/--
规范轨迹第 `index` 项等于源序列前 `index` 项从 `seed` 开始的折叠值。
-/
theorem nat_sequence_code_trace_from_getElem? (seed : Nat) (sequence : List Nat) (index : Nat) (hIndex : index ≤ sequence.length) :
    (nat_sequence_code_trace_from seed sequence)[index]? =
      some (nat_sequence_code_from seed (sequence.take index)) := by
  simp only [nat_sequence_code_trace_from_eq_scanl, List.getElem?_scanl,
    hIndex, if_true, nat_sequence_code_from]
/-- 规范轨迹的最后一项就是整个源序列的折叠值。 -/
theorem nat_sequence_code_trace_from_last (seed : Nat) (sequence : List Nat) : (nat_sequence_code_trace_from seed sequence)[sequence.length]? =
      some (nat_sequence_code_from seed sequence) := by
  simpa using
    nat_sequence_code_trace_from_getElem?
      seed sequence sequence.length (by omega)
/-- 初值为零时，规范轨迹的最后一项就是规范序列代码。 -/
theorem nat_sequence_code_trace_last (sequence : List Nat) : (nat_sequence_code_trace sequence)[sequence.length]? =
      some (nat_sequence_code_value sequence) := by
  simpa [nat_sequence_code_trace,
    nat_sequence_code_value] using
    nat_sequence_code_trace_from_last 0 sequence
/--
若源序列第 `index` 项为 `item`，轨迹下一项就是当前前缀代码与 `item` 的编码一步。
-/
theorem nat_sequence_code_trace_from_step (seed : Nat) (sequence : List Nat) (index item : Nat) (hItem : sequence[index]? = some item) :
    (nat_sequence_code_trace_from seed sequence)[index + 1]? =
      some (nat_sequence_code_step (nat_sequence_code_from seed (sequence.take index))
          item) := by
  obtain ⟨hIndex, _⟩ := List.getElem_of_getElem? hItem
  rw [nat_sequence_code_trace_from_eq_scanl, List.getElem?_succ_scanl,
    ← nat_sequence_code_trace_from_eq_scanl,
    nat_sequence_code_trace_from_getElem? seed sequence index
      (Nat.le_of_lt hIndex), hItem]
  rfl
/-- 初值为零时的规范轨迹递归步。 -/
theorem nat_sequence_code_trace_step (sequence : List Nat) (index item : Nat) (hItem : sequence[index]? = some item) :
    (nat_sequence_code_trace sequence)[index + 1]? =
      some (nat_sequence_code_step (nat_sequence_code_from 0 (sequence.take index))
          item) := by
  simpa [nat_sequence_code_trace] using
    nat_sequence_code_trace_from_step
      0 sequence index item hItem
/--
规范轨迹中的每个前缀代码都不超过同一折叠过程的最终代码。
-/
theorem trace_mem_le_nat_sequence_code_from
    {seed value : Nat} {sequence : List Nat} (hValue :
      value ∈ nat_sequence_code_trace_from seed sequence) :
    value ≤ nat_sequence_code_from seed sequence := by
  induction sequence generalizing seed with
  | nil =>
      simp [nat_sequence_code_trace_from] at hValue
      subst value
      exact Nat.le_refl seed
  | cons item rest ih =>
      rcases List.mem_cons.mp hValue with
        hSeed | hRest
      · subst value
        exact seed_le_nat_sequence_code_from seed (item :: rest)
      · exact ih (seed := nat_sequence_code_step seed item)
          hRest
/-- 初值为零时，规范轨迹完全受最终序列代码控制。 -/
theorem trace_mem_le_nat_sequence_code_value
    {value : Nat} {sequence : List Nat} (hValue : value ∈ nat_sequence_code_trace sequence) :
    value ≤ nat_sequence_code_value sequence := by
  exact trace_mem_le_nat_sequence_code_from (seed := 0) hValue
/-- 任意前缀的折叠代码都不超过整条序列的折叠代码。 -/
theorem take_code_le_nat_sequence_code_from (seed : Nat) (sequence : List Nat) (index : Nat) (hIndex : index ≤ sequence.length) :
    nat_sequence_code_from seed (sequence.take index) ≤
      nat_sequence_code_from seed sequence := by
  have hLookup :=
    nat_sequence_code_trace_from_getElem?
      seed sequence index hIndex
  exact trace_mem_le_nat_sequence_code_from (List.mem_of_getElem? hLookup)
/-- 初值为零时的前缀代码界。 -/
theorem take_code_le_nat_sequence_code_value (sequence : List Nat) (index : Nat) (hIndex : index ≤ sequence.length) :
    nat_sequence_code_value (sequence.take index) ≤
      nat_sequence_code_value sequence := by
  simpa [nat_sequence_code_value] using
    take_code_le_nat_sequence_code_from
      0 sequence index hIndex
/-- 正初值经过任意有限折叠后仍为正。 -/
private theorem nat_sequence_code_from_pos_of_pos_seed (seed : Nat) (sequence : List Nat) (hSeed : 0 < seed) :
    0 < nat_sequence_code_from seed sequence := by
  induction sequence generalizing seed with
  | nil =>
      exact hSeed
  | cons head tail ih =>
      change
        0 <
          nat_sequence_code_from (nat_sequence_code_step seed head) tail
      exact ih _ (Nat.succ_pos _)
/-- 每个非空序列的代码严格为正。 -/
theorem nat_sequence_code_value_pos_of_ne_nil
    {sequence : List Nat} (hSequence : sequence ≠ []) :
    0 < nat_sequence_code_value sequence := by
  cases sequence with
  | nil =>
      exact False.elim (hSequence rfl)
  | cons head tail =>
      change
        0 <
          nat_sequence_code_from (nat_sequence_code_step 0 head) tail
      exact nat_sequence_code_from_pos_of_pos_seed
        _ _ (Nat.succ_pos _)
/-- 固定初值 `0` 的逆序递归编码是单射。 -/
private theorem nat_sequence_reverse_code_injective :
    Function.Injective (nat_sequence_reverse_code_from 0) := by
  intro left
  induction left with
  | nil =>
      intro right hCode
      cases right with
      | nil =>
          rfl
      | cons head tail =>
          simp only [nat_sequence_reverse_code_from,
            nat_sequence_code_step] at hCode
          omega
  | cons head tail ih =>
      intro right hCode
      cases right with
      | nil =>
          simp only [nat_sequence_reverse_code_from,
            nat_sequence_code_step] at hCode
          omega
      | cons otherHead otherTail =>
          simp only [nat_sequence_reverse_code_from,
            nat_sequence_code_step] at hCode
          have hPair :
              godel_pair_value (nat_sequence_reverse_code_from 0 tail) head =
                godel_pair_value (nat_sequence_reverse_code_from 0 otherTail)
                  otherHead := by
            omega
          rcases godel_pair_value_eq_iff.mp hPair with
            ⟨hTailCode, hHead⟩
          have hTail := ih hTailCode
          subst otherTail
          subst otherHead
          rfl
/-- 自然数有限序列编码是单射。 -/
theorem nat_sequence_code_value_injective :
    Function.Injective nat_sequence_code_value := by
  intro left right hCode
  have hReverseCode :
      nat_sequence_reverse_code_from 0 left.reverse =
        nat_sequence_reverse_code_from 0 right.reverse := by
    rw [← nat_sequence_code_from_eq_reverse_code,
      ← nat_sequence_code_from_eq_reverse_code]
    exact hCode
  have hReverse :=
    nat_sequence_reverse_code_injective hReverseCode
  simpa using congrArg List.reverse hReverse
/-! ## 自然数有限序列的规范反演 -/
/--
从自然数代码规范解出唯一有限序列。
非零代码先去掉外层后继，再反配对为旧累积值与末项；旧累积值严格小于当前代码，
故该定义按代码良基递归终止。结果按末项追加恢复原来的正向折叠顺序。
-/
def nat_sequence_decode :
    Nat → List Nat
  | 0 => []
  | code + 1 =>
      let pair := godel_unpair_value code
      nat_sequence_decode pair.1 ++ [pair.2]
termination_by code => code
decreasing_by
  exact Nat.lt_succ_of_le (godel_unpair_value_left_le code)
/-- 规范解码再编码恢复原自然数代码。 -/
theorem nat_sequence_code_value_decode (code : Nat) :
    nat_sequence_code_value (nat_sequence_decode code) =
      code := by
  refine Nat.strongRecOn code ?_
  intro code ih
  cases code with
  | zero =>
      simp [nat_sequence_decode,
        nat_sequence_code_value,
        nat_sequence_code_from]
  | succ code =>
      rw [nat_sequence_decode]
      rw [nat_sequence_code_value_append_singleton]
      rw [ih (godel_unpair_value code).1 (Nat.lt_succ_of_le (godel_unpair_value_left_le code))]
      simp [nat_sequence_code_step,
        godel_unpair_value_spec]
/-- 规范编码再解码恢复原有限序列。 -/
theorem nat_sequence_decode_code_value (sequence : List Nat) :
    nat_sequence_decode (nat_sequence_code_value sequence) =
      sequence := by
  apply nat_sequence_code_value_injective
  exact nat_sequence_code_value_decode (nat_sequence_code_value sequence)
/-! ## 自然数序列编码的递归图 -/
/--
从给定初值开始的序列编码递归图。
构造子按源序列的正向顺序推进初值，因此与对象公式中从索引 `0` 到定义域末端的
轨迹完全同形。
-/
inductive NatSequenceCodeFrom :
    Nat → List Nat → Nat → Prop where
  | nil (seed : Nat) :
      NatSequenceCodeFrom seed [] seed
  | cons (seed item : Nat) {rest : List Nat} {code : Nat} (hRest :
        NatSequenceCodeFrom (nat_sequence_code_step seed item) rest code) :
      NatSequenceCodeFrom seed (item :: rest) code
/-- 以 `0` 为初值的规范自然数序列编码关系。 -/
abbrev NatSequenceCode (sequence : List Nat) (code : Nat) :
    Prop :=
  NatSequenceCodeFrom 0 sequence code
/-- 递归图恰好表示可计算的左折叠函数。 -/
theorem natseq_code_from_iff
    {seed code : Nat} {sequence : List Nat} :
    NatSequenceCodeFrom seed sequence code ↔
      code = nat_sequence_code_from seed sequence := by
  constructor
  · intro hCode
    induction hCode with
    | nil =>
        rfl
    | cons seed item hRest ih =>
        exact ih
  · intro hCode
    subst code
    induction sequence generalizing seed with
    | nil =>
        exact NatSequenceCodeFrom.nil seed
    | cons item rest ih =>
        exact NatSequenceCodeFrom.cons seed item (ih (seed :=
            nat_sequence_code_step seed item))
/-- 固定初值 `0` 时，递归关系等价于等于规范计算值。 -/
theorem natseq_code_iff
    {sequence : List Nat} {code : Nat} :
    NatSequenceCode sequence code ↔
      code = nat_sequence_code_value sequence :=
  natseq_code_from_iff
/-- 规范编码关系在给定序列上由规范计算值实现。 -/
theorem natseq_code_value_spec (sequence : List Nat) :
    NatSequenceCode sequence (nat_sequence_code_value sequence) := by
  exact natseq_code_iff.mpr rfl
/-- 自然数有限序列的递归编码总是存在。 -/
theorem natseq_code_exists (sequence : List Nat) :
    ∃ code, NatSequenceCode sequence code :=
  ⟨nat_sequence_code_value sequence,
    natseq_code_value_spec sequence⟩
/-- 自然数有限序列的递归编码是单值的。 -/
theorem natseq_code_functional
    {sequence : List Nat} {left right : Nat} (hLeft : NatSequenceCode sequence left) (hRight : NatSequenceCode sequence right) :
    left = right := by
  rw [natseq_code_iff] at hLeft hRight
  exact hLeft.trans hRight.symm
/-- 每个自然数有限序列存在唯一的递归编码。 -/
theorem natseq_code_exists_unique (sequence : List Nat) :
    ∃ code,
      NatSequenceCode sequence code ∧
        ∀ other,
          NatSequenceCode sequence other →
            other = code := by
  refine ⟨nat_sequence_code_value sequence,
    natseq_code_value_spec sequence, ?_⟩
  intro code hCode
  exact natseq_code_functional hCode (natseq_code_value_spec sequence)
/-- 规范递归编码关系在源序列参数上保持单射。 -/
theorem natseq_code_injective
    {left right : List Nat} {code : Nat} (hLeft : NatSequenceCode left code) (hRight : NatSequenceCode right code) :
    left = right := by
  rw [natseq_code_iff] at hLeft hRight
  apply nat_sequence_code_value_injective
  exact hLeft.symm.trans hRight
/-! ## 证明序列折叠 -/
/-- 从给定初值开始逐行编码证明序列。 -/
def proof_sequence_code_from (seed : Nat) (sequence : List (List Nat)) :
    Nat :=
  nat_sequence_code_from seed (sequence.map nat_sequence_code_value)
/-- 逐行编码后再编码整条有限证明序列。 -/
def proof_sequence_code_value (sequence : List (List Nat)) :
    Nat :=
  proof_sequence_code_from 0 sequence

/-- 在证明序列尾部追加一行时的二维编码递归方程。 -/
@[simp]
theorem proof_sequence_code_value_append_singleton
    (sequence : List (List Nat))
    (row : List Nat) :
    proof_sequence_code_value (sequence ++ [row]) =
      nat_sequence_code_step
        (proof_sequence_code_value sequence)
        (nat_sequence_code_value row) := by
  change
    nat_sequence_code_value
        ((sequence ++ [row]).map nat_sequence_code_value) =
      nat_sequence_code_step
        (nat_sequence_code_value
          (sequence.map nat_sequence_code_value))
        (nat_sequence_code_value row)
  rw [List.map_append, List.map_singleton,
    nat_sequence_code_value_append_singleton]

/-! ## 证明序列编码的规范轨迹 -/
/--
从给定初值开始的二维证明序列编码轨迹。
每一行先取一维规范代码，再复用自然数序列的前缀折叠轨迹；因此该定义与
`proof_sequence_code_step_condition` 的两级见证结构逐步对应。
-/
def proof_sequence_code_trace_from (seed : Nat) (sequence : List (List Nat)) :
    List Nat :=
  nat_sequence_code_trace_from seed (sequence.map nat_sequence_code_value)
/-- 初值为零的规范二维证明序列编码轨迹。 -/
def proof_sequence_code_trace (sequence : List (List Nat)) :
    List Nat :=
  proof_sequence_code_trace_from 0 sequence
/-- 二维规范轨迹的长度恰为证明序列长度加一。 -/
@[simp]
theorem proof_sequence_code_trace_from_length (seed : Nat) (sequence : List (List Nat)) : (proof_sequence_code_trace_from seed sequence).length =
      sequence.length + 1 := by
  simp [proof_sequence_code_trace_from]
/-- 初值为零时的二维规范轨迹长度。 -/
@[simp]
theorem proof_sequence_code_trace_length (sequence : List (List Nat)) : (proof_sequence_code_trace sequence).length =
      sequence.length + 1 := by
  simp [proof_sequence_code_trace]
/--
二维规范轨迹第 `index` 项是前 `index` 行从 `seed` 开始的折叠代码。
-/
theorem proof_sequence_code_trace_from_getElem? (seed : Nat) (sequence : List (List Nat)) (index : Nat) (hIndex : index ≤ sequence.length) :
    (proof_sequence_code_trace_from seed sequence)[index]? =
      some (proof_sequence_code_from seed (sequence.take index)) := by
  simpa [proof_sequence_code_trace_from,
    proof_sequence_code_from] using (nat_sequence_code_trace_from_getElem?
      seed (sequence.map nat_sequence_code_value)
      index (by simpa using hIndex))
/-- 二维规范轨迹的最后一项就是整条证明序列的折叠代码。 -/
theorem proof_sequence_code_trace_from_last (seed : Nat) (sequence : List (List Nat)) : (proof_sequence_code_trace_from seed sequence)[sequence.length]? =
      some (proof_sequence_code_from seed sequence) := by
  simpa using
    proof_sequence_code_trace_from_getElem?
      seed sequence sequence.length (by omega)
/-- 初值为零时，二维规范轨迹的最后一项就是规范证明序列代码。 -/
theorem proof_sequence_code_trace_last (sequence : List (List Nat)) : (proof_sequence_code_trace sequence)[sequence.length]? =
      some (proof_sequence_code_value sequence) := by
  simpa [proof_sequence_code_trace,
    proof_sequence_code_value] using
    proof_sequence_code_trace_from_last 0 sequence
/--
若第 `index` 行为 `row`，二维轨迹下一项由当前前缀代码与该行的一维代码组成。
-/
theorem proof_sequence_code_trace_from_step (seed : Nat) (sequence : List (List Nat)) (index : Nat) (row : List Nat) (hRow : sequence[index]? = some row) :
    (proof_sequence_code_trace_from seed sequence)[index + 1]? =
      some (nat_sequence_code_step (proof_sequence_code_from seed (sequence.take index)) (nat_sequence_code_value row)) := by
  have hRowCode : (sequence.map nat_sequence_code_value)[index]? =
        some (nat_sequence_code_value row) := by
    simpa using congrArg (Option.map nat_sequence_code_value) hRow
  simpa [proof_sequence_code_trace_from,
    proof_sequence_code_from] using (nat_sequence_code_trace_from_step
      seed (sequence.map nat_sequence_code_value)
      index (nat_sequence_code_value row) hRowCode)
/-- 初值为零时的二维规范轨迹递归步。 -/
theorem proof_sequence_code_trace_step (sequence : List (List Nat)) (index : Nat) (row : List Nat) (hRow : sequence[index]? = some row) :
    (proof_sequence_code_trace sequence)[index + 1]? =
      some (nat_sequence_code_step (proof_sequence_code_from 0 (sequence.take index)) (nat_sequence_code_value row)) := by
  simpa [proof_sequence_code_trace] using
    proof_sequence_code_trace_from_step
      0 sequence index row hRow
/-- 二维证明序列代码控制证明的行数。 -/
theorem proof_sequence_length_le_code (sequence : List (List Nat)) :
    sequence.length ≤ proof_sequence_code_value sequence := by
  simpa only [proof_sequence_code_value, proof_sequence_code_from,
    nat_sequence_code_value, List.length_map] using
    nat_sequence_length_le_code (sequence.map nat_sequence_code_value)
/-- 证明中的每个行代码都严格小于整条二维证明代码。 -/
theorem row_code_lt_proof_sequence_code_from
    {seed : Nat} {sequence : List (List Nat)}
    {row : List Nat} (hRow : row ∈ sequence) :
    nat_sequence_code_value row <
      proof_sequence_code_from seed sequence := by
  apply mem_lt_nat_sequence_code_from
  simpa using List.mem_map.mpr
    ⟨row, hRow, rfl⟩
/-- 初值为零时，每个行代码严格小于规范二维证明代码。 -/
theorem row_code_lt_proof_sequence_code_value
    {sequence : List (List Nat)} {row : List Nat} (hRow : row ∈ sequence) :
    nat_sequence_code_value row <
      proof_sequence_code_value sequence := by
  exact row_code_lt_proof_sequence_code_from (seed := 0) hRow
/--
证明行中的每个 token 都严格小于该行代码，进而严格小于整条二维证明代码。
-/
theorem token_lt_proof_sequence_code_value
    {sequence : List (List Nat)} {row : List Nat}
    {token : Nat} (hRow : row ∈ sequence) (hToken : token ∈ row) :
    token < proof_sequence_code_value sequence := by
  exact Nat.lt_trans (mem_lt_nat_sequence_code_value hToken) (row_code_lt_proof_sequence_code_value hRow)
/-- 每一行的长度都严格小于包含它的二维证明代码。 -/
theorem row_length_lt_proof_sequence_code_value
    {sequence : List (List Nat)} {row : List Nat} (hRow : row ∈ sequence) :
    row.length < proof_sequence_code_value sequence := by
  exact Nat.lt_of_le_of_lt (nat_sequence_length_le_code row) (row_code_lt_proof_sequence_code_value hRow)
/-- 二维规范轨迹中的每个前缀代码都受最终证明代码控制。 -/
theorem proof_trace_mem_le_proof_sequence_code_from
    {seed value : Nat}
    {sequence : List (List Nat)} (hValue :
      value ∈ proof_sequence_code_trace_from seed sequence) :
    value ≤ proof_sequence_code_from seed sequence := by
  exact trace_mem_le_nat_sequence_code_from hValue
/-- 初值为零时的二维规范轨迹界。 -/
theorem proof_trace_mem_le_proof_sequence_code_value
    {value : Nat} {sequence : List (List Nat)} (hValue : value ∈ proof_sequence_code_trace sequence) :
    value ≤ proof_sequence_code_value sequence := by
  exact proof_trace_mem_le_proof_sequence_code_from (seed := 0) hValue
/-- 任意证明前缀的二维代码都不超过整条证明的代码。 -/
theorem take_proof_code_le_proof_sequence_code_from (seed : Nat) (sequence : List (List Nat)) (index : Nat) (hIndex : index ≤ sequence.length) :
    proof_sequence_code_from seed (sequence.take index) ≤
      proof_sequence_code_from seed sequence := by
  simpa [proof_sequence_code_from] using
    take_code_le_nat_sequence_code_from
      seed (sequence.map nat_sequence_code_value)
      index (by simpa using hIndex)
/-- 初值为零时的证明前缀代码界。 -/
theorem take_proof_code_le_proof_sequence_code_value (sequence : List (List Nat)) (index : Nat) (hIndex : index ≤ sequence.length) :
    proof_sequence_code_value (sequence.take index) ≤
      proof_sequence_code_value sequence := by
  simpa [proof_sequence_code_value] using
    take_proof_code_le_proof_sequence_code_from
      0 sequence index hIndex
/-- 对列表逐项应用单射函数仍得到单射。 -/
private theorem list_map_injective_of_injective
    {α : Type u₁} {β : Type v₁} (function : α → β) (hFunction : Function.Injective function) :
    Function.Injective (List.map function) := by
  intro left
  induction left with
  | nil =>
      intro right hMap
      cases right with
      | nil =>
          rfl
      | cons head tail =>
          simp at hMap
  | cons head tail ih =>
      intro right hMap
      cases right with
      | nil =>
          simp at hMap
      | cons otherHead otherTail =>
          simp only [List.map_cons] at hMap
          have hParts := List.cons.inj hMap
          have hHead :=
            hFunction hParts.1
          have hTail := ih hParts.2
          subst otherHead
          subst otherTail
          rfl
/-- 逐项应用自然数序列编码保持列表单射。 -/
private theorem map_nat_sequence_code_value_injective :
    Function.Injective (List.map nat_sequence_code_value) :=
  list_map_injective_of_injective
    nat_sequence_code_value
    nat_sequence_code_value_injective
/-- 有限证明序列的二维自然数编码是单射。 -/
theorem proof_sequence_code_value_injective :
    Function.Injective proof_sequence_code_value := by
  intro left right hCode
  apply map_nat_sequence_code_value_injective
  apply nat_sequence_code_value_injective
  exact hCode
/-! ## 二维证明序列的规范反演 -/
/--
从二维证明码规范解出证明行 token 序列。
先把外层代码解为逐行自然数代码，再逐项复用一维解码。该定义与证明码的两层折叠
结构完全一致，可作为任意对象层证明序列见证的 canonical 比较目标。
-/
def proof_sequence_decode (code : Nat) :
    List (List Nat) := (nat_sequence_decode code).map
    nat_sequence_decode
/-- 规范二维解码再编码恢复原证明码。 -/
theorem proof_sequence_code_value_decode (code : Nat) :
    proof_sequence_code_value (proof_sequence_decode code) =
      code := by
  change
    nat_sequence_code_value (((nat_sequence_decode code).map
        nat_sequence_decode).map
          nat_sequence_code_value) =
      code
  rw [List.map_map]
  have hFunction :
      nat_sequence_code_value ∘
          nat_sequence_decode =
        id := by
    funext value
    exact nat_sequence_code_value_decode value
  rw [hFunction]
  simpa using nat_sequence_code_value_decode code
/-- 规范二维编码再解码恢复原证明序列。 -/
theorem proof_sequence_decode_code_value (sequence : List (List Nat)) :
    proof_sequence_decode (proof_sequence_code_value sequence) =
      sequence := by
  apply proof_sequence_code_value_injective
  exact proof_sequence_code_value_decode (proof_sequence_code_value sequence)
/-! ## 证明行证书标签 -/
/-- 自然数层的行证书标签，不携带外部公式或理论证书对象。 -/
inductive HilbertLineCertificateCode where
  | logical (certificateCode : Nat)
  | theory (certificateCode : Nat)
  | modusPonens (implicationIndex premiseIndex : Nat)
  deriving DecidableEq

/-- 证明行证书标签的自然数编码。 -/
def HilbertLineCertificateCode.value :
    HilbertLineCertificateCode → Nat
  | .logical certificateCode =>
      godel_pair_value 0 certificateCode
  | .theory certificateCode =>
      godel_pair_value 1 certificateCode
  | .modusPonens implicationIndex premiseIndex =>
      godel_pair_value 2
        (godel_pair_value implicationIndex premiseIndex)

/-- 从自然数恢复行证书标签及其自然数载荷。 -/
def HilbertLineCertificateCode.decode (code : Nat) :
    Option HilbertLineCertificateCode :=
  let pair := godel_unpair_value code
  if pair.1 = 0 then
    some (.logical pair.2)
  else if pair.1 = 1 then
    some (.theory pair.2)
  else if pair.1 = 2 then
    let indices := godel_unpair_value pair.2
    some (.modusPonens indices.1 indices.2)
  else
    none

/-- 证书标签的规范自然数码可被解码器精确恢复。 -/
theorem HilbertLineCertificateCode.decode_value
    (certificate : HilbertLineCertificateCode) :
    HilbertLineCertificateCode.decode certificate.value =
      some certificate := by
  cases certificate with
  | logical certificateCode =>
      simp [HilbertLineCertificateCode.value,
        HilbertLineCertificateCode.decode,
        godel_unpair_value_pair]
  | theory certificateCode =>
      simp [HilbertLineCertificateCode.value,
        HilbertLineCertificateCode.decode,
        godel_unpair_value_pair]
  | modusPonens implicationIndex premiseIndex =>
      simp [HilbertLineCertificateCode.value,
        HilbertLineCertificateCode.decode,
        godel_unpair_value_pair]

/-! ## 证明序列编码的递归图 -/
/--
从给定初值开始的二维证明序列编码递归图。
每一行必须先满足一维编码关系；随后才把行代码送入外层折叠。这与
`proof_sequence_code_step_condition` 的两级存在见证完全一致。
-/
inductive ProofSequenceCodeFrom :
    Nat → List (List Nat) → Nat → Prop where
  | nil (seed : Nat) :
      ProofSequenceCodeFrom seed [] seed
  | cons (seed : Nat) (row : List Nat) (rowCode : Nat)
      {rest : List (List Nat)} {code : Nat} (hRow : NatSequenceCode row rowCode) (hRest :
        ProofSequenceCodeFrom (nat_sequence_code_step seed rowCode)
          rest code) :
      ProofSequenceCodeFrom seed (row :: rest) code
/-- 以 `0` 为初值的规范二维证明序列编码关系。 -/
abbrev ProofSequenceCode (sequence : List (List Nat)) (code : Nat) :
    Prop :=
  ProofSequenceCodeFrom 0 sequence code
/-- 二维递归图恰好表示逐行编码后的可计算左折叠。 -/
theorem proofseq_code_from_iff
    {seed code : Nat} {sequence : List (List Nat)} :
    ProofSequenceCodeFrom seed sequence code ↔
      code = proof_sequence_code_from seed sequence := by
  constructor
  · intro hCode
    induction hCode with
    | nil =>
        rfl
    | cons seed row rowCode hRow hRest ih =>
        have hRowValue :
            rowCode = nat_sequence_code_value row := by
          rw [natseq_code_iff] at hRow
          exact hRow
        subst rowCode
        exact ih
  · intro hCode
    subst code
    induction sequence generalizing seed with
    | nil =>
        exact ProofSequenceCodeFrom.nil seed
    | cons row rest ih =>
        exact ProofSequenceCodeFrom.cons
          seed row (nat_sequence_code_value row) (natseq_code_value_spec row) (ih (seed :=
            nat_sequence_code_step seed (nat_sequence_code_value row)))
/-- 固定初值 `0` 时，二维递归关系等价于等于规范计算值。 -/
theorem proofseq_code_iff
    {sequence : List (List Nat)} {code : Nat} :
    ProofSequenceCode sequence code ↔
      code = proof_sequence_code_value sequence :=
  proofseq_code_from_iff
/-- 规范二维编码关系由规范计算值实现。 -/
theorem proofseq_code_value_spec (sequence : List (List Nat)) :
    ProofSequenceCode sequence (proof_sequence_code_value sequence) := by
  exact proofseq_code_iff.mpr rfl
/-- 每条有限证明序列都有二维自然数代码。 -/
theorem proofseq_code_exists (sequence : List (List Nat)) :
    ∃ code, ProofSequenceCode sequence code :=
  ⟨proof_sequence_code_value sequence,
    proofseq_code_value_spec sequence⟩
/-- 二维证明序列编码关系是单值的。 -/
theorem proofseq_code_functional
    {sequence : List (List Nat)} {left right : Nat} (hLeft : ProofSequenceCode sequence left) (hRight : ProofSequenceCode sequence right) :
    left = right := by
  rw [proofseq_code_iff] at hLeft hRight
  exact hLeft.trans hRight.symm
/-- 每条有限证明序列存在唯一的二维自然数代码。 -/
theorem proofseq_code_exists_unique (sequence : List (List Nat)) :
    ∃ code,
      ProofSequenceCode sequence code ∧
        ∀ other,
          ProofSequenceCode sequence other →
            other = code := by
  refine ⟨proof_sequence_code_value sequence,
    proofseq_code_value_spec sequence, ?_⟩
  intro code hCode
  exact proofseq_code_functional hCode (proofseq_code_value_spec sequence)
/-- 二维递归编码关系在证明序列参数上保持单射。 -/
theorem proofseq_code_injective
    {left right : List (List Nat)} {code : Nat} (hLeft : ProofSequenceCode left code) (hRight : ProofSequenceCode right code) :
    left = right := by
  rw [proofseq_code_iff] at hLeft hRight
  apply proof_sequence_code_value_injective
  exact hLeft.symm.trans hRight
end ProofCode
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
