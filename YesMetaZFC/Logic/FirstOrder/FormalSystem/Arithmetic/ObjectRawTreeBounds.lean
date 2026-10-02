import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectCodeBounds
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectPacketData
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectArithmeticTerm

/-! # 原始树码关于实际传输包的初等上界

按树和列表的结构成本归纳，再以规范 token 序列的长度与各 token 数值给出统一界。
该界只用于隐藏中间码；不增加运行时燃料上限或证明内核前提。
-/
namespace YesMetaZFC.Automation.ObjectRawTreeBounds
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofT NatPacket IntrinsicQuotation ProofCode
open ObjectHorn ObjectCodeBounds ObjectArithmeticTerm
set_option autoImplicit false

mutual
def cost : Tree → Nat
  | .node _ children => forestCost children + 1
def forestCost : List Tree → Nat
  | [] => 0
  | head :: tail => cost head + forestCost tail + 1
end

mutual
theorem cost_lt_tokens (input : Tree) : cost input < (treeTokens input).length := by
  cases input with
  | node tag children =>
    have h := forestCost_le_tokens children
    simp only [cost, treeTokens, List.length_cons]
    omega
termination_by sizeOf input

theorem forestCost_le_tokens (input : List Tree) : forestCost input ≤ (input.flatMap treeTokens).length := by
  cases input with
  | nil => simp [forestCost]
  | cons head tail =>
    have hHead := cost_lt_tokens head
    have hTail := forestCost_le_tokens tail
    simp only [forestCost, List.flatMap_cons, List.length_append]
    omega
termination_by sizeOf input
end

mutual
theorem tree_bound (base : Nat) (hBase : 2 ≤ base) (input : Tree)
    (hTokens : ∀ n, n ∈ treeTokens input → n ≤ base) : treeValue input ≤ base ^ (16 ^ cost input) := by
  cases input with
  | node tag children =>
    have hTag := hTokens tag (by simp [treeTokens])
    have hChildren := forest_bound base hBase children
      (fun n hn => hTokens n (by simp only [treeTokens, List.mem_cons]; exact Or.inr (Or.inr hn)))
    let bound := base ^ (16 ^ forestCost children)
    have hBaseBound : base ≤ bound := Nat.le_pow (Nat.pow_pos (by decide))
    have h := pair_succ_bound bound tag (forestValue children)
      (Nat.le_trans hBase hBaseBound) (Nat.le_trans hTag hBaseBound) hChildren
    change godel_pair_value tag (forestValue children) + 1 ≤ base ^ (16 ^ (forestCost children + 1))
    calc
      _ ≤ bound ^ 4 := h
      _ ≤ bound ^ 16 := Nat.pow_le_pow_right (by omega) (by decide)
      _ = _ := by rw [← Nat.pow_mul]; simp only [Nat.pow_succ]
termination_by sizeOf input

theorem forest_bound (base : Nat) (hBase : 2 ≤ base) (input : List Tree)
    (hTokens : ∀ n, n ∈ input.flatMap treeTokens → n ≤ base) :
    forestValue input ≤ base ^ (16 ^ forestCost input) := by
  cases input with
  | nil => change 1 ≤ base ^ (16 ^ 0); exact Nat.one_le_pow _ _ (by omega)
  | cons head tail =>
    have hHead := tree_bound base hBase head
      (fun n hn => hTokens n (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inl hn))
    have hTail := forest_bound base hBase tail
      (fun n hn => hTokens n (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr hn))
    let bound := base ^ (16 ^ (cost head + forestCost tail))
    have hBaseBound : base ≤ bound := Nat.le_pow (Nat.pow_pos (by decide))
    have hLeft : treeValue head ≤ bound := Nat.le_trans hHead
      (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by decide) (by omega)))
    have hRight : forestValue tail ≤ bound := Nat.le_trans hTail
      (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by decide) (by omega)))
    have hPair := pair_succ_bound bound _ _ (by omega) hLeft hRight
    have hOuter := pair_succ_bound (bound ^ 4) 1 (godel_pair_value (treeValue head) (forestValue tail))
      (Nat.le_trans (by omega : 2 ≤ bound) (Nat.le_pow (by decide)))
      (Nat.one_le_pow _ _ (by omega)) (by omega)
    change godel_pair_value 1 (godel_pair_value (treeValue head) (forestValue tail)) + 1 ≤
      base ^ (16 ^ (cost head + forestCost tail + 1))
    calc
      _ ≤ (bound ^ 4) ^ 4 := hOuter
      _ = _ := by rw [← Nat.pow_mul]; change (base ^ (16 ^ (cost head + forestCost tail))) ^ 16 = _
                  rw [← Nat.pow_mul, Nat.pow_succ]
termination_by sizeOf input
end

def tokens (input : List Nat) (tail : Nat) : Nat := input.foldr ObjectPacket.token tail

@[simp] theorem tokens_nil (tail : Nat) : tokens [] tail = tail := rfl
@[simp] theorem tokens_cons (head : Nat) (rest : List Nat) (tail : Nat) :
    tokens (head :: rest) tail = ObjectPacket.token head (tokens rest tail) := rfl

theorem tokens_bytes (input : List Nat) (tail : Nat) :
    tokens input tail = ObjectPacket.bytes (input.flatMap varint) tail := by
  induction input <;> simp_all [tokens_cons, ObjectPacket.token, ObjectPacket.bytes]

theorem token_strict (n tail : Nat) (hTail : 0 < tail) : tail < ObjectPacket.token n tail := by
  rw [ObjectPacket.token, varint.eq_def]
  split
  · change tail < n + 256 * tail
    omega
  · change tail < n % 128 + 128 + 256 * ObjectPacket.bytes (varint (n / 128)) tail
    have h := ObjectPacket.bytes_tail_le (varint (n / 128)) tail
    omega

theorem tokens_tail_le (input : List Nat) (tail : Nat) : tail ≤ tokens input tail := by
  induction input with
  | nil => exact Nat.le_refl _
  | cons head rest ih => exact Nat.le_trans ih (ObjectPacket.token_tail_le head _)

theorem tokens_length (input : List Nat) : input.length < tokens input 1 := by
  induction input with
  | nil => decide
  | cons head rest ih =>
    have h := token_strict head (tokens rest 1) (by omega)
    simp only [List.length_cons, tokens_cons]
    omega

theorem tokens_member (input : List Nat) (n : Nat) (h : n ∈ input) : n ≤ tokens input 1 := by
  induction input with
  | nil => cases h
  | cons head rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ObjectPacket.token_number_le _ _
    · exact Nat.le_trans (ih h) (ObjectPacket.token_tail_le head _)

/-- 任意成功包的原始树码都低于由包本身计算的固定项。 -/
theorem packet_bound (input : Tree) : treeValue input ≤ tableBoundValue (NatPacket.encode input) := by
  have hCode : tokens (1 :: treeTokens input) 1 = NatPacket.encode input := tokens_bytes _ _
  have hLength := tokens_length (1 :: treeTokens input)
  have hCost := cost_lt_tokens input
  rw [hCode] at hLength
  have hBound := tree_bound (NatPacket.encode input + 8) (by omega) input (by
    intro n hn
    have h := tokens_member (1 :: treeTokens input) n (List.mem_cons_of_mem 1 hn)
    rw [hCode] at h
    omega)
  exact Nat.le_trans hBound (Nat.pow_le_pow_right (by omega)
    (Nat.pow_le_pow_right (by decide) (by simp only [List.length_cons] at hLength; omega)))

end YesMetaZFC.Automation.ObjectRawTreeBounds
