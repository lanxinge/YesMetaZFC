import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectHornValues
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatPacketCanonical

/-! # 传输包字节前缀的数值运算与结构规格 -/
namespace YesMetaZFC.Automation.ObjectPacket
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem ProofT NatPacket
open ObjectHorn
set_option autoImplicit false

def bytes (input : List Nat) (tail : Nat) : Nat := input.foldr (fun byte rest => byte + 256 * rest) tail
def token (n tail : Nat) : Nat := bytes (varint n) tail
def tree (input : Tree) (tail : Nat) : Nat := bytes ((treeTokens input).flatMap varint) tail
def forest (input : List Tree) (tail : Nat) : Nat := bytes ((input.flatMap treeTokens).flatMap varint) tail

theorem bytes_append (left right : List Nat) (tail : Nat) :
    bytes (left ++ right) tail = bytes left (bytes right tail) := by simp [bytes]

theorem bytes_tail_le (input : List Nat) (tail : Nat) : tail ≤ bytes input tail := by
  induction input with
  | nil => exact Nat.le_refl _
  | cons head rest ih => change tail ≤ head + 256 * bytes rest tail; omega

theorem token_small (n tail : Nat) (h : n < 128) : token n tail = n + 256 * tail := by
  rw [token, varint_small n h]
  rfl

theorem token_large (digit rest tail : Nat) (hDigit : digit < 128) (hRest : 0 < rest) :
    token (digit + 128 * rest) tail = digit + 128 + 256 * token rest tail := by
  rw [token, varint_large digit rest hDigit hRest]
  rfl

theorem token_tail_le (n tail : Nat) : tail ≤ token n tail := bytes_tail_le _ _

theorem token_number_le (n tail : Nat) : n ≤ token n tail := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n < 128
    · rw [token_small _ _ h]; omega
    · have hRest : 0 < n / 128 := by omega
      have hSmall : n / 128 < n := Nat.div_lt_self (by omega) (by decide)
      have hDigit : n % 128 < 128 := Nat.mod_lt _ (by decide)
      have hRec := ih (n / 128) hSmall
      have hValue := token_large (n % 128) (n / 128) tail hDigit hRest
      rw [Nat.mod_add_div] at hValue
      rw [hValue]
      have := Nat.mod_add_div n 128
      omega

theorem tree_node (tag : Nat) (children : List Tree) (tail : Nat) :
    tree (.node tag children) tail = token tag (token children.length (forest children tail)) := by
  simp only [tree, treeTokens, List.flatMap_cons, bytes_append]
  rfl

theorem forest_nil (tail : Nat) : forest [] tail = tail := rfl
theorem forest_cons (head : Tree) (rest : List Tree) (tail : Nat) :
    forest (head :: rest) tail = tree head (forest rest tail) := by
  simp [forest, List.flatMap_cons, List.flatMap_append, bytes_append, tree]

theorem tree_tail_le (input : Tree) (tail : Nat) : tail ≤ tree input tail := bytes_tail_le _ _
theorem forest_tail_le (input : List Tree) (tail : Nat) : tail ≤ forest input tail := bytes_tail_le _ _

theorem encode_eq (input : Tree) : NatPacket.encode input = 1 + 256 * tree input 1 := by
  simp only [NatPacket.encode, List.flatMap_cons, varint_small 1 (by decide),
    List.singleton_append, List.foldr_cons]
  rfl

theorem list_field_le {head : Nat} {fields : List Nat} (h : head ∈ fields) : head ≤ listValue fields := by
  induction fields with
  | nil => cases h
  | cons first rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (ProofCode.left_le_godel_pair_value _ _)
        (Nat.le_trans (ProofCode.right_le_godel_pair_value _ _) (Nat.le_succ _))
    · exact Nat.le_trans (ih h) (Nat.le_trans (ProofCode.right_le_godel_pair_value _ _)
        (Nat.le_trans (ProofCode.right_le_godel_pair_value _ _) (Nat.le_succ _)))

theorem field_le (tag : Nat) {field : Nat} {fields : List Nat} (h : field ∈ fields) :
    field ≤ nodeValue tag fields :=
  Nat.le_trans (list_field_le h)
    (Nat.le_trans (ProofCode.right_le_godel_pair_value _ _) (Nat.le_succ _))

def Expr.addConst {n : Nat} : Nat → Expr n → Expr n
  | 0, input => input
  | k + 1, input => .succ (Expr.addConst k input)

@[simp] theorem Expr.addConst_eval {n : Nat} (k : Nat) (input : Expr n) (values : Fin n → Nat) :
    (Expr.addConst k input).eval values = input.eval values + k := by
  induction k <;> simp_all [Expr.addConst, Expr.eval, Nat.add_assoc]

@[simp] theorem Expr.addConst_variables {n : Nat} (k : Nat) (input : Expr n) :
    (Expr.addConst k input).variables = input.variables := by
  induction k <;> simp_all [Expr.addConst, Expr.variables]

end YesMetaZFC.Automation.ObjectPacket
