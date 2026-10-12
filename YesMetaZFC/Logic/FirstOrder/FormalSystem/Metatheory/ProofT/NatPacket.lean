import Lean

/-!
# 自然数证书的有限数据包

数据包以最高位字节 `1` 为终止标记，其余字节按低位优先读取。
自然数 token 使用规范 unsigned LEB128，树按「标签、子树数、各子树」先序排列。
最外层 token `1` 是格式版本。解析拒绝缺失标记、非规范 varint、截断和尾随数据。
字节解析按自然数值严格递减；树 token 解析燃料取自输入长度，不施加固定上限。
这里定义宿主证书传输格式；它不宣称与旧 `ProofCode` 配数格式相同。
-/

namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket

/-- 数值标签与有限子树组成的原始数据树。 -/
inductive Tree where
  | node (tag : Nat) (children : List Tree)
  deriving Repr

/-- 可执行的树节点计数，用作解析燃料。 -/
def Tree.weight : Tree → Nat
  | .node _ children => 1 + (children.map Tree.weight).sum
termination_by tree => sizeOf tree

def leaf (value : Nat) : Tree := .node value []

def scalar : Tree → Option Nat
  | .node value [] => some value
  | _ => none

def readBytes (code : Nat) (acc : List Nat) : Option (List Nat) :=
  if h : code < 2 then
    if code == 1 then some acc.reverse else none
  else readBytes (code / 256) (code % 256 :: acc)
termination_by code
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def readTokens : List Nat → Nat → Nat → List Nat → Option (List Nat)
  | [], value, scale, acc =>
      if scale == 1 && value == 0 then some acc.reverse else none
  | byte :: rest, value, scale, acc =>
      if byte < 128 then
        if scale != 1 && byte == 0 then none
        else readTokens rest 0 1 ((value + byte * scale) :: acc)
      else readTokens rest (value + (byte - 128) * scale) (scale * 128) acc

mutual

def readTree : Nat → List Nat → Option (Tree × List Nat)
  | 0, _ => none
  | fuel + 1, tag :: count :: rest => do
      let (children, tail) ← readForest fuel count rest
      return (.node tag children, tail)
  | _, _ => none

def readForest : Nat → Nat → List Nat → Option (List Tree × List Nat)
  | _, 0, rest => some ([], rest)
  | 0, _ + 1, _ => none
  | fuel + 1, count + 1, rest => do
      let (head, tail) ← readTree fuel rest
      let (children, tail') ← readForest fuel count tail
      return (head :: children, tail')

end

/-- 完整消费一个自然数数据包；非法格式返回 `none`。 -/
def decode (code : Nat) : Option Tree := do
  let bytes ← readBytes code []
  let tokens ← readTokens bytes 0 1 []
  match tokens with
  | 1 :: payload =>
      let (tree, tail) ← readTree (payload.length + 1) payload
      if tail.isEmpty then some tree else none
  | _ => none

def varint (value : Nat) : List Nat :=
  if h : value < 128 then [value]
  else (value % 128 + 128) :: varint (value / 128)
termination_by value
decreasing_by
  exact Nat.div_lt_self
    (Nat.lt_of_lt_of_le (by decide : 0 < 128) (Nat.le_of_not_lt h)) (by decide)

/-- 成员的大小严格小于整个列表；直接使用结构证据。 -/
private theorem list_sizeOf_lt_of_mem {α : Type u} [SizeOf α] {a : α} {as : List α}
    (h : a ∈ as) : sizeOf a < sizeOf as := by
  induction h with
  | head =>
      exact Nat.lt_of_lt_of_le
        (Nat.lt_add_of_pos_left (Nat.zero_lt_succ 0)) (Nat.le_add_right _ _)
  | tail _ _ ih =>
      exact Nat.lt_trans ih (Nat.lt_add_of_pos_left
        (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_add_right 1 _)))

def treeTokens : Tree → List Nat
  | .node tag children =>
      tag :: children.length :: children.flatMap treeTokens
termination_by tree => sizeOf tree
decreasing_by
  change sizeOf _ < sizeOf (Tree.node _ _)
  rw [Tree.node.sizeOf_spec]
  exact Nat.lt_of_lt_of_le (list_sizeOf_lt_of_mem (by assumption)) (Nat.le_add_left ..)

/-- 数据树的传输编码；完整往返定理见 `NatPacketRoundtrip.decode_encode`。 -/
def encode (tree : Tree) : Nat :=
  let bytes := (1 :: treeTokens tree).flatMap varint
  bytes.foldr (fun byte rest => byte + 256 * rest) 1

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket
