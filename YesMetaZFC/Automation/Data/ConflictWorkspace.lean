import YesMetaZFC.Automation.Data.ClauseArena

/-!
# 冲突分析 slab 工作区

冲突分析冻结一次 clause arena 视图，后续 resolution 直接用 header 指向 literal slab。
reason 不再复制成独立数组；当前 resolvent 作为线性局部数组流入下一步，让 Lean 运行时
保持唯一所有权。
-/

namespace YesMetaZFC
namespace Automation
namespace Data

/--
当前规范字句与 arena reason slice 做线性 resolution。

两个输入都按 packed literal 排序；主元从两侧全部跳过，输出同步去重。
-/
def resolvePackedWithArena (current : Array PackedLit) (arena : ClauseArena)
    (reasonId : ClauseId) (pivot : Nat) : Array PackedLit := Id.run do
  let some header := arena.header? reasonId
    | return (current.filter fun lit => PackedLit.var lit != pivot)
  let mut left := 0
  let mut right := 0
  let mut out := Array.emptyWithCapacity (current.size + header.length)
  while left < current.size || right < header.length do
    while left < current.size && PackedLit.var current[left]! == pivot do
      left := left + 1
    while right < header.length &&
        PackedLit.var arena.literals[header.start + right]! == pivot do
      right := right + 1
    if left >= current.size && right >= header.length then
      break
    let next :=
      if right >= header.length then
        current[left]!
      else if left >= current.size then
        arena.literals[header.start + right]!
      else
        Nat.min current[left]! arena.literals[header.start + right]!
    if left < current.size && current[left]! == next then
      left := left + 1
    if right < header.length && arena.literals[header.start + right]! == next then
      right := right + 1
    if out.isEmpty || out[out.size - 1]! != next then
      out := out.push next
  return out

/-- packed 规范字句是否含有相邻的互补文字。 -/
def packedClauseTautological (clause : Array PackedLit) : Bool := Id.run do
  let mut previous? : Option PackedLit := none
  for lit in clause do
    if let some previous := previous? then
      if PackedLit.var previous == PackedLit.var lit && previous != lit then
        return true
    previous? := some lit
  return false

end Data
end Automation
end YesMetaZFC
