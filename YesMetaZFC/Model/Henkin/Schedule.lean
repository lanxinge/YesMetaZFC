import YesMetaZFC.Model.Henkin.Construction
import YesMetaZFC.Logic.FirstOrder.NatPairing

/-!
# 可数 Henkin 闭句的公平调度

本模块把可数性压缩成一个单射编码合同。调度对象已经是内在良构的 Henkin 闭句，
因此不再携带 raw 公式检查、`Admissible` 筛选或作用域失败分支。

配对函数使用二进制分解 `2 ^ left * (2 * right + 1)`。第一投影提供被重复的编码，
第二投影提供任意大的重放位置，从而保证每条闭句在任意阶段之后再次出现。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Completeness
namespace Henkin

open HenkinSignature

universe u v w z

/-! ## 从单射得到部分解码 -/

/-- 一个类型到自然数的可审计单射编码。 -/
structure NatCoding (α : Type z) where
  encode : α → Nat
  injective : Function.Injective encode

namespace NatCoding

/-- 自然数的恒等编码。 -/
def nat : NatCoding Nat where
  encode := id
  injective := fun _ _ h => h

/-- 列表编码；零表示空表，正数通过配对保存表头与表尾。 -/
def list_encode {α : Type z} (coding : NatCoding α) : List α → Nat
  | [] => 0
  | head :: tail =>
      NatPairing.pair (coding.encode head) (list_encode coding tail) + 1

/-- 列表编码保持单射。 -/
theorem list_encode_injective {α : Type z} (coding : NatCoding α) :
    Function.Injective (list_encode coding) := by
  intro left
  induction left with
  | nil =>
      intro right hCode
      cases right with
      | nil => rfl
      | cons head tail =>
          simp [list_encode] at hCode
  | cons head tail ih =>
      intro right hCode
      cases right with
      | nil =>
          simp [list_encode] at hCode
      | cons head' tail' =>
          simp only [list_encode] at hCode
          have hPair := Nat.add_right_cancel hCode
          rcases NatPairing.pair_eq_pair_iff.mp hPair with
            ⟨hHead, hTail⟩
          rw [coding.injective hHead, ih hTail]

/-- 单射编码在有限列表上的标准提升。 -/
def list {α : Type z} (coding : NatCoding α) : NatCoding (List α) where
  encode := list_encode coding
  injective := list_encode_injective coding

/--
从单射编码选择对应逆像。该函数只服务于非计算性的 Henkin 完备性构造；证明搜索后端
不执行它。
-/
noncomputable def decode {α : Type z}
    (coding : NatCoding α) (code : Nat) : Option α := by
  classical
  exact
    if hCode : ∃ value, coding.encode value = code then
      some (Classical.choose hCode)
    else
      none

/-- 解码自己的编码精确返回原值。 -/
@[simp]
theorem decode_encode {α : Type z}
    (coding : NatCoding α) (value : α) :
    coding.decode (coding.encode value) = some value := by
  classical
  unfold decode
  split
  · rename_i hCode
    exact congrArg some
      (coding.injective (Classical.choose_spec hCode))
  · rename_i hCode
    exact False.elim (hCode ⟨value, rfl⟩)

end NatCoding

/-! ## 公平闭句重放 -/

namespace Schedule

/-- 调度索引中被公平重复的基础编码。 -/
def fair_code (index : Nat) : Nat :=
  NatPairing.first index

/-- 每个自然数编码在任意起点之后都会再次出现。 -/
theorem fair_code_cofinal (code start : Nat) :
    ∃ index, start ≤ index ∧ fair_code index = code := by
  refine ⟨NatPairing.pair code start,
    NatPairing.le_pair_right code start, ?_⟩
  simp [fair_code]

/--
任意 Henkin 闭句单射编码都产生公平调度。未命中的自然数统一回落到真式；命中目标
闭句自身编码时，`decode_encode` 保证精确重现。
-/
noncomputable def of_coding {σ : Signature.{u, v, w}}
    (coding : NatCoding (Sentence (HSignature σ))) :
    Schedule σ := by
  classical
  refine {
    sentence := fun index =>
      match coding.decode (fair_code index) with
      | some sentence => sentence
      | none => .truth
    cofinal := ?_
  }
  intro target start
  rcases fair_code_cofinal (coding.encode target) start with
    ⟨index, hStart, hCode⟩
  refine ⟨index, hStart, ?_⟩
  simp [hCode]

end Schedule
end Henkin
end Completeness
end FirstOrder
end Logic
end YesMetaZFC
