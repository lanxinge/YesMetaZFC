import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectSyntaxTransformAccept
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Arithmetic.ObjectSyntaxTransformSound

/-! # 共用变换图的全自然数规格

固定对象公式的布尔检查与实际 quotation 解码、递归变换精确一致。
非法输入、未定义的模式和越界查表均参与同一正负表示。
-/
namespace YesMetaZFC.Automation.ObjectSyntaxTransform
open Logic Logic.FirstOrder Logic.FirstOrder.FormalSystem
open Logic.FirstOrder.Nonlogical.BasicSetTheory ProofT NatPacket IntrinsicQuotation
open ObjectHorn
set_option autoImplicit false

/-- 计算规格同时覆盖成功结果、失败输入以及错误的候选输出。 -/
theorem checked_iff (mode depth parameter input output : Nat) :
    checked mode depth parameter input output = true ↔
      (decodeTree input).bind (SyntaxTransform.formula mode depth parameter) = some output := by
  constructor
  · intro h
    obtain ⟨tree, rfl, hRun⟩ := checked_sound mode depth parameter input output h
    simpa using hRun
  · intro h
    obtain ⟨tree, hTree, hRun⟩ := Option.bind_eq_some_iff.mp h
    rw [← treeValue_of_decode hTree]
    exact checked_complete mode depth parameter tree output hRun

theorem checked_false_iff (mode depth parameter input output : Nat) :
    checked mode depth parameter input output = false ↔
      (decodeTree input).bind (SyntaxTransform.formula mode depth parameter) ≠ some output := by
  rw [Bool.eq_false_iff]
  exact not_congr (checked_iff mode depth parameter input output)

/-- 同一输入至多接受一个输出。 -/
theorem checked_functional (mode depth parameter input left right : Nat)
    (hLeft : checked mode depth parameter input left = true)
    (hRight : checked mode depth parameter input right = true) : left = right :=
  Option.some.inj (((checked_iff _ _ _ _ _).mp hLeft).symm.trans ((checked_iff _ _ _ _ _).mp hRight))

end YesMetaZFC.Automation.ObjectSyntaxTransform
