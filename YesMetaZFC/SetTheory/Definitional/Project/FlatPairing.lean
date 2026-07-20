import YesMetaZFC.SetTheory.Definitional.Project.Definitions

/-!
# 项目原子核的平坦有序对编码

本模块保留 Quine--Rosser 型有序对定义，但外延等同和子集在公式中保持为项目原子。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project

namespace Formula

/-- `set` 是包含空集并对后继封闭的归纳集。 -/
def isInductive {depth : Nat} (set : Term depth) : Formula 1 depth :=
  .conj
    (.existsE <| .conj (isEmpty Term.newest) (.mem Term.newest set.weaken))
    (Formula.forallMem set <| .existsE <|
      .conj (isSuccessor Term.newest (.bound 1))
        (.mem Term.newest set.weaken.weaken))

/-- `omega` 是最小归纳集。 -/
def isOmega {depth : Nat} (omega : Term depth) : Formula 1 depth :=
  .conj (isInductive omega) <| .forallE <|
    .imp (isInductive Term.newest) (subset omega.weaken Term.newest)

end Formula

namespace FlatPairing

/-- 自然数向后平移一位，非自然数保持不变。 -/
def isShift {depth : Nat}
    (shifted original omega : Term depth) : Formula 1 depth :=
  .disj
    (.conj (.mem original omega) (Formula.isSuccessor shifted original))
    (.conj (.neg (.mem original omega))
      (Formula.extensionalEq shifted original))

/-- 左标签 `f0(original) = s``original`。 -/
def isLeftTag {depth : Nat}
    (tag original omega : Term depth) : Formula 1 depth :=
  .forallE <| .iff (.mem Term.newest tag.weaken) <|
    Formula.existsMem original.weaken <|
      isShift (.bound 1) Term.newest omega.weaken.weaken

/-- 右标签 `f1(original) = s``original union {empty}`。 -/
def isRightTag {depth : Nat}
    (tag original omega : Term depth) : Formula 1 depth :=
  .forallE <| .iff (.mem Term.newest tag.weaken) <|
    .disj (Formula.isEmpty Term.newest) <|
      Formula.existsMem original.weaken <|
        isShift (.bound 1) Term.newest omega.weaken.weaken

/-- 在固定 `omega` 上形成 Quine--Rosser 平坦有序对。 -/
def codeOver {depth : Nat}
    (pair left right omega : Term depth) : Formula 1 depth :=
  .forallE <| .iff (.mem Term.newest pair.weaken) <|
    .disj
      (Formula.existsMem left.weaken <|
        isLeftTag (.bound 1) Term.newest omega.weaken.weaken)
      (Formula.existsMem right.weaken <|
        isRightTag (.bound 1) Term.newest omega.weaken.weaken)

/-- 参数自由的平坦有序对编码。 -/
def code {depth : Nat}
    (pair left right : Term depth) : Formula 1 depth :=
  .existsE <|
    .conj (Formula.isOmega Term.newest) <|
      codeOver pair.weaken left.weaken right.weaken Term.newest

/-- 项目原子核中的默认平坦有序对约定。 -/
def convention : OrderedPairConvention where
  code := code
  freeClosed_code := by
    intro depth pair left right hPair hLeft hRight
    simp [code, codeOver, isLeftTag, isRightTag, isShift,
      Formula.isOmega, Formula.isInductive, Formula.isEmpty,
      Formula.isSuccessor, Formula.existsMem, Formula.forallMem,
      Formula.FreeClosed, Definitional.Term.newest,
      Formula.extensionalEq_freeClosed_iff, Formula.subset_freeClosed_iff,
      hPair, hLeft, hRight]

end FlatPairing

end Project
end Definitional
end SetTheory
end YesMetaZFC
