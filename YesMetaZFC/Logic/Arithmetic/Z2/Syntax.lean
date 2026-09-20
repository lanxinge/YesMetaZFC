import YesMetaZFC.Logic.Arithmetic.Signature
import YesMetaZFC.Logic.Arithmetic.Robinson

/-! # 二阶算术的最小双排序语言

仅包含数、数集、0/S/加/乘和成员关系。数集量词仍由原多排序一阶
AST 表达；不加入 BMS 符号，不需要纯语言布尔检查。
-/
namespace YesMetaZFC.Logic.Arithmetic.Z2
open FirstOrder
set_option autoImplicit false

inductive sort_m where
  | num | set
  deriving DecidableEq

inductive rel_m where
  | mem
  deriving DecidableEq

abbrev signature_m : Signature where
  SortSymbol := sort_m
  FuncSymbol := Arithmetic.func_m
  RelSymbol := rel_m
  funcDomain
    | .zero => []
    | .succ => [.num]
    | .add | .mul => [.num, .num]
  funcCodomain _ := .num
  relDomain | .mem => [.num, .set]

variable {Γ Δ : SortContext signature_m}

def zero_m : Term signature_m Γ Δ .num := Term.app (σ := signature_m) .zero .nil

def succ_m (t : Term signature_m Γ Δ .num) : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .succ (.cons t .nil)

def add_m (s t : Term signature_m Γ Δ .num) : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .add (.cons s (.cons t .nil))

def mul_m (s t : Term signature_m Γ Δ .num) : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .mul (.cons s (.cons t .nil))

def mem_m (n : Term signature_m Γ Δ .num) (X : Term signature_m Γ Δ .set) :
    Formula signature_m Γ Δ := Formula.rel (σ := signature_m) .mem (.cons n (.cons X .nil))

/-- 保留首个数变量，在其与原参数之间插入一个新集合槽。 -/
def insert_m (φ : Formula signature_m [] (.num :: Δ)) :
    Formula signature_m [] (.num :: .set :: Δ) :=
  φ.renameFree (VariableRenaming.lift (introduced := sort_m.num)
    (VariableRenaming.weaken sort_m.set))

def next_m : VariableSubstitution signature_m (.num :: Δ) [] (.num :: Δ) :=
  VariableSubstitution.cons (succ_m (.fvar .here))
    (VariableSubstitution.of_renaming (VariableRenaming.weaken sort_m.num))

/-- 此处只是公式；全公式归纳随后由理解与集合归纳推导。 -/
def induction_m (φ : Formula signature_m [] (.num :: Δ)) : Formula signature_m [] Δ :=
  .imp (.conj (φ.instantiateFreeTop zero_m)
    ((Formula.imp φ (φ.substituteFree next_m)).forallFreeTop sort_m.num))
    (φ.forallFreeTop sort_m.num)

end YesMetaZFC.Logic.Arithmetic.Z2
