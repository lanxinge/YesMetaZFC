import YesMetaZFC.Model.FirstOrder.SubstitutionSemantics

/-! # 类型安全的函数图消去

源符号由目标语言中的固定关系公式解释。复合项的参数同时变成新 bound 见证，
然后断言参数图及函数图。所有源排序、目标排序和变量提升均保留在类型中；
翻译支持任意有限元数，不使用变量名字或外部新鲜性条件。
-/
namespace YesMetaZFC.Automation.RelationalTranslation
open Logic Logic.FirstOrder
set_option autoImplicit false

variable {σ τ : Signature.{0, 0, 0}}

/-- 每个函数由“输出在首槽”的关系图解释；关系符号也有固定定义正文。 -/
structure Interpretation (σ τ : Signature.{0, 0, 0}) where
  sort : σ.SortSymbol → τ.SortSymbol
  function : (symbol : σ.FuncSymbol) → Formula τ []
    (sort (σ.funcCodomain symbol) :: (σ.funcDomain symbol).map sort)
  relation : (symbol : σ.RelSymbol) → Formula τ [] ((σ.relDomain symbol).map sort)

/-- 将排序异质参数列视作类型安全的同时自由代入。 -/
def argumentsSubstitution {bound free sorts : SortContext τ}
    (arguments : Arguments τ bound free sorts) : VariableSubstitution τ sorts bound free :=
  fun entry => match arguments, entry with
    | .cons head _, .here => head
    | .cons _ tail, .there previous => argumentsSubstitution tail previous

def applyTemplate {bound free sorts : SortContext τ}
    (body : Formula τ [] sorts) (arguments : Arguments τ bound free sorts) : Formula τ bound free :=
  body.substituteMapped VariableSubstitution.empty (argumentsSubstitution arguments)

/-- 旧变量跨过整个新 bound 块。 -/
def skip (introduced : SortContext τ) {bound : SortContext τ} {sort : τ.SortSymbol}
    (entry : Variable bound sort) : Variable (introduced ++ bound) sort :=
  match introduced with
  | [] => entry
  | _ :: rest => .there (skip rest entry)

def weakenTerm (introduced : SortContext τ) {bound free : SortContext τ} {sort : τ.SortSymbol}
    (term : Term τ bound free sort) : Term τ (introduced ++ bound) free sort :=
  term.renameMapped (skip introduced) VariableRenaming.id

/-- 整个新 bound 块的异质参数列。 -/
def witnesses (sorts : SortContext τ) {bound free : SortContext τ} :
    Arguments τ (sorts ++ bound) free sorts :=
  match sorts with
  | [] => .nil
  | sort :: rest => .cons (.bvar .here) ((witnesses rest).weakenBound sort)

/-- 关闭 bound 块，最前面的变量先关闭。 -/
def existsBlock (sorts : SortContext τ) {bound free : SortContext τ}
    (body : Formula τ (sorts ++ bound) free) : Formula τ bound free :=
  match sorts with
  | [] => body
  | sort :: rest => existsBlock rest (.existsE sort body)

abbrev TermAssignment (I : Interpretation σ τ) (source : SortContext σ)
    (bound free : SortContext τ) :=
  {sort : σ.SortSymbol} → Variable source sort → Term τ bound free (I.sort sort)

def weakenAssignment (I : Interpretation σ τ) (introduced : SortContext τ)
    {source : SortContext σ} {bound free : SortContext τ}
    (assignment : TermAssignment I source bound free) : TermAssignment I source (introduced ++ bound) free :=
  fun entry => weakenTerm introduced (assignment entry)

mutual
/-- 任意源项的目标关系图，输出是任意目标项。 -/
def term (I : Interpretation σ τ) {sb sf : SortContext σ}
    {bound free : SortContext τ} {sort : σ.SortSymbol}
    (bs : TermAssignment I sb bound free) (fs : TermAssignment I sf bound free)
    (input : Term σ sb sf sort) (output : Term τ bound free (I.sort sort)) : Formula τ bound free :=
  match input with
  | .bvar entry => .equal output (bs entry)
  | .fvar entry => .equal output (fs entry)
  | .app symbol args =>
    existsBlock ((σ.funcDomain symbol).map I.sort)
      (.conj
        (arguments I (weakenAssignment I _ bs) (weakenAssignment I _ fs) args (witnesses _))
        (applyTemplate (I.function symbol)
          (.cons (weakenTerm _ output) (witnesses _))))

/-- 参数图逐槽连接，保留异质排序及所有参数之间的共享变量。 -/
def arguments (I : Interpretation σ τ) {sb sf : SortContext σ}
    {bound free : SortContext τ} {sorts : SortContext σ}
    (bs : TermAssignment I sb bound free) (fs : TermAssignment I sf bound free)
    (input : Arguments σ sb sf sorts) (output : Arguments τ bound free (sorts.map I.sort)) : Formula τ bound free :=
  match input, output with
  | .nil, .nil => .truth
  | .cons head tail, .cons first rest =>
    .conj (term I bs fs head first) (arguments I bs fs tail rest)
end

/-- 源 bound 量词提升赋值；源 free 变量只做目标 weakening。 -/
def liftAssignment (I : Interpretation σ τ) (sort : σ.SortSymbol)
    {source : SortContext σ} {bound free : SortContext τ}
    (assignment : TermAssignment I source bound free) :
    TermAssignment I (sort :: source) (I.sort sort :: bound) free :=
  fun entry => match entry with
  | .here => .bvar .here
  | .there previous => (assignment previous).weakenBound (I.sort sort)

/-- 完整十一构造子翻译；否定不移到项图内部。 -/
def formula (I : Interpretation σ τ) {sb sf : SortContext σ} {bound free : SortContext τ}
    (bs : TermAssignment I sb bound free) (fs : TermAssignment I sf bound free)
    (input : Formula σ sb sf) : Formula τ bound free :=
  match input with
  | .falsum => .falsum
  | .truth => .truth
  | .rel symbol args =>
    existsBlock ((σ.relDomain symbol).map I.sort)
      (.conj
        (arguments I (weakenAssignment I _ bs) (weakenAssignment I _ fs) args (witnesses _))
        (applyTemplate (I.relation symbol) (witnesses _)))
  | .equal (sort := sort) left right =>
    .existsE (I.sort sort)
      (.conj
        (term I (weakenAssignment I [I.sort sort] bs) (weakenAssignment I [I.sort sort] fs) left (.bvar .here))
        (term I (weakenAssignment I [I.sort sort] bs) (weakenAssignment I [I.sort sort] fs) right (.bvar .here)))
  | .neg body => .neg (formula I bs fs body)
  | .conj left right => .conj (formula I bs fs left) (formula I bs fs right)
  | .disj left right => .disj (formula I bs fs left) (formula I bs fs right)
  | .imp left right => .imp (formula I bs fs left) (formula I bs fs right)
  | .iff left right => .iff (formula I bs fs left) (formula I bs fs right)
  | .forallE sort body => .forallE (I.sort sort)
      (formula I (liftAssignment I sort bs) (weakenAssignment I [I.sort sort] fs) body)
  | .existsE sort body => .existsE (I.sort sort)
      (formula I (liftAssignment I sort bs) (weakenAssignment I [I.sort sort] fs) body)

/-- 闭句翻译，无自由赋值参数。 -/
def sentence (I : Interpretation σ τ) (input : Sentence σ) : Sentence τ :=
  formula I (fun {sort} (entry : Variable [] sort) => nomatch entry)
    (fun {sort} (entry : Variable [] sort) => nomatch entry) input

@[simp] theorem sentence_neg (I : Interpretation σ τ) (input : Sentence σ) :
    sentence I (.neg input) = .neg (sentence I input) := rfl

end YesMetaZFC.Automation.RelationalTranslation
