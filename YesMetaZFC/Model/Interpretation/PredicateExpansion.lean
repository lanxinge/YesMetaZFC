import YesMetaZFC.Model.Interpretation.RelationalDefinitions

/-! # 带集合参数的谓词展开与正出现单调性

关系正文可使用一个显式参数项。展开保留函数项，量词下提升该参数；
语义接口使用独立关系赋值，供相互递归谓词的内部集合构造复用。
-/
namespace YesMetaZFC.Automation.PredicateExpansion
open Logic Logic.FirstOrder
set_option autoImplicit false
universe x
variable {σ : Signature.{0,0,0}}

abbrev Relations (M : Structure.{0,0,0,x} σ) :=
  (symbol : σ.RelSymbol) → Values M.Carrier (σ.relDomain symbol) → Prop

def evaluate {M : Structure.{0,0,0,x} σ} (relations : Relations M)
    {bound free : SortContext σ} (env : Env M bound free) : Formula σ bound free → Prop
  | .falsum => False
  | .truth => True
  | .rel symbol args => relations symbol (args.eval env)
  | .equal left right => left.eval env = right.eval env
  | .neg body => ¬ evaluate relations env body
  | .conj left right => evaluate relations env left ∧ evaluate relations env right
  | .disj left right => evaluate relations env left ∨ evaluate relations env right
  | .imp left right => evaluate relations env left → evaluate relations env right
  | .iff left right => evaluate relations env left ↔ evaluate relations env right
  | .forallE sort body => ∀ value : M.Carrier sort, evaluate relations (env.pushBound value) body
  | .existsE sort body => ∃ value : M.Carrier sort, evaluate relations (env.pushBound value) body

def withRelations (M : Structure.{0,0,0,x} σ) (relations : Relations M) : Structure.{0,0,0,x} σ where
  Carrier := M.Carrier
  nonempty := M.nonempty
  funcInterp := M.funcInterp
  relInterp := relations

def withEnv {M : Structure.{0,0,0,x} σ} (relations : Relations M)
    {bound free : SortContext σ} (env : Env M bound free) : Env (withRelations M relations) bound free where
  boundVal := env.boundVal
  freeVal := env.freeVal

mutual
theorem term_withRelations {M : Structure.{0,0,0,x} σ} (relations : Relations M)
    {bound free : SortContext σ} (env : Env M bound free) {sort : σ.SortSymbol} (input : Term σ bound free sort) :
    input.eval (withEnv relations env) = input.eval env := by
  cases input with
  | bvar entry => rfl
  | fvar entry => rfl
  | app symbol args => exact congrArg (M.funcInterp symbol) (arguments_withRelations relations env args)

theorem arguments_withRelations {M : Structure.{0,0,0,x} σ} (relations : Relations M)
    {bound free sorts : SortContext σ} (env : Env M bound free) (args : Arguments σ bound free sorts) :
    args.eval (withEnv relations env) = args.eval env := by
  cases args with
  | nil => rfl
  | cons head tail =>
    change Values.cons (head.eval (withEnv relations env)) (tail.eval (withEnv relations env)) = Values.cons (head.eval env) (tail.eval env)
    rw [term_withRelations relations env head,arguments_withRelations relations env tail]
    rfl
end

theorem evaluate_correct {M : Structure.{0,0,0,x} σ} (relations : Relations M)
    {bound free : SortContext σ} (env : Env M bound free) (body : Formula σ bound free) :
    body.satisfies (withEnv relations env) ↔ evaluate relations env body := by
  induction body with
  | falsum => rfl
  | truth => rfl
  | rel symbol args =>
    change relations symbol (args.eval (withEnv relations env)) ↔ relations symbol (args.eval env)
    rw [arguments_withRelations relations env args]
  | equal left right =>
    change (left.eval (withEnv relations env) = right.eval (withEnv relations env)) ↔ (left.eval env = right.eval env)
    rw [term_withRelations relations env left,term_withRelations relations env right]
    rfl
  | neg body ih => exact not_congr (ih env)
  | conj left right ihLeft ihRight => exact and_congr (ihLeft env) (ihRight env)
  | disj left right ihLeft ihRight => exact or_congr (ihLeft env) (ihRight env)
  | imp left right ihLeft ihRight => exact imp_congr (ihLeft env) (ihRight env)
  | iff left right ihLeft ihRight => exact iff_congr (ihLeft env) (ihRight env)
  | forallE sort body ih => exact forall_congr' (fun value => ih (env.pushBound value))
  | existsE sort body ih => exact exists_congr (fun value => ih (env.pushBound value))

private theorem values_withRelations {M : Structure.{0,0,0,x} σ} (relations : Relations M)
    {sorts : SortContext σ} (values : Values M.Carrier sorts) {sort : σ.SortSymbol} (entry : Variable sorts sort) :
    @RelationalTranslation.valuesAssignment σ (withRelations M relations) sorts values sort entry =
      @RelationalTranslation.valuesAssignment σ M sorts values sort entry := by
  cases values with
  | nil => cases entry
  | cons head tail => cases entry with
    | here => rfl
    | there previous => exact values_withRelations relations tail previous

theorem with_templateEnv {M : Structure.{0,0,0,x} σ} (relations : Relations M)
    {sorts : SortContext σ} (values : Values M.Carrier sorts) :
    (RelationalTranslation.templateEnv values : Env (withRelations M relations) [] sorts) =
      withEnv relations (RelationalTranslation.templateEnv values) := by
  apply Env.ext
  · intro sort entry; cases entry
  · intro sort entry; exact values_withRelations relations values entry

theorem evaluate_applyTemplate {M : Structure.{0,0,0,x} σ} (relations : Relations M)
    {bound free sorts : SortContext σ} (env : Env M bound free)
    (body : Formula σ [] sorts) (args : Arguments σ bound free sorts) :
    evaluate relations env (RelationalTranslation.applyTemplate body args) ↔
      evaluate relations (RelationalTranslation.templateEnv (args.eval env)) body := by
  apply (evaluate_correct relations env _).symm.trans
  rw [RelationalTranslation.applyTemplate_satisfies,arguments_withRelations]
  rw [with_templateEnv]
  exact evaluate_correct relations (RelationalTranslation.templateEnv (args.eval env)) body

abbrev Replacements (σ : Signature.{0,0,0}) (parameterSort : σ.SortSymbol) :=
  {bound free : SortContext σ} → Term σ bound free parameterSort →
    (symbol : σ.RelSymbol) → Arguments σ bound free (σ.relDomain symbol) → Formula σ bound free

def expand {parameterSort : σ.SortSymbol} (replace : Replacements σ parameterSort)
    {bound free : SortContext σ} (parameter : Term σ bound free parameterSort) :
    Formula σ bound free → Formula σ bound free
  | .falsum => .falsum
  | .truth => .truth
  | .rel symbol args => replace parameter symbol args
  | .equal left right => .equal left right
  | .neg body => .neg (expand replace parameter body)
  | .conj left right => .conj (expand replace parameter left) (expand replace parameter right)
  | .disj left right => .disj (expand replace parameter left) (expand replace parameter right)
  | .imp left right => .imp (expand replace parameter left) (expand replace parameter right)
  | .iff left right => .iff (expand replace parameter left) (expand replace parameter right)
  | .forallE sort body => .forallE sort (expand replace (parameter.weakenBound sort) body)
  | .existsE sort body => .existsE sort (expand replace (parameter.weakenBound sort) body)

theorem expand_correct {M : Structure.{0,0,0,x} σ} {parameterSort : σ.SortSymbol}
    (replace : Replacements σ parameterSort) (relations : M.Carrier parameterSort → Relations M)
    (hAtom : ∀ {bound free} (env : Env M bound free) (parameter : Term σ bound free parameterSort) symbol args,
      (replace parameter symbol args).satisfies env ↔ relations (parameter.eval env) symbol (args.eval env))
    {bound free : SortContext σ} (env : Env M bound free) (parameter : Term σ bound free parameterSort)
    (body : Formula σ bound free) :
    (expand replace parameter body).satisfies env ↔ evaluate (relations (parameter.eval env)) env body := by
  induction body with
  | falsum => rfl
  | truth => rfl
  | rel symbol args => exact hAtom env parameter symbol args
  | equal left right => rfl
  | neg body ih => exact not_congr (ih env parameter)
  | conj left right ihLeft ihRight => exact and_congr (ihLeft env parameter) (ihRight env parameter)
  | disj left right ihLeft ihRight => exact or_congr (ihLeft env parameter) (ihRight env parameter)
  | imp left right ihLeft ihRight => exact imp_congr (ihLeft env parameter) (ihRight env parameter)
  | iff left right ihLeft ihRight => exact iff_congr (ihLeft env parameter) (ihRight env parameter)
  | forallE sort body ih =>
    apply forall_congr'; intro value
    simpa only [Term.eval_weakenBound] using ih (env.pushBound value) (parameter.weakenBound sort)
  | existsE sort body ih =>
    apply exists_congr; intro value
    simpa only [Term.eval_weakenBound] using ih (env.pushBound value) (parameter.weakenBound sort)

def independent (selected : σ.RelSymbol → Bool) {bound free : SortContext σ} : Formula σ bound free → Bool
  | .falsum | .truth | .equal _ _ => true
  | .rel symbol _ => !selected symbol
  | .neg body | .forallE _ body | .existsE _ body => independent selected body
  | .conj left right | .disj left right | .imp left right | .iff left right =>
    independent selected left && independent selected right

def positive (selected : σ.RelSymbol → Bool) {bound free : SortContext σ} : Formula σ bound free → Bool
  | .falsum | .truth | .rel _ _ | .equal _ _ => true
  | .neg body => independent selected body
  | .conj left right | .disj left right => positive selected left && positive selected right
  | .imp left right => independent selected left && positive selected right
  | .iff left right => independent selected left && independent selected right
  | .forallE _ body | .existsE _ body => positive selected body

theorem independent_correct {M : Structure.{0,0,0,x} σ} (selected : σ.RelSymbol → Bool)
    (first second : Relations M)
    (hSame : ∀ symbol, selected symbol = false → ∀ args, first symbol args ↔ second symbol args)
    {bound free : SortContext σ} (env : Env M bound free) (body : Formula σ bound free)
    (hIndependent : independent selected body = true) : evaluate first env body ↔ evaluate second env body := by
  induction body with
  | falsum => rfl
  | truth => rfl
  | rel symbol args => exact hSame symbol (by cases h : selected symbol <;> simp_all [independent]) _
  | equal left right => rfl
  | neg body ih => exact not_congr (ih env hIndependent)
  | conj left right ihLeft ihRight =>
    have h := Bool.and_eq_true_iff.mp hIndependent
    exact and_congr (ihLeft env h.1) (ihRight env h.2)
  | disj left right ihLeft ihRight =>
    have h := Bool.and_eq_true_iff.mp hIndependent
    exact or_congr (ihLeft env h.1) (ihRight env h.2)
  | imp left right ihLeft ihRight =>
    have h := Bool.and_eq_true_iff.mp hIndependent
    exact imp_congr (ihLeft env h.1) (ihRight env h.2)
  | iff left right ihLeft ihRight =>
    have h := Bool.and_eq_true_iff.mp hIndependent
    exact iff_congr (ihLeft env h.1) (ihRight env h.2)
  | forallE sort body ih => exact forall_congr' (fun value => ih (env.pushBound value) hIndependent)
  | existsE sort body ih => exact exists_congr (fun value => ih (env.pushBound value) hIndependent)

theorem monotone {M : Structure.{0,0,0,x} σ} (selected : σ.RelSymbol → Bool) (first second : Relations M)
    (hIncrease : ∀ symbol args, first symbol args → second symbol args)
    (hSame : ∀ symbol, selected symbol = false → ∀ args, first symbol args ↔ second symbol args)
    {bound free : SortContext σ} (env : Env M bound free) (body : Formula σ bound free)
    (hPositive : positive selected body = true) : evaluate first env body → evaluate second env body := by
  induction body with
  | falsum => exact id
  | truth => exact id
  | rel symbol args => exact hIncrease symbol _
  | equal left right => exact id
  | neg body => exact (not_congr (independent_correct selected first second hSame env body hPositive)).mp
  | conj left right ihLeft ihRight =>
    have h := Bool.and_eq_true_iff.mp hPositive
    exact fun hBody => ⟨ihLeft env h.1 hBody.1,ihRight env h.2 hBody.2⟩
  | disj left right ihLeft ihRight =>
    have h := Bool.and_eq_true_iff.mp hPositive
    exact fun hBody => hBody.elim (fun hLeft => Or.inl (ihLeft env h.1 hLeft)) (fun hRight => Or.inr (ihRight env h.2 hRight))
  | imp left right _ ihRight =>
    have h := Bool.and_eq_true_iff.mp hPositive
    exact fun hBody hLeft => ihRight env h.2 (hBody ((independent_correct selected first second hSame env left h.1).mpr hLeft))
  | iff left right =>
    have h := Bool.and_eq_true_iff.mp hPositive
    exact (iff_congr (independent_correct selected first second hSame env left h.1)
      (independent_correct selected first second hSame env right h.2)).mp
  | forallE sort body ih => exact fun hBody value => ih (env.pushBound value) hPositive (hBody value)
  | existsE sort body ih => exact fun ⟨value,hBody⟩ => ⟨value,ih (env.pushBound value) hPositive hBody⟩

end YesMetaZFC.Automation.PredicateExpansion
