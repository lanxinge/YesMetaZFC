import YesMetaZFC.SetTheory.Extension
import YesMetaZFC.SetTheory.Automation.Generators
import YesMetaZFC.Automation.HostFocusedSequent

/-!
# 纯集合论公理切片到 `prove_auto`

KP、ZF、ZFC 含有无限公理模式，搜索器不能也不应枚举整个理论。本模块使用显式有限
`TheorySlice`：

1. 每个切片条目都携带其属于原理论的证明；
2. 句子稳定翻译到 preprocessing core 与 SearchSignature；
3. source/deep problem 之间的反模型桥由语义归纳证明；
4. 搜索成功后先得到切片定理，再由成员证明自动提升到完整理论。

materializer 不猜测公理模式来源；所有来源都由 `TheorySlice.member` 固定。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Automation

open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.Automation.CoreSyntax
open _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm

abbrev SearchSignature := SearchMaterialization.SearchSignature
abbrev SearchStructure :=
  LogicSoundness.SetLevel.Structure SearchSignature
abbrev SearchEnv {M : SearchStructure} :=
  LogicSoundness.SetLevel.Env M
abbrev SearchTerm :=
  Logic.FirstOrder.Term SearchSignature
abbrev SearchFormula :=
  Logic.FirstOrder.Formula SearchSignature
abbrev ProjectTerm (depth : Nat) :=
  Definitional.Project.Term depth
abbrev ProjectFormula (depth : Nat) :=
  Definitional.Project.Formula 1 depth
abbrev ProjectSentence :=
  Definitional.Project.Sentence

/-- 纯集合论隶属原子在 preprocessing core 中的唯一谓词描述。 -/
def membershipPredicate : CoreSyntax.PredicateSymbol := {
  id := 1
  arity := 2
  role := .membership
  inputSorts := [.object, .object]
}

/-- 项目外延等同原子在搜索层中的稳定谓词描述。 -/
def extensionalEqPredicate : CoreSyntax.PredicateSymbol := {
  id := 3
  arity := 2
  role := .relation
  inputSorts := [.object, .object]
}

/-- 项目子集原子在搜索层中的稳定谓词描述。 -/
def subsetPredicate : CoreSyntax.PredicateSymbol := {
  id := 4
  arity := 2
  role := .relation
  inputSorts := [.object, .object]
}

@[simp] theorem extensionalEqPredicate_ne_membership :
    extensionalEqPredicate ≠ membershipPredicate := by
  decide

@[simp] theorem subsetPredicate_ne_membership :
    subsetPredicate ≠ membershipPredicate := by
  decide

@[simp] theorem subsetPredicate_ne_extensionalEq :
    subsetPredicate ≠ extensionalEqPredicate := by
  decide

namespace Translate

/-- 纯集合论项到 preprocessing core。 -/
def coreTerm {depth : Nat} : ProjectTerm depth → CoreSyntax.Term
  | .bound entry => .bvar .object entry.val
  | .free id => .fvar .object id

/-- 项目原子核公式到 preprocessing core，定义原子保持为搜索谓词。 -/
def coreFormula {depth : Nat} : ProjectFormula depth → CoreSyntax.Formula
  | .falsum => .falseE
  | .truth => .trueE
  | .mem left right =>
      .atom membershipPredicate [coreTerm left, coreTerm right]
  | .atom symbol _ arguments =>
      match symbol with
      | .extensionalEq =>
          .atom extensionalEqPredicate
            [coreTerm (arguments 0), coreTerm (arguments 1)]
      | .subset =>
          .atom subsetPredicate
            [coreTerm (arguments 0), coreTerm (arguments 1)]
  | .neg body => .neg (coreFormula body)
  | .conj left right => .conj (coreFormula left) (coreFormula right)
  | .disj left right => .disj (coreFormula left) (coreFormula right)
  | .imp left right => .imp (coreFormula left) (coreFormula right)
  | .iff left right => .iffE (coreFormula left) (coreFormula right)
  | .forallE body => .forallE .object (coreFormula body)
  | .existsE body => .existsE .object (coreFormula body)

/-- 纯集合论项到一阶 DAG 搜索签名。 -/
def searchTerm {depth : Nat} : ProjectTerm depth → SearchTerm
  | .bound entry => .var (.bvar .object entry.val)
  | .free id => .var (.fvar .object id)

/-- 项目原子核公式到一阶 DAG 搜索签名。 -/
def searchFormula {depth : Nat} : ProjectFormula depth → SearchFormula
  | .falsum => .falsum
  | .truth => .truth
  | .mem left right =>
      .rel .member [searchTerm left, searchTerm right]
  | .atom symbol _ arguments =>
      match symbol with
      | .extensionalEq =>
          .rel (.predicate extensionalEqPredicate)
            [searchTerm (arguments 0), searchTerm (arguments 1)]
      | .subset =>
          .rel (.predicate subsetPredicate)
            [searchTerm (arguments 0), searchTerm (arguments 1)]
  | .neg body => .neg (searchFormula body)
  | .conj left right => .conj (searchFormula left) (searchFormula right)
  | .disj left right => .disj (searchFormula left) (searchFormula right)
  | .imp left right => .imp (searchFormula left) (searchFormula right)
  | .iff left right => .iff (searchFormula left) (searchFormula right)
  | .forallE body => .forallE .object (searchFormula body)
  | .existsE body => .existsE .object (searchFormula body)

end Translate

/-! ## Search countermodel 到 preprocessing core -/

/-- 搜索模型扩张为纯一阶 core preprocessing 模型。 -/
@[reducible] noncomputable def coreModelOfSearch (M : SearchStructure) :
    Semantics.Model := by
  classical
  exact {
    Carrier := M.Domain
    default := Classical.choice M.nonempty
    sortInterp := M.sortInterp
    sortNonempty := M.sortNonempty
    functionInterp := fun symbol arguments =>
      if hArguments :
          Logic.FirstOrder.ArgsSatisfy M.sortInterp arguments
            (SearchSignature.funcDomain
              (FirstOrderProjection.functionSymbol symbol)) then
        M.funcInterp (FirstOrderProjection.functionSymbol symbol) arguments
      else
        Classical.choose (M.sortNonempty symbol.outputSort)
    predicateInterp := fun predicate arguments =>
      if predicate = membershipPredicate then
        M.relInterp .member arguments
      else
        M.relInterp (.predicate predicate) arguments
    applyInterp := fun _ _ => Classical.choice M.nonempty
    boolValue := fun _ => Classical.choice M.nonempty
    notValue := fun _ => Classical.choice M.nonempty
    andValue := fun _ _ => Classical.choice M.nonempty
    orValue := fun _ _ => Classical.choice M.nonempty
    impValue := fun _ _ => Classical.choice M.nonempty
    iffValue := fun _ _ => Classical.choice M.nonempty
    quoteValue := fun _ => Classical.choice M.nonempty
    lambdaValue := fun _ _ _ => Classical.choice M.nonempty
    iteValue := fun _ _ _ => Classical.choice M.nonempty
    boolHolds := fun _ => False
  }

/-- 搜索环境在 core 模型中的对应环境。 -/
@[reducible] noncomputable def coreEnvOfSearch
    {M : SearchStructure} (env : SearchEnv (M := M)) :
    Semantics.Env (coreModelOfSearch M) where
  boundVal := fun index => env.boundVal .object index
  freeVal := env.freeVal

/-- 搜索对象压栈与 core 压栈交换。 -/
theorem coreEnvOfSearch_pushBound
    {M : SearchStructure} (env : SearchEnv (M := M))
    (value : M.Domain) (hValue : M.sortInterp .object value) :
    coreEnvOfSearch (env.pushBound .object value hValue) =
      (coreEnvOfSearch env).push value := by
  unfold coreEnvOfSearch Semantics.Env.push Logic.FirstOrder.Env.pushBound
  rw [Semantics.Env.mk.injEq]
  constructor
  · funext index
    cases index <;> rfl
  · rfl

/-- core 模型中的函数解释保持 codomain sort。 -/
theorem coreModel_functionSort (M : SearchStructure) :
    ∀ symbol arguments,
      (coreModelOfSearch M).sortInterp symbol.outputSort
        ((coreModelOfSearch M).functionInterp symbol arguments) := by
  intro symbol arguments
  classical
  by_cases hArguments :
      Logic.FirstOrder.ArgsSatisfy M.sortInterp arguments
        (SearchSignature.funcDomain
          (FirstOrderProjection.functionSymbol symbol))
  · simpa only [coreModelOfSearch, hArguments, ↓reduceDIte] using
      M.funcSort (FirstOrderProjection.functionSymbol symbol)
        arguments hArguments
  · simpa only [coreModelOfSearch, hArguments, ↓reduceDIte] using
      Classical.choose_spec (M.sortNonempty symbol.outputSort)

/-- 搜索环境保持全部 typed free assignment。 -/
theorem coreEnv_respectsFree
    {M : SearchStructure} (env : SearchEnv (M := M)) :
    Semantics.Env.RespectsFree (coreEnvOfSearch env) := by
  intro sort id
  exact env.freeSort sort id

mutual

  /-- core/search 翻译给出相同项解释。 -/
  theorem eval_coreTerm
      {M : SearchStructure} (env : SearchEnv (M := M)) {depth : Nat} :
      ∀ term : ProjectTerm depth,
        Semantics.Term.eval (coreEnvOfSearch env)
            (Translate.coreTerm term) =
          Logic.FirstOrder.Term.eval env (Translate.searchTerm term)
    | .bound entry => by
        simp [Translate.coreTerm, Translate.searchTerm,
          Semantics.Term.eval, Logic.FirstOrder.Term.eval,
          coreEnvOfSearch]
    | .free id => by
        simp [Translate.coreTerm, Translate.searchTerm,
          Semantics.Term.eval, Logic.FirstOrder.Term.eval,
          coreEnvOfSearch]

  /-- core/search 翻译给出相同参数列表解释。 -/
  theorem eval_coreTermList
      {M : SearchStructure} (env : SearchEnv (M := M))
      {depth : Nat} :
      ∀ terms : List (ProjectTerm depth),
        terms.map
            (Semantics.Term.eval (coreEnvOfSearch env) ∘
              Translate.coreTerm) =
          terms.map
            (Logic.FirstOrder.Term.eval env ∘ Translate.searchTerm)
    | [] => rfl
    | term :: rest => by
        simp only [List.map_cons, Function.comp_apply]
        rw [eval_coreTerm env term, eval_coreTermList env rest]

end

/-- 搜索公式与 core source 翻译语义一致。 -/
theorem satisfies_coreFormula
    {M : SearchStructure} (env : SearchEnv (M := M)) {depth : Nat} :
    ∀ formula : ProjectFormula depth,
      Semantics.Formula.Satisfies
          (coreEnvOfSearch env) (Translate.coreFormula formula) ↔
        Logic.FirstOrder.Formula.satisfies
          env (Translate.searchFormula formula)
  | .falsum => by
      simp [Translate.coreFormula, Translate.searchFormula,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
  | .truth => by
      simp [Translate.coreFormula, Translate.searchFormula,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
  | .mem left right => by
      simp only [Translate.coreFormula, Translate.searchFormula,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies, coreModelOfSearch,
        membershipPredicate, ↓reduceIte]
      simp only [List.map_cons, List.map_nil]
      have hLeft :
          Semantics.Term.eval (coreEnvOfSearch env)
              (Translate.coreTerm left) =
            Logic.FirstOrder.Term.eval env
              (Translate.searchTerm left) :=
        eval_coreTerm env left
      have hRight :
          Semantics.Term.eval (coreEnvOfSearch env)
              (Translate.coreTerm right) =
            Logic.FirstOrder.Term.eval env
              (Translate.searchTerm right) :=
        eval_coreTerm env right
      have hArguments :
          [Semantics.Term.eval (coreEnvOfSearch env)
              (Translate.coreTerm left),
            Semantics.Term.eval (coreEnvOfSearch env)
              (Translate.coreTerm right)] =
          [Logic.FirstOrder.Term.eval env
              (Translate.searchTerm left),
            Logic.FirstOrder.Term.eval env
              (Translate.searchTerm right)] := by
        rw [hLeft, hRight]
      constructor
      · intro h
        exact hArguments ▸ h
      · intro h
        exact hArguments.symm ▸ h
  | .atom symbol _ arguments => by
      cases symbol with
      | extensionalEq =>
          simp only [Translate.coreFormula, Translate.searchFormula,
            Semantics.Formula.Satisfies, Semantics.Formula.eval,
            Logic.FirstOrder.Formula.satisfies, coreModelOfSearch,
            extensionalEqPredicate_ne_membership, ↓reduceIte]
          simp only [List.map_cons, List.map_nil]
          rw [eval_coreTerm env (arguments 0),
            eval_coreTerm env (arguments 1)]
      | subset =>
          simp only [Translate.coreFormula, Translate.searchFormula,
            Semantics.Formula.Satisfies, Semantics.Formula.eval,
            Logic.FirstOrder.Formula.satisfies, coreModelOfSearch,
            subsetPredicate_ne_membership, ↓reduceIte]
          simp only [List.map_cons, List.map_nil]
          rw [eval_coreTerm env (arguments 0),
            eval_coreTerm env (arguments 1)]
  | .neg body => by
      simpa [Translate.coreFormula, Translate.searchFormula,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies] using
          not_congr (satisfies_coreFormula env body)
  | .conj left right => by
      simp only [Translate.coreFormula, Translate.searchFormula,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      exact and_congr
        (satisfies_coreFormula env left)
        (satisfies_coreFormula env right)
  | .disj left right => by
      simp only [Translate.coreFormula, Translate.searchFormula,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      exact or_congr
        (satisfies_coreFormula env left)
        (satisfies_coreFormula env right)
  | .imp left right => by
      simp only [Translate.coreFormula, Translate.searchFormula,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      exact imp_congr
        (satisfies_coreFormula env left)
        (satisfies_coreFormula env right)
  | .iff left right => by
      simp only [Translate.coreFormula, Translate.searchFormula,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      exact iff_congr
        (satisfies_coreFormula env left)
        (satisfies_coreFormula env right)
  | .forallE body => by
      simp only [Translate.coreFormula, Translate.searchFormula,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      constructor
      · intro hAll value hValue
        have hBody := hAll value hValue
        rw [← coreEnvOfSearch_pushBound env value hValue] at hBody
        exact
          (satisfies_coreFormula
            (env.pushBound .object value hValue) body).mp hBody
      · intro hAll value hValue
        have hBody :=
          (satisfies_coreFormula
            (env.pushBound .object value hValue) body).mpr
              (hAll value hValue)
        rw [coreEnvOfSearch_pushBound env value hValue] at hBody
        exact hBody
  | .existsE body => by
      simp only [Translate.coreFormula, Translate.searchFormula,
        Semantics.Formula.Satisfies, Semantics.Formula.eval,
        Logic.FirstOrder.Formula.satisfies]
      constructor
      · rintro ⟨value, hValue, hBody⟩
        refine ⟨value, hValue, ?_⟩
        rw [← coreEnvOfSearch_pushBound env value hValue] at hBody
        exact
          (satisfies_coreFormula
            (env.pushBound .object value hValue) body).mp hBody
      · rintro ⟨value, hValue, hBody⟩
        refine ⟨value, hValue, ?_⟩
        have hCore :=
          (satisfies_coreFormula
            (env.pushBound .object value hValue) body).mpr hBody
        rw [coreEnvOfSearch_pushBound env value hValue] at hCore
        exact hCore

/-! ## 纯集合模型到 SearchSignature -/

/-- 把纯隶属结构扩张为所有 sort 都由同一对象域解释的搜索结构。 -/
@[reducible] noncomputable def searchStructureOfSet
    (ℳ : SetTheory.Structure.{0}) : SearchStructure where
  Domain := ℳ.Domain
  nonempty := ℳ.nonempty
  sortInterp := fun _ _ => True
  sortNonempty := fun _ =>
    let ⟨value⟩ := ℳ.nonempty
    ⟨value, trivial⟩
  funcInterp := fun _ _ =>
    Classical.choice ℳ.nonempty
  funcSort := by
    intro symbol arguments hArguments
    trivial
  relInterp := fun relation arguments =>
    match relation, arguments with
    | .member, [left, right] => ℳ.mem left right
    | .predicate symbol, [left, right] =>
        if symbol = extensionalEqPredicate then
          ∀ value, ℳ.mem value left ↔ ℳ.mem value right
        else if symbol = subsetPredicate then
          ∀ value, ℳ.mem value left → ℳ.mem value right
        else
          False
    | _, _ => False

/-- 纯集合环境与扩张后的搜索环境在有效对象变量上相符。 -/
structure SearchAgreement {ℳ : SetTheory.Structure.{0}} {depth : Nat}
    (env : SetTheory.Env ℳ depth)
    (searchEnv : SearchEnv (M := searchStructureOfSet ℳ)) : Prop where
  bound :
    ∀ entry : Fin depth,
      searchEnv.boundVal .object entry.val = env.bound entry
  free :
    ∀ id, searchEnv.freeVal .object id = env.free id

namespace SearchAgreement

/-- 同时压入同一对象后环境相符关系保持。 -/
theorem push {ℳ : SetTheory.Structure.{0}} {depth : Nat}
    {env : SetTheory.Env ℳ depth}
    {searchEnv : SearchEnv (M := searchStructureOfSet ℳ)}
    (hEnv : SearchAgreement env searchEnv) (value : ℳ.Domain) :
    SearchAgreement (env.push value)
      (searchEnv.pushBound .object value trivial) := by
  constructor
  · intro entry
    refine Fin.cases ?_ (fun previous => ?_) entry
    · rfl
    · simpa [Logic.FirstOrder.Env.pushBound, SetTheory.Env.push] using
        hEnv.bound previous
  · intro id
    simpa [Logic.FirstOrder.Env.pushBound, SetTheory.Env.push] using
      hEnv.free id

end SearchAgreement

namespace Translate

/-- 相符环境对纯集合项与搜索项给出相同解释。 -/
theorem eval_searchTerm
    {ℳ : SetTheory.Structure.{0}} {depth : Nat}
    {env : SetTheory.Env ℳ depth}
    {searchEnv : SearchEnv (M := searchStructureOfSet ℳ)}
    (hEnv : SearchAgreement env searchEnv) :
    ∀ term : ProjectTerm depth,
      Logic.FirstOrder.Term.eval searchEnv (searchTerm term) =
        Definitional.Term.eval env term
  | .bound entry => by
      simpa [searchTerm, Logic.FirstOrder.Term.eval,
        Definitional.Term.eval] using hEnv.bound entry
  | .free id => by
      simpa [searchTerm, Logic.FirstOrder.Term.eval,
        Definitional.Term.eval] using hEnv.free id

/-- 纯集合语义与搜索签名语义一致。 -/
theorem satisfies_searchFormula
    {ℳ : SetTheory.Structure.{0}} {depth : Nat}
    {env : SetTheory.Env ℳ depth}
    {searchEnv : SearchEnv (M := searchStructureOfSet ℳ)}
    (hEnv : SearchAgreement env searchEnv) :
    ∀ formula : ProjectFormula depth,
      Definitional.Project.Formula.satisfies env formula ↔
        Logic.FirstOrder.Formula.satisfies searchEnv
          (searchFormula formula)
  | .falsum => by
      simp [Definitional.Project.Formula.satisfies_falsum_iff, searchFormula,
        Logic.FirstOrder.Formula.satisfies]
  | .truth => by
      simp [Definitional.Project.Formula.satisfies_truth_iff, searchFormula,
        Logic.FirstOrder.Formula.satisfies]
  | .mem left right => by
      rw [Definitional.Project.Formula.satisfies_mem_iff]
      simp only [searchFormula, Logic.FirstOrder.Formula.satisfies]
      change
        ℳ.mem (Definitional.Term.eval env left)
            (Definitional.Term.eval env right) ↔
          ℳ.mem
            (Logic.FirstOrder.Term.eval searchEnv (searchTerm left))
            (Logic.FirstOrder.Term.eval searchEnv (searchTerm right))
      rw [eval_searchTerm hEnv left, eval_searchTerm hEnv right]
  | .atom symbol hStage arguments => by
      cases symbol with
      | extensionalEq =>
          rw [Definitional.Project.Formula.satisfies_atom_extensionalEq_iff]
          simp only [searchFormula,
            Logic.FirstOrder.Formula.satisfies, searchStructureOfSet,
            List.map_cons, List.map_nil, subsetPredicate_ne_extensionalEq,
            ↓reduceIte]
          rw [← eval_searchTerm hEnv (arguments 0),
            ← eval_searchTerm hEnv (arguments 1)]
      | subset =>
          rw [Definitional.Project.Formula.satisfies_atom_subset_iff]
          simp only [searchFormula,
            Logic.FirstOrder.Formula.satisfies, searchStructureOfSet,
            List.map_cons, List.map_nil, subsetPredicate_ne_extensionalEq,
            ↓reduceIte]
          rw [← eval_searchTerm hEnv (arguments 0),
            ← eval_searchTerm hEnv (arguments 1)]
  | .neg body =>
      by
        simpa [Definitional.Project.Formula.satisfies_neg_iff, searchFormula,
          Logic.FirstOrder.Formula.satisfies] using
            not_congr (satisfies_searchFormula hEnv body)
  | .conj left right => by
      simpa [Definitional.Project.Formula.satisfies_conj_iff, searchFormula,
        Logic.FirstOrder.Formula.satisfies] using
        and_congr
        (satisfies_searchFormula hEnv left)
        (satisfies_searchFormula hEnv right)
  | .disj left right => by
      simpa [Definitional.Project.Formula.satisfies_disj_iff, searchFormula,
        Logic.FirstOrder.Formula.satisfies] using
        or_congr
        (satisfies_searchFormula hEnv left)
        (satisfies_searchFormula hEnv right)
  | .imp left right => by
      simpa [Definitional.Project.Formula.satisfies_imp_iff, searchFormula,
        Logic.FirstOrder.Formula.satisfies] using
        imp_congr
        (satisfies_searchFormula hEnv left)
        (satisfies_searchFormula hEnv right)
  | .iff left right => by
      simpa [Definitional.Project.Formula.satisfies_iff_iff, searchFormula,
        Logic.FirstOrder.Formula.satisfies] using
        iff_congr
        (satisfies_searchFormula hEnv left)
        (satisfies_searchFormula hEnv right)
  | .forallE body => by
      rw [Definitional.Project.Formula.satisfies_forall_iff]
      simp only [searchFormula,
        Logic.FirstOrder.Formula.satisfies]
      constructor
      · intro hAll value _hValue
        exact
          (satisfies_searchFormula (hEnv.push value) body).mp
            (hAll value)
      · intro hAll value
        exact
          (satisfies_searchFormula (hEnv.push value) body).mpr
            (hAll value trivial)
  | .existsE body => by
      rw [Definitional.Project.Formula.satisfies_exists_iff]
      simp only [searchFormula,
        Logic.FirstOrder.Formula.satisfies]
      constructor
      · rintro ⟨value, hBody⟩
        exact ⟨value, trivial,
          (satisfies_searchFormula (hEnv.push value) body).mp hBody⟩
      · rintro ⟨value, _hValue, hBody⟩
        exact ⟨value,
          (satisfies_searchFormula (hEnv.push value) body).mpr hBody⟩

end Translate

/-- 为纯集合环境构造一个相符的全 sort 搜索环境。 -/
@[reducible] noncomputable def searchEnvOfSet
    {ℳ : SetTheory.Structure.{0}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) :
    SearchEnv (M := searchStructureOfSet ℳ) := by
  classical
  exact {
    boundVal := fun _ index =>
      if hIndex : index < depth then
        env.bound ⟨index, hIndex⟩
      else
        Classical.choice ℳ.nonempty
    freeVal := fun _ id => env.free id
    boundSort := by
      intro sort index
      trivial
    freeSort := by
      intro sort id
      trivial
  }

/-- `searchEnvOfSet` 与原纯集合环境相符。 -/
theorem searchEnvOfSet_agrees
    {ℳ : SetTheory.Structure.{0}} {depth : Nat}
    (env : SetTheory.Env ℳ depth) :
    SearchAgreement env (searchEnvOfSet env) := by
  constructor
  · intro entry
    simp [entry.isLt]
  · intro id
    rfl

/-- core 合取列表逐项满足时，其整体也满足。 -/
theorem coreSatisfiesConjunctionList
    {M : Semantics.Model} (env : Semantics.Env M)
    (formulas : List CoreSyntax.Formula)
    (hFormulas :
      ∀ formula ∈ formulas, Semantics.Formula.Satisfies env formula) :
    Semantics.Formula.Satisfies env
      (CoreSyntax.Formula.conjunctionList formulas) := by
  induction formulas with
  | nil =>
      simp [CoreSyntax.Formula.conjunctionList,
        Semantics.Formula.Satisfies, Semantics.Formula.eval]
  | cons head tail ih =>
      cases tail with
      | nil =>
          simpa [CoreSyntax.Formula.conjunctionList] using
            hFormulas head (by simp)
      | cons next rest =>
          simp only [CoreSyntax.Formula.conjunctionList,
            Semantics.Formula.Satisfies, Semantics.Formula.eval]
          constructor
          · exact hFormulas head (by simp)
          · apply ih
            intro formula hFormula
            exact hFormulas formula (by simp [hFormula])

/-! ## 有限理论切片 -/

/-- 无限集合论公理系统的显式有限搜索切片。 -/
structure TheorySlice (theory : Theory) where
  axioms : List ProjectSentence
  member : ∀ sentence, sentence ∈ axioms → theory sentence

namespace TheorySlice

/-- 空切片。 -/
def empty (theory : Theory) : TheorySlice theory where
  axioms := []
  member := by simp

/-- 由一条已证明属于理论的公理构造单元素切片。 -/
def singleton {theory : Theory} (sentence : ProjectSentence)
    (hSentence : theory sentence) : TheorySlice theory where
  axioms := [sentence]
  member := by
    intro candidate hCandidate
    simp only [List.mem_singleton] at hCandidate
    subst candidate
    exact hSentence

/-- 向切片前端加入一条来源已证明的公理。 -/
def push {theory : Theory} (slice : TheorySlice theory)
    (sentence : ProjectSentence) (hSentence : theory sentence) :
    TheorySlice theory where
  axioms := sentence :: slice.axioms
  member := by
    intro candidate hCandidate
    rcases List.mem_cons.mp hCandidate with rfl | hTail
    · exact hSentence
    · exact slice.member candidate hTail

/-- 沿公理逐字映射把一个切片提升到更强理论。 -/
def mapTheory {weak strong : Theory} (slice : TheorySlice weak)
    (hMap : ∀ sentence, weak sentence → strong sentence) :
    TheorySlice strong where
  axioms := slice.axioms
  member := by
    intro sentence hSentence
    exact hMap sentence (slice.member sentence hSentence)

/-- 切片自身形成的有限理论。 -/
def asTheory {theory : Theory} (slice : TheorySlice theory) : Theory :=
  fun sentence => sentence ∈ slice.axioms

/-- 切片公理逐字包含于原理论。 -/
theorem subtheory {theory : Theory} (slice : TheorySlice theory) :
    Theory.Subtheory slice.asTheory theory :=
  slice.member

/-- 切片句子进入 preprocessing core。 -/
def sourceProblem {theory : Theory} (slice : TheorySlice theory)
    (target : ProjectSentence) : SourcePreprocessing.Problem := {
  premises := slice.axioms.map fun sentence =>
    Translate.coreFormula sentence.formula
  target := Translate.coreFormula target.formula
}

/-- 切片句子进入 SearchSignature 深问题。 -/
def deepProblem {theory : Theory} (slice : TheorySlice theory)
    (target : ProjectSentence) : SourcePreprocessing.DeepProblem := {
  premises := slice.axioms.map fun sentence =>
    Translate.searchFormula sentence.formula
  target := Translate.searchFormula target.formula
}

/-- SearchSignature 上的切片定理提升为原集合论理论的定理。 -/
theorem soundOfSearch {theory : Theory} (slice : TheorySlice theory)
    (target : ProjectSentence)
    (hSearch :
      LogicSoundness.SetLevel.SemanticallyEntails
        (slice.deepProblem target).theory
        (slice.deepProblem target).target) :
    SemanticallyEntails.{0} theory target := by
  intro ℳ hModels free
  let env : SetTheory.Env ℳ 0 := {
    bound := Fin.elim0
    free := free
  }
  let searchEnv := searchEnvOfSet env
  have hAgreement : SearchAgreement env searchEnv :=
    searchEnvOfSet_agrees env
  have hSearchTarget :=
    hSearch searchEnv (by
      intro formula hFormula
      rcases List.mem_map.mp hFormula with
        ⟨sentence, hSentence, rfl⟩
      exact
        (Translate.satisfies_searchFormula hAgreement
          sentence.formula).mp
          (hModels.2 sentence (slice.member sentence hSentence) free))
  exact
    (Translate.satisfies_searchFormula hAgreement
      target.formula).mpr hSearchTarget

/-- 切片 source/deep 问题之间的纯一阶反模型桥。 -/
def firstOrderBridge {theory : Theory} (slice : TheorySlice theory)
    (target : ProjectSentence) :
    SourcePreprocessing.FirstOrderProblemBridge
      (slice.sourceProblem target) (slice.deepProblem target) := by
  constructor
  intro M env hModels hTarget
  refine ⟨{
    model := coreModelOfSearch M
    functionSort := coreModel_functionSort M
    env := coreEnvOfSearch env
    respectsFree := coreEnv_respectsFree env
    satisfies := ?_
  }⟩
  unfold sourceProblem SourcePreprocessing.Problem.refutationSource
  apply coreSatisfiesConjunctionList
  intro formula hFormula
  simp only [List.mem_append, List.mem_singleton] at hFormula
  rcases hFormula with hPremise | hTargetFormula
  · rcases List.mem_map.mp hPremise with
      ⟨sentence, hSentence, rfl⟩
    exact
      (satisfies_coreFormula env sentence.formula).mpr <|
        hModels (Translate.searchFormula sentence.formula) <| by
          exact List.mem_map.mpr ⟨sentence, hSentence, rfl⟩
  · subst formula
    have hCoreTarget :
        ¬ Semantics.Formula.Satisfies
          (coreEnvOfSearch env)
          (Translate.coreFormula target.formula) := by
      intro hCore
      exact hTarget <|
        (satisfies_coreFormula env target.formula).mp hCore
    simpa [Semantics.Formula.Satisfies, Semantics.Formula.eval] using
      hCoreTarget

/-- 一个集合论切片对应的裸 `prove_auto` proof-carrying 请求。 -/
@[reducible] def goalRequest {theory : Theory}
    (slice : TheorySlice theory) (target : ProjectSentence)
    (settings : SourcePreprocessing.FirstOrderSettings := {})
    (avatarConfig : SourcePreprocessing.AvatarConfig := {})
    (label : String := "pure set theory") :
    ProveAutoRequest.GoalRequest
      (SemanticallyEntails.{0} theory target) where
  run :=
    let problem := slice.deepProblem target
    let attempt :=
      SourcePreprocessing.runFirstOrderProvider
        (slice.sourceProblem target) problem
        (slice.firstOrderBridge target)
        settings avatarConfig label
    {
      closed := attempt.closed
      summary := attempt.summary
      sound := fun hClosed =>
        slice.soundOfSearch target <|
          ProveAutoRequest.GoalAttempt.backendSoundOfClosed
            problem attempt hClosed
    }

end TheorySlice

end Automation

namespace KP

/-- KP 的固定有限公理切片；模式实例按证明需要继续 `push`。 -/
def automationCoreSlice : Automation.TheorySlice SetTheory.KP :=
  Automation.TheorySlice.empty SetTheory.KP
    |>.push Axioms.extensionality Axiom.extensionality
    |>.push Axioms.emptySet Axiom.emptySet
    |>.push Axioms.pairing Axiom.pairing
    |>.push Axioms.union Axiom.union
    |>.push Axioms.infinity Axiom.infinity
    |>.push Axioms.foundation Axiom.foundation

end KP

namespace ZF

/-- ZF 的固定有限公理切片；分离/收集实例按证明需要继续 `push`。 -/
def automationCoreSlice : Automation.TheorySlice SetTheory.ZF :=
  Automation.TheorySlice.empty SetTheory.ZF
    |>.push Axioms.extensionality Axiom.extensionality
    |>.push Axioms.emptySet Axiom.emptySet
    |>.push Axioms.pairing Axiom.pairing
    |>.push Axioms.union Axiom.union
    |>.push Axioms.powerSet Axiom.powerSet
    |>.push Axioms.infinity Axiom.infinity
    |>.push Axioms.foundation Axiom.foundation

end ZF

namespace ZFC

/-- ZFC 的固定有限公理切片；模式实例按证明需要继续 `push`。 -/
def automationCoreSlice : Automation.TheorySlice SetTheory.ZFC :=
  ZF.automationCoreSlice
    |>.mapTheory (fun _ hSentence => Axiom.zf hSentence)
    |>.push Axioms.choice Axiom.choice

end ZFC

end SetTheory
end YesMetaZFC
