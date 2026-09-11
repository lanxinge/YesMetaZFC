import YesMetaZFC.Model.SetTheory.ProjectSemantics

/-! # 类型化纯公式到 Project 公式的反向桥

两类变量均映入显式的有限参数槽，量词只在槽前压入新变量。此翻译生成自由闭合
的 Project 正文，使当前纯语言的任意公式可以使用已有 ZF 公理模式。
-/
namespace YesMetaZFC.SetTheory.Definitional.Project.FromFirstOrder
open Logic.FirstOrder
set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature
universe x

abbrev Slots (context : SortContext ℒ) (depth : Nat) :=
  {sort : SetSort} → Variable context sort → Fin depth

def lift {context : SortContext ℒ} {depth : Nat} (slots : Slots context depth) (introduced : SetSort) :
    Slots (introduced :: context) (depth + 1)
  | _, .here => 0
  | _, .there previous => (slots previous).succ

def termIndex {bound free : SortContext ℒ} {depth : Nat}
    (bs : Slots bound depth) (fs : Slots free depth) :
    {sort : SetSort} → Logic.FirstOrder.Term ℒ bound free sort → Fin depth
  | _, .bvar entry => bs entry
  | _, .fvar entry => fs entry
  | _, .app symbol _ => nomatch symbol

def translate {bound free : SortContext ℒ} {depth : Nat}
    (bs : Slots bound depth) (fs : Slots free depth) :
    Logic.FirstOrder.Formula ℒ bound free → Project.Formula 1 depth
  | .falsum => .falsum
  | .truth => .truth
  | .equal left right => Project.Formula.extensionalEq (.bound (termIndex bs fs left)) (.bound (termIndex bs fs right))
  | .rel .membership (.cons left (.cons right .nil)) =>
      .mem (.bound (termIndex bs fs left)) (.bound (termIndex bs fs right))
  | .neg body => .neg (translate bs fs body)
  | .conj left right => .conj (translate bs fs left) (translate bs fs right)
  | .disj left right => .disj (translate bs fs left) (translate bs fs right)
  | .imp left right => .imp (translate bs fs left) (translate bs fs right)
  | .iff left right => .iff (translate bs fs left) (translate bs fs right)
  | .forallE sort body => .forallE (translate (lift bs sort) (fun entry => (fs entry).succ) body)
  | .existsE sort body => .existsE (translate (lift bs sort) (fun entry => (fs entry).succ) body)

theorem freeClosed {bound free : SortContext ℒ} {depth : Nat}
    (bs : Slots bound depth) (fs : Slots free depth) (formula : Logic.FirstOrder.Formula ℒ bound free) :
    (translate bs fs formula).FreeClosed := by
  induction formula generalizing depth with
  | falsum => simp only [translate, Definitional.Formula.FreeClosed]
  | truth => simp only [translate, Definitional.Formula.FreeClosed]
  | equal left right => exact (Project.Formula.extensionalEq_freeClosed_iff _ _).mpr ⟨rfl, rfl⟩
  | rel symbol args =>
      cases symbol
      match args with
      | .cons left (.cons right .nil) =>
        simp only [translate, Definitional.Formula.FreeClosed]
        exact ⟨rfl, rfl⟩
  | neg body ih => simpa only [translate, Definitional.Formula.FreeClosed] using ih bs fs
  | conj left right ihLeft ihRight =>
      simp only [translate, Definitional.Formula.FreeClosed]
      exact ⟨ihLeft _ _, ihRight _ _⟩
  | disj left right ihLeft ihRight =>
      simp only [translate, Definitional.Formula.FreeClosed]
      exact ⟨ihLeft _ _, ihRight _ _⟩
  | imp left right ihLeft ihRight =>
      simp only [translate, Definitional.Formula.FreeClosed]
      exact ⟨ihLeft _ _, ihRight _ _⟩
  | iff left right ihLeft ihRight =>
      simp only [translate, Definitional.Formula.FreeClosed]
      exact ⟨ihLeft _ _, ihRight _ _⟩
  | forallE sort body ih =>
      simp only [translate, Definitional.Formula.FreeClosed]
      exact ih _ _
  | existsE sort body ih =>
      simp only [translate, Definitional.Formula.FreeClosed]
      exact ih _ _

theorem term_correct {ℳ : Logic.FirstOrder.Structure.{0, 0, 0, x} ℒ}
    {bound free : SortContext ℒ} {depth : Nat} (bs : Slots bound depth) (fs : Slots free depth)
    (env : Logic.FirstOrder.Env ℳ bound free) (project : SetTheory.Env (FirstOrderSemantics.reduct ℳ) depth)
    (hBound : ∀ entry : Variable bound SetSort.set, project.bound (bs entry) = env.boundVal entry)
    (hFree : ∀ entry : Variable free SetSort.set, project.bound (fs entry) = env.freeVal entry)
    (term : Logic.FirstOrder.Term ℒ bound free SetSort.set) :
    project.bound (termIndex bs fs term) = term.eval env := by
  match term with
  | .bvar entry => exact hBound entry
  | .fvar entry => exact hFree entry
  | .app symbol _ => exact nomatch symbol

/-- 外延模型中，翻译保持任意公式的语义；不要求模型外部良基或标准。 -/
theorem correct {ℳ : Logic.FirstOrder.Structure.{0, 0, 0, x} ℒ}
    (hExt : Extensional (FirstOrderSemantics.reduct ℳ))
    {bound free : SortContext ℒ} {depth : Nat} (formula : Logic.FirstOrder.Formula ℒ bound free)
    (bs : Slots bound depth) (fs : Slots free depth)
    (env : Logic.FirstOrder.Env ℳ bound free) (project : SetTheory.Env (FirstOrderSemantics.reduct ℳ) depth)
    (hBound : ∀ entry : Variable bound SetSort.set, project.bound (bs entry) = env.boundVal entry)
    (hFree : ∀ entry : Variable free SetSort.set, project.bound (fs entry) = env.freeVal entry) :
    Project.Formula.satisfies project (translate bs fs formula) ↔ formula.satisfies env := by
  induction formula generalizing depth with
  | falsum => simp only [translate, Project.Formula.satisfies, Definitional.Semantics.satisfies, Logic.FirstOrder.Formula.satisfies]
  | truth => simp only [translate, Project.Formula.satisfies, Definitional.Semantics.satisfies, Logic.FirstOrder.Formula.satisfies]
  | @equal bound free sort left right =>
      cases sort
      simp only [translate.eq_def, Project.Formula.satisfies_extensionalEq_iff_eq hExt,
        Definitional.Term.eval, term_correct bs fs env project hBound hFree,
        Logic.FirstOrder.Formula.satisfies]
      rfl
  | rel symbol args =>
      cases symbol
      match args with
      | .cons left (.cons right .nil) =>
        simp only [translate.eq_def, Project.Formula.satisfies_mem_iff,
          Definitional.Term.eval, term_correct bs fs env project hBound hFree,
          Logic.FirstOrder.Formula.satisfies, Arguments.eval]
        rfl
  | neg body ih =>
      simp only [translate, Project.Formula.satisfies, Definitional.Semantics.satisfies, Logic.FirstOrder.Formula.satisfies]
      exact not_congr (ih _ _ _ _ hBound hFree)
  | conj left right ihLeft ihRight =>
      simp only [translate, Project.Formula.satisfies, Definitional.Semantics.satisfies, Logic.FirstOrder.Formula.satisfies]
      exact and_congr (ihLeft _ _ _ _ hBound hFree) (ihRight _ _ _ _ hBound hFree)
  | disj left right ihLeft ihRight =>
      simp only [translate, Project.Formula.satisfies, Definitional.Semantics.satisfies, Logic.FirstOrder.Formula.satisfies]
      exact or_congr (ihLeft _ _ _ _ hBound hFree) (ihRight _ _ _ _ hBound hFree)
  | imp left right ihLeft ihRight =>
      simp only [translate, Project.Formula.satisfies, Definitional.Semantics.satisfies, Logic.FirstOrder.Formula.satisfies]
      exact imp_congr (ihLeft _ _ _ _ hBound hFree) (ihRight _ _ _ _ hBound hFree)
  | iff left right ihLeft ihRight =>
      simp only [translate, Project.Formula.satisfies, Definitional.Semantics.satisfies, Logic.FirstOrder.Formula.satisfies]
      exact iff_congr (ihLeft _ _ _ _ hBound hFree) (ihRight _ _ _ _ hBound hFree)
  | forallE sort body ih =>
      cases sort
      simp only [translate, Project.Formula.satisfies, Definitional.Semantics.satisfies, Logic.FirstOrder.Formula.satisfies]
      apply forall_congr'
      intro value
      apply ih _ _ (env.pushBound value) (project.push value)
      · intro entry; cases entry with
        | here => rfl
        | there previous => exact hBound previous
      · exact hFree
  | existsE sort body ih =>
      cases sort
      simp only [translate, Project.Formula.satisfies, Definitional.Semantics.satisfies, Logic.FirstOrder.Formula.satisfies]
      apply exists_congr
      intro value
      apply ih _ _ (env.pushBound value) (project.push value)
      · intro entry; cases entry with
        | here => rfl
        | there previous => exact hBound previous
      · exact hFree

end YesMetaZFC.SetTheory.Definitional.Project.FromFirstOrder
