import YesMetaZFC.Model.FirstOrder.Semantics
import YesMetaZFC.Logic.FreeVariableSupport.Basic

/-!
# 自由变量支持的语义接口

本模块把上下文内在的支持掩码连接到类型化环境：

* 环境一致性只比较真实存在的类型化变量；
* 项解释与公式满足性只依赖各自的自由变量支持；
* overlay 与有限 merge 保持可计算，不需要经典选择；
* bound 上下文由类型索引固定，压栈保持性只需结构归纳。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x

namespace Env

/-- 两个环境在完整 bound 上下文上逐点一致。 -/
def SameBoundStack {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (left right : Env M bound free) : Prop :=
  ∀ {sort} (entry : Variable bound sort),
    left.boundVal entry = right.boundVal entry

namespace SameBoundStack

/-- bound 环境一致性的自反性。 -/
theorem refl {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} (env : Env M bound free) :
    SameBoundStack env env :=
  fun _ => rfl

/-- bound 环境一致性的对称性。 -/
theorem symm {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {left right : Env M bound free}
    (hBound : SameBoundStack left right) :
    SameBoundStack right left :=
  fun entry => (hBound entry).symm

/-- bound 环境一致性的传递性。 -/
theorem trans {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {left middle right : Env M bound free}
    (hLeft : SameBoundStack left middle)
    (hRight : SameBoundStack middle right) :
    SameBoundStack left right :=
  fun entry => (hLeft entry).trans (hRight entry)

/-- 两侧压入同一个 bound 值后仍逐点一致。 -/
theorem pushBound {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    {left right : Env M bound free}
    (hBound : SameBoundStack left right) (value : M.Carrier sort) :
    SameBoundStack (left.pushBound value) (right.pushBound value) := by
  intro target entry
  cases entry with
  | here =>
      rfl
  | there previous =>
      exact hBound previous

end SameBoundStack

/--
两个环境在给定自由变量支持上一致。
bound 赋值整体一致；free 赋值只比较支持中的上下文位置。
-/
def AgreesOn {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (support : FreeSupport σ free)
    (left right : Env M bound free) : Prop :=
  SameBoundStack left right ∧
    ∀ {sort} (entry : Variable free sort),
      support.Contains entry.position →
        left.freeVal entry = right.freeVal entry

namespace AgreesOn

/-- 环境在任意支持上与自身一致。 -/
theorem refl {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (support : FreeSupport σ free) (env : Env M bound free) :
    AgreesOn support env env :=
  ⟨SameBoundStack.refl env, fun _ _ => rfl⟩

/-- 支持上一致性是对称的。 -/
theorem symm {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    {support : FreeSupport σ free} {left right : Env M bound free}
    (hEnv : AgreesOn support left right) :
    AgreesOn support right left :=
  ⟨Env.SameBoundStack.symm hEnv.1,
    fun entry hMem => (hEnv.2 entry hMem).symm⟩

/-- 支持上一致性是传递的。 -/
theorem trans {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    {support : FreeSupport σ free}
    {left middle right : Env M bound free}
    (hLeft : AgreesOn support left middle)
    (hRight : AgreesOn support middle right) :
    AgreesOn support left right :=
  ⟨Env.SameBoundStack.trans hLeft.1 hRight.1,
    fun entry hMem => (hLeft.2 entry hMem).trans (hRight.2 entry hMem)⟩

/-- 在大支持上一致可限制到任意子支持。 -/
theorem mono {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    {small large : FreeSupport σ free}
    {left right : Env M bound free}
    (hEnv : AgreesOn large left right)
    (hSubset : FreeSupport.Subset small large) :
    AgreesOn small left right :=
  ⟨hEnv.1, fun entry hMem => hEnv.2 entry (hSubset entry.position hMem)⟩

/-- 两侧压入同一个 bound 值后，free 支持上一致性保持。 -/
theorem pushBound {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    {support : FreeSupport σ free}
    {left right : Env M bound free}
    (hEnv : AgreesOn support left right) (value : M.Carrier sort) :
    AgreesOn support (left.pushBound value) (right.pushBound value) :=
  ⟨Env.SameBoundStack.pushBound hEnv.1 value,
    fun entry hMem => hEnv.2 entry hMem⟩

end AgreesOn
end Env

mutual

/-- 项解释只依赖其自由变量支持和完整 bound 赋值。 -/
theorem Term.eval_eq_of_agreesOn {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sort : σ.SortSymbol}
    {left right : Env M bound free} (term : Term σ bound free sort)
    (hEnv : Env.AgreesOn term.freeSupport left right) :
    term.eval left = term.eval right := by
  cases term with
  | bvar entry =>
      exact hEnv.1 entry
  | fvar entry =>
      exact hEnv.2 entry (by
        simp [Term.freeSupport])
  | app function arguments =>
      exact congrArg (M.funcInterp function)
        (Arguments.eval_eq_of_agreesOn arguments hEnv)

/-- 异质参数列的解释只依赖其自由变量支持。 -/
theorem Arguments.eval_eq_of_agreesOn {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} {sorts : List σ.SortSymbol}
    {left right : Env M bound free}
    (arguments : Arguments σ bound free sorts)
    (hEnv : Env.AgreesOn arguments.freeSupport left right) :
    arguments.eval left = arguments.eval right := by
  cases arguments with
  | nil =>
      rfl
  | cons term rest =>
      have hTerm : Env.AgreesOn term.freeSupport left right :=
        hEnv.mono (fun position hMem =>
          FreeSupport.contains_union.mpr (Or.inl hMem))
      have hRest : Env.AgreesOn rest.freeSupport left right :=
        hEnv.mono (fun position hMem =>
          FreeSupport.contains_union.mpr (Or.inr hMem))
      simp [Arguments.eval, Term.eval_eq_of_agreesOn term hTerm,
        Arguments.eval_eq_of_agreesOn rest hRest]

end

namespace Formula

/-- 公式满足性只依赖其自由变量支持和完整 bound 赋值。 -/
theorem satisfies_iff_of_agreesOn {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    {left right : Env M bound free} (φ : Formula σ bound free)
    (hEnv : Env.AgreesOn φ.freeSupport left right) :
    satisfies left φ ↔ satisfies right φ := by
  induction φ with
  | falsum =>
      simp [satisfies]
  | truth =>
      simp [satisfies]
  | rel relation arguments =>
      simp [satisfies, Arguments.eval_eq_of_agreesOn arguments hEnv]
  | equal leftTerm rightTerm =>
      have hLeft : Env.AgreesOn leftTerm.freeSupport left right :=
        hEnv.mono (fun position hMem =>
          FreeSupport.contains_union.mpr (Or.inl hMem))
      have hRight : Env.AgreesOn rightTerm.freeSupport left right :=
        hEnv.mono (fun position hMem =>
          FreeSupport.contains_union.mpr (Or.inr hMem))
      simp [satisfies, Term.eval_eq_of_agreesOn leftTerm hLeft,
        Term.eval_eq_of_agreesOn rightTerm hRight]
  | neg body ih =>
      simpa [satisfies] using not_congr (ih hEnv)
  | conj leftFormula rightFormula ihLeft ihRight
  | disj leftFormula rightFormula ihLeft ihRight
  | imp leftFormula rightFormula ihLeft ihRight
  | iff leftFormula rightFormula ihLeft ihRight =>
      have hLeft : Env.AgreesOn leftFormula.freeSupport left right :=
        hEnv.mono (fun position hMem =>
          FreeSupport.contains_union.mpr (Or.inl hMem))
      have hRight : Env.AgreesOn rightFormula.freeSupport left right :=
        hEnv.mono (fun position hMem =>
          FreeSupport.contains_union.mpr (Or.inr hMem))
      simp [satisfies, ihLeft hLeft, ihRight hRight]
  | forallE sort body ih =>
      constructor
      · intro hSat value
        exact (ih (hEnv.pushBound value)).mp (hSat value)
      · intro hSat value
        exact (ih (hEnv.pushBound value)).mpr (hSat value)
  | existsE sort body ih =>
      constructor
      · rintro ⟨value, hBody⟩
        exact ⟨value, (ih (hEnv.pushBound value)).mp hBody⟩
      · rintro ⟨value, hBody⟩
        exact ⟨value, (ih (hEnv.pushBound value)).mpr hBody⟩

end Formula

namespace Env

/-- 一个带局部 free 支持的类型化环境。 -/
structure Supported {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ)
    (bound free : SortContext σ) where
  support : FreeSupport σ free
  env : Env M bound free

namespace Supported

/-- 有限环境族中的支持两两不交。 -/
def PairwiseDisjoint {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ} :
    List (Supported M bound free) → Prop
  | [] => True
  | entry :: rest =>
      (∀ other, other ∈ rest →
        FreeSupport.Disjoint entry.support other.support) ∧
      PairwiseDisjoint rest

/-- 有限环境族与基环境共享完整 bound 赋值。 -/
def AllSameBoundStack {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (base : Env M bound free)
    (entries : List (Supported M bound free)) : Prop :=
  ∀ entry, entry ∈ entries → SameBoundStack base entry.env

end Supported

/-- 在给定支持上用 source 覆盖 base 的 free 赋值。 -/
def overlay {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (support : FreeSupport σ free)
    (source base : Env M bound free) : Env M bound free where
  boundVal := base.boundVal
  freeVal := fun entry =>
    match support entry.position with
    | true => source.freeVal entry
    | false => base.freeVal entry

/-- overlay 在覆盖支持上投影回源环境。 -/
theorem overlay_agreesOn_source {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    {support : FreeSupport σ free}
    {source base : Env M bound free}
    (hBound : SameBoundStack base source) :
    AgreesOn support (overlay support source base) source := by
  constructor
  · exact hBound
  · intro sort entry hMem
    change support entry.position = true at hMem
    simp [overlay, hMem]

/-- 若局部支持与覆盖支持不交，overlay 在局部支持上投影回基环境。 -/
theorem overlay_agreesOn_base_of_disjoint {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    {overlaySupport support : FreeSupport σ free}
    {source base : Env M bound free}
    (hDisjoint : FreeSupport.Disjoint overlaySupport support) :
    AgreesOn support (overlay overlaySupport source base) base := by
  constructor
  · exact SameBoundStack.refl base
  · intro sort entry hMem
    have hNotMem : ¬ overlaySupport.Contains entry.position :=
      fun hOverlay => hDisjoint entry.position hOverlay hMem
    change ¬ overlaySupport entry.position = true at hNotMem
    cases hValue : overlaySupport entry.position with
    | false =>
        simp [overlay, hValue]
    | true =>
        exact False.elim (hNotMem hValue)

/-- 按列表顺序合并有限支持环境；较早条目的支持优先。 -/
def merge {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (base : Env M bound free) :
    List (Supported M bound free) → Env M bound free
  | [] => base
  | entry :: rest => overlay entry.support entry.env (merge base rest)

/-- 合并环境保留基环境的完整 bound 赋值。 -/
theorem merge_sameBoundStack {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (base : Env M bound free) (entries : List (Supported M bound free)) :
    SameBoundStack (merge base entries) base := by
  induction entries with
  | nil =>
      exact SameBoundStack.refl base
  | cons entry rest ih =>
      exact ih

/-- 若没有条目负责某个位置，合并环境保留基环境的值。 -/
theorem merge_freeVal_of_not_mem {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (base : Env M bound free) (entries : List (Supported M bound free))
    {sort : σ.SortSymbol} (freeEntry : Variable free sort)
    (hMissing : ∀ entry, entry ∈ entries →
      ¬ entry.support.Contains freeEntry.position) :
    (merge base entries).freeVal freeEntry = base.freeVal freeEntry := by
  induction entries with
  | nil =>
      rfl
  | cons entry rest ih =>
      have hHead : ¬ entry.support.Contains freeEntry.position :=
        hMissing entry List.mem_cons_self
      have hRest : ∀ other, other ∈ rest →
          ¬ other.support.Contains freeEntry.position := by
        intro other hMem
        exact hMissing other (List.mem_cons_of_mem entry hMem)
      change ¬ entry.support freeEntry.position = true at hHead
      cases hValue : entry.support freeEntry.position with
      | false =>
          simpa [merge, overlay, hValue] using ih hRest
      | true =>
          exact False.elim (hHead hValue)

private theorem agreesOn_merge_cons_of_disjoint
    {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    {base source : Env M bound free}
    {support : FreeSupport σ free}
    {first : Supported M bound free}
    {rest : List (Supported M bound free)}
    (hDisjoint : FreeSupport.Disjoint first.support support)
    (hEnv : AgreesOn support (merge base rest) source) :
    AgreesOn support (merge base (first :: rest)) source := by
  constructor
  · exact hEnv.1
  · intro sort entry hMem
    have hNotMem : ¬ first.support.Contains entry.position :=
      fun hFirst => hDisjoint entry.position hFirst hMem
    change ¬ first.support entry.position = true at hNotMem
    cases hValue : first.support entry.position with
    | false =>
        simpa [merge, overlay, hValue] using hEnv.2 entry hMem
    | true =>
        exact False.elim (hNotMem hValue)

/--
两两不交且共享 bound 赋值的有限环境族可同时合并。
结果在每个条目的支持上都与该条目的源环境一致。
-/
theorem merge_agreesOn {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ}
    {bound free : SortContext σ}
    (base : Env M bound free) (entries : List (Supported M bound free))
    (hDisjoint : Supported.PairwiseDisjoint entries)
    (hBound : Supported.AllSameBoundStack base entries) :
    ∀ entry, entry ∈ entries →
      AgreesOn entry.support (merge base entries) entry.env := by
  induction entries with
  | nil =>
      intro entry hMem
      cases hMem
  | cons first rest ih =>
      rcases hDisjoint with ⟨hFirstDisjoint, hRestDisjoint⟩
      have hRestBound : Supported.AllSameBoundStack base rest := by
        intro other hOther
        exact hBound other (List.mem_cons_of_mem first hOther)
      intro entry hMem
      rcases List.mem_cons.mp hMem with hEq | hRestMem
      · cases hEq
        constructor
        · exact Env.SameBoundStack.trans
            (merge_sameBoundStack base (first :: rest))
            (hBound first List.mem_cons_self)
        · intro sort freeEntry hSupport
          change first.support freeEntry.position = true at hSupport
          simp [merge, overlay, hSupport]
      · apply agreesOn_merge_cons_of_disjoint
          (hFirstDisjoint entry hRestMem)
        exact ih hRestDisjoint hRestBound entry hRestMem

end Env
end FirstOrder
end Logic
end YesMetaZFC
