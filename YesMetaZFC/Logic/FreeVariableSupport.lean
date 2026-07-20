import YesMetaZFC.Logic.Semantics

/-!
# 一阶自由变量支持与环境合并

本模块把自由变量支持集保留为有限列表。列表允许重复，但所有语义接口都只通过成员
关系消费它，因此它在证明层等价于有限集合，同时避免给语义核引入额外容器依赖。

有限环境合并采用有序 overlay：较早条目的支持优先。两两不交时，合并环境在每个条目
的支持上都投影回该条目的环境；这正是 AVATAR component 语义分解后续需要的公共基础。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder

universe u v w x

/-- 自由变量由 sort 与稳定编号共同确定。 -/
abbrev FreeVariable (σ : Signature.{u, v, w}) := σ.SortSymbol × FreeVarId

/-- 有限自由变量支持。重复成员不影响环境一致性语义。 -/
abbrev FreeVariable.Support (σ : Signature.{u, v, w}) := List (FreeVariable σ)

namespace FreeVariable.Support

/-- 两个自由变量支持不相交。 -/
def Disjoint {σ : Signature.{u, v, w}}
    (left right : FreeVariable.Support σ) : Prop :=
  ∀ fv, fv ∈ left → fv ∈ right → False

/-- 支持不交关系是对称的。 -/
theorem Disjoint.symm {σ : Signature.{u, v, w}}
    {left right : FreeVariable.Support σ} (hDisjoint : Disjoint left right) :
    Disjoint right left :=
  fun fv hRight hLeft => hDisjoint fv hLeft hRight

end FreeVariable.Support

namespace Term

mutual
  /-- 项的自由变量支持。 -/
  def freeSupport {σ : Signature.{u, v, w}} : Term σ → FreeVariable.Support σ
    | .var (.bvar ..) => []
    | .var (.fvar sort id) => [(sort, id)]
    | .app _ args => freeSupportList args

  /-- 项列表的自由变量支持。 -/
  def freeSupportList {σ : Signature.{u, v, w}} :
      List (Term σ) → FreeVariable.Support σ
    | [] => []
    | term :: rest => freeSupport term ++ freeSupportList rest
end

end Term

namespace Formula

/-- 公式的自由变量支持；LN bound variable 不进入支持。 -/
def freeSupport {σ : Signature.{u, v, w}} : Formula σ → FreeVariable.Support σ
  | .falsum => []
  | .truth => []
  | .rel _ args => Term.freeSupportList args
  | .equal left right => Term.freeSupport left ++ Term.freeSupport right
  | .neg φ => freeSupport φ
  | .conj φ ψ => freeSupport φ ++ freeSupport ψ
  | .disj φ ψ => freeSupport φ ++ freeSupport ψ
  | .imp φ ψ => freeSupport φ ++ freeSupport ψ
  | .iff φ ψ => freeSupport φ ++ freeSupport ψ
  | .forallE _ body => freeSupport body
  | .existsE _ body => freeSupport body

end Formula

namespace Env

/-- 两个环境具有相同的 LN bound stack。 -/
def SameBoundStack {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (left right : Env M) : Prop :=
  ∀ sort index, left.boundVal sort index = right.boundVal sort index

namespace SameBoundStack

/-- bound stack 一致性的自反性。 -/
theorem refl {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (env : Env M) : SameBoundStack env env :=
  fun _ _ => rfl

/-- bound stack 一致性的对称性。 -/
theorem symm {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {left right : Env M} (hBound : SameBoundStack left right) :
    SameBoundStack right left :=
  fun sort index => (hBound sort index).symm

/-- bound stack 一致性的传递性。 -/
theorem trans {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {left middle right : Env M} (hLeft : SameBoundStack left middle)
    (hRight : SameBoundStack middle right) : SameBoundStack left right :=
  fun sort index => (hLeft sort index).trans (hRight sort index)

end SameBoundStack

/--
两个环境在给定自由变量支持上一致。

bound stack 始终整体一致；free assignment 只要求在支持成员上相等。
-/
def AgreesOn {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (support : FreeVariable.Support σ) (left right : Env M) : Prop :=
  SameBoundStack left right ∧
    ∀ fv, fv ∈ support →
      left.freeVal fv.1 fv.2 = right.freeVal fv.1 fv.2

namespace AgreesOn

/-- 环境在任意支持上与自身一致。 -/
theorem refl {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (support : FreeVariable.Support σ) (env : Env M) : AgreesOn support env env :=
  ⟨SameBoundStack.refl env, fun _ _ => rfl⟩

/-- 支持上一致性是对称的。 -/
theorem symm {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {support : FreeVariable.Support σ} {left right : Env M}
    (hEnv : AgreesOn support left right) : AgreesOn support right left :=
  ⟨hEnv.1.symm, fun fv hMem => (hEnv.2 fv hMem).symm⟩

/-- 支持上一致性是传递的。 -/
theorem trans {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {support : FreeVariable.Support σ} {left middle right : Env M}
    (hLeft : AgreesOn support left middle) (hRight : AgreesOn support middle right) :
    AgreesOn support left right :=
  ⟨hLeft.1.trans hRight.1,
    fun fv hMem => (hLeft.2 fv hMem).trans (hRight.2 fv hMem)⟩

/-- 在大支持上一致可限制到任意子支持。 -/
theorem mono {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    {small large : FreeVariable.Support σ} {left right : Env M}
    (hEnv : AgreesOn large left right)
    (hSubset : ∀ fv, fv ∈ small → fv ∈ large) :
    AgreesOn small left right :=
  ⟨hEnv.1, fun fv hMem => hEnv.2 fv (hSubset fv hMem)⟩

/-- 两侧压入同一个 bound 值后，原自由变量支持上的一致性保持。 -/
theorem pushBound {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} {support : FreeVariable.Support σ}
    {left right : Env M} (hEnv : AgreesOn support left right)
    (sort : σ.SortSymbol) (value : M.Domain) (hValue : M.sortInterp sort value) :
    AgreesOn support (left.pushBound sort value hValue)
      (right.pushBound sort value hValue) := by
  constructor
  · intro target index
    by_cases hTarget : target = sort
    · subst hTarget
      cases index with
      | zero =>
          simp [Env.pushBound]
      | succ previous =>
          simpa [Env.pushBound] using hEnv.1 target previous
    · simpa [Env.pushBound, hTarget] using hEnv.1 target index
  · intro fv hMem
    simpa [Env.pushBound] using hEnv.2 fv hMem

end AgreesOn

end Env

namespace Term

/-- 项解释只依赖其自由变量支持和完整 bound stack。 -/
theorem eval_eq_of_agreesOn {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {left right : Env M} :
    ∀ term : Term σ, Env.AgreesOn (freeSupport term) left right →
      eval left term = eval right term := by
  refine Term.rec
    (motive_1 := fun term =>
      Env.AgreesOn (freeSupport term) left right →
        eval left term = eval right term)
    (motive_2 := fun terms =>
      Env.AgreesOn (freeSupportList terms) left right →
        terms.map (eval left) = terms.map (eval right))
    ?_ ?_ ?_ ?_
  · intro fv hEnv
    cases fv with
    | bvar sort index =>
        simpa [freeSupport, eval] using hEnv.1 sort index
    | fvar sort id =>
        simpa [freeSupport, eval] using
          hEnv.2 (sort, id) (by simp [freeSupport])
  · intro function args ihArgs hEnv
    simpa [eval] using congrArg (M.funcInterp function) (ihArgs hEnv)
  · intro _hEnv
    rfl
  · intro head tail ihHead ihTail hEnv
    have hHead : Env.AgreesOn (freeSupport head) left right :=
      hEnv.mono (by
        intro fv hMem
        simp [freeSupportList, hMem])
    have hTail : Env.AgreesOn (freeSupportList tail) left right :=
      hEnv.mono (by
        intro fv hMem
        simp [freeSupportList, hMem])
    simp [ihHead hHead, ihTail hTail]

/-- 项列表的逐项解释只依赖该列表的自由变量支持。 -/
theorem evalList_eq_of_agreesOn {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} {left right : Env M}
    (terms : List (Term σ))
    (hEnv : Env.AgreesOn (freeSupportList terms) left right) :
    terms.map (eval left) = terms.map (eval right) := by
  induction terms with
  | nil =>
      rfl
  | cons head tail ih =>
      have hHead : Env.AgreesOn (freeSupport head) left right :=
        hEnv.mono (by
          intro fv hMem
          simp [freeSupportList, hMem])
      have hTail : Env.AgreesOn (freeSupportList tail) left right :=
        hEnv.mono (by
          intro fv hMem
          simp [freeSupportList, hMem])
      simp [eval_eq_of_agreesOn head hHead, ih hTail]

end Term

namespace Formula

/-- 公式满足性只依赖其自由变量支持和完整 bound stack。 -/
theorem satisfies_iff_of_agreesOn {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    {left right : Env M} (φ : Formula σ)
    (hEnv : Env.AgreesOn (freeSupport φ) left right) :
    satisfies left φ ↔ satisfies right φ := by
  induction φ generalizing left right with
  | falsum =>
      simp [satisfies]
  | truth =>
      simp [satisfies]
  | rel relation args =>
      have hArgs := Term.evalList_eq_of_agreesOn args
        (by simpa [freeSupport] using hEnv)
      simp [satisfies, hArgs]
  | equal leftTerm rightTerm =>
      have hLeft : Env.AgreesOn (Term.freeSupport leftTerm) left right :=
        hEnv.mono (by
          intro fv hMem
          simp [freeSupport, hMem])
      have hRight : Env.AgreesOn (Term.freeSupport rightTerm) left right :=
        hEnv.mono (by
          intro fv hMem
          simp [freeSupport, hMem])
      simp [satisfies, Term.eval_eq_of_agreesOn leftTerm hLeft,
        Term.eval_eq_of_agreesOn rightTerm hRight]
  | neg φ ih =>
      simpa [satisfies] using not_congr (ih hEnv)
  | conj φ ψ ihφ ihψ =>
      have hφ : Env.AgreesOn (freeSupport φ) left right :=
        hEnv.mono (by
          intro fv hMem
          simp [freeSupport, hMem])
      have hψ : Env.AgreesOn (freeSupport ψ) left right :=
        hEnv.mono (by
          intro fv hMem
          simp [freeSupport, hMem])
      simp [satisfies, ihφ hφ, ihψ hψ]
  | disj φ ψ ihφ ihψ =>
      have hφ : Env.AgreesOn (freeSupport φ) left right :=
        hEnv.mono (by
          intro fv hMem
          simp [freeSupport, hMem])
      have hψ : Env.AgreesOn (freeSupport ψ) left right :=
        hEnv.mono (by
          intro fv hMem
          simp [freeSupport, hMem])
      simp [satisfies, ihφ hφ, ihψ hψ]
  | imp φ ψ ihφ ihψ =>
      have hφ : Env.AgreesOn (freeSupport φ) left right :=
        hEnv.mono (by
          intro fv hMem
          simp [freeSupport, hMem])
      have hψ : Env.AgreesOn (freeSupport ψ) left right :=
        hEnv.mono (by
          intro fv hMem
          simp [freeSupport, hMem])
      simp [satisfies, ihφ hφ, ihψ hψ]
  | iff φ ψ ihφ ihψ =>
      have hφ : Env.AgreesOn (freeSupport φ) left right :=
        hEnv.mono (by
          intro fv hMem
          simp [freeSupport, hMem])
      have hψ : Env.AgreesOn (freeSupport ψ) left right :=
        hEnv.mono (by
          intro fv hMem
          simp [freeSupport, hMem])
      simp [satisfies, ihφ hφ, ihψ hψ]
  | forallE sort body ih =>
      constructor
      · intro hSat value hValue
        exact
          (ih (hEnv.pushBound sort value hValue)).mp
            (hSat value hValue)
      · intro hSat value hValue
        exact
          (ih (hEnv.pushBound sort value hValue)).mpr
            (hSat value hValue)
  | existsE sort body ih =>
      constructor
      · rintro ⟨value, hValue, hBody⟩
        exact
          ⟨value, hValue,
            (ih (hEnv.pushBound sort value hValue)).mp hBody⟩
      · rintro ⟨value, hValue, hBody⟩
        exact
          ⟨value, hValue,
            (ih (hEnv.pushBound sort value hValue)).mpr hBody⟩

end Formula

namespace Env

/-- 一个带有局部自由变量支持的环境。 -/
structure Supported {σ : Signature.{u, v, w}} (M : Structure.{u, v, w, x} σ) where
  support : FreeVariable.Support σ
  env : Env M

namespace Supported

/-- 有限环境族中的支持两两不交。 -/
def PairwiseDisjoint {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ} :
    List (Supported M) → Prop
  | [] => True
  | entry :: rest =>
      (∀ other, other ∈ rest →
        FreeVariable.Support.Disjoint entry.support other.support) ∧
      PairwiseDisjoint rest

/-- 有限环境族与基环境共享同一个 bound stack。 -/
def AllSameBoundStack {σ : Signature.{u, v, w}} {M : Structure.{u, v, w, x} σ}
    (base : Env M) (entries : List (Supported M)) : Prop :=
  ∀ entry, entry ∈ entries → SameBoundStack base entry.env

end Supported

/--
在给定支持上用 `source` 覆盖 `base` 的 free assignment。

bound stack 始终来自 `base`。
-/
def overlay {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (support : FreeVariable.Support σ)
    (source base : Env M) : Env M where
  boundVal := base.boundVal
  freeVal := fun sort id =>
    if (sort, id) ∈ support then
      source.freeVal sort id
    else
      base.freeVal sort id
  boundSort := base.boundSort
  freeSort := by
    intro sort id
    by_cases hMem : (sort, id) ∈ support
    · simpa [hMem] using source.freeSort sort id
    · simpa [hMem] using base.freeSort sort id

/-- overlay 在覆盖支持上投影回源环境。 -/
theorem overlay_agreesOn_source {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    {support : FreeVariable.Support σ} {source base : Env M}
    (hBound : SameBoundStack base source) :
    AgreesOn support (overlay support source base) source := by
  constructor
  · simpa [overlay] using hBound
  · intro fv hMem
    simp [overlay, hMem]

/-- 若局部支持与覆盖支持不交，overlay 在局部支持上仍投影回基环境。 -/
theorem overlay_agreesOn_base_of_disjoint {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    {overlaySupport support : FreeVariable.Support σ} {source base : Env M}
    (hDisjoint : FreeVariable.Support.Disjoint overlaySupport support) :
    AgreesOn support (overlay overlaySupport source base) base := by
  constructor
  · intro sort index
    rfl
  · intro fv hMem
    have hNotMem : fv ∉ overlaySupport :=
      fun hOverlay => hDisjoint fv hOverlay hMem
    simp [overlay, hNotMem]

/--
按列表顺序合并有限支持环境。

较早条目的支持优先；两两不交时该顺序不影响各支持上的投影定理。
-/
def merge {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (base : Env M) :
    List (Supported M) → Env M
  | [] => base
  | entry :: rest => overlay entry.support entry.env (merge base rest)

/-- 合并环境保留基环境的完整 bound stack。 -/
theorem merge_sameBoundStack {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (base : Env M) (entries : List (Supported M)) :
    SameBoundStack (merge base entries) base := by
  induction entries with
  | nil =>
      intro sort index
      rfl
  | cons entry rest ih =>
      simpa [merge, overlay] using ih

/-- 若没有条目负责某个自由变量，合并环境保留基环境的值。 -/
theorem merge_freeVal_of_not_mem {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (base : Env M) (entries : List (Supported M))
    (sort : σ.SortSymbol) (id : FreeVarId)
    (hMissing : ∀ entry, entry ∈ entries → (sort, id) ∉ entry.support) :
    (merge base entries).freeVal sort id = base.freeVal sort id := by
  induction entries with
  | nil =>
      rfl
  | cons entry rest ih =>
      have hHead : (sort, id) ∉ entry.support :=
        hMissing entry List.mem_cons_self
      have hRest : ∀ other, other ∈ rest → (sort, id) ∉ other.support := by
        intro other hMem
        exact hMissing other (List.mem_cons_of_mem entry hMem)
      simp [merge, overlay, hHead, ih hRest]

private theorem agreesOn_merge_cons_of_disjoint {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    {base source : Env M} {support : FreeVariable.Support σ}
    {first : Supported M} {rest : List (Supported M)}
    (hDisjoint : FreeVariable.Support.Disjoint first.support support)
    (hEnv : AgreesOn support (merge base rest) source) :
    AgreesOn support (merge base (first :: rest)) source := by
  constructor
  · simpa [merge, overlay] using hEnv.1
  · intro fv hMem
    have hNotMem : fv ∉ first.support :=
      fun hFirst => hDisjoint fv hFirst hMem
    simpa [merge, overlay, hNotMem] using hEnv.2 fv hMem

/--
两两不交且共享 bound stack 的有限环境族可同时合并。

结果在每个条目的支持上都与该条目的源环境一致。
-/
theorem merge_agreesOn {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ}
    (base : Env M) (entries : List (Supported M))
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
        exact hBound other (List.mem_cons_of_mem _ hOther)
      intro entry hMem
      rcases List.mem_cons.mp hMem with hEq | hRestMem
      · cases hEq
        constructor
        · intro sort index
          exact
            (merge_sameBoundStack base (first :: rest) sort index).trans
              (hBound first List.mem_cons_self sort index)
        · intro fv hSupport
          simp [merge, overlay, hSupport]
      · apply agreesOn_merge_cons_of_disjoint
          (hFirstDisjoint entry hRestMem)
        exact ih hRestDisjoint hRestBound entry hRestMem

end Env

end FirstOrder
end Logic
end YesMetaZFC
