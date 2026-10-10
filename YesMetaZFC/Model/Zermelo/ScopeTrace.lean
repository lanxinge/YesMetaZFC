import YesMetaZFC.SetTheory.Axioms.ZF
import YesMetaZFC.SetTheory.Definitional.Project.Derivation
import Lean

/-! # 原 ZF 证明的范围分析输入
只展开已经存在的证明项；提取出的原核证明仍由 Lean 重新检查。
JSON 供候选范围求解器使用，求解结果本身不是语义证明。
-/
namespace YesMetaZFC.Model.Zermelo
open Logic Logic.FirstOrder SetTheory SetTheory.Definitional Lean
attribute [local implicit_reducible] SetTheory.signature
open Lean Meta in
partial def rs_head (e : Expr) : MetaM Expr := withTransparency .all do
  let e ← whnf e
  let .const n us := e.getAppFn | return e
  match ← getConstInfo n with
  | .thmInfo d => rs_head (mkAppN (d.value.instantiateLevelParams d.levelParams us) e.getAppArgs)
  | .recInfo d =>
    let a := e.getAppArgs
    let j := d.getMajorIdx
    if h : j < a.size then
      let v ← rs_head a[j]
      if v != a[j] then return ← rs_head (mkAppN e.getAppFn (a.set j v))
    return e
  | _ => return e
open Lean Elab Term in
elab "rs_reify " t:term : term => do
  let e ← rs_head (← elabTerm t none)
  unless e.getAppFn.isConstOf ``Nonempty.intro do throwError "未得到原核证明树"
  return e.getAppArgs.back!

private def rs_j (xs : List Json) : Json := .arr xs.toArray
private def rs_tm {b f s} : FirstOrder.Term ℒ b f s → Json
  | .bvar i => rs_j [toJson "b", toJson i.index]
  | .fvar i => rs_j [toJson "f", toJson i.index]
  | .app g _ => nomatch g
private def rs_fm {b f} : FirstOrder.Formula ℒ b f → Json
  | .falsum => rs_j [toJson "false"] | .truth => rs_j [toJson "true"]
  | .equal t s => rs_j [toJson "eq", rs_tm t, rs_tm s]
  | .rel .membership (.cons t (.cons s .nil)) => rs_j [toJson "mem", rs_tm t, rs_tm s]
  | .neg p => rs_j [toJson "not", rs_fm p]
  | .conj p q => rs_j [toJson "and", rs_fm p, rs_fm q]
  | .disj p q => rs_j [toJson "or", rs_fm p, rs_fm q]
  | .imp p q => rs_j [toJson "imp", rs_fm p, rs_fm q]
  | .iff p q => rs_j [toJson "iff", rs_fm p, rs_fm q]
  | .forallE _ p => rs_j [toJson "all", rs_fm p]
  | .existsE _ p => rs_j [toJson "ex", rs_fm p]
private def rs_sub {b f} : (s : SortContext ℒ) → VariableSubstitution ℒ s b f → List Json
  | .nil, _ => []
  | SetSort.set :: s, θ => rs_tm (θ .here) :: rs_sub s (fun j => θ (.there j))
private def rs_ax {f φ} (p : HilbertBaseAxiom ℒ (free := f) φ) : Json := match p with
  | .forall_specialization _ _ t | .exists_introduction _ _ t => rs_tm t
  | _ => .null
/-- 导出全部六条原核规则、原公式和实际代入项，不从语义假设反造证明。 -/
def rs_proof {f φ} (p : HilbertDerivation (Project.fo_theory SetTheory.ZF) f φ) : Json :=
  let d := match p with
    | .logical_axiom a => [toJson "L", toJson a.ctorIdx, rs_ax a]
    | .theory_axiom _ => [toJson "T"]
    | .modus_ponens p q => [toJson "M", rs_proof p, rs_proof q]
    | .forall_generalization p => [toJson "G", rs_proof p]
    | .free_strengthening p => [toJson "W", rs_proof p]
    | @HilbertDerivation.free_substitution _ _ s _ θ _ p => [toJson "S", toJson (rs_sub s θ), rs_proof p]
  rs_j (toJson f.length :: rs_fm φ :: d)
end YesMetaZFC.Model.Zermelo
