import YesMetaZFC.SetTheory.Definitional.Project.Hierarchy

/-! # 原 Project 公式的有限 Lévy 层级

极性 true 表示 Σ，false 表示 Π。换极性提升一层，同极性量词不提升层级；
有界量词与布尔运算保留层级。证书直接分类生产 AST，不引入新的解释符号。
-/
namespace YesMetaZFC.SetTheory.Definitional.Project.Formula

inductive IsLevy : Bool → Nat → {d : Nat} → Formula 1 d → Prop where
  | base {p d} {φ : Formula 1 d} : φ.IsDelta0 → IsLevy p 0 φ
  | lift {p n d} {φ : Formula 1 d} : IsLevy (!p) n φ → IsLevy p (n+1) φ
  | neg {p n d} {φ : Formula 1 d} : IsLevy (!p) n φ → IsLevy p n (.neg φ)
  | conj {p n d} {φ ψ : Formula 1 d} : IsLevy p n φ → IsLevy p n ψ → IsLevy p n (.conj φ ψ)
  | disj {p n d} {φ ψ : Formula 1 d} : IsLevy p n φ → IsLevy p n ψ → IsLevy p n (.disj φ ψ)
  | existsE {n d} {φ : Formula 1 (d+1)} : IsLevy true (n+1) φ → IsLevy true (n+1) (.existsE φ)
  | forallE {n d} {φ : Formula 1 (d+1)} : IsLevy false (n+1) φ → IsLevy false (n+1) (.forallE φ)
  | existsMem {p n d} (x : Term d) {φ : Formula 1 (d+1)} :
      IsLevy p n φ → IsLevy p n (existsMem x φ)
  | forallMem {p n d} (x : Term d) {φ : Formula 1 (d+1)} :
      IsLevy p n φ → IsLevy p n (forallMem x φ)

abbrev IsSigma1 {d} (φ : Formula 1 d) := IsLevy true 1 φ
abbrev IsPi1 {d} (φ : Formula 1 d) := IsLevy false 1 φ
abbrev IsSigma2 {d} (φ : Formula 1 d) := IsLevy true 2 φ
abbrev IsPi2 {d} (φ : Formula 1 d) := IsLevy false 2 φ

end YesMetaZFC.SetTheory.Definitional.Project.Formula
