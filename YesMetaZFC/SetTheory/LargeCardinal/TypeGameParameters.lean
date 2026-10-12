import YesMetaZFC.SetTheory.LargeCardinal.TypeGameCatalogRead
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameClock

/-! # 辅助类型游戏的固定参数

十二个参数分别是内部时钟、树和字母表、重置高度及三张实际代码表。
参数记录只组织已构造的数据；有限历史仍以模型自己的函数图表示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u v

structure Tg_params_d (α : Type u) where
  ω : α
  e : α
  a : α
  b : α
  c : α
  δ : α
  A : α
  S : α
  ν : α
  E : α
  P : α
  Q : α

def Tg_params_d.map_l {α : Type u} {β : Type v} (p : Tg_params_d α) (f : α → β) : Tg_params_d β :=
  ⟨f p.ω, f p.e, f p.a, f p.b, f p.c, f p.δ, f p.A, f p.S, f p.ν, f p.E, f p.P, f p.Q⟩

def Tg_params_d.closed_l {d} (p : Tg_params_d (Term d)) : Prop :=
  p.ω.freeSupport = [] ∧ p.e.freeSupport = [] ∧ p.a.freeSupport = [] ∧ p.b.freeSupport = [] ∧
  p.c.freeSupport = [] ∧ p.δ.freeSupport = [] ∧ p.A.freeSupport = [] ∧ p.S.freeSupport = [] ∧
  p.ν.freeSupport = [] ∧ p.E.freeSupport = [] ∧ p.P.freeSupport = [] ∧ p.Q.freeSupport = []

@[simp] theorem Tg_params_d.weaken_closed_l {d} (p : Tg_params_d (Term d)) (h : p.closed_l) :
    (p.map_l Term.weaken).closed_l := by
  simpa only [Tg_params_d.closed_l, Tg_params_d.map_l, Definitional.Term.freeSupport_weaken] using h

end YesMetaZFC.SetTheory.LargeCardinal
