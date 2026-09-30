import YesMetaZFC.Model.ReducedProduct.Germ
import YesMetaZFC.Model.FirstOrder.Morphism

/-! # 同层多排序约化积

指标 `I : Type x`，原结构预先位于 `max x y` 层；截面、商载体和结果结构均不升层。
独立参数 `y` 允许载体原本就比指标大，不必提升较小指标或改变原结构。
变化的结构族须显式给出各排序截面空间非空的 Prop 证书，不能从逐点非空偷选截面。
恒定结构族的超幂不需要这个额外假设，见 `Ultrapower`。
-/

namespace YesMetaZFC.Logic.FirstOrder.ReducedProduct
open Model SetTheory
universe u v w x y
variable {σ : Signature.{u, v, w}} {I : Type x}
variable (ℳ : I → Structure.{u, v, w, max x y} σ) (U : Filter I)

/-- 仅要求每个排序的截面空间非空，不选定全排序基点族。 -/
def Nonempty_m : Prop := ∀ s, Nonempty ((i : I) → (ℳ i).Carrier s)

/-- 截面结构；其关系只用于提供一般一阶结构，商关系仍按滤子直接解释。 -/
@[implicit_reducible] def product_m (h : Nonempty_m ℳ) : Structure.{u, v, w, max x y} σ where
  Carrier s := (i : I) → (ℳ i).Carrier s
  nonempty := h
  funcInterp r ts i := (ℳ i).funcInterp r (ts.map (fun _ a => a i))
  relInterp r ts := ∀ i, (ℳ i).relInterp r (ts.map (fun _ a => a i))

/-- 有限异质列的商装配；逐坐标商消去，不选取一个代表元族。 -/
def values_m : {ss : List σ.SortSymbol} →
    Values (fun s => Germ_l U (fun i => (ℳ i).Carrier s)) ss →
      Germ_l U (fun i => Values (ℳ i).Carrier ss)
  | _, .nil => Germ_l.class_l U (fun _ => .nil)
  | _, .cons a ts => Germ_l.map₂_l U (fun _ => Values.cons) a (values_m ts)

theorem values_class_m {ss} (ts : Values (fun s => (i : I) → (ℳ i).Carrier s) ss) :
    values_m ℳ U (ts.map (fun _ => Germ_l.class_l U)) =
      Germ_l.class_l U (fun i => ts.map (fun _ a => a i)) := by
  induction ts with
  | nil => rfl
  | cons a ts ih =>
      change Germ_l.map₂_l U _ _ (values_m ℳ U _) = _
      rw [ih]
      rfl

/-- 任意滤子的实际约化积；超滤性质仅在 Łoś 定理中需要。 -/
@[implicit_reducible] def structure_m (h : Nonempty_m ℳ) : Structure.{u, v, w, max x y} σ where
  Carrier s := Germ_l U (fun i => (ℳ i).Carrier s)
  nonempty s := by
    obtain ⟨a⟩ := h s
    exact ⟨Germ_l.class_l U a⟩
  funcInterp r ts := Germ_l.map_l U (fun i => (ℳ i).funcInterp r) (values_m ℳ U ts)
  relInterp r ts := Germ_l.pred_l U (fun i => (ℳ i).relInterp r) (values_m ℳ U ts)

def projection_m (h : Nonempty_m ℳ) (i : I) : Fn_map (product_m ℳ h) (ℳ i) where
  map _ a := a i
  function_eq _ _ := rfl

def quotient_m (h : Nonempty_m ℳ) : Fn_map (product_m ℳ h) (structure_m ℳ U h) where
  map _ := Germ_l.class_l U
  function_eq r ts := by
    change Germ_l.class_l U _ = Germ_l.map_l U _ (values_m ℳ U _)
    rw [values_class_m]
    rfl

theorem relation_class_m (h : Nonempty_m ℳ) (r : σ.RelSymbol)
    (ts : Values (product_m ℳ h).Carrier (σ.relDomain r)) :
    (structure_m ℳ U h).relInterp r (ts.map (quotient_m ℳ U h).map) ↔
      U.sets (fun i => (ℳ i).relInterp r (ts.map (projection_m ℳ h i).map)) := by
  change Germ_l.pred_l U _ (values_m ℳ U (ts.map (fun _ => Germ_l.class_l U))) ↔ _
  rw [values_class_m]
  rfl

/-- 有限参数赋值在 Prop 中逐项回拉；不是为所有商类选择代表元。 -/
theorem assignment_surjective_m (h : Nonempty_m ℳ) {ss}
    (a : Assignment (structure_m ℳ U h) ss) :
    ∃ b : Assignment (product_m ℳ h) ss, ∀ {s} (i : Variable ss s),
      (quotient_m ℳ U h).map s (b i) = a i := by
  induction ss with
  | nil => exact ⟨Assignment.empty, fun i => nomatch i⟩
  | cons s ss ih =>
      obtain ⟨b, hb⟩ := ih (fun i => a (.there i))
      obtain ⟨c, hc⟩ := Germ_l.exists_rep_l U (A := fun i => (ℳ i).Carrier s) (a .here)
      refine ⟨Assignment.push c b, ?_⟩
      intro t i
      cases i with
      | here => exact hc
      | there i => exact hb i

/-- 任意有限商环境都有截面环境，故 Łoś 接口覆盖全部商结构参数。 -/
theorem env_surjective_m (h : Nonempty_m ℳ) {b f} (ρ : Env (structure_m ℳ U h) b f) :
    ∃ τ : Env (product_m ℳ h) b f, τ.map (quotient_m ℳ U h).map = ρ := by
  obtain ⟨a, ha⟩ := assignment_surjective_m ℳ U h ρ.boundVal
  obtain ⟨b, hb⟩ := assignment_surjective_m ℳ U h ρ.freeVal
  exact ⟨⟨a, b⟩, Env.ext ha hb⟩

end YesMetaZFC.Logic.FirstOrder.ReducedProduct
