import YesMetaZFC.Model.ReducedProduct.Los
import YesMetaZFC.Model.FirstOrder.Elementary

/-! # 任意签名的同层超幂

固定 `I : Type x` 和 `ℳ : Structure.{u,v,w,max x y} σ`，所得结构仍为原类型，载体
保持原有 `Type (max u x y)`。较小指标可以直接调用；不使用 `ULift`、代表元选择
或新的对象语言公理。输入结构预先覆盖指标层，不是构造后再将模型升层。
实际商结构只需滤子；对角嵌入需要真滤子，初等性需要超滤和明确的见证拼接合同。
-/

namespace YesMetaZFC.Logic.FirstOrder.Ultrapower
open Model SetTheory
universe u v w x y
variable {σ : Signature.{u, v, w}} {I : Type x}
variable (ℳ : Structure.{u, v, w, max x y} σ) (U : Filter I)

theorem nonempty_m : ReducedProduct.Nonempty_m (fun _ : I => ℳ) := by
  intro s
  obtain ⟨a⟩ := ℳ.nonempty s
  exact ⟨fun _ => a⟩

/-- 固定原结构的 universe；不是在 `max` 新指标层后提升原模型。 -/
@[implicit_reducible] def structure_m : Structure.{u, v, w, max x y} σ :=
  ReducedProduct.structure_m (fun _ => ℳ) U (nonempty_m ℳ)

def constant_m : Fn_map ℳ (ReducedProduct.product_m (fun _ : I => ℳ) (nonempty_m ℳ)) where
  map _ a _ := a
  function_eq r ts := by
    funext i
    change ℳ.funcInterp r ts = ℳ.funcInterp r _
    rw [Values.map_comp, Values.map_id]

def diagonal_fn_m : Fn_map ℳ (structure_m ℳ U) :=
  (ReducedProduct.quotient_m (fun _ => ℳ) U (nonempty_m ℳ)).comp (constant_m ℳ)

def diagonal_m (hU : U.Proper) : Str_emb ℳ (structure_m ℳ U) where
  toFn_map := diagonal_fn_m ℳ U
  map_injective s a b h :=
    (U.const_iff_l hU (a = b)).mp ((Germ_l.class_eq_l U (fun _ => a) (fun _ => b)).mp h)
  relation_iff r ts := by
    have k := ReducedProduct.relation_class_m (fun _ => ℳ) U (nonempty_m ℳ)
      r (ts.map (constant_m ℳ).map)
    have he (i : I) :
        (ts.map (constant_m ℳ).map).map
          (ReducedProduct.projection_m (fun _ => ℳ) (nonempty_m ℳ) i).map = ts := by
      rw [Values.map_comp]
      exact Values.map_id ts
    simp only [he] at k
    exact ((U.const_iff_l hU _).symm.trans k.symm).trans (by
      rw [Values.map_comp]
      rfl)

/-- 只在完整 Łoś 定理及初等性中消费的见证合同，不影响商结构本身。 -/
def Witness_m : Prop := ReducedProduct.Witness_m (fun _ => ℳ) U (nonempty_m ℳ)

theorem constant_projection_m {b f} (ρ : Env ℳ b f) (i : I) :
    (ρ.map (constant_m ℳ).map).map
      (ReducedProduct.projection_m (fun _ => ℳ) (nonempty_m ℳ) i).map = ρ := rfl

theorem diagonal_elementary_m (hU : U.IsUltrafilter) (hW : Witness_m ℳ U) :
    (diagonal_m ℳ U hU.1).Elementary_m := by
  intro b f φ ρ
  have k := ReducedProduct.los_m (fun _ => ℳ) U (nonempty_m ℳ) hU hW
    φ (ρ.map (constant_m ℳ).map)
  simp only [constant_projection_m] at k
  simpa only using! (k.trans (U.const_iff_l hU.1 _)).symm

theorem models_iff_m (hU : U.IsUltrafilter) (hW : Witness_m ℳ U) (T : Theory σ) :
    Theory.Models (structure_m ℳ U) T ↔ Theory.Models ℳ T :=
  ((diagonal_m ℳ U hU.1).elementary_models_iff_m (diagonal_elementary_m ℳ U hU hW) T).symm

/-- 主超滤的见证只需取指定指标处的一次存在见证，不需要任何选择原则。 -/
theorem principal_witness_m (i : I) : Witness_m ℳ (Filter.point_l i) := by
  intro b f s φ ρ hφ
  obtain ⟨a, ha⟩ := (Filter.point_mem_l i _).mp hφ
  exact ⟨fun _ => a, (Filter.point_mem_l i _).mpr ha⟩

/-- 在主超滤的指定点求值；商运算直接下降为实际数据函数。 -/
def evaluation_m (i : I) (s : σ.SortSymbol)
    (a : (structure_m ℳ (Filter.point_l i)).Carrier s) : ℳ.Carrier s :=
  Quotient.liftOn a (fun f => f i) (fun _ _ h => h rfl)

/-- 主超幂与原结构的显式同构；其逆不是从满射证明选择出来的。 -/
def principal_iso_m (i : I) : Str_iso ℳ (structure_m ℳ (Filter.point_l i)) where
  toStr_emb := diagonal_m ℳ (Filter.point_l i) (Filter.point_proper_l i)
  inverse := evaluation_m ℳ i
  left_inv _ _ := rfl
  right_inv s a := by
    refine Germ_l.induction_l (Filter.point_l i) (A := fun _ => ℳ.Carrier s)
      (P := fun a => Germ_l.class_l (Filter.point_l i) (fun _ => evaluation_m ℳ i s a) = a) a ?_
    intro f
    apply (Germ_l.class_eq_l (Filter.point_l i) _ f).mpr
    exact (Filter.point_mem_l i _).mpr rfl

end YesMetaZFC.Logic.FirstOrder.Ultrapower
