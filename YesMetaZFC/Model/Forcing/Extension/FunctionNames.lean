import YesMetaZFC.Model.Forcing.Check.Order
import YesMetaZFC.Model.Forcing.Maximum.UniqueRules

/-! # 覆盖全部扩张函数的规范名字族

先正规化为旧乘积的子集名字，再用旧常值函数修补不满足函数公式的部分。
名字族在地模型中一次分离，对所有泛型同时有效；其成员全局被迫为函数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem function_names_l {B R z b D X : M.Domain} (O : Cond_order_d M B R z)
    (hb : M.mem b B) (top : ∀ p, M.mem p B → Entry_d M p b R) (inh : ∃ x, M.mem x X) :
    ∃ t w P a f s W A, Check_d M b D t ∧ Check_d M b X w ∧
      M.IsCartesianProduct I P D X ∧ Check_d M b P a ∧ M.IsSetFunctionFromTo I f D X ∧
      Check_d M b f s ∧ Name_pool_d M B a s W ∧ M.mem s A ∧
      (∀ v, M.mem v A ↔ M.mem v W ∧ ∀ p, M.mem p B → p ≠ z →
        Forces_d M B R z fn_body_m (fn_env_l t w v) p) ∧
      ∀ U (generic : Generic_d M B R z U),
        ∀ d x y : (extension_l M hZF B R z U).Domain,
          Qval_d M B R z U t d → Qval_d M B R z U w x →
          (extension_l M hZF B R z U).IsSetFunctionFromTo
            (kpair_interpretation_l _ (extension_ext_l O hZF generic)
              (internal_pair_l O hZF generic)) y d x →
          ∃ v, M.mem v A ∧ Qval_d M B R z U v y := by
  obtain ⟨x,hx⟩ := inh
  obtain ⟨f,fn,_⟩ := ZF.exists_constantFunction hZF I (source := D) hx
  obtain ⟨P,product⟩ := ZF.exists_cartesianProduct hZF I D X
  obtain ⟨t,ht,nt,_⟩ := zf_check_l M hZF hb D
  obtain ⟨w,hw,nw,_⟩ := zf_check_l M hZF hb X
  obtain ⟨a,ha,na,_⟩ := zf_check_l M hZF hb P
  obtain ⟨s,hs,ns,_⟩ := zf_check_l M hZF hb f
  obtain ⟨W,pool⟩ := name_pool_exists_l M hZF na ns
  let ρ : Env M 2 := (⟨fun _ => w,fun _ => w⟩ : Env M 1).push t
  let φ : UnarySchema 2 := { body := fn_body_m,freeClosed := fn_body_closed_l }
  have fallback p hp hz := check_function_force_l O hZF hb ht hw hs fn ⟨hp,hz,top p hp⟩
  let η := ((ρ.push B).push R).push z
  let e : Fin 3 → Term 6 := Fin.cases .newest (Fin.cases (.bound 4) (fun _ => .bound 5))
  let χ : UnarySchema 5 := {
    body := force_all_m fn_body_m e (.bound 3) (.bound 2) (.bound 1)
    freeClosed := force_all_closed_l _ _ _ _ _ fn_body_closed_l
      (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl rfl rfl }
  have spec v : χ.denote η v ↔ ∀ p, M.mem p B → p ≠ z →
      Forces_d M B R z fn_body_m (fn_env_l t w v) p := by
    rw [UnarySchema.denote,force_all_sat_l hZF.1]
    apply forall_congr'; intro p
    apply imp_congr_right; intro _
    apply imp_congr_right; intro _
    exact forces_env_l hZF.1 fn_body_m fn_body_closed_l _ (fn_env_l t w v)
      (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) p
  obtain ⟨A,sep⟩ := ZF.separation_exists_d hZF χ η W
  have family v := (sep v).trans (and_congr_right fun _ => spec v)
  refine ⟨t,w,P,a,f,s,W,A,ht,hw,product,ha,fn,hs,pool,
    (family s).mpr ⟨pool.right,fallback⟩,family,?_⟩
  intro U generic d x y td wx fy
  let E := extension_l M hZF B R z U
  have hE : E.Models ZF := preserves_zf_l O hZF generic
  obtain ⟨p,hp⟩ := generic.inhabited
  obtain ⟨j,checks,full,inj⟩ := check_map_l O hZF generic (generic.upward p b hp hb (top p (generic.proper p hp).1))
  have dt := qval_unique_l (checks D t ht) td
  have xw := qval_unique_l (checks X w hw) wx
  have product' := image_product_l (hEN := hE.1) (hPN := KP.exists_pair (ZF.modelsKP hE)) j inj full product
  have subset : E.MemberSubset y (j P) := by
    intro q hq
    obtain ⟨i,v,pair⟩ := fy.1.1 q hq
    have edge : Entry_d E i v y := ⟨q,pair,hq⟩
    exact (product' q).mpr ⟨i,dt.symm ▸ fy.input_mem_of_pairMember edge,
      v,xw.symm ▸ fy.output_mem_of_pairMember edge,pair⟩
  obtain ⟨v,_,vy⟩ := value_name_l y
  obtain ⟨H,hull,bounds⟩ := pool
  obtain ⟨q,_,hq,_,qy⟩ := normalize_name_l O hZF generic hull.closed hull.left vy (checks P a ha) subset
  have qW : M.mem q W := (bounds q).mpr (fun p hp => by
    obtain ⟨v,r,hv,hr,pair⟩ := hq p hp
    exact ⟨v,r,pair,hv,hr⟩)
  have pool : Name_pool_d M B a s W := ⟨H,hull,bounds⟩
  have values : Env_val_d hZF (fn_env_l t w q) (fn_env_l d x y) := by
    intro v; cases v with
    | free _ => exact wx
    | bound i => exact Fin.cases qy (Fin.cases td (fun _ => wx)) i
  have truth : Formula.satisfies (fn_env_l d x y) fn_body_m :=
    (Formula.satisfies_isFunctionFromTo_iff
      (kpair_interpretation_l E hE.1 (KP.exists_pair (ZF.modelsKP hE))) hE.1 _ _ _ _).mpr fy
  obtain ⟨p,hp,forced⟩ := (forcing_truth_l O hZF generic fn_body_m fn_body_closed_l _ _ values).mpr truth
  obtain ⟨v,vW,all,eq⟩ := name_pool_patch_l O hZF φ ρ (Fin.cases nt (fun _ => nw))
    pool qW pool.right fallback
  obtain ⟨v',vv'⟩ := name_value_l (R := R) (z := z) (U := U) (show Name_d M B v from ⟨W,vW,pool.closed⟩)
  have same : v' = y := (qval_eq_l O hZF generic vv' qy).mp ⟨p,hp,eq p (generic.proper p hp).1 forced⟩
  exact ⟨v,(family v).mpr ⟨vW,all⟩,same ▸ vv'⟩

end YesMetaZFC.Model.Forcing.Internal
