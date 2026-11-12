import YesMetaZFC.SetTheory.CumulativeClosure
import YesMetaZFC.SetTheory.KP.Kuratowski

/-! # KP 中实际秩层内的乘积

KP 的已有乘积构造给出实际集合，给定极限秩历史的关系闭包把它回收。
没有使用全局幂集公理，也没有另选超出原历史的秩层。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem KP.v_product_exists_l (hKP : M.Models KP) {δ U A B : M.Domain}
    (rank : V_d (kp_pair_l hKP) δ U) (limit : M.IsLimitOrdinal δ)
    (ha : M.mem A U) (hb : M.mem B U) :
    ∃ P, M.mem P U ∧ M.IsCartesianProduct (kp_pair_l hKP) P A B := by
  let J := kp_pair_l hKP
  obtain ⟨Y,hY,ay,by'⟩ := v_joint_bound_l J rank ha hb
  obtain ⟨P,product⟩ := KP.kprod_exists_l hKP A B
  refine ⟨P,v_relation_mem_l J rank limit hY (fun p hp => ?_),product⟩
  obtain ⟨a,ha,b,hb,pair⟩ := (product p).mp hp
  exact ⟨a,ay a ha,b,by' b hb,pair⟩

end YesMetaZFC.SetTheory
