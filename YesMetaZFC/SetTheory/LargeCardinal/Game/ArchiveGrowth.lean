import YesMetaZFC.SetTheory.LargeCardinal.Game.ArchiveEdge
import YesMetaZFC.SetTheory.LargeCardinal.Game.RestartLinkSyntax

/-! # 同一锥目标中的原继续边

五个原边像沿新锥腿进入目标，再由交换律和旧锥腿的函数性识别为旧节点坐标。
完整继续方程因此给出相同的树、长度后继、三图包含和恢复图的精确单点追加。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 两端目标向量均按长度、树、实数图、标签图、恢复图排列。 -/
theorem Tg_archive_step_d.image_l {ω d N W j p q : M.Domain}
    {s t : Tg_archive_row_d M.Domain} {v w : Fin 54 → M.Domain}
    (step : Tg_archive_step_d I s t j) (hw : M.IsOmega ω)
    (model : Smdl_d I t.c t.X t.R) (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (edge : M.IsSetFunctionFromTo I j s.X t.X) (left : M.IsSetFunction I p)
    (right : Smap_d I ω t.c d t.X N q)
    (square : ∀ x y z, Rd_entry_d x y j → Rd_entry_d y z q → Rd_entry_d x z p)
    (cv : Tg_saved_code_d s.X s.R s.w s.U s.q v)
    (cw : Tg_saved_code_d t.X t.R t.w t.U t.q w)
    (a b : Fin 5 → M.Domain)
    (ia : ∀ i, Rd_entry_d (v ([22,19,40,41,42].get i)) (a i) p)
    (ib : ∀ i, Rd_entry_d (w ([22,19,40,41,42].get i)) (b i) q) :
    a 1 = b 1 ∧ M.SuccessorOf (b 0) (a 0) ∧
    (∀ i : Fin 3, M.MemberSubset (a ([2,3,4].get i)) (b ([2,3,4].get i))) ∧
    ∃ x, Rd_entry_d (a 0) x (b 4) ∧ ∀ r, M.mem r (b 4) ↔ M.mem r (a 4) ∨ KPair_d M r (a 0) x := by
  obtain ⟨v',w',cv',cw',u,images,link⟩ := step
  have ev : v' = v := funext fun i => congrFun (cv'.inj_l I hZF.1 cv) i.succ.succ
  subst v'
  have ew : w' = w := funext fun i => congrFun (cw'.inj_l I hZF.1 cw) i.succ.succ
  subst w'
  let a' : Fin 5 → M.Domain := fun i => [a 1,a 0,a 2,a 3,a 4].get i
  have old : ∀ i, Rd_entry_d (v ([19,22,40,41,42].get i)) (a' i) p :=
    Fin.cases (ia 1) (Fin.cases (ia 0) (Fin.cases (ia 2) (Fin.cases (ia 3)
      (Fin.cases (ia 4) (fun i => Fin.elim0 i)))))
  have moved i : Rd_entry_d (u i) (a' i) q := by
    obtain ⟨y,_,hy⟩ := right.1.1.2.2 (u i) (edge.output_mem_of_pairMember (images i))
    have eq := left.2 _ y (a' i) (square _ _ _ (images i) hy) (old i)
    exact eq ▸ hy
  obtain ⟨name,succ,real,labels,x,entry,graph⟩ :=
    link.image_l hZF hw model target nt right a' b moved ib
  have recovery : M.MemberSubset (a 4) (b 4) := fun r hr => (graph r).mpr (Or.inl hr)
  exact ⟨name,succ,Fin.cases real (Fin.cases labels (Fin.cases recovery (fun i => Fin.elim0 i))),x,entry,graph⟩

end YesMetaZFC.SetTheory.LargeCardinal
