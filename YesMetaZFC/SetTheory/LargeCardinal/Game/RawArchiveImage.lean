import YesMetaZFC.SetTheory.LargeCardinal.Game.RawIterationUnion
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNode
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.BranchTail

/-! # 真实原档案在指定锥中的五坐标像

像始终绑定同一11项档案行、同一54项原存档和该节点自己的锥腿。
长度、树、实数图、标签图和恢复图一次搬运；档案与锥的函数性保证这些像唯一。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Tg_raw_archive_image_d (D P m i : M.Domain) (v : Fin 5 → M.Domain) : Prop :=
  ∃ r, ∃ row : Tg_raw_archive_row_d M.Domain, Rd_entry_d m r D ∧ Rt_tuple_d row.values_d r ∧ row.i = i ∧
    ∃ w : Fin 54 → M.Domain, Tg_saved_code_d row.X row.R row.w row.U row.q w ∧
      ∃ j, Rd_entry_d i j P ∧ ∀ a, Rd_entry_d (w ([22,19,40,41,42].get a)) (v a) j

/-- 给定实际行和完整存档码时，像关系读回同一条锥腿及五个坐标。 -/
theorem Tg_raw_archive_image_d.read_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {D P m i r : M.Domain} {v : Fin 5 → M.Domain} {row : Tg_raw_archive_row_d M.Domain}
    {w : Fin 54 → M.Domain} (h : Tg_raw_archive_image_d D P m i v)
    (archive : ∀ x y z, Rd_entry_d x y D → Rd_entry_d x z D → y = z)
    (entry : Rd_entry_d m r D) (tuple : Rt_tuple_d row.values_d r)
    (code : Tg_saved_code_d row.X row.R row.w row.U row.q w) :
    row.i = i ∧ ∃ j, Rd_entry_d row.i j P ∧ ∀ a, Rd_entry_d (w ([22,19,40,41,42].get a)) (v a) j := by
  obtain ⟨r',old,entry',tuple',index,w',code',j,leg,images⟩ := h
  have eq := archive m r' r entry' entry
  subst r'
  have eq := Tg_raw_archive_row_d.eq_l (rt_tuple_inj_l tuple' tuple)
  subst old
  have eq : w' = w := funext fun a => congrFun (code'.inj_l I hE code) a.succ.succ
  subst w'
  exact ⟨index,j,index.symm ▸ leg,images⟩

/-- 同一档案索引的像节点唯一；只用实际档案、锥及锥腿的函数性。 -/
theorem Tg_raw_archive_image_d.unique_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {D P m i k : M.Domain} {v w : Fin 5 → M.Domain}
    (archive : ∀ x y z, Rd_entry_d x y D → Rd_entry_d x z D → y = z)
    (pf : ∀ x y z, Rd_entry_d x y P → Rd_entry_d x z P → y = z)
    (legs : ∀ i j, Rd_entry_d i j P → ∀ x y z, Rd_entry_d x y j → Rd_entry_d x z j → y = z)
    (hv : Tg_raw_archive_image_d D P m i v) (hw : Tg_raw_archive_image_d D P m k w) : i = k ∧ v = w := by
  obtain ⟨r,row,entry,tuple,index,a,code,j,leg,images⟩ := hv
  obtain ⟨index',j',leg',images'⟩ := hw.read_l I hE archive entry tuple code
  have leg : Rd_entry_d row.i j P := index.symm ▸ leg
  have eq := pf row.i j' j leg' leg
  subst j'
  exact ⟨index.symm.trans index',funext fun b => legs row.i j leg _ _ _ (images b) (images' b)⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H : M.Domain}

/-- 同一行的原模型、数字、名字和根切片均从它实际所在的有限阶段进入并档案。 -/
theorem Tg_raw_iteration_run_d.archive_read_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {m r : M.Domain} (row : Tg_raw_archive_row_d M.Domain)
    (entry : Rd_entry_d m r (U 5)) (tuple : Rt_tuple_d row.values_d r) :
    Rd_entry_d row.i row.c (U 1) ∧ Smdl_d I row.c row.X row.R ∧
      Tg_saved_d I row.w row.X row.R row.η row.C row.L row.U row.q ∧
      (∃ z, Rr_layer_d I ω row.X row.R row.w z) ∧
      Tg_saved_name_d I S₀ row.X row.R row.w row.U row.q row.p ∧
      Tg_raw_saved_base_d I X₀ R₀ γ₀ D₀ C₀ row.X row.R row.w row.C row.U row.q row.p ∧
      Tg_raw_cofinal_d I row.w row.X row.R row.L ∧
      It_map_d (U 2) o row.i row.p ∧ Rd_entry_d row.i row.L (U 4) := by
  obtain ⟨p,pair,hp⟩ := entry
  obtain ⟨v,k,s,hs,pack,hp⟩ := (u.columns 5 p).mp hp
  have state := h.read_l hZF v hs pack
  have entry : Rd_entry_d m r (v 13) := ⟨p,pair,hp⟩
  obtain ⟨model,saved,numbers,name,base,cofinal,_⟩ := (state.request.views m r entry).read_l I tuple
  have links := state.request.links m r row entry tuple
  obtain ⟨q,qp,hq⟩ := links.2.1
  obtain ⟨b,bp,e,ep,he⟩ := links.2.2.1
  obtain ⟨l,lp,hl⟩ := links.2.2.2
  exact ⟨⟨q,qp,(u.columns 1 q).mpr ⟨v,k,s,hs,pack,hq⟩⟩,model,saved,numbers,name,base,cofinal,
    ⟨b,bp,e,ep,(u.columns 2 e).mpr ⟨v,k,s,hs,pack,he⟩⟩,
    ⟨l,lp,(u.columns 4 l).mpr ⟨v,k,s,hs,pack,hl⟩⟩⟩

/-- 原档案沿指定锥实际生成有限目标节点；不要求原模型有隶属呈示。 -/
theorem Tg_raw_iteration_run_d.archive_images_l
    (h : Tg_raw_iteration_run_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ S₀ A₀ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_raw_iteration_union_d hZF ω c o X₀ R₀ γ₀ D₀ C₀ H U)
    {b d N W P m r : M.Domain} (cone : It_embedding_d (kp_pair_l (ZF.modelsKP hZF)) ω b (U 1) (U 2) d N W P)
    (target : Smem_d I d N W) (nt : M.TransitiveSet N)
    (row : Tg_raw_archive_row_d M.Domain) (entry : Rd_entry_d m r (U 5))
    (tuple : Rt_tuple_d row.values_d r) (hi : M.mem row.i b) :
    ∃ v : Fin 5 → M.Domain, M.mem (v 0) ω ∧ (∀ a, M.mem (v a) N) ∧
      Tg_node_d I (v 0) (v 1) (v 2) (v 3) (v 4) ∧ Tg_raw_archive_image_d (U 5) P m row.i v := by
  obtain ⟨node,model,saved,⟨z,numbers⟩,_⟩ := h.archive_read_l hZF u row entry tuple
  obtain ⟨j,leg⟩ := (cone.domain row.i).mp hi
  have map := cone.elementary row.i j row.c row.X row.R leg node model
  obtain ⟨_,ρ,code,_⟩ := saved.read_l I hZF.1
  let w : Fin 54 → M.Domain := fun i => (ρ.bound i).val.val
  have code : Tg_saved_code_d row.X row.R row.w row.U row.q w := code
  obtain ⟨w',images,finite,valid⟩ := saved.image_node_l hZF u.tree.omega model numbers target nt map code
  let v : Fin 5 → M.Domain := fun i => w' ([22,19,40,41,42].get i)
  have points (i : Fin 5) : Rd_entry_d (w ([22,19,40,41,42].get i)) (v i) j := images _
  exact ⟨v,finite,fun i => map.1.1.output_mem_of_pairMember (points i),valid,
    r,row,entry,tuple,rfl,w,code,j,leg,points⟩

end YesMetaZFC.SetTheory.LargeCardinal
