import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Syntax
import YesMetaZFC.Model.SetTheory.Internal.TransitiveStructure

/-! # 原定向系统及指定直接极限的传递读取

每个无界见证都出现在已有图条目中，故由图的拥有性回收。核与极限关系
因而仍是原共同后继关系，不把它们换成另一张等价关系。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {Z : M.Domain}
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
include hKP hZ
local notation "N" => rt_model_l Z nz

theorem rt_di_order_l (J L : (N).Domain) (h : Di_order_d J L) : Di_order_d J.val L.val := by
  have ent := rt_entry_l hZ nz hKP.1
  refine ⟨fun i hi => (ent ..).mp (h.refl ⟨i, hZ J.val J.property i hi⟩ hi), ?_, ?_, ?_⟩
  · intro i j k hij hjk
    have ij := rd_entry_transitive_l hZ L.property hij
    have jk := rd_entry_transitive_l hZ L.property hjk
    exact (ent ..).mp (h.trans ⟨i, ij.1⟩ ⟨j, ij.2⟩ ⟨k, jk.2⟩ ((ent ..).mpr hij) ((ent ..).mpr hjk))
  · intro i j hij
    have ij := rd_entry_transitive_l hZ L.property hij
    exact h.bound ⟨i, ij.1⟩ ⟨j, ij.2⟩ ((ent ..).mpr hij)
  · intro i j hi hj
    obtain ⟨k, hk, hik, hjk⟩ := h.directed ⟨i, hZ J.val J.property i hi⟩ ⟨j, hZ J.val J.property j hj⟩ hi hj
    exact ⟨k.val, hk, (ent ..).mp hik, (ent ..).mp hjk⟩

theorem rt_di_system_l (J L A p T R : (N).Domain) (h : Di_system_d J L A p T R) :
    Di_system_d J.val L.val A.val p.val T.val R.val := by
  have ent := rt_entry_l hZ nz hKP.1
  have mem (f : (N).Domain) {x y} (h : Rd_entry_d x y f.val) := rd_entry_transitive_l hZ f.property h
  refine ⟨rt_di_order_l hKP hZ nz J L h.order, (rt_fn_l hZ nz hKP.1 ..).mp h.index,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact h.bound ⟨x, (mem T hxy).1⟩ ⟨y, (mem T hxy).2⟩ ((ent ..).mpr hxy)
  · intro x y i j hxi hyj hxy
    exact (ent ..).mp (h.forward ⟨x, (mem p hxi).1⟩ ⟨y, (mem p hyj).1⟩
      ⟨i, (mem p hxi).2⟩ ⟨j, (mem p hyj).2⟩ ((ent ..).mpr hxi) ((ent ..).mpr hyj) ((ent ..).mpr hxy))
  · intro x hx
    exact (ent ..).mp (h.identity ⟨x, hZ A.val A.property x hx⟩ hx)
  · intro x y z hxy hyz
    exact (ent ..).mp (h.comp ⟨x, (mem T hxy).1⟩ ⟨y, (mem T hxy).2⟩ ⟨z, (mem T hyz).2⟩
      ((ent ..).mpr hxy) ((ent ..).mpr hyz))
  · intro x i j hxi hij
    obtain ⟨y, hyj, hxy⟩ := h.total ⟨x, (mem p hxi).1⟩ ⟨i, (mem p hxi).2⟩ ⟨j, (mem L hij).2⟩
      ((ent ..).mpr hxi) ((ent ..).mpr hij)
    exact ⟨y.val, (ent ..).mp hyj, (ent ..).mp hxy⟩
  · intro x y z j hyj hzj hxy hxz
    exact congrArg Subtype.val (h.unique ⟨x, (mem T hxy).1⟩ ⟨y, (mem p hyj).1⟩ ⟨z, (mem p hzj).1⟩
      ⟨j, (mem p hyj).2⟩ ((ent ..).mpr hyj) ((ent ..).mpr hzj) ((ent ..).mpr hxy) ((ent ..).mpr hxz))
  · intro x y z i hxi hyi hxz hyz
    exact congrArg Subtype.val (h.injective ⟨x, (mem p hxi).1⟩ ⟨y, (mem p hyi).1⟩ ⟨z, (mem T hxz).2⟩
      ⟨i, (mem p hxi).2⟩ ((ent ..).mpr hxi) ((ent ..).mpr hyi) ((ent ..).mpr hxz) ((ent ..).mpr hyz))
  · intro x y hxy
    obtain ⟨i, hxi, hyi⟩ := h.locality ⟨x, (mem R hxy).1⟩ ⟨y, (mem R hxy).2⟩ ((ent ..).mpr hxy)
    exact ⟨i.val, (ent ..).mp hxi, (ent ..).mp hyi⟩
  · intro x y i u v j hxi hyi huj hvj hxu hyv
    exact (ent ⟨x, (mem p hxi).1⟩ ⟨y, (mem p hyi).1⟩ R).symm.trans
      ((h.relation _ _ ⟨i, (mem p hxi).2⟩ ⟨u, (mem p huj).1⟩ ⟨v, (mem p hvj).1⟩ ⟨j, (mem p huj).2⟩
        ((ent ..).mpr hxi) ((ent ..).mpr hyi) ((ent ..).mpr huj) ((ent ..).mpr hvj)
        ((ent ..).mpr hxu) ((ent ..).mpr hyv)).trans (ent ..))

theorem rt_di_eq_l (T x y : (N).Domain) : Di_eq_d T x y ↔ Di_eq_d T.val x.val y.val := by
  have ent := rt_entry_l hZ nz hKP.1
  exact ⟨fun ⟨z, hx, hy⟩ => ⟨z.val, (ent ..).mp hx, (ent ..).mp hy⟩,
    fun ⟨z, hx, hy⟩ => ⟨⟨z, (rd_entry_transitive_l hZ T.property hx).2⟩, (ent ..).mpr hx, (ent ..).mpr hy⟩⟩

theorem rt_di_rel_l (p T R x y : (N).Domain) :
    Di_rel_d p T R x y ↔ Di_rel_d p.val T.val R.val x.val y.val := by
  have ent := rt_entry_l hZ nz hKP.1
  constructor
  · rintro ⟨i, u, v, hui, hvi, hxu, hyv, huv⟩
    exact ⟨i.val, u.val, v.val, (ent ..).mp hui, (ent ..).mp hvi, (ent ..).mp hxu, (ent ..).mp hyv, (ent ..).mp huv⟩
  · rintro ⟨i, u, v, hui, hvi, hxu, hyv, huv⟩
    have ui := rd_entry_transitive_l hZ p.property hui
    have vi := rd_entry_transitive_l hZ p.property hvi
    exact ⟨⟨i, ui.2⟩, ⟨u, ui.1⟩, ⟨v, vi.1⟩,
      (ent ..).mpr hui, (ent ..).mpr hvi, (ent ..).mpr hxu, (ent ..).mpr hyv, (ent ..).mpr huv⟩

theorem rt_di_limit_l
    (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
    (A p T R q C S : (N).Domain) (h : Di_limit_d A p T R q C S) :
    Di_limit_d A.val p.val T.val R.val q.val C.val S.val := by
  have ent := rt_entry_l hZ nz hKP.1
  refine ⟨(rt_fn_l hZ nz hKP.1 ..).mp h.projection,
    (rt_range_l hZ nz hKP.1 (KP.exists_pair hKP) pair C q).mp h.range, ?_, ?_, ?_,
    (rt_relation_l hKP hZ nz pair S).mp h.graph⟩
  · intro x y B D hx hy
    have xb := rd_entry_transitive_l hZ q.property hx
    have yd := rd_entry_transitive_l hZ q.property hy
    exact (show B = D ↔ (⟨B, xb.2⟩ : (N).Domain) = ⟨D, yd.2⟩ from
      ⟨fun e => Subtype.ext e, congrArg Subtype.val⟩).trans
      ((h.kernel ⟨x, xb.1⟩ ⟨y, yd.1⟩ ⟨B, xb.2⟩ ⟨D, yd.2⟩ ((ent ..).mpr hx) ((ent ..).mpr hy)).trans
        (rt_di_eq_l hKP hZ nz ..))
  · intro x y B D hx hy
    have xb := rd_entry_transitive_l hZ q.property hx
    have yd := rd_entry_transitive_l hZ q.property hy
    exact (ent ⟨B, xb.2⟩ ⟨D, yd.2⟩ S).symm.trans
      ((h.relation ⟨x, xb.1⟩ ⟨y, yd.1⟩ ⟨B, xb.2⟩ ⟨D, yd.2⟩ ((ent ..).mpr hx) ((ent ..).mpr hy)).trans
        (rt_di_rel_l hKP hZ nz ..))
  · intro B D hBD
    have bd := rd_entry_transitive_l hZ S.property hBD
    exact h.bounded ⟨B, bd.1⟩ ⟨D, bd.2⟩ ((ent ..).mpr hBD)

end YesMetaZFC.SetTheory.Internal
