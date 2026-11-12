import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.SetTheory.Collapse.NaturalBasis

/-! # 特殊实数在传递成员结构中的实际解释

常零与后继图的解释只用传递性及背景外延性。向外读取时只需已识别的
背景 ω；不会把源内的函数断言当作完整源理论来使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open InnerModel
universe u
variable {M : Structure.{u}} {Q : M.Domain} (ht : M.TransitiveSet Q)
  (hn : Nonempty {x // M.mem x Q}) (hE : Extensional M)
include ht hE

theorem rt_nat_into_l (w z c s : (rt_model_l Q hn).Domain)
    (h : Mc_nat_d w.val z.val c.val s.val) : Mc_nat_d w z c s := by
  refine ⟨rt_omega_l ht hn hE w h.omega,fun x => h.empty x.val,
    (rt_fn_l ht hn hE w w c).mpr h.constant,?_,(rt_fn_l ht hn hE w w s).mpr h.successor,?_⟩
  · intro n y
    exact (rt_entry_l ht hn hE n y c).trans ((h.constant_entry n.val y.val).trans
      (and_congr_right fun _ => ⟨Subtype.ext,congrArg Subtype.val⟩))
  · intro n y
    exact (rt_entry_l ht hn hE n y s).trans ((h.successor_entry n.val y.val).trans
      (and_congr_right fun _ => (rt_successor_l ht hn hE y n).symm))

theorem rt_nat_out_l (w z c s : (rt_model_l Q hn).Domain) (hw : M.IsOmega w.val)
    (h : Mc_nat_d w z c s) : Mc_nat_d w.val z.val c.val s.val := by
  have fc := (rt_fn_l ht hn hE w w c).mp h.constant
  have fs := (rt_fn_l ht hn hE w w s).mp h.successor
  refine ⟨hw,fun x hx => h.empty ⟨x,ht z.val z.property x hx⟩ hx,fc,?_,fs,?_⟩
  · intro n y
    constructor
    · intro ny
      have nb := (fc.bound_l ny).1
      have yb := (fc.bound_l ny).2
      let a : (rt_model_l Q hn).Domain := ⟨n,ht w.val w.property n nb⟩
      let b : (rt_model_l Q hn).Domain := ⟨y,ht w.val w.property y yb⟩
      exact ⟨nb,congrArg Subtype.val ((h.constant_entry a b).mp ((rt_entry_l ht hn hE a b c).mpr ny)).2⟩
    · rintro ⟨nb,rfl⟩
      let a : (rt_model_l Q hn).Domain := ⟨n,ht w.val w.property n nb⟩
      exact (rt_entry_l ht hn hE a z c).mp ((h.constant_entry a z).mpr ⟨nb,rfl⟩)
  · intro n y
    constructor
    · intro ny
      have nb := (fs.bound_l ny).1
      have yb := (fs.bound_l ny).2
      let a : (rt_model_l Q hn).Domain := ⟨n,ht w.val w.property n nb⟩
      let b : (rt_model_l Q hn).Domain := ⟨y,ht w.val w.property y yb⟩
      exact ⟨nb,(rt_successor_l ht hn hE b a).mp
        ((h.successor_entry a b).mp ((rt_entry_l ht hn hE a b s).mpr ny)).2⟩
    · rintro ⟨nb,succ⟩
      obtain ⟨v,hv,vb⟩ := hw.1.2 n nb
      have yb : M.mem y w.val := Structure.SuccessorOf.eq hE hv succ ▸ vb
      let a : (rt_model_l Q hn).Domain := ⟨n,ht w.val w.property n nb⟩
      let b : (rt_model_l Q hn).Domain := ⟨y,ht w.val w.property y yb⟩
      exact (rt_entry_l ht hn hE a b s).mp
        ((h.successor_entry a b).mpr ⟨nb,(rt_successor_l ht hn hE b a).mpr succ⟩)

end YesMetaZFC.SetTheory.Internal
