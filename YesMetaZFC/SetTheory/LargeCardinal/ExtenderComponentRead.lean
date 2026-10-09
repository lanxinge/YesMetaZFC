import YesMetaZFC.SetTheory.LargeCardinal.ExtenderComponents
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderReadSource
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Relative

/-! # 从传递工作源读取原超幂分量

有限幂的全部背景函数由已证有限闭性回收；商结构则沿原投影读取。
输出保留原结构码，不另造同构分量来替换指定见证。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem Fs_read_d.space_read_l (hZF : M.Models ZF) {ω Z : M.Domain}
    (source : Fs_read_d ω Z) (nz : Nonempty {x // M.mem x Z})
    (μ n D : (rt_model_l Z nz).Domain) (hn : M.mem n.val ω) :
    Ep_space_d μ n D ↔ Ep_space_d μ.val n.val D.val := by
  constructor
  · intro h f
    constructor
    · intro hf
      exact (rt_fn_l source.transitive nz hZF.1 n μ _).mp
        ((h ⟨f, source.transitive D.val D.property f hf⟩).mp hf)
    · intro hf
      have mem := source.functions n.val μ.val f hn (source.transitive μ.val μ.property) hf
      exact (h ⟨f, mem⟩).mpr ((rt_fn_l source.transitive nz hZF.1 ..).mpr hf)
  · intro h f
    exact (h f.val).trans (rt_fn_l source.transitive nz hZF.1 ..).symm

theorem Fs_read_d.component_read_l (hZF : M.Models ZF) {ω Z : M.Domain}
    (source : Fs_read_d ω Z) (nz : Nonempty {x // M.mem x Z})
    (w μ L X R F a c : (rt_model_l Z nz).Domain) (hw : w.val = ω)
    (h : Ep_component_d (rt_pair_l source.transitive nz hZF.1 source.pair) w μ L X R F a c) :
    Ep_component_d (kp_pair_l (ZF.modelsKP hZF)) ω μ.val L.val X.val R.val F.val a.val c.val := by
  obtain ⟨n, D, U, G, p, C, T, hn, ha, hd, hu, family, model⟩ := h
  have hn : M.mem n.val ω := hw ▸ hn
  refine ⟨n.val, D.val, U.val, G.val, p.val, C.val, T.val, hn,
    (rt_fn_l source.transitive nz hZF.1 ..).mp ha,
    (source.space_read_l hZF nz _ n D hn).mp hd,
    (rt_entry_l source.transitive nz hZF.1 ..).mp hu, ?_,
    (rt_rp_model_l (ZF.modelsKP hZF) source.transitive nz source.pair ..).mp model⟩
  intro f
  constructor
  · intro hf
    obtain ⟨hx, fn⟩ := (family ⟨f, source.transitive G.val G.property f hf⟩).mp hf
    exact ⟨hx, (rt_fn_l source.transitive nz hZF.1 ..).mp fn⟩
  · rintro ⟨hx, fn⟩
    exact (family ⟨f, source.transitive X.val X.property f hx⟩).mpr
      ⟨hx, (rt_fn_l source.transitive nz hZF.1 ..).mpr fn⟩

end YesMetaZFC.SetTheory.LargeCardinal
