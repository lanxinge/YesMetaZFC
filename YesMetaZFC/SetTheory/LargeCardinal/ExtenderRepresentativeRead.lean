import YesMetaZFC.SetTheory.LargeCardinal.ExtenderComponentRead
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSystemCode
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiniteSyntax

/-! # 有限支撑代表与过渡方程的绝对性

坐标列允许任意内部有限长度。所有背景坐标拉回都属于工作源，所以相对
方程实际覆盖原超幂的全部代表，不只覆盖先选出的像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem Fs_read_d.fun_read_l (hZF : M.Models ZF) {ω Z : M.Domain}
    (source : Fs_read_d ω Z) (nz : Nonempty {x // M.mem x Z})
    (μ X n f : (rt_model_l Z nz).Domain) (hn : M.mem n.val ω) :
    Ep_fun_d μ X n f ↔ Ep_fun_d μ.val X.val n.val f.val := by
  constructor
  · rintro ⟨D, hd, hf⟩
    exact ⟨D.val, (source.space_read_l hZF nz μ n D hn).mp hd, (rt_fn_l source.transitive nz hZF.1 ..).mp hf⟩
  · intro h
    obtain ⟨D, hD, hd⟩ := source.spaces μ.val n.val μ.property hn
    exact ⟨⟨D, hD⟩, (source.space_read_l hZF nz μ n _ hn).mpr hd,
      (rt_fn_l source.transitive nz hZF.1 ..).mpr (h.at_l hZF.1 hd)⟩

theorem Fs_read_d.pull_read_l (hZF : M.Models ZF) {ω Z : M.Domain}
    (source : Fs_read_d ω Z) (nz : Nonempty {x // M.mem x Z})
    (μ X m n q f g : (rt_model_l Z nz).Domain) (hm : M.mem m.val ω) (hn : M.mem n.val ω) :
    Ep_pull_d μ X m n q f g ↔ Ep_pull_d μ.val X.val m.val n.val q.val f.val g.val := by
  have ent := rt_entry_l source.transitive nz hZF.1
  refine and_congr (source.fun_read_l hZF nz μ X m f hm)
    (and_congr (source.fun_read_l hZF nz μ X n g hn) ?_)
  constructor
  · intro h s r hs hr x
    have finite {b t} (hb : M.mem b ω) (ht : Fn0_d b μ.val t) :=
      source.functions b μ.val t hb (source.transitive μ.val μ.property) ht
    let s' : (rt_model_l Z nz).Domain := ⟨s, finite hn hs⟩
    let r' : (rt_model_l Z nz).Domain := ⟨r, finite hm hr.1⟩
    have hh := h s' r' ((rt_fn_l source.transitive nz hZF.1 ..).mpr hs)
      ((rt_cp_l source.transitive nz hZF.1 ..).mpr hr)
    constructor
    · intro hx
      exact (ent ..).mp ((hh ⟨x, (rd_entry_transitive_l source.transitive g.property hx).2⟩).mp ((ent ..).mpr hx))
    · intro hx
      exact (ent ..).mp ((hh ⟨x, (rd_entry_transitive_l source.transitive f.property hx).2⟩).mpr ((ent ..).mpr hx))
  · intro h s r hs hr x
    exact (ent s x g).trans ((h s.val r.val ((rt_fn_l source.transitive nz hZF.1 ..).mp hs)
      ((rt_cp_l source.transitive nz hZF.1 ..).mp hr) x.val).trans (ent r x f).symm)

theorem rt_ei_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (nz : Nonempty {x // M.mem x Z}) (ω L a : (rt_model_l Z nz).Domain) :
    Ei_d ω L a ↔ Ei_d ω.val L.val a.val := by
  let ρ : Env (rt_model_l Z nz) 3 := ⟨Fin.cases a (Fin.cases L (fun _ => ω)), fun _ => ω⟩
  exact (ei_sat_l (rt_model_ext_l hKP.1 hZ nz) ρ (.bound 2) (.bound 1) .newest).symm.trans
    ((rt_model_delta_l hZ nz (ei_delta_l ..) ρ).trans (ei_sat_l hKP.1 ..))

theorem rt_ei_map_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (nz : Nonempty {x // M.mem x Z}) (ω L a b q : (rt_model_l Z nz).Domain) :
    Ei_map_d ω L a b q ↔ Ei_map_d ω.val L.val a.val b.val q.val := by
  let ρ : Env (rt_model_l Z nz) 5 := ⟨Fin.cases q (Fin.cases b (Fin.cases a (Fin.cases L (fun _ => ω)))), fun _ => ω⟩
  exact (ei_map_sat_l (rt_model_ext_l hKP.1 hZ nz) ρ (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
    ((rt_model_delta_l hZ nz (ei_map_delta_l ..) ρ).trans (ei_map_sat_l hKP.1 ..))

theorem Fs_read_d.arrow_read_l (hZF : M.Models ZF) {ω Z : M.Domain}
    (source : Fs_read_d ω Z) (nz : Nonempty {x // M.mem x Z})
    (w μ L X a b B C : (rt_model_l Z nz).Domain) (hw : w.val = ω) :
    Ep_arrow_d w μ L X a b B C ↔ Ep_arrow_d ω μ.val L.val X.val a.val b.val B.val C.val := by
  constructor
  · rintro ⟨m, n, q, f, g, hm, hn, hq, hb, ha, hf, hg, pull⟩
    exact ⟨m.val, n.val, q.val, f.val, g.val, hw ▸ hm, hw ▸ hn,
      (rt_fn_l source.transitive nz hZF.1 ..).mp hq, (rt_fn_l source.transitive nz hZF.1 ..).mp hb,
      (rt_cp_l source.transitive nz hZF.1 ..).mp ha, hf, hg,
      (source.pull_read_l hZF nz μ X m n q f g (hw ▸ hm) (hw ▸ hn)).mp pull⟩
  · rintro ⟨m, n, q, f, g, hm, hn, hq, hb, ha, hf, hg, pull⟩
    have hmZ := source.transitive ω source.omega_mem m hm
    have hnZ := source.transitive ω source.omega_mem n hn
    have hqZ := source.functions m n q hm (source.transitive n hnZ) hq
    refine ⟨⟨m, hmZ⟩, ⟨n, hnZ⟩, ⟨q, hqZ⟩, ⟨f, source.transitive B.val B.property f hf⟩,
      ⟨g, source.transitive C.val C.property g hg⟩, (show M.mem m w.val from hw.symm ▸ hm), (show M.mem n w.val from hw.symm ▸ hn),
      (rt_fn_l source.transitive nz hZF.1 ..).mpr hq, (rt_fn_l source.transitive nz hZF.1 ..).mpr hb,
      (rt_cp_l source.transitive nz hZF.1 ..).mpr ha, hf, hg, ?_⟩
    exact (source.pull_read_l hZF nz μ X _ _ _ _ _ hm hn).mpr pull

end YesMetaZFC.SetTheory.LargeCardinal
