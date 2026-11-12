import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.Model.SetTheory.DirectedSystem.Relative
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemSource

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

/-! ## 原有限支撑超幂系统的一阶证书

分量公式、标签、过渡代表和直接系统均原样编码，量化的是实际集合图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def ep_graph_m {d} (ω κ L X R F J O Z A p T S : Term d) : Formula 1 d := set[d] ⟪
  ⌜di_order_m⌝ₚ(⌜J⌝ₛ, ⌜O⌝ₛ) ∧
  (∀ a b, ⌜rd_entry0_m⌝ₚ(a, b, ⌜O⌝ₛ) ↔ a ∈ ⌜J⌝ₛ ∧ b ∈ ⌜J⌝ₛ ∧ (∃ q, ⌜ei_map_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, a, b, q))) ∧
  ⌜fn0_m⌝ₚ(⌜A⌝ₛ, ⌜J⌝ₛ, ⌜p⌝ₛ) ∧ (∀ a, a ∈ ⌜J⌝ₛ ↔ ⌜ei_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, a)) ∧
  (∃ Q, ⌜fn0_m⌝ₚ(⌜J⌝ₛ, Q, ⌜Z⌝ₛ) ∧ (∀ a c, ⌜rd_entry0_m⌝ₚ(a, c, ⌜Z⌝ₛ) →
    ⌜ep_component_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, ⌜F⌝ₛ, a, c))) ∧
  (∀ u, u ∈ ⌜A⌝ₛ ↔ ∃ a B, ⌜kpair0_m⌝ₚ(u, a, B) ∧ ⌜ep_at_m⌝ₚ(⌜Z⌝ₛ, a, B)) ∧
  (∀ u a B, ⌜kpair0_m⌝ₚ(u, a, B) → (⌜rd_entry0_m⌝ₚ(u, a, ⌜p⌝ₛ) ↔ u ∈ ⌜A⌝ₛ)) ∧
  (∀ u v, ⌜rd_entry0_m⌝ₚ(u, v, ⌜T⌝ₛ) ↔ u ∈ ⌜A⌝ₛ ∧ v ∈ ⌜A⌝ₛ ∧ (∃ a b B C,
    ⌜kpair0_m⌝ₚ(u, a, B) ∧ ⌜kpair0_m⌝ₚ(v, b, C) ∧ ⌜ep_arrow_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, a, b, B, C))) ∧
  (∀ u v, ⌜rd_entry0_m⌝ₚ(u, v, ⌜S⌝ₛ) ↔ u ∈ ⌜A⌝ₛ ∧ v ∈ ⌜A⌝ₛ ∧ (∃ a B C,
    ⌜kpair0_m⌝ₚ(u, a, B) ∧ ⌜kpair0_m⌝ₚ(v, a, C) ∧ ⌜ep_rel_m⌝ₚ(⌜Z⌝ₛ, a, B, C)))⟫
derive_free_closed ep_graph_m

theorem ep_graph_sat_l (hE : Extensional M) {d} (η : Env M d) (ω κ L X R F J O Z A p T S : Term d) :
    Formula.satisfies η (ep_graph_m ω κ L X R F J O Z A p T S) ↔
      Ep_graph_d I (ω.eval η) (κ.eval η) (L.eval η) (X.eval η) (R.eval η) (F.eval η)
        (J.eval η) (O.eval η) (Z.eval η) (A.eval η) (p.eval η) (T.eval η) (S.eval η) := by
  simp only [ep_graph_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, di_order_sat_l hE,
    fn0_sat_l hE, rd_entry0_sat_l hE, kpair0_sat_l hE, ei_map_sat_l hE, ei_sat_l hE,
    ep_component_sat_l I hE, ep_at_sat_l hE, ep_arrow_sat_l hE, ep_rel_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, ⟨Q, e, models⟩, f, g, h, i⟩ => ⟨⟨a, b, c, d, ⟨Q, e⟩, f, g, h, i⟩, models⟩,
    fun h => ⟨h.order, h.order_spec, h.projection, h.indices, (h.codes.elim fun Q hz => ⟨Q, hz, h.components⟩), h.nodes, h.index, h.arrows, h.relations⟩⟩

def ep_lift_m {d} (ω κ L X a b B C : Term d) : Formula 1 d := set[d] ⟪
  ∀ f ∈ ⌜B⌝ₛ, ∃ m n q g, m ∈ ⌜ω⌝ₛ ∧ n ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(m, n, q) ∧ ⌜fn0_m⌝ₚ(n, ⌜L⌝ₛ, ⌜b⌝ₛ) ∧
    ⌜cp0_m⌝ₚ(m, n, ⌜L⌝ₛ, q, ⌜b⌝ₛ, ⌜a⌝ₛ) ∧ g ∈ ⌜C⌝ₛ ∧ ⌜ep_pull_m⌝ₚ(⌜κ⌝ₛ, ⌜X⌝ₛ, m, n, q, f, g)⟫
derive_free_closed ep_lift_m

theorem ep_lift_sat_l (hE : Extensional M) {d} (η : Env M d) (ω κ L X a b B C : Term d) :
    Formula.satisfies η (ep_lift_m ω κ L X a b B C) ↔ Ep_lift_d
      (ω.eval η) (κ.eval η) (L.eval η) (X.eval η) (a.eval η) (b.eval η) (B.eval η) (C.eval η) := by
  simp only [ep_lift_m, Ep_lift_d, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, fn0_sat_l hE, cp0_sat_l hE,
    ep_pull_sat_l hE, Definitional.Term.eval_weaken]; rfl

def ep_system_m {d} (ω κ L X R F J O Z A p T S : Term d) : Formula 1 d := set[d] ⟪
  ⌜ep_graph_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, ⌜F⌝ₛ, ⌜J⌝ₛ, ⌜O⌝ₛ, ⌜Z⌝ₛ, ⌜A⌝ₛ, ⌜p⌝ₛ, ⌜T⌝ₛ, ⌜S⌝ₛ) ∧
  ⌜di_system_m⌝ₚ(⌜J⌝ₛ, ⌜O⌝ₛ, ⌜A⌝ₛ, ⌜p⌝ₛ, ⌜T⌝ₛ, ⌜S⌝ₛ) ∧
  (∀ u v a b B C, ⌜kpair0_m⌝ₚ(u, a, B) → ⌜kpair0_m⌝ₚ(v, b, C) → ⌜rd_entry0_m⌝ₚ(u, v, ⌜T⌝ₛ) →
    ⌜ep_lift_m⌝ₚ(⌜ω⌝ₛ, ⌜κ⌝ₛ, ⌜L⌝ₛ, ⌜X⌝ₛ, a, b, B, C))⟫
derive_free_closed ep_system_m

theorem ep_system_sat_l (hE : Extensional M) {d} (η : Env M d) (ω κ L X R F J O Z A p T S : Term d) :
    Formula.satisfies η (ep_system_m ω κ L X R F J O Z A p T S) ↔
      Ep_system_d I (ω.eval η) (κ.eval η) (L.eval η) (X.eval η) (R.eval η) (F.eval η)
        (J.eval η) (O.eval η) (Z.eval η) (A.eval η) (p.eval η) (T.eval η) (S.eval η) := by
  simp only [ep_system_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    kpair0_sat_l hE, rd_entry0_sat_l hE, ep_graph_sat_l I hE, di_system_sat_l hE, ep_lift_sat_l hE,
    Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun h => ⟨h.toEp_graph_d, h.diagram, h.representatives⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 有限支撑代表与过渡方程的绝对性

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

/-! ## 从传递工作源读取整个指定超幂系统

索引、分量、商类、过渡图及全部代表方程一次恢复到背景模型。尤其索引
列和标签并的反向包含覆盖全部背景有限支撑，不预设壳的外部可数闭性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

private theorem rt_ep_at_l (hKP : M.Models KP) {V : M.Domain} (hv : M.TransitiveSet V) (nv : Nonempty {x // M.mem x V})
    (pair : ∀ a b, M.mem a V → M.mem b V → ∃ p, M.mem p V ∧ Pair_d M p a b)
    (Z a B : (rt_model_l V nv).Domain) : Ep_at_d Z a B ↔ Ep_at_d Z.val a.val B.val := by
  have ent := rt_entry_l hv nv hKP.1
  have kp := rt_kpair_l hKP.1 (KP.exists_pair hKP) hv nv pair
  constructor
  · rintro ⟨c, C, S, hc, hp, hb⟩
    exact ⟨c.val, C.val, S.val, (ent ..).mp hc, (kp ..).mp hp, hb⟩
  · rintro ⟨c, C, S, hc, hp, hb⟩
    have cm := (rd_entry_transitive_l hv Z.property hc).2
    have cs := hp.mem_l M hv cm
    exact ⟨⟨c, cm⟩, ⟨C, cs.1⟩, ⟨S, cs.2⟩, (ent ..).mpr hc, (kp ..).mpr hp, hb⟩

private theorem rt_ep_rel_l (hKP : M.Models KP) {V : M.Domain} (hv : M.TransitiveSet V) (nv : Nonempty {x // M.mem x V})
    (pair : ∀ a b, M.mem a V → M.mem b V → ∃ p, M.mem p V ∧ Pair_d M p a b)
    (Z a B D : (rt_model_l V nv).Domain) : Ep_rel_d Z a B D ↔ Ep_rel_d Z.val a.val B.val D.val := by
  have ent := rt_entry_l hv nv hKP.1
  have kp := rt_kpair_l hKP.1 (KP.exists_pair hKP) hv nv pair
  constructor
  · rintro ⟨c, C, S, hc, hp, hd⟩
    exact ⟨c.val, C.val, S.val, (ent ..).mp hc, (kp ..).mp hp, (ent ..).mp hd⟩
  · rintro ⟨c, C, S, hc, hp, hd⟩
    have cm := (rd_entry_transitive_l hv Z.property hc).2
    have cs := hp.mem_l M hv cm
    exact ⟨⟨c, cm⟩, ⟨C, cs.1⟩, ⟨S, cs.2⟩, (ent ..).mpr hc, (kp ..).mpr hp, (ent ..).mpr hd⟩

theorem Fs_read_d.graph_read_l (hZF : M.Models ZF) {ω V : M.Domain}
    (source : Fs_read_d ω V) (nv : Nonempty {x // M.mem x V})
    (w μ L X R F J O Z A p T S : (rt_model_l V nv).Domain) (hw : w.val = ω)
    (h : Ep_graph_d (rt_pair_l source.transitive nv hZF.1 source.pair) w μ L X R F J O Z A p T S) :
    Ep_graph_d (kp_pair_l (ZF.modelsKP hZF)) ω μ.val L.val X.val R.val F.val J.val O.val Z.val A.val p.val T.val S.val := by
  have vt := source.transitive
  have ent := rt_entry_l vt nv hZF.1
  have kp := rt_kpair_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) vt nv source.pair
  have node := rt_ep_at_l (ZF.modelsKP hZF) vt nv source.pair
  have rel := rt_ep_rel_l (ZF.modelsKP hZF) vt nv source.pair
  have arrow := source.arrow_read_l hZF nv w μ L X
  have finite {n B f} (hn : M.mem n ω) (hB : M.mem B V) (hf : Fn0_d n B f) : M.mem f V := by
    exact source.functions n B f hn (vt B hB) hf
  have order (a b : (rt_model_l V nv).Domain) :
      Rd_entry_d a.val b.val O.val ↔ M.mem a.val J.val ∧ M.mem b.val J.val ∧ ∃ q, Ei_map_d ω L.val a.val b.val q := by
    refine (ent a b O).symm.trans ((h.order_spec a b).trans (and_congr Iff.rfl (and_congr Iff.rfl ?_)))
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q.val, hw ▸ (rt_ei_map_l (ZF.modelsKP hZF) vt nv w L a b q).mp hq⟩
    · rintro ⟨q, hq⟩
      have old := hq
      obtain ⟨m, n, hm, hn, fn, _⟩ := hq
      have hqV := finite hm (vt ω source.omega_mem n hn) fn
      exact ⟨⟨q, hqV⟩, (rt_ei_map_l (ZF.modelsKP hZF) vt nv w L a b _).mpr (hw.symm ▸ old)⟩
  obtain ⟨B, models⟩ := h.codes
  have components := h.components
  refine ⟨⟨rt_di_order_l (ZF.modelsKP hZF) vt nv J O h.order, ?_, (rt_fn_l vt nv hZF.1 ..).mp h.projection,
    ?_, ⟨B.val, (rt_fn_l vt nv hZF.1 ..).mp models⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b
    constructor
    · intro hab
      have ab := rd_entry_transitive_l vt O.property hab
      exact (order ⟨a, ab.1⟩ ⟨b, ab.2⟩).mp hab
    · intro hab
      exact (order ⟨a, vt J.val J.property a hab.1⟩ ⟨b, vt J.val J.property b hab.2.1⟩).mpr hab
  · intro a
    constructor
    · intro ha
      exact hw ▸ (rt_ei_l (ZF.modelsKP hZF) vt nv w L _).mp ((h.indices ⟨a, vt J.val J.property a ha⟩).mp ha)
    · intro ha
      have old := ha
      obtain ⟨n, hn, fn, _⟩ := ha
      exact (h.indices ⟨a, finite hn L.property fn⟩).mpr
        ((rt_ei_l (ZF.modelsKP hZF) vt nv w L _).mpr (hw.symm ▸ old))
  · intro u
    constructor
    · intro hu
      obtain ⟨a, B, hp, hat⟩ := (h.nodes ⟨u, vt A.val A.property u hu⟩).mp hu
      exact ⟨a.val, B.val, (kp ..).mp hp, (node ..).mp hat⟩
    · rintro ⟨a, B, hp, hat⟩
      obtain ⟨c, C, R, hc, cp, hb⟩ := hat
      have ac := rd_entry_transitive_l vt Z.property hc
      have hB := vt C (cp.mem_l M vt ac.2).1 B hb
      obtain ⟨u', hu', hp'⟩ := source.kpair_l ac.1 hB
      have hu := kpair_unique_l M hZF.1 hp' hp ▸ hu'
      exact (h.nodes ⟨u, hu⟩).mpr ⟨⟨a, ac.1⟩, ⟨B, hB⟩, (kp ..).mpr hp,
        (node ..).mpr ⟨c, C, R, hc, cp, hb⟩⟩
  · intro u a B hp
    have read (hu : M.mem u V) : Rd_entry_d u a p.val ↔ M.mem u A.val := by
      have ab := hp.mem_l M vt hu
      exact (ent ⟨u, hu⟩ ⟨a, ab.1⟩ p).symm.trans (h.index _ _ ⟨B, ab.2⟩ ((kp ..).mpr hp))
    exact ⟨fun hu => (read (rd_entry_transitive_l vt p.property hu).1).mp hu,
      fun hu => (read (vt A.val A.property u hu)).mpr hu⟩
  · intro u v
    have read (u v : (rt_model_l V nv).Domain) := h.arrows u v
    constructor
    · intro huv
      have uv := rd_entry_transitive_l vt T.property huv
      obtain ⟨hu, hv, a, b, B, C, hp, hq, hc⟩ := (read ⟨u, uv.1⟩ ⟨v, uv.2⟩).mp ((ent ..).mpr huv)
      exact ⟨hu, hv, a.val, b.val, B.val, C.val, (kp ..).mp hp, (kp ..).mp hq, (arrow a b B C hw).mp hc⟩
    · rintro ⟨hu, hv, a, b, B, C, hp, hq, hc⟩
      have uV := vt A.val A.property u hu
      have vV := vt A.val A.property v hv
      have ab := hp.mem_l M vt uV
      have bc := hq.mem_l M vt vV
      exact (ent ..).mp ((read ⟨u, uV⟩ ⟨v, vV⟩).mpr ⟨hu, hv, ⟨a, ab.1⟩, ⟨b, bc.1⟩,
        ⟨B, ab.2⟩, ⟨C, bc.2⟩, (kp ..).mpr hp, (kp ..).mpr hq, (arrow _ _ _ _ hw).mpr hc⟩)
  · intro u v
    constructor
    · intro huv
      have uv := rd_entry_transitive_l vt S.property huv
      obtain ⟨hu, hv, a, B, C, hp, hq, hc⟩ := (h.relations ⟨u, uv.1⟩ ⟨v, uv.2⟩).mp ((ent ..).mpr huv)
      exact ⟨hu, hv, a.val, B.val, C.val, (kp ..).mp hp, (kp ..).mp hq, (rel ..).mp hc⟩
    · rintro ⟨hu, hv, a, B, C, hp, hq, hc⟩
      have uV := vt A.val A.property u hu
      have vV := vt A.val A.property v hv
      have ab := hp.mem_l M vt uV
      have ac := hq.mem_l M vt vV
      exact (ent ..).mp ((h.relations ⟨u, uV⟩ ⟨v, vV⟩).mpr ⟨hu, hv, ⟨a, ab.1⟩, ⟨B, ab.2⟩, ⟨C, ac.2⟩,
        (kp ..).mpr hp, (kp ..).mpr hq, (rel ..).mpr hc⟩)
  · intro a c hac
    have ac := rd_entry_transitive_l vt Z.property hac
    exact source.component_read_l hZF nv w μ L X R F ⟨a, ac.1⟩ ⟨c, ac.2⟩ hw
      (components _ _ ((ent ..).mpr hac))

theorem Fs_read_d.system_read_l (hZF : M.Models ZF) {ω V : M.Domain}
    (source : Fs_read_d ω V) (nv : Nonempty {x // M.mem x V})
    (w μ L X R F J O Z A p T S : (rt_model_l V nv).Domain) (hw : w.val = ω)
    (h : Ep_system_d (rt_pair_l source.transitive nv hZF.1 source.pair) w μ L X R F J O Z A p T S) :
    Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω μ.val L.val X.val R.val F.val J.val O.val Z.val A.val p.val T.val S.val := by
  have vt := source.transitive
  have ent := rt_entry_l vt nv hZF.1
  have kp := rt_kpair_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) vt nv source.pair
  refine ⟨source.graph_read_l hZF nv w μ L X R F J O Z A p T S hw h.toEp_graph_d,
    rt_di_system_l (ZF.modelsKP hZF) vt nv J O A p T S h.diagram, ?_⟩
  intro u v a b B C hu hv huv f hf
  have uv := rd_entry_transitive_l vt T.property huv
  have ab := hu.mem_l M vt uv.1
  have bc := hv.mem_l M vt uv.2
  obtain ⟨m, n, q, g, hm, hn, hq, hb, ha, hg, pull⟩ :=
    h.representatives ⟨u, uv.1⟩ ⟨v, uv.2⟩ ⟨a, ab.1⟩ ⟨b, bc.1⟩ ⟨B, ab.2⟩ ⟨C, bc.2⟩
      ((kp ..).mpr hu) ((kp ..).mpr hv) ((ent ..).mpr huv) ⟨f, vt B ab.2 f hf⟩ hf
  exact ⟨m.val, n.val, q.val, g.val, hw ▸ hm, hw ▸ hn, (rt_fn_l vt nv hZF.1 ..).mp hq,
    (rt_fn_l vt nv hZF.1 ..).mp hb, (rt_cp_l vt nv hZF.1 ..).mp ha, hg,
    (source.pull_read_l hZF nv μ X m n q _ g (hw ▸ hm) (hw ▸ hn)).mp pull⟩

end YesMetaZFC.SetTheory.LargeCardinal
