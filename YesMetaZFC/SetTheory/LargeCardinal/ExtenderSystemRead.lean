import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRepresentativeRead
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Relative

/-! # 从传递工作源读取整个指定超幂系统

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
  obtain ⟨B, models, components⟩ := h.models
  refine ⟨rt_di_order_l (ZF.modelsKP hZF) vt nv J O h.order, ?_, (rt_fn_l vt nv hZF.1 ..).mp h.projection,
    ?_, ⟨B.val, (rt_fn_l vt nv hZF.1 ..).mp models, ?_⟩, ?_, ?_, ?_, ?_⟩
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
  · intro a c hac
    have ac := rd_entry_transitive_l vt Z.property hac
    exact source.component_read_l hZF nv w μ L X R F ⟨a, ac.1⟩ ⟨c, ac.2⟩ hw
      (components _ _ ((ent ..).mpr hac))
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
