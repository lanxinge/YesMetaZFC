import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedCollapse
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFunctionCode
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderValue

/-! # 所属源的求值图辨认施加超幂的实际临界点像

有限 κ 幂子集的一致性双向搬运 κ 值函数。由这些原代表构造到指定极限
的投影，关系恰为隶属关系的逆像，递归唯一性再辨认原求值图的每个值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_pool_d.realize_l
    {ω κ K K₀ L X R N R₀ F J O Z A p T S q C W Y g D₀ a₀ f₀ H Γ D Q P G U V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K₀ N R₀)
    (agree : Ea_agree_d ω κ X N) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (wc : Wc_graph_d C W g) (bij : M.IsSetBijectionFromTo I g C Y)
    (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ κ f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (hHΓ : Rd_entry_d H Γ g) (hΓ : M.TransitiveSet Γ) (pool : Eb_pool_d ω κ L N κ J K₀ P G D)
    (range : M.IsRangeOf I U F) (membership : Rd_fun_d .mem κ κ κ V)
    (edges : ∀ u v, Rd_entry_d u v Q ↔ M.mem u D ∧ M.mem v D ∧ Eb_link_d ω κ L κ J K₀ U V F G u v) :
    ∃ e, Wc_map_d D Q Γ e ∧
      (∀ u x, Rd_entry_d u x e ↔ M.mem u D ∧ ∃ a f, KPair_d M u a f ∧ Ep_value_d q g a f x) ∧
      ∀ u v x y, Rd_entry_d u x e → Rd_entry_d v y e → (Rd_entry_d u v Q ↔ M.mem x y) := by
  have eq := hZF.1.eq_of_same_members K₀ K (fun f => (owner.finite f).trans (source.finite f).symm)
  subst K₀
  have reverse : Ea_subset_d ω κ N X := fun n D A hn hd sub => (agree n D A hn hd sub).mpr
  obtain ⟨v, vf, values⟩ := eb_projection_l hZF source family system limit
    (source.transitive κ source.cardinal_mem) (fun u hu => by
      obtain ⟨n, a, D', f, hn, ha, fn, space, hf, gf, pair⟩ := pool.read_l hZF owner hu
      exact ⟨a, ha, f, reverse.function_l hZF owner source hn space hf gf, pair,
        n, hn, D', source.space_mem_l hZF hn space, fn,
        (eb_space_iff_l (ZF.modelsKP hZF) source.finite hn).mpr space, gf⟩)
  obtain ⟨t, tf, ts⟩ := ZF.exists_compositionFunction hZF I (fn0_function_l (ZF.modelsKP hZF) vf) bij.1.1
  have evaluation u x : Rd_entry_d u x t ↔ M.mem u D ∧ ∃ a f, KPair_d M u a f ∧ Ep_value_d q g a f x := by
    refine (ts u x).trans ⟨?_, ?_⟩
    · rintro ⟨hu, E, huE, hEx⟩
      obtain ⟨_, a, f, pair, ev⟩ := (values u E).mp huE
      exact ⟨hu, a, f, pair, E, ev, hEx⟩
    · rintro ⟨hu, a, f, pair, E, ev, hEx⟩
      exact ⟨hu, E, (values u E).mpr ⟨hu, a, f, pair, ev⟩, hEx⟩
  obtain ⟨_, n₀, hn₀, ha₀, D₁, space₀, ff₀⟩ := fv.source_l hZF family system limit
  have eq := ff₀.domain_eq_l hZF.1 ff
  subst D₁
  have into u x (hux : Rd_entry_d u x t) : M.mem x Γ := by
    obtain ⟨hu, a, f, pair, E, ev, hEx⟩ := (evaluation u x).mp hux
    obtain ⟨n, a', D', f', hn, _, ha, space, _, gf, pair'⟩ := pool.read_l hZF owner hu
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair' pair
    exact (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hEx hHΓ).mp
      (ep_repr_bound_mem_l hZF source family system limit ff constant fv source.cardinal_mem hn ha space gf ev)
  have onto x (hx : M.mem x Γ) : ∃ u, M.mem u D ∧ Rd_entry_d u x t := by
    obtain ⟨E, _, edge, hEx⟩ := ((wc.2 H Γ hHΓ).2.2 x).mp hx
    obtain ⟨n, a, D', f, hn, haJ, ha, space, hf, gf, ev⟩ :=
      ep_repr_bounded_l hZF source family system limit hn₀ ha₀ space₀ ff constant fv source.cardinal_mem edge
    have hfN := agree.subset_l.function_l hZF source owner hn space hf gf
    obtain ⟨u, pair⟩ := (I).total a f
    have hu := pool.node_l hZF owner hn haJ ha space hfN gf pair
    exact ⟨u, hu, (evaluation u x).mpr ⟨hu, a, f, pair, E, ev, hEx⟩⟩
  have relation x y (hx : M.mem x κ) (hy : M.mem y κ) : Rd_entry_d x y V ↔ Rd_entry_d x y R := by
    obtain ⟨c, code⟩ := source.code
    have κX := source.transitive κ source.cardinal_mem
    refine ⟨fun ⟨p, pair, hp⟩ => ?_, fun h => ?_⟩
    · obtain ⟨a, b, ha, hb, hab, pair'⟩ := (membership p).mp hp
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair' pair
      exact (code.2 a b).mpr ⟨κX a ha, κX b hb, hab⟩
    · obtain ⟨p, pair⟩ := (I).total x y
      exact ⟨p, pair, (membership p).mpr ⟨x, y, hx, hy, ((code.2 x y).mp h).2.2, pair⟩⟩
  have member u w x y (hx : Rd_entry_d u x t) (hy : Rd_entry_d w y t) : Rd_entry_d u w Q ↔ M.mem x y := by
    obtain ⟨hu, a, f, pair, E, ev, hEx⟩ := (evaluation u x).mp hx
    obtain ⟨hw, b, k, pair', H, kv, hHy⟩ := (evaluation w y).mp hy
    obtain ⟨a', ha, f', hf, up, _, _, D', _, _, _, gf⟩ := (pool.nodes u).mp hu
    obtain ⟨b', hb, k', hk, wp, _, _, D'', _, _, _, kf⟩ := (pool.nodes w).mp hw
    obtain ⟨ea, ef⟩ := kpair_injective_l M up pair
    obtain ⟨eb, ek⟩ := kpair_injective_l M wp pair'
    subst a' f' b' k'
    have link : Eb_link_d ω κ L κ J K U V F G u w ↔ Eb_edge_d ω κ L κ J K U V F a f b k := by
      refine ⟨?_, fun h => ⟨a, ha, f, hf, b, hb, k, hk, pair, pair', h⟩⟩
      rintro ⟨a', _, f', _, b', _, k', _, up', wp', h⟩
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M up' pair
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M wp' pair'
      exact h
    exact (edges u w).trans ((Iff.intro (And.right ∘ And.right) (fun h => ⟨hu, hw, h⟩)).trans
      (link.trans ((eb_edge_iff_l hZF source family system limit (source.transitive κ source.cardinal_mem)
        (fun a U' h => (range U').mpr ⟨a, h⟩) relation gf kf ev kv).trans
          (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hEx hHy))))
  have map' : Wc_map_d D Q Γ t := ⟨hΓ, (fn0_of_function_l (ZF.modelsKP hZF) tf).retarget_l into, onto,
    fun u _ x _ hux y hy => ⟨fun hyx => (onto y hy).elim fun w hw =>
      ⟨w, hw.1, (member w u y x hw.2 hux).mpr hyx, hw.2⟩,
      fun ⟨w, _, hwu, hwy⟩ => (member w u y x hwy hux).mp hwu⟩⟩
  exact ⟨t, map', evaluation, member⟩

/-- 任一所属源内的有界塌缩证书都恢复同一个施加超幂值及同一求值图。 -/
theorem Eb_collapse_d.realize_l
    {ω κ K K₀ L X R N R₀ F J O Z A p T S q C W Y g D₀ a₀ f₀ H Γ B D Q e : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K₀ N R₀)
    (agree : Ea_agree_d ω κ X N) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (wc : Wc_graph_d C W g) (bij : M.IsSetBijectionFromTo I g C Y)
    (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ κ f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (hHΓ : Rd_entry_d H Γ g) (hΓ : M.TransitiveSet Γ) (collapse : Eb_collapse_d ω κ L K₀ N κ F D Q B e) :
    B = Γ ∧ ∀ u x, Rd_entry_d u x e ↔ M.mem u D ∧ ∃ a f, KPair_d M u a f ∧ Ep_value_d q g a f x := by
  obtain ⟨J₀, P, G, U, V, pool, indices, _, _, _, _, range, membership, _, edges, map, _⟩ := collapse
  have eq := hZF.1.eq_of_same_members J₀ J (fun a => (indices a).trans (system.indices a).symm)
  subst J₀
  obtain ⟨t, map', evaluation, _⟩ := pool.realize_l hZF source owner agree family system limit wc bij ff constant fv hHΓ hΓ range membership edges
  exact ⟨map.unique_l hZF map', map.graph_unique_l hZF map' ▸ evaluation⟩

/-- 小节点集在所属源中塌缩，直接回收原施加超幂的临界点像，无需构造所属源的完整超幂。 -/
theorem eb_owned_value_l
    {ω κ K K₀ L X R N R₀ F J O Z A p T S q C W Y g D₀ a₀ f₀ H Γ V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K₀ N R₀)
    (agree : Ea_agree_d ω κ X N) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (wc : Wc_graph_d C W g) (bij : M.IsSetBijectionFromTo I g C Y)
    (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ κ f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (hHΓ : Rd_entry_d H Γ g) (hΓ : M.TransitiveSet Γ)
    (power : Sc_power_d N) (hL : M.mem L N) (hF : M.mem F N)
    (hl : M.IsLimitOrdinal L) (level : Er_level_d N L V) (hκ : M.mem κ V) :
    M.mem Γ N ∧ ∃ D Q e, Eb_collapse_d ω κ L K₀ N κ F D Q Γ e ∧
      ∀ u x, Rd_entry_d u x e ↔ M.mem u D ∧ ∃ a f, KPair_d M u a f ∧ Ep_value_d q g a f x := by
  obtain ⟨c, code⟩ := owner.code
  let φ : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  obtain ⟨V₀, hV₀, shape, rel⟩ := sc_relation_source_l hZF owner.omega owner.transitive code owner.theory φ (.mem ..)
    ⟨Fin.elim0, fun _ => κ⟩ (fun i => Fin.elim0 i) owner.cardinal_mem owner.cardinal_mem
  have read x y : Rd_entry_d x y V₀ ↔ M.mem x κ ∧ M.mem y κ ∧ M.mem x y :=
    (rel x y).trans (and_congr_right fun _ => and_congr_right fun _ => Formula.satisfies_mem_iff ..)
  have membership : Rd_fun_d .mem κ κ κ V₀ := by
    intro p
    refine ⟨fun hp => ?_, ?_⟩
    · obtain ⟨x, y, pair⟩ := shape p hp
      obtain ⟨hx, hy, hxy⟩ := (read x y).mp ⟨p, pair, hp⟩
      exact ⟨x, y, hx, hy, hxy, pair⟩
    · rintro ⟨x, y, hx, hy, hxy, pair⟩
      obtain ⟨q, qp, hq⟩ := (read x y).mpr ⟨hx, hy, hxy⟩
      exact kpair_unique_l M hZF.1 qp pair ▸ hq
  obtain ⟨P, G, D, pool⟩ := eb_pool_l hZF owner power hL owner.cardinal_mem system.indices
  obtain ⟨U, Q, hU, hQ, range, graph, edges⟩ := pool.relation_l hZF owner hL owner.cardinal_mem hF hV₀
  obtain ⟨e, map, evaluation, member⟩ := pool.realize_l hZF source owner agree family system limit wc bij ff constant fv hHΓ hΓ range membership edges
  obtain ⟨hΓN, he⟩ := sc_presentation_l hZF owner.omega owner.transitive code owner.theory owner.collapse
    pool.carrier hQ (pool.rank_small_l hZF owner hL hl level hκ hκ) graph hΓ map.function map.onto member
  exact ⟨hΓN, D, Q, e, ⟨J, P, G, U, V₀, pool, system.indices, hU, hV₀, hQ, he, range, membership,
    fun p hp => (graph.1 p hp).elim fun u hu => hu.elim fun v hv =>
      ⟨u, (graph.2 u v ⟨p, hv, hp⟩).1, v, (graph.2 u v ⟨p, hv, hp⟩).2, hv⟩,
    edges, map, member⟩, evaluation⟩

end YesMetaZFC.SetTheory.LargeCardinal
