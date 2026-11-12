import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawOwnedCopy
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SetCode
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Value
import YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedRaw

/-! # 所属源的求值图辨认施加超幂的实际常值像

同一有界函数族给出到指定极限的实际投影，关系恰为隶属关系的逆像，
递归唯一性再辨认原求值图的每个值。κ 值情形的函数一致性由有限幂子集一致性取得。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_pool_d.realize_l
    {ω κ K K₀ L X R N R₀ F J O Z A p T S q C W Y g D₀ a₀ f₀ H Γ B D Q P G U V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ N R₀)
    (common : ∀ n D f, M.mem n ω → Ep_space_d κ n D → Fn0_d D B f → (M.mem f X ↔ M.mem f N))
    (hB : M.mem B X) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (wc : Wc_graph_d C W g) (bij : M.IsSetBijectionFromTo I g C Y)
    (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ B f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (hHΓ : Rd_entry_d H Γ g) (hΓ : M.TransitiveSet Γ) (pool : Eb_pool_d ω κ L N B J K₀ P G D)
    (range : M.IsRangeOf I U F) (membership : Rd_fun_d .mem B B B V)
    (edges : ∀ u v, Rd_entry_d u v Q ↔ M.mem u D ∧ M.mem v D ∧ Eb_link_d ω κ L B J K₀ U V F G u v) :
    ∃ e, Wc_map_d D Q Γ e ∧
      (∀ u x, Rd_entry_d u x e ↔ M.mem u D ∧ ∃ a f, KPair_d M u a f ∧ Ep_value_d q g a f x) ∧
      ∀ u v x y, Rd_entry_d u x e → Rd_entry_d v y e → (Rd_entry_d u v Q ↔ M.mem x y) := by
  obtain ⟨v, vf, values, reads, covers⟩ := pool.raw_l hZF source owner common hB family system limit
    ff constant fv range membership edges
  obtain ⟨t, tf, ts⟩ := ZF.exists_compositionFunction hZF I (fn0_function_l (ZF.modelsKP hZF) vf) bij.1.1
  have evaluation u x : Rd_entry_d u x t ↔ M.mem u D ∧ ∃ a f, KPair_d M u a f ∧ Ep_value_d q g a f x := by
    refine (ts u x).trans ⟨?_, ?_⟩
    · rintro ⟨hu, E, huE, hEx⟩
      obtain ⟨_, a, f, pair, value⟩ := (values u E).mp huE
      exact ⟨hu, a, f, pair, E, value, hEx⟩
    · rintro ⟨hu, a, f, pair, E, value, hEx⟩
      exact ⟨hu, E, (values u E).mpr ⟨hu, a, f, pair, value⟩, hEx⟩
  have into u x (hux : Rd_entry_d u x t) : M.mem x Γ := by
    obtain ⟨hu, E, huE, hEx⟩ := (ts u x).mp hux
    exact (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hEx hHΓ).mp
      ((covers E).mp ⟨u, hu, huE⟩)
  have onto x (hx : M.mem x Γ) : ∃ u, M.mem u D ∧ Rd_entry_d u x t := by
    obtain ⟨E, _, edge, hEx⟩ := ((wc.2 H Γ hHΓ).2.2 x).mp hx
    obtain ⟨u, hu, huE⟩ := (covers E).mpr edge
    exact ⟨u, hu, (ts u x).mpr ⟨hu, E, huE, hEx⟩⟩
  have member u w x y (hx : Rd_entry_d u x t) (hy : Rd_entry_d w y t) : Rd_entry_d u w Q ↔ M.mem x y := by
    obtain ⟨_, E, huE, hEx⟩ := (ts u x).mp hx
    obtain ⟨_, H, hwH, hHy⟩ := (ts w y).mp hy
    exact (reads u w E H huE hwH).trans
      (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hEx hHy)
  exact ⟨t, ⟨hΓ, (fn0_of_function_l (ZF.modelsKP hZF) tf).retarget_l into, onto,
    fun u _ x _ hux y hy => ⟨fun hyx => (onto y hy).elim fun w hw =>
      ⟨w, hw.1, (member w u y x hw.2 hux).mpr hyx, hw.2⟩,
      fun ⟨w, _, hwu, hwy⟩ => (member w u y x hwy hux).mp hwu⟩⟩, evaluation, member⟩

/-- 同一有界函数族上的所属塌缩恢复任意指定常值像及其完整求值图。 -/
theorem Eb_collapse_d.realize_l
    {ω κ K K₀ L X R N R₀ F J O Z A p T S q C W Y g D₀ a₀ f₀ H Γ β B D Q e : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ N R₀)
    (common : ∀ n D f, M.mem n ω → Ep_space_d κ n D → Fn0_d D β f → (M.mem f X ↔ M.mem f N))
    (hβ : M.mem β X) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (wc : Wc_graph_d C W g) (bij : M.IsSetBijectionFromTo I g C Y)
    (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ β f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (hHΓ : Rd_entry_d H Γ g) (hΓ : M.TransitiveSet Γ) (collapse : Eb_collapse_d ω κ L K₀ N β F D Q B e) :
    B = Γ ∧ ∀ u x, Rd_entry_d u x e ↔ M.mem u D ∧ ∃ a f, KPair_d M u a f ∧ Ep_value_d q g a f x := by
  obtain ⟨J₀, P, G, U, V, pool, indices, _, _, _, _, range, membership, _, edges, map, _⟩ := collapse
  have eq := hZF.1.eq_of_same_members J₀ J (fun a => (indices a).trans (system.indices a).symm)
  subst J₀
  obtain ⟨t, map', evaluation, _⟩ := pool.realize_l hZF source owner common hβ
    family system limit wc bij ff constant fv hHΓ hΓ range membership edges
  exact ⟨map.unique_l hZF map', map.graph_unique_l hZF map' ▸ evaluation⟩

/-- 小节点集在所属源中塌缩，直接回收原施加超幂的临界点像，无需构造所属源的完整超幂。 -/
theorem eb_owned_value_l
    {ω κ K K₀ L X R N R₀ F J O Z A p T S q C W Y g D₀ a₀ f₀ H Γ V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ N R₀)
    (agree : Ea_agree_d ω κ X N) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
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
  have common (n D f : M.Domain) (hn : M.mem n ω) (space : Ep_space_d κ n D)
      (gf : Fn0_d D κ f) : M.mem f X ↔ M.mem f N :=
    ⟨fun hf => agree.subset_l.function_l hZF source owner hn space hf gf,
      fun hf => (show Ea_subset_d ω κ N X from fun n D A hn hd hA => (agree n D A hn hd hA).mpr).function_l
        hZF owner source hn space hf gf⟩
  obtain ⟨e, map, evaluation, member⟩ := pool.realize_l hZF source owner common source.cardinal_mem
    family system limit wc bij ff constant fv hHΓ hΓ range membership edges
  obtain ⟨hΓN, he⟩ := sc_presentation_l hZF owner.omega owner.transitive code owner.theory owner.collapse
    pool.carrier hQ (pool.rank_small_l hZF owner hL hl level hκ hκ) graph hΓ map.function map.onto member
  exact ⟨hΓN, D, Q, e, ⟨J, P, G, U, V₀, pool, system.indices, hU, hV₀, hQ, he, range, membership,
    fun p hp => (graph.1 p hp).elim fun u hu => hu.elim fun v hv =>
      ⟨u, (graph.2 u v ⟨p, hv, hp⟩).1, v, (graph.2 u v ⟨p, hv, hp⟩).2, hv⟩,
    edges, map, member⟩, evaluation⟩

end YesMetaZFC.SetTheory.LargeCardinal
