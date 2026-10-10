import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRelation

/-! # 有界代表关系的源内图与原极限投影

图由已有源内界中的分离构造，投影由原商元素的唯一性构造。
所得关系逐对等于原极限关系的逆像，供枝反射回收同一超幂的下降链。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_pool_d.relation_l {ω κ K X R₀ L B J P G A F R : M.Domain}
    (source : Ep_source_d hZF ω κ K X R₀) (pool : Eb_pool_d ω κ L X B J K P G A)
    (hL : M.mem L X) (hB : M.mem B X) (hF : M.mem F X) (hR : M.mem R X) : ∃ V Q,
      M.mem V X ∧ M.mem Q X ∧ M.IsRangeOf I V F ∧ M.IsSetRelationOn I Q A ∧
      ∀ u v, Rd_entry_d u v Q ↔ M.mem u A ∧ M.mem v A ∧ Eb_link_d ω κ L B J K V R F G u v := by
  obtain ⟨c, code⟩ := source.code
  obtain ⟨V, hV, range⟩ := sc_range_source_l hZF source.omega source.transitive code source.theory hF
  let ρ : Env M 10 := ⟨Fin.cases G (Fin.cases F (Fin.cases R (Fin.cases V (Fin.cases K
    (Fin.cases J (Fin.cases B (Fin.cases L (Fin.cases κ (fun _ => ω))))))))), fun _ => ω⟩
  let φ : BinarySchema 10 := {
    body := eb_link_m (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨Q, hQ, graph, spec⟩ := sc_relation_source_l hZF source.omega source.transitive code source.theory φ (eb_link_delta_l ..) ρ
    (Fin.cases pool.functions (Fin.cases hF (Fin.cases hR (Fin.cases hV (Fin.cases source.finite_mem
      (Fin.cases pool.indices (Fin.cases hB (Fin.cases hL (Fin.cases source.cardinal_mem (fun _ => source.omega_mem)))))))))) pool.carrier pool.carrier
  exact ⟨V, Q, hV, hQ, range, ⟨graph, fun u v h => ⟨((spec u v).mp h).1, ((spec u v).mp h).2.1⟩⟩,
    fun u v => (spec u v).trans (and_congr_right fun _ => and_congr_right fun _ => eb_link_sat_l hZF.1 ..)⟩

def Eb_value_d (q u E : M.Domain) : Prop := ∃ a f, KPair_d M u a f ∧ Ep_repr_d q a f E

def eb_value_m {d} (q u E : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (kpair0_m u.weaken.weaken (.bound 1) .newest) (ep_repr_m q.weaken.weaken (.bound 1) .newest E.weaken.weaken)))
derive_free_closed eb_value_m

theorem eb_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (q u E : Term d) :
    Formula.satisfies ρ (eb_value_m q u E) ↔ Eb_value_d (q.eval ρ) (u.eval ρ) (E.eval ρ) := by
  simp only [eb_value_m, Eb_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, ep_repr_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem eb_projection_l {ω κ K X R₀ R L F J O Z A p T S q C W B D : M.Domain}
    (source : Ep_source_d hZF ω κ K X R₀) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (hB : M.MemberSubset B X) (nodes : ∀ u, M.mem u D → Eb_node_d ω κ L K B J X X u) : ∃ e, Fn0_d D C e ∧
      ∀ u E, Rd_entry_d u E e ↔ M.mem u D ∧ Eb_value_d q u E := by
  let ρ : Env M 1 := ⟨fun _ => q, fun _ => q⟩
  let φ : BinarySchema 1 := { body := eb_value_m (.bound 2) (.bound 1) .newest }
  have sat u E : φ.denote ρ u E ↔ Eb_value_d q u E := eb_value_sat_l hZF.1 ..
  have total u (hu : M.mem u D) : ∃ E, φ.denote ρ u E := by
    obtain ⟨a, ha, f, hf, pair, n, hn, Y, _, hna, space, fn⟩ := nodes u hu
    obtain ⟨E, _, value⟩ := ep_repr_exists_l hZF family system limit ha hna
      ((eb_space_iff_l (ZF.modelsKP hZF) source.finite hn).mp space) hf (fn.mono_target_l hB)
    exact ⟨E, (sat u E).mpr ⟨a, f, pair, value⟩⟩
  have unique u (_ : M.mem u D) E H (he : φ.denote ρ u E) (hh : φ.denote ρ u H) : E = H := by
    obtain ⟨a, f, pair, fv⟩ := (sat u E).mp he
    obtain ⟨b, g, pair', gv⟩ := (sat u H).mp hh
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair pair'
    obtain ⟨_, n, hn, ha, Y, hy, fn⟩ := fv.source_l hZF family system limit
    obtain ⟨U, haU⟩ := family.total n a hn ha
    exact (ep_repr_atoms_l hZF family system limit haU fv gv).1.mpr (rp_eq_refl_l (family.at_l hZF.1 haU ha hy).base fn)
  have bounded u E (_ : M.mem u D) (he : φ.denote ρ u E) : M.mem E C := by
    obtain ⟨_, _, _, v, _, _, _, hvE⟩ := (sat u E).mp he
    exact (limit.projection.bound_l hvE).2
  obtain ⟨e, he, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique bounded
  exact ⟨e, fn0_of_function_l (ZF.modelsKP hZF) he, fun u E => (spec u E).trans (and_congr_right fun _ => sat u E)⟩

/-- 给定实际节点池的投影覆盖全部 B 值代表，并精确读取原极限关系。 -/
theorem Eb_pool_d.projection_l {ω κ K X R₀ R L F J O Z A p T S q C W B R' P G D V Q : M.Domain}
    (source : Ep_source_d hZF ω κ K X R₀) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (pool : Eb_pool_d ω κ L X B J K P G D) (hB : M.MemberSubset B X)
    (range : M.IsRangeOf I V F) (relation : ∀ x y, M.mem x B → M.mem y B → (Rd_entry_d x y R' ↔ Rd_entry_d x y R))
    (edges : ∀ u v, Rd_entry_d u v Q ↔ M.mem u D ∧ M.mem v D ∧ Eb_link_d ω κ L B J K V R' F G u v) :
    ∃ e, Fn0_d D C e ∧ (∀ u E, Rd_entry_d u E e ↔ M.mem u D ∧ Eb_value_d q u E) ∧
      (∀ u v E H, Rd_entry_d u E e → Rd_entry_d v H e → (Rd_entry_d u v Q ↔ Rd_entry_d E H W)) ∧
      ∀ n a Y f E, M.mem n ω → M.mem a J → Fn0_d n L a → Ep_space_d κ n Y → M.mem f X → Fn0_d Y B f →
        Ep_repr_d q a f E → ∃ u, M.mem u D ∧ Rd_entry_d u E e := by
  obtain ⟨e, he, values⟩ := eb_projection_l hZF source family system limit hB (fun u hu => by
    obtain ⟨n, a, D', f, hn, ha, fn, space, hf, ff, pair⟩ := pool.read_l hZF source hu
    exact ⟨a, ha, f, hf, pair, n, hn, D', source.space_mem_l hZF hn space, fn,
      (eb_space_iff_l (ZF.modelsKP hZF) source.finite hn).mpr space, ff⟩)
  refine ⟨e, he, values, ?_, ?_⟩
  · intro u v E H hu hv
    obtain ⟨hud, a', f', up', fv⟩ := (values u E).mp hu
    obtain ⟨hvd, b', g', vp', gv⟩ := (values v H).mp hv
    obtain ⟨a, ha, f, hf, up, _, _, Y, _, _, _, ff⟩ := (pool.nodes u).mp hud
    obtain ⟨b, hb, g, hg, vp, _, _, Y', _, _, _, gg⟩ := (pool.nodes v).mp hvd
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M up up'
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M vp vp'
    have link : Eb_link_d ω κ L B J K V R' F G u v ↔ Eb_edge_d ω κ L B J K V R' F a f b g := by
      refine ⟨?_, fun h => ⟨a, ha, f, hf, b, hb, g, hg, up, vp, h⟩⟩
      rintro ⟨a', _, f', _, b', _, g', _, up', vp', h⟩
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M up up'
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M vp vp'
      exact h
    exact (edges u v).trans ((Iff.intro (And.right ∘ And.right) (fun h => ⟨hud, hvd, h⟩)).trans
      (link.trans (eb_edge_iff_l hZF source family system limit hB
        (fun a U h => (range U).mpr ⟨a, h⟩) relation ff gg fv gv)))
  · intro n a Y f E hn ha hna space hf fn value
    obtain ⟨u, hu⟩ := (I).total a f
    have hd := pool.node_l hZF source hn ha hna space hf fn hu
    exact ⟨u, hd, (values u E).mpr ⟨hd, a, f, hu, value⟩⟩

/-- 分离构造源内有界代表图，再使用它在同一极限中的原投影。 -/
theorem eb_graph_l {ω κ K X R₀ R L F J O Z A p T S q C W B R' : M.Domain}
    (source : Ep_source_d hZF ω κ K X R₀) (power : Sc_power_d X) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (hL : M.mem L X) (hF : M.mem F X) (hB : M.mem B X) (hR : M.mem R' X)
    (relation : ∀ x y, M.mem x B → M.mem y B → (Rd_entry_d x y R' ↔ Rd_entry_d x y R)) :
    ∃ P G D V Q e, Eb_pool_d ω κ L X B J K P G D ∧ M.mem V X ∧ M.mem Q X ∧ M.IsRangeOf I V F ∧
      M.IsSetRelationOn I Q D ∧ Fn0_d D C e ∧ (∀ u E, Rd_entry_d u E e ↔ M.mem u D ∧ Eb_value_d q u E) ∧
      (∀ u v, Rd_entry_d u v Q ↔ M.mem u D ∧ M.mem v D ∧ Eb_link_d ω κ L B J K V R' F G u v) ∧
      (∀ u v E H, Rd_entry_d u E e → Rd_entry_d v H e → (Rd_entry_d u v Q ↔ Rd_entry_d E H W)) ∧
      ∀ n a Y f E, M.mem n ω → M.mem a J → Fn0_d n L a → Ep_space_d κ n Y → M.mem f X → Fn0_d Y B f →
        Ep_repr_d q a f E → ∃ u, M.mem u D ∧ Rd_entry_d u E e := by
  obtain ⟨P, G, D, pool⟩ := eb_pool_l hZF source power hL hB system.indices
  obtain ⟨V, Q, hV, hQ, range, graph, edges⟩ := pool.relation_l hZF source hL hB hF hR
  obtain ⟨e, he, values, reads, covers⟩ := pool.projection_l hZF source family system limit (source.transitive B hB) range relation edges
  exact ⟨P, G, D, V, Q, e, pool, hV, hQ, range, graph, he, values, edges, reads, covers⟩

end YesMetaZFC.SetTheory.LargeCardinal
