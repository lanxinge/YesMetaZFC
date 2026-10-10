import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedGraph
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRepresentative
import YesMetaZFC.SetTheory.Collapse.RelationMap

/-! # 有界节点在指定实际超幂中的求值

原商投影与传递坍缩复合，覆盖常值像中的全部成员。该图既满足塌缩递归，
又逐对精确读取节点关系，因此可用于源内呈示和既有求值证书的唯一性比较。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_pool_d.evaluation_l {ω κ K X R L F J O Z A p T S q C W B R' P G D U Q N g D₀ a₀ f₀ H B' : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (pool : Eb_pool_d ω κ L X B J K P G D) (hB : M.mem B X) (range : M.IsRangeOf I U F)
    (relation : ∀ x y, M.mem x B → M.mem y B → (Rd_entry_d x y R' ↔ Rd_entry_d x y R))
    (edges : ∀ u v, Rd_entry_d u v Q ↔ M.mem u D ∧ M.mem v D ∧ Eb_link_d ω κ L B J K U R' F G u v)
    (wc : Wc_graph_d C W g) (bij : M.IsSetBijectionFromTo I g C N)
    (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ B f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (hHB : Rd_entry_d H B' g) (trans : M.TransitiveSet B') : ∃ t, Wc_map_d D Q B' t ∧
      (∀ u x, Rd_entry_d u x t ↔ M.mem u D ∧ ∃ E, Eb_value_d q u E ∧ Rd_entry_d E x g) ∧
      ∀ u v x y, Rd_entry_d u x t → Rd_entry_d v y t → (Rd_entry_d u v Q ↔ M.mem x y) := by
  obtain ⟨v, vf, values, reads, covers⟩ := pool.projection_l hZF source family system limit
    (source.transitive B hB) range relation edges
  obtain ⟨t, tf, ts⟩ := ZF.exists_compositionFunction hZF I (fn0_function_l (ZF.modelsKP hZF) vf) bij.1.1
  obtain ⟨_, n, hn, ha, D₁, hd, ff'⟩ := fv.source_l hZF family system limit
  have eq := ff'.domain_eq_l hZF.1 ff
  subst D₁
  have into u x (hux : Rd_entry_d u x t) : M.mem x B' := by
    obtain ⟨hu, E, huE, hEx⟩ := (ts u x).mp hux
    obtain ⟨m, a, D', f, hm, _, hma, space, _, fn, pair⟩ := pool.read_l hZF source hu
    obtain ⟨_, a', f', pair', ev⟩ := (values u E).mp huE
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair pair'
    exact (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hEx hHB).mp
      (ep_repr_bound_mem_l hZF source family system limit ff constant fv hB hm hma space fn ev)
  have onto x (hx : M.mem x B') : ∃ u, M.mem u D ∧ Rd_entry_d u x t := by
    obtain ⟨E, _, edge, hEx⟩ := ((wc.2 H B' hHB).2.2 x).mp hx
    obtain ⟨m, a, D', f, hm, haJ, hma, space, hf, fn, ev⟩ :=
      ep_repr_bounded_l hZF source family system limit hn ha hd ff constant fv hB edge
    obtain ⟨u, hu, huE⟩ := covers m a D' f E hm haJ hma space hf fn ev
    exact ⟨u, hu, (ts u x).mpr ⟨hu, E, huE, hEx⟩⟩
  have member u v x y (hx : Rd_entry_d u x t) (hy : Rd_entry_d v y t) : Rd_entry_d u v Q ↔ M.mem x y := by
    obtain ⟨_, E, huE, hEx⟩ := (ts u x).mp hx
    obtain ⟨_, H', hvH, hHy⟩ := (ts v y).mp hy
    exact (reads u v E H' huE hvH).trans
      (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hEx hHy)
  refine ⟨t, ⟨trans, (fn0_of_function_l (ZF.modelsKP hZF) tf).retarget_l into, onto, ?_⟩, ?_, member⟩
  · intro u _ x _ hux y hy
    exact ⟨fun hyx => (onto y hy).elim fun v hv => ⟨v, hv.1, (member v u y x hv.2 hux).mpr hyx, hv.2⟩,
      fun ⟨v, _, hvu, hvy⟩ => (member v u y x hvy hux).mp hvu⟩
  · intro u x
    exact (ts u x).trans ⟨fun ⟨hu, E, huE, hEx⟩ => ⟨hu, E, ((values u E).mp huE).2, hEx⟩,
      fun ⟨hu, E, value, hEx⟩ => ⟨hu, E, (values u E).mpr ⟨hu, value⟩, hEx⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
