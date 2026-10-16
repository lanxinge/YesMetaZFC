import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedGraph
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRepresentative

/-! # 共同有界代表池到未坍塌商的满呈示

所属源和施加源在同一个有界函数族上一致时，原代表池恰好覆盖 B 的常值像
的全部成员，且完整反映原商关系。此处没有整体坍塌图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_pool_d.raw_l {ω κ K K₀ L X R N R₀ F J O Z A p T S q C W D₀ a₀ f₀ H B D Q P G U V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (owner : Ep_source_d hZF ω κ K₀ N R₀)
    (common : ∀ n D f, M.mem n ω → Ep_space_d κ n D → Fn0_d D B f → (M.mem f X ↔ M.mem f N))
    (hB : M.mem B X) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ B f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (pool : Eb_pool_d ω κ L N B J K₀ P G D) (range : M.IsRangeOf I U F)
    (membership : Rd_fun_d .mem B B B V)
    (edges : ∀ u v, Rd_entry_d u v Q ↔ M.mem u D ∧ M.mem v D ∧ Eb_link_d ω κ L B J K₀ U V F G u v) :
    ∃ v, Fn0_d D C v ∧
      (∀ u E, Rd_entry_d u E v ↔ M.mem u D ∧ Eb_value_d q u E) ∧
      (∀ u w E H, Rd_entry_d u E v → Rd_entry_d w H v → (Rd_entry_d u w Q ↔ Rd_entry_d E H W)) ∧
      ∀ E, (∃ u, M.mem u D ∧ Rd_entry_d u E v) ↔ Rd_entry_d E H W := by
  have eq := hZF.1.eq_of_same_members K₀ K (fun f => (owner.finite f).trans (source.finite f).symm)
  subst K₀
  obtain ⟨v, vf, values⟩ := eb_projection_l hZF source family system limit (source.transitive B hB) (fun u hu => by
    obtain ⟨n, a, D', f, hn, ha, fn, space, hf, gf, pair⟩ := pool.read_l hZF owner hu
    exact ⟨a, ha, f, (common n D' f hn space gf).mpr hf, pair,
      n, hn, D', source.space_mem_l hZF hn space, fn,
      (eb_space_iff_l (ZF.modelsKP hZF) source.finite hn).mpr space, gf⟩)
  have relation x y (hx : M.mem x B) (hy : M.mem y B) : Rd_entry_d x y V ↔ Rd_entry_d x y R := by
    obtain ⟨c, code⟩ := source.code
    exact (rt_mem_graph_l (ZF.modelsKP hZF) membership x y).trans
      ⟨fun h => (code.2 x y).mpr ⟨source.transitive B hB x h.1, source.transitive B hB y h.2.1, h.2.2⟩,
        fun h => ⟨hx, hy, ((code.2 x y).mp h).2.2⟩⟩
  have reads u w E H (hu : Rd_entry_d u E v) (hw : Rd_entry_d w H v) : Rd_entry_d u w Q ↔ Rd_entry_d E H W := by
    obtain ⟨hud, a', f', up', fv⟩ := (values u E).mp hu
    obtain ⟨hwd, b', g', wp', gv⟩ := (values w H).mp hw
    obtain ⟨a, ha, f, hf, up, _, _, Y, _, _, _, ff⟩ := (pool.nodes u).mp hud
    obtain ⟨b, hb, g, hg, wp, _, _, Y', _, _, _, gg⟩ := (pool.nodes w).mp hwd
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M up up'
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M wp wp'
    have link : Eb_link_d ω κ L B J K U V F G u w ↔ Eb_edge_d ω κ L B J K U V F a f b g := by
      refine ⟨?_, fun h => ⟨a, ha, f, hf, b, hb, g, hg, up, wp, h⟩⟩
      rintro ⟨a', _, f', _, b', _, g', _, up', wp', h⟩
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M up up'
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M wp wp'
      exact h
    exact (edges u w).trans ((Iff.intro (And.right ∘ And.right) (fun h => ⟨hud, hwd, h⟩)).trans
      (link.trans (eb_edge_iff_l hZF source family system limit (source.transitive B hB)
        (fun a U h => (range U).mpr ⟨a, h⟩) relation ff gg fv gv)))
  refine ⟨v, vf, values, reads, fun E => ⟨?_, ?_⟩⟩
  · rintro ⟨u, hu, huE⟩
    obtain ⟨n, a, D', f, hn, _, ha, space, _, gf, pair⟩ := pool.read_l hZF owner hu
    obtain ⟨_, a', f', pair', value⟩ := (values u E).mp huE
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair' pair
    exact ep_repr_bound_mem_l hZF source family system limit ff constant fv hB hn ha space gf value
  · intro edge
    obtain ⟨_, n₀, hn₀, ha₀, D₁, space₀, ff₀⟩ := fv.source_l hZF family system limit
    have eq := ff₀.domain_eq_l hZF.1 ff
    subst D₁
    obtain ⟨n, a, D', f, hn, haJ, ha, space, hf, gf, value⟩ :=
      ep_repr_bounded_l hZF source family system limit hn₀ ha₀ space₀ ff constant fv hB edge
    obtain ⟨u, pair⟩ := (I).total a f
    have hu := pool.node_l hZF owner hn haJ ha space ((common n D' f hn space gf).mp hf) gf pair
    exact ⟨u, hu, (values u E).mpr ⟨hu, a, f, pair, value⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
