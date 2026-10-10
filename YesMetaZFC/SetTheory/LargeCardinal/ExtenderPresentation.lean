import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedGraph
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderProductIndex
import YesMetaZFC.Model.SetTheory.Internal.SourcePresentation

/-! # 可数源的完整超幂在包含源中的实际呈示

全部节点为有限支撑与原源函数的配对，关系由同一扩展器的测度一约束给出。
节点集在包含源内可数；原商投影及塌缩给出满射呈示，源内塌缩与唯一性
遂回收原超幂本身及其可数编号。无需假设商集或原求值图已经属于包含源。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_countable_ultra_l {ω κ K X R μ K' Z R' L F ι η J O V A p T S q C W P g : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (store : Ep_source_d hZF ω μ K' Z R')
    (hX : M.mem X Z) (hL : M.mem L Z) (hF : M.mem F Z) (hι : M.mem ι Z) (hη : M.mem η Z)
    (ix : M.IsSetInjectionFromTo I ι X ω) (il : M.IsSetInjectionFromTo I η L ω)
    (family : Em_source_d ω κ L X F) (system : Ep_system_d I ω κ L X R F J O V A p T S)
    (limit : Di_limit_d A p T S q C W)
    (wc : Wc_graph_d C W g) (bij : M.IsSetBijectionFromTo I g C P) :
    M.mem P Z ∧ ∃ ξ, M.mem ξ Z ∧ M.IsSetInjectionFromTo I ξ P ω := by
  have hP : M.TransitiveSet P := by
    intro x hx y hy
    obtain ⟨E, _, hEx⟩ := bij.2 x hx
    obtain ⟨H, _, _, hHy⟩ := ((wc.2 E x hEx).2.2 y).mp hy
    exact bij.1.1.output_mem_of_pairMember hHy
  obtain ⟨b, model⟩ := store.code
  obtain ⟨c, original⟩ := source.code
  have hκ := store.transitive X hX κ source.cardinal_mem
  have hK := store.transitive X hX K source.finite_mem
  have hR := store.membership_relation_l hZF hX original
  have hJ := ep_indices_mem_l hZF store hL system.indices
  obtain ⟨H, hH, seq⟩ := store.sequences.space L hL
  have js a (ha : M.mem a J) : M.mem a H := by
    obtain ⟨n, hn, fn, _⟩ := (system.indices a).mp ha
    exact (seq a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) fn⟩
  obtain ⟨U, hU, product⟩ := store.theory.algebra.product H X hH hX
  -- 有界分离选出所有且仅有的原源代表，有限定义域仍取原源中的同一集合。
  let ρ : Env M 6 := ⟨Fin.cases X (Fin.cases J (Fin.cases K (Fin.cases L (Fin.cases κ (fun _ => ω))))), fun _ => ω⟩
  let φ : UnarySchema 6 := {
    body := eb_node_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 2) (.bound 1) (.bound 1) .newest }
  obtain ⟨D, hD, ds⟩ := sc_separate_source_l I hZF store.omega store.transitive model store.theory φ
    (eb_node_delta_l ..) ρ (Fin.cases hX (Fin.cases hJ (Fin.cases hK (Fin.cases hL (Fin.cases hκ (fun _ => store.omega_mem)))))) hU
  have nodes u : M.mem u D ↔ Eb_node_d ω κ L K X J X X u := (ds u).trans
    ((and_congr_right fun _ => eb_node_sat_l hZF.1 ..).trans ⟨And.right, fun h => ⟨by
      obtain ⟨a, ha, f, hf, pair, _⟩ := h
      exact (product u).mpr ⟨a, js a ha, f, hf, pair⟩, h⟩⟩)
  obtain ⟨B, hB, range⟩ := sc_range_source_l hZF store.omega store.transitive model store.theory hF
  let θ : Env M 10 := ⟨Fin.cases X (Fin.cases F (Fin.cases R (Fin.cases B (Fin.cases K
    (Fin.cases J (Fin.cases X (Fin.cases L (Fin.cases κ (fun _ => ω))))))))), fun _ => ω⟩
  let ψ : BinarySchema 10 := {
    body := eb_link_m (.bound 11) (.bound 10) (.bound 9) (.bound 8)
      (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨Q, hQ, qr, qs⟩ := sc_relation_source_l hZF store.omega store.transitive model store.theory ψ
    (eb_link_delta_l ..) θ (Fin.cases hX (Fin.cases hF (Fin.cases hR (Fin.cases hB (Fin.cases hK
      (Fin.cases hJ (Fin.cases hX (Fin.cases hL (Fin.cases hκ (fun _ => store.omega_mem)))))))))) hD hD
  have edges u v : Rd_entry_d u v Q ↔ M.mem u D ∧ M.mem v D ∧ Eb_link_d ω κ L X J K B R F X u v :=
    (qs u v).trans (and_congr_right fun _ => and_congr_right fun _ => eb_link_sat_l hZF.1 ..)
  obtain ⟨v, vf, values⟩ := eb_projection_l hZF source family system limit (fun _ h => h) (fun u hu => (nodes u).mp hu)
  obtain ⟨e, ef, es⟩ := ZF.exists_compositionFunction hZF I (fn0_function_l (ZF.modelsKP hZF) vf) bij.1.1
  have onto x (hx : M.mem x P) : ∃ u, M.mem u D ∧ Rd_entry_d u x e := by
    obtain ⟨E, hE, hEx⟩ := bij.2 x hx
    obtain ⟨n, a, Y, f, hn, ha, fn, space, hf, ff, value⟩ := ep_repr_surjective_l hZF family system limit hE
    obtain ⟨u, pair⟩ := (I).total a f
    have hu := (nodes u).mpr ⟨a, ha, f, hf, pair, n, hn, Y, source.space_mem_l hZF hn space, fn,
      (eb_space_iff_l (ZF.modelsKP hZF) source.finite hn).mpr space, ff⟩
    exact ⟨u, hu, (es u x).mpr ⟨hu, E, (values u E).mpr ⟨hu, a, f, pair, value⟩, hEx⟩⟩
  have member u v x y (hx : Rd_entry_d u x e) (hy : Rd_entry_d v y e) : Rd_entry_d u v Q ↔ M.mem x y := by
    obtain ⟨hu, E, huE, hEx⟩ := (es u x).mp hx
    obtain ⟨hv, H, hvH, hHy⟩ := (es v y).mp hy
    obtain ⟨_, a, f, up, fv⟩ := (values u E).mp huE
    obtain ⟨_, a', f', vp, gv⟩ := (values v H).mp hvH
    obtain ⟨a₀, ha, f₀, hf, up', _, _, Y, _, _, _, ff⟩ := (nodes u).mp hu
    obtain ⟨a₁, ha', f₁, hf', vp', _, _, Y', _, _, _, gg⟩ := (nodes v).mp hv
    obtain ⟨ea, ef⟩ := kpair_injective_l M up' up
    obtain ⟨eb, eg⟩ := kpair_injective_l M vp' vp
    subst a₀ f₀ a₁ f₁
    have link : Eb_link_d ω κ L X J K B R F X u v ↔ Eb_edge_d ω κ L X J K B R F a f a' f' := by
      refine ⟨?_, fun h => ⟨a, ha, f, hf, a', ha', f', hf', up, vp, h⟩⟩
      rintro ⟨a₀, _, f₀, _, a₁, _, f₁, _, up', vp', h⟩
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M up' up
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M vp' vp
      exact h
    exact (edges u v).trans ((Iff.intro (And.right ∘ And.right) (fun h => ⟨hu, hv, h⟩)).trans
      (link.trans ((eb_edge_iff_l hZF source family system limit (fun _ h => h)
        (fun a U h => (range U).mpr ⟨a, h⟩) (fun _ _ _ _ => Iff.rfl) ff gg fv gv).trans
          (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hEx hHy))))
  -- 支撑列与原函数集都已有 ω 编号；同一编号限制到节点，再传给实际满射像。
  obtain ⟨K₀, small⟩ := store.rebase_l hZF store.omega_mem (fun _ h => h) (store.cardinal_small.mono_l store.below)
  obtain ⟨t, ht, ti⟩ := store.sequences.index L H ω η hL hH store.omega_mem hη seq (fun _ h => h)
    (Sc_index_d.of_injection_l (ZF.modelsKP hZF) (store.omega.isOrdinal hZF) il)
  obtain ⟨r, hr, ri⟩ := ep_product_index_l hZF small hH hX hU product ht hι ti
    (Sc_index_d.of_injection_l (ZF.modelsKP hZF) (store.omega.isOrdinal hZF) ix)
  have idx := Sc_index_d.of_injection_l (ZF.modelsKP hZF) (store.omega.isOrdinal hZF) ri
  have di := idx.mono_l (fun u hu => ((ds u).mp hu).1)
  obtain ⟨hp, he⟩ := sc_presentation_l hZF store.omega store.transitive model store.theory store.collapse hD hQ
    ⟨ω, r, store.omega_mem, hr, di⟩ ⟨qr, fun u v h => ⟨((edges u v).mp h).1, ((edges u v).mp h).2.1⟩⟩
    hP (fn0_of_function_l (ZF.modelsKP hZF) ef) onto member
  obtain ⟨ξ, hξ, xi⟩ := sc_index_image_l hZF store.omega store.transitive model store.theory hD hp he store.omega_mem hr di
    (fn0_of_function_l (ZF.modelsKP hZF) ef) onto
  exact ⟨hp, xi.restrict_l hZF store.omega store.transitive model store.theory hp store.omega_mem hξ⟩

end YesMetaZFC.SetTheory.LargeCardinal
