import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.RelativeRankSegment
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.EmbeddingCountableBound
import YesMetaZFC.SetTheory.LargeCardinal.Extender.BoundedGraph
import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.Model.SetTheory.Source.Presentation
import YesMetaZFC.SetTheory.LargeCardinal.Extender.CopySeed
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SuccessorApplication
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceNode
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RankLift
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SourceSubsets
import YesMetaZFC.SetTheory.LargeCardinal.Extender.CopyBounded
import YesMetaZFC.SetTheory.LargeCardinal.Extender.CopySubsets
import YesMetaZFC.Model.SetTheory.Embedding.RankFixed
import YesMetaZFC.Model.SetTheory.Source.RankSizeInitial

/-! # 复制的序数限制在目标内还原为完整小域限制

所属模型内的旧图 σ 在 κ 以下有共同小界时，先分离 σ↾κ，再由已证明的
有限幂一致性搬运此图。复制在支撑上等于 σ，故该图正是新复制的限制。
随后关系回拉与塌缩自动恢复整个小传递域上的复制图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_copy_restriction_l {ω κ K X R μ K₀ Z V K' Y S c d j σ U ζ B f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K₀ Z V)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' Y S) (subsets : Ea_subset_d ω μ Z Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hU : M.TransitiveSet U) (hσ : Fn0_d U Z σ) (hσZ : M.mem σ Z) (hκσ : Rd_entry_d κ ζ σ)
    (bounded : ∀ a b, M.mem a κ → Rd_entry_d a b σ → M.mem a μ ∧ M.mem b μ)
    (fixed : ∀ a b, M.mem a κ → Rd_entry_d a b σ → Rd_entry_d a b j)
    (hB : M.TransitiveSet B) (hf : M.mem f X) (bij : M.IsSetBijectionFromTo I f κ B) :
    M.mem B Y ∧ ∃ k, M.mem k Y ∧ M.IsRestrictionOf I k j B := by
  have κZ := (rd_entry_transitive_l owner.transitive hσZ hκσ).1
  obtain ⟨b, code⟩ := owner.code
  let ρ : Env M 2 := ⟨Fin.cases κ (fun _ => μ), fun _ => κ⟩
  let φ : UnarySchema 2 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)) }
  have sat q : φ.denote ρ q ↔ ∃ a, M.mem a κ ∧ ∃ v, M.mem v μ ∧ KPair_d M q a v := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  obtain ⟨p, hpZ, spec⟩ := sc_separate_source_l I hZF source.omega owner.transitive code owner.theory φ
    (.existsMem _ (.existsMem _ (kpair0_delta_l ..))) ρ (Fin.cases κZ (fun _ => owner.cardinal_mem)) hσZ
  have shape q (hq : M.mem q p) : ∃ a, M.mem a κ ∧ ∃ v, M.mem v μ ∧ KPair_d M q a v :=
    (sat q).mp ((spec q).mp hq).2
  have entry a v : Rd_entry_d a v p ↔ M.mem a κ ∧ Rd_entry_d a v σ := by
    constructor
    · rintro ⟨q, hq, hqp⟩
      obtain ⟨a', ha', v', _, hq'⟩ := shape q hqp
      obtain ⟨ea, _⟩ := kpair_injective_l M hq' hq
      exact ⟨ea ▸ ha', q, hq, ((spec q).mp hqp).1⟩
    · rintro ⟨ha, q, hq, hqσ⟩
      exact ⟨q, hq, (spec q).mpr ⟨hqσ, (sat q).mpr ⟨a, ha, v, (bounded a v ha ⟨q, hq, hqσ⟩).2, hq⟩⟩⟩
  have hpY := subsets.relation_l hZF owner target hpZ (fun q hq => by
    obtain ⟨a, ha, v, hv, hq'⟩ := shape q hq
    exact ⟨a, (bounded a v ha ((entry a v).mp ⟨q, hq', hq⟩).2).1, v, hv, hq'⟩)
  have res : M.IsRestrictionOf I p j κ := by
    refine ⟨fun q hq => (shape q hq).elim fun a ha => ha.2.elim fun v hv => ⟨a, v, hv.2⟩, fun a v => ⟨?_, ?_⟩⟩
    · intro hav
      obtain ⟨ha, hav⟩ := (entry a v).mp hav
      exact ⟨ha, fixed a v ha hav⟩
    · rintro ⟨ha, hav⟩
      obtain ⟨w, _, haw⟩ := hσ.2.1 a (hU κ (hσ.bound_l hκσ).1 a ha)
      exact (entry a v).mpr ⟨ha, hj.1.1.1.2 a w v (fixed a w ha haw) hav ▸ haw⟩
  exact smap_small_restriction_l hZF source target hm hn hj hpY res hB hf bij

/-- 模型内可数性实际产生小界，故只要求 φ 以下逐层一致，无需 φ 上的全部子集一致。 -/
theorem ep_copy_countable_restriction_l
    {ω κ K X R φ K₀ Z V K' Y S c d j σ U R₀ c₀ d₀ ι B f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω φ K₀ Z V)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω φ K' Y S) (subsets : ∀ μ, M.mem μ φ → Ea_subset_d ω μ Z Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hU : M.TransitiveSet U) (h₀ : Smem_d I c₀ U R₀) (h₁ : Smem_d I d₀ Z V)
    (hσ : Smap_d I ω c₀ d₀ U Z σ) (hσZ : M.mem σ Z) (hιZ : M.mem ι Z)
    (countable : M.IsSetInjectionFromTo I ι σ ω) (hκ : M.IsOrdinal κ) (hκφ : Rd_entry_d κ φ σ)
    (regular : Sc_omega_bound_d ω Z φ)
    (fixed : ∀ a b, M.mem a κ → Rd_entry_d a b σ → Rd_entry_d a b j)
    (hB : M.TransitiveSet B) (hf : M.mem f X) (bij : M.IsSetBijectionFromTo I f κ B) :
    M.mem B Y ∧ ∃ k, M.mem k Y ∧ M.IsRestrictionOf I k j B := by
  obtain ⟨μ, hμ, bounded⟩ := smap_countable_bound_l hZF owner hU h₀ h₁ hσ hσZ hιZ countable hκ hκφ regular
  have hωμ : M.MemberSubset ω μ := by
    intro i hi
    have hiκ := source.below i hi
    obtain ⟨v, _, hiv⟩ := hσ.1.1.2.2 i (hU κ (hσ.1.1.input_mem_of_pairMember hκφ) i hiκ)
    exact (bounded i v hiκ hiv).1
  have hφ := hσ.ordinal_l hZF source.omega hU owner.transitive h₀ h₁ hκφ hκ
  obtain ⟨K₁, owner'⟩ := owner.rebase_l (owner.transitive φ owner.cardinal_mem μ hμ) hωμ (owner.cardinal_small.mono_mem_l I h₁ (owner.transitive φ owner.cardinal_mem μ hμ) (hφ.transitive μ hμ))
  obtain ⟨K₂, target'⟩ := target.rebase_l (target.transitive φ target.cardinal_mem μ hμ) hωμ (target.cardinal_small.mono_mem_l I hn (target.transitive φ target.cardinal_mem μ hμ) (hφ.transitive μ hμ))
  exact ep_copy_restriction_l hZF source owner' target' (subsets μ hμ) hm hn hj hU
    (fn0_of_function_l (ZF.modelsKP hZF) hσ.1.1) hσZ hκφ bounded fixed hB hf bij

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 可数源的完整超幂在包含源中的实际呈示

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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (store : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' Z R')
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
  have hK := store.transitive X hX K source.finite.mem_l
  have hR := store.membership_relation_l hZF hX original
  have hJ := ep_indices_mem_l hZF store hL system.indices
  obtain ⟨H, hH, seq⟩ := (store.sequences_l (ZF.modelsKP hZF)).1 L hL
  have js a (ha : M.mem a J) : M.mem a H := by
    obtain ⟨n, hn, fn, _⟩ := (system.indices a).mp ha
    exact (seq a).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) fn⟩
  obtain ⟨U, hU, product⟩ := (store.algebra_l (ZF.modelsKP hZF)).product H X hH hX
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
      (eb_space_iff_l (ZF.modelsKP hZF) (source.finite_l (ZF.modelsKP hZF)) hn).mpr space, ff⟩
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
  obtain ⟨K₀, small⟩ := store.rebase_l store.omega_mem (fun _ h => h) (store.cardinal_small.mono_mem_l I model store.omega_mem store.below)
  obtain ⟨t, ht, ti⟩ := (store.sequences_l (ZF.modelsKP hZF)).2 L H ω η hL hH store.omega_mem hη seq (fun _ h => h)
    (Sc_index_d.of_injection_l (ZF.modelsKP hZF) (store.omega.isOrdinal (ZF.modelsKP hZF)) il)
  obtain ⟨r, hr, ri⟩ := ep_product_index_l hZF small hH hX hU product ht hι ti
    (Sc_index_d.of_injection_l (ZF.modelsKP hZF) (store.omega.isOrdinal (ZF.modelsKP hZF)) ix)
  have idx := Sc_index_d.of_injection_l (ZF.modelsKP hZF) (store.omega.isOrdinal (ZF.modelsKP hZF)) ri
  have di := idx.mono_l (fun u hu => ((ds u).mp hu).1)
  obtain ⟨hp, he⟩ := sc_presentation_l hZF store.omega store.transitive model store.theory store.collapse hD hQ
    ⟨ω, r, store.omega_mem, hr, di⟩ ⟨qr, fun u v h => ⟨((edges u v).mp h).1, ((edges u v).mp h).2.1⟩⟩
    hP (fn0_of_function_l (ZF.modelsKP hZF) ef) onto member
  obtain ⟨ξ, hξ, xi⟩ := sc_index_image_l hZF store.omega store.transitive model store.theory hD hp he store.omega_mem hr di
    (fn0_of_function_l (ZF.modelsKP hZF) ef) onto
  exact ⟨hp, xi.restrict_l hZF store.omega store.transitive model store.theory hp store.omega_mem hξ⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从有限幂子集的一致性恢复整个小传递集合上的映射

实际枚举把隶属关系编码在 κ² 上。两图搬运同一关系码，Mostowski 唯一性
识别集合的像及枚举图的像；在 κ 上逐点相同便推出整个传递集合上相同。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ea_maps_d.relation_l {ω κ κ' K K₀ X R Y S N R₀ N' R₁ c d b b' π σ T T' : M.Domain}
    (maps : Ea_maps_d ω κ X π σ) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ N R₀) (hY : M.TransitiveSet Y) (hN' : M.TransitiveSet N')
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁) (hσ : Smap_d I ω b b' N N' σ)
    (hκπ : Rd_entry_d κ κ' π) (hκσ : Rd_entry_d κ κ' σ) (hT : M.mem T X)
    (bound : ∀ p, M.mem p T → ∃ a, M.mem a κ ∧ ∃ b, M.mem b κ ∧ KPair_d M p a b)
    (hTT : Rd_entry_d T T' π) : Rd_entry_d T T' σ := by
  have sub : Ea_subset_d ω κ X N := by
    intro n D A hn hd bound hA
    obtain ⟨A', _, hAA⟩ := hπ.1.1.2.2 A hA
    exact hσ.1.1.input_mem_of_pairMember (maps n D A A' hn hd hA bound hAA)
  obtain ⟨T'', _, hTT'⟩ := hσ.1.1.2.2 T (sub.relation_l hZF source owner hT bound)
  obtain ⟨n, z, o, D, C, hnω, hzω, hoω, hd, hC, hs, code⟩ := ep_relation_code_l hZF source hT
  obtain ⟨C', _, hCC⟩ := hπ.1.1.2.2 C hC
  have hCσ := maps n D C C' hnω hd hC hs hCC
  have natπ := hπ.natural_l hZF source.omega source.transitive hY hm hn source.omega_mem
  have natσ := hσ.natural_l hZF source.omega owner.transitive hN' h₀ h₁ owner.omega_mem
  let φ : Formula 1 5 := .conj
    (Formula.forallMem .newest (Formula.existsMem (.bound 3)
      (Formula.existsMem (.bound 4) (kpair0_m (.bound 2) (.bound 1) .newest))))
    (Formula.forallMem (.bound 2) (Formula.forallMem (.bound 3)
      (.iff (rd_entry0_m (.bound 1) .newest (.bound 2)) (Formula.existsMem (.bound 3)
        (.conj (rd_entry0_m (.bound 6) (.bound 2) .newest) (rd_entry0_m (.bound 7) (.bound 1) .newest))))))
  have closed : φ.FreeClosed := by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]
  have delta : φ.IsDelta0 := .conj (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..) (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))
  let ρ : Env M 5 := ⟨Fin.cases T (Fin.cases C (Fin.cases κ (Fin.cases z (fun _ => o)))), fun _ => o⟩
  have tr := smap_delta_l I hZF source.omega source.transitive hY hm hn hπ φ closed delta ρ
    ⟨Fin.cases T' (Fin.cases C' (Fin.cases κ' (Fin.cases z (fun _ => o)))), fun _ => o⟩
    (Fin.cases hTT (Fin.cases hCC (Fin.cases hκπ (Fin.cases (natπ z hzω) (fun _ => natπ o hoω)))))
  have tr' := smap_delta_l I hZF source.omega owner.transitive hN' h₀ h₁ hσ φ closed delta ρ
    ⟨Fin.cases T'' (Fin.cases C' (Fin.cases κ' (Fin.cases z (fun _ => o)))), fun _ => o⟩
    (Fin.cases hTT' (Fin.cases hCσ (Fin.cases hκσ (Fin.cases (natσ z hzω) (fun _ => natσ o hoω)))))
  simp only [φ, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_iff_iff, kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1] at tr tr'
  obtain ⟨shape, read⟩ := tr.mp ⟨bound, fun a ha b hb => code a b ha hb⟩
  obtain ⟨shape', read'⟩ := tr'.mp ⟨bound, fun a ha b hb => code a b ha hb⟩
  have same a ha b hb := (read a ha b hb).trans (read' a ha b hb).symm
  have eq : T' = T'' := hZF.1.eq_of_same_members T' T'' (fun p => ⟨fun hp => by
    obtain ⟨a, ha, b, hb, pair⟩ := shape p hp
    obtain ⟨q, qp, hq⟩ := (same a ha b hb).mp ⟨p, pair, hp⟩
    have eq : q = p := kpair_unique_l M hZF.1 qp pair
    exact eq ▸ hq, fun hp => by
    obtain ⟨a, ha, b, hb, pair⟩ := shape' p hp
    obtain ⟨q, qp, hq⟩ := (same a ha b hb).mpr ⟨p, pair, hp⟩
    have eq : q = p := kpair_unique_l M hZF.1 qp pair
    exact eq ▸ hq⟩)
  exact eq.symm ▸ hTT'

/-- 源内已有枚举自动给出共同塌缩和整个传递集合上的逐点一致性。 -/
theorem Ea_maps_d.transitive_l {ω κ κ' K K₀ X R Y S N R₀ N' R₁ c d b b' π σ B F : M.Domain}
    (maps : Ea_maps_d ω κ X π σ) (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ N R₀) (hY : M.TransitiveSet Y) (hN' : M.TransitiveSet N')
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁) (hσ : Smap_d I ω b b' N N' σ)
    (hκπ : Rd_entry_d κ κ' π) (hκσ : Rd_entry_d κ κ' σ)
    (fixed : ∀ a a', M.mem a κ → Rd_entry_d a a' σ → Rd_entry_d a a' π)
    (hB : M.TransitiveSet B) (hF : M.mem F X) (bij : M.IsSetBijectionFromTo I F κ B) :
    M.mem B N ∧ M.mem F N ∧ (∀ B', Rd_entry_d B B' π → Rd_entry_d B B' σ) ∧
      ∀ x x', M.mem x B → (Rd_entry_d x x' π ↔ Rd_entry_d x x' σ) := by
  obtain ⟨T, hT, bound, iso⟩ := ep_transitive_code_l hZF source hB hF bij
  obtain ⟨T', _, hTT⟩ := hπ.1.1.2.2 T hT
  have hTσ := maps.relation_l hZF source owner hY hN' hm hn hπ h₀ h₁ hσ hκπ hκσ hT bound hTT
  obtain ⟨B₀, F₀, hB₀, hF₀, iso₀⟩ := owner.collapse.collapse_l I (ZF.modelsKP hZF) owner.transitive h₀ owner.cardinal_mem
    (hσ.1.1.input_mem_of_pairMember hTσ) (owner.cardinal_small_l (ZF.modelsKP hZF)) (iso.well_founded_l (ZF.modelsKP hZF)) (iso.extensional_l hZF.1)
  have eq := iso₀.unique_l hZF iso
  subst B₀
  have eq := iso₀.graph_unique_l hZF iso
  subst F₀
  obtain ⟨B₀, hBX, range⟩ := sc_range_source_l hZF source.omega source.transitive hm source.theory hF
  have eq := hZF.1.eq_of_same_members B₀ B fun x => (range x).trans
    ⟨fun ⟨_, h⟩ => bij.1.1.output_mem_of_pairMember h, fun hx => (bij.2 x hx).imp fun _ h => h.2⟩
  subst B₀
  obtain ⟨B', _, hBB⟩ := hπ.1.1.2.2 B hBX
  obtain ⟨F', _, hFF⟩ := hπ.1.1.2.2 F hF
  obtain ⟨B'', _, hBσ⟩ := hσ.1.1.2.2 B hB₀
  obtain ⟨F'', _, hFσ⟩ := hσ.1.1.2.2 F hF₀
  let φ : Formula 1 4 := wc_iso_m (.bound 3) (.bound 2) (.bound 1) .newest
  let ρ : Env M 4 := ⟨Fin.cases F (Fin.cases B (Fin.cases T (fun _ => κ))), fun _ => κ⟩
  have tr := smap_delta_l I hZF source.omega source.transitive hY hm hn hπ φ
    (by simp -implicitDefEqProofs [φ]) (wc_iso_delta_l ..) ρ
    ⟨Fin.cases F' (Fin.cases B' (Fin.cases T' (fun _ => κ'))), fun _ => κ'⟩
    (Fin.cases hFF (Fin.cases hBB (Fin.cases hTT (fun _ => hκπ))))
  have tr' := smap_delta_l I hZF source.omega owner.transitive hN' h₀ h₁ hσ φ
    (by simp -implicitDefEqProofs [φ]) (wc_iso_delta_l ..) ρ
    ⟨Fin.cases F'' (Fin.cases B'' (Fin.cases T' (fun _ => κ'))), fun _ => κ'⟩
    (Fin.cases hFσ (Fin.cases hBσ (Fin.cases hTσ (fun _ => hκσ))))
  simp only [φ, wc_iso_sat_l hZF.1] at tr tr'
  have iso' : Wc_iso_d κ' T' B' F' := tr.mp iso
  have iso'' : Wc_iso_d κ' T' B'' F'' := tr'.mp iso
  have eq := iso'.unique_l hZF iso''
  subst B''
  have eq := iso'.graph_unique_l hZF iso''
  subst F''
  have point x x' (hx : M.mem x B) (hxx : Rd_entry_d x x' π) : Rd_entry_d x x' σ := by
    obtain ⟨a, ha, hax⟩ := iso.onto x hx
    obtain ⟨a', _, haa⟩ := hσ.1.1.2.2 a (owner.transitive κ owner.cardinal_mem a ha)
    obtain ⟨x'', _, hxx'⟩ := hσ.1.1.2.2 x (owner.transitive B hB₀ x hx)
    have hx' := (hπ.entry_l hZF source.omega source.transitive hY hm hn (fixed a a' ha haa) hxx hFF).mp hax
    have hx'' := (hσ.entry_l hZF source.omega owner.transitive hN' h₀ h₁ haa hxx' hFσ).mp hax
    exact ((fn0_function_l (ZF.modelsKP hZF) iso'.function).1.2 a' x' x'' hx' hx'').symm ▸ hxx'
  refine ⟨hB₀, hF₀, fun C hBC => hπ.1.1.1.2 B B' C hBB hBC ▸ hBσ, fun x x' hx => ⟨point x x' hx, ?_⟩⟩
  intro hxx
  obtain ⟨y, _, hxy⟩ := hπ.1.1.2.2 x (source.transitive B hBX x hx)
  exact hσ.1.1.1.2 x y x' (point x y hx hxy) hxx ▸ hxy

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一复制图在传递后继上的支撑保持

把已构造的商复制与两侧坍塌共轭，实际得到后继之间的完整初等图。
坐标类的精确坍塌值证明这张图在整个支撑上等于所属模型的 σ。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_copy_collapse_l
    {ω κ κ' K K' L L' X R Y S N R₀ N' R₁ c d b b' π σ F F'
      J O Z A p T V q e C W J' O' Z' A' p' T' V' q' e' C' W' τ P P' o Rₚ o' g g' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π) (hκπ : Rd_entry_d κ κ' π)
    (owner : M.TransitiveSet N) (owner' : M.TransitiveSet N') (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁)
    (hσ : Smap_d I ω b b' N N' σ) (hωN : M.mem ω N) (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (hκ : M.TransitiveSet κ) (hL : M.TransitiveSet L)
    (family : Em_source_d ω κ L X F) (family' : Em_source_d ω κ' L' Y F')
    (coherent : Ec_source_d I ω κ L X F) (coherent' : Ec_source_d I ω κ' L' Y F')
    (atoms : Ea_atoms_d ω κ L F) (atoms' : Ea_atoms_d ω κ' L' F')
    (normal : En_source_d ω κ L X F) (normal' : En_source_d ω κ' L' Y F')
    (h : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (h' : Ep_system_d I ω κ' L' Y S F' J' O' Z' A' p' T' V') (limit' : Di_limit_d A' p' T' V' q' C' W')
    (hτ : Smap_d I ω e e' C C' τ)
    (copy : ∀ B E, Rd_entry_d B E τ ↔ M.mem B C ∧ ∃ u, Rd_entry_d u B q ∧ Ec_node_d π σ q' u E)
    (model : Smdl_d I e C W) (mdl : Smem_d I o P Rₚ)
    (wc : Wc_graph_d C W g) (bij : M.IsSetBijectionFromTo I g C P)
    (wc' : Wc_graph_d C' W' g') (bij' : M.IsSetBijectionFromTo I g' C' P')
    (forward : Smap_d I ω e' o' C' P' g') : ∃ k, Smap_d I ω o o' P P' k ∧
      M.MemberSubset L P ∧ M.MemberSubset L' P' ∧
      (∀ E E' x y, Rd_entry_d E x g → Rd_entry_d E' y g' → (Rd_entry_d x y k ↔ Rd_entry_d E E' τ)) ∧
      ∀ α α', M.mem α L → Rd_entry_d α α' σ → Rd_entry_d α α' k := by
  obtain ⟨inv, bi, inverse⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  have back := smap_of_iso_l I hZF source.omega mdl.1 model bi (fun x y E H hx hy =>
    ((mdl.2 x y).trans ⟨And.right ∘ And.right, fun h =>
      ⟨bi.1.1.input_mem_of_pairMember hx, bi.1.1.input_mem_of_pairMember hy, h⟩⟩).trans
      (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2
        ((inverse x E).mp hx) ((inverse y H).mp hy)).symm)
  obtain ⟨t, ht, ts⟩ := smap_comp_l I hZF back hτ
  obtain ⟨k, hk, ks⟩ := smap_comp_l I hZF ht forward
  have law E E' x y (hx : Rd_entry_d E x g) (hy : Rd_entry_d E' y g') :
      Rd_entry_d x y k ↔ Rd_entry_d E E' τ := by
    constructor
    · intro hxy
      obtain ⟨_, H, hxH, hHy⟩ := (ks x y).mp hxy
      obtain ⟨_, B, hxB, hBH⟩ := (ts x H).mp hxH
      exact bij.1.2 B E x ((inverse x B).mp hxB) hx ▸ bij'.1.2 H E' y hHy hy ▸ hBH
    · intro hEE
      exact (ks x y).mpr ⟨bij.1.1.output_mem_of_pairMember hx, E',
        (ts x E').mpr ⟨bij.1.1.output_mem_of_pairMember hx, E, (inverse x E).mpr hx, hEE⟩, hy⟩
  have κtr := smap_delta_l I hZF source.omega source.transitive target.transitive hm hn hπ (n := 1)
    (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _)
    ⟨fun _ => κ, fun _ => κ⟩ ⟨fun _ => κ', fun _ => κ'⟩ (fun _ => hκπ)
  have Ltr := smap_delta_l I hZF source.omega owner owner' h₀ h₁ hσ (n := 1)
    (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _)
    ⟨fun _ => L, fun _ => L⟩ ⟨fun _ => L', fun _ => L'⟩ (fun _ => hLσ)
  simp only [Formula.satisfies_isTransitive_iff] at κtr Ltr
  obtain ⟨cover, fixed⟩ := ep_seed_collapse_l hZF source hκ hL family coherent atoms normal h limit wc
    (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)
  obtain ⟨cover', fixed'⟩ := ep_seed_collapse_l hZF target (κtr.mp hκ) (Ltr.mp hL) family' coherent'
    atoms' normal' h' limit' wc' (fn0_of_function_l (ZF.modelsKP hZF) bij'.1.1)
  refine ⟨k, hk, cover, cover', law, ?_⟩
  intro α α' hα hαα
  obtain ⟨E, hEC, seed⟩ := ep_seed_exists_l hZF source family h limit hα
  obtain ⟨E', _, hEE⟩ := hτ.1.1.2.2 E hEC
  have seed' := ep_copy_seed_l hZF source target hm hn hπ hκπ owner owner' h₀ h₁ hσ hωN hLσ hFσ
    family family' h limit h' limit' (fn0_of_function_l (ZF.modelsKP hZF) hτ.1.1) copy hαα seed hEE
  exact (law E E' α α' (fixed α E seed) (fixed' α' E' seed')).mpr hEE

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 已有实际超幂的双映射复制与支撑保持

原所属模型中的短扩展器公式沿 σ 搬运，目标的内部共同纤维产生实际后继。
原超幂及其坍塌保持为输入中的同一个对象，可直接使用原树已经辨认的秩段。
支撑秩段的实际枚举使临界点像及求值图回到所属源；复制因而在支撑端点
也等于 σ，完整支撑迹继而给出所有有限 L 幂子集上的一致性；源内 L 枚举
再将一致性提升到整个小传递集合，包括相对秩层。
旧嵌入图在各自目标中可数时，同一次复制目标还包含原超幂及其实际可数编号。
原可数模型无需枝反射，常值方块和目标下一步不变量同时保留。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_copy_successor_l
    {ω κ κ' K K' K₀ K₁ L L' X R Y S N R₀ N' R₁ c d b b' π σ F F' P Rₚ o j₀ V₀ : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' Y S)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ N R₀) (owner' : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K₁ N' R₁)
    (agree : Ea_agree_d ω κ X N) (agree' : Ea_agree_d ω κ' Y N') (inside : M.MemberSubset N' Y)
    (branches : Sc_branch_d ω Y) (hierarchy : Sc_hierarchy_d Y) (power : Sc_power_d Y)
    (cover : Sc_cover_d Y) (small : Sh_source_d (ZF.modelsKP hZF) ω Y)
    (ob : Sc_branch_d ω N') (op : Sc_power_d N') (oc : Sc_cover_d N')
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π) (hκπ : Rd_entry_d κ κ' π)
    (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁) (hσ : Smap_d I ω b b' N N' σ)
    (hκσ : Rd_entry_d κ κ' σ) (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (maps : Ea_maps_d ω κ X π σ) (loc : It_local_d I ω N R₀ κ L F)
    (hlim : M.IsLimitOrdinal L) (level : Er_level_d N L V₀)
    (mdl : Smem_d I o P Rₚ) (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c o j₀) :
    ∃ P' Rₚ' o' j' k, Ep_successor_d hZF ω κ' L' Y S F' P' Rₚ' ∧ Smem_d I o' P' Rₚ' ∧
      It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' L' F' d o' j' ∧
      Smap_d I ω o o' P P' k ∧ M.mem L P ∧ M.mem L' P' ∧
      (∀ α α', M.mem α L → Rd_entry_d α α' σ → Rd_entry_d α α' k) ∧
      Rd_entry_d L L' k ∧
      Ea_maps_d ω L P k σ ∧
      (∀ x x' y y', Rd_entry_d x x' π → Rd_entry_d x y j₀ → Rd_entry_d x' y' j' → Rd_entry_d y y' k) ∧
      (∃ Γ Γ', M.mem Γ N ∧ Rd_entry_d κ Γ j₀ ∧ Rd_entry_d κ' Γ' j' ∧ Rd_entry_d Γ Γ' σ ∧ Rd_entry_d Γ Γ' k ∧
        ∀ x x', M.mem x Γ → Rd_entry_d x x' σ → Rd_entry_d x x' k) ∧
      Sc_branch_d ω P' ∧ Sc_hierarchy_d P' ∧ Sc_power_d P' ∧ Sc_cover_d P' ∧ Sh_source_d (ZF.modelsKP hZF) ω P' ∧
      (Sc_inaccessible_closure_d I ω Y → Sc_inaccessible_closure_d I ω P') ∧
      Ea_subset_d ω L' P' N' ∧
      (∀ ι η, M.mem π Y → M.mem ι Y → M.IsSetInjectionFromTo I ι π ω →
        M.mem σ N' → M.mem η N' → M.IsSetInjectionFromTo I η σ ω →
        M.mem P P' ∧ ∃ ξ, M.mem ξ P' ∧ M.IsSetInjectionFromTo I ξ P ω) ∧
      (∀ B f, M.TransitiveSet B → M.mem f P → M.IsSetBijectionFromTo I f L B →
        M.mem B N ∧ M.mem f N ∧ (∀ x x', M.mem x B → (Rd_entry_d x x' k ↔ Rd_entry_d x x' σ)) ∧
        ∀ p, M.mem p P' → M.IsRestrictionOf I p k L → M.mem B P' ∧ ∃ r, M.mem r P' ∧ M.IsRestrictionOf I r k B) ∧
      (∃ K, Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω L K P Rₚ) ∧
      (∃ K, Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω L' K P' Rₚ') := by
  obtain ⟨X₀, R₂, Q₀, S₀, J, O, Z, A, p, T, V, q, c₀, C, W, i₀, g,
    mx, nx, h, limit, model, wc, bij, hg, _, constants, hj, js⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨ep, es⟩ := smdl_unique_l I nx.1 mdl.1
  subst X₀ R₂ Q₀ S₀
  have hP : M.TransitiveSet P := by
    intro x hx y hy
    obtain ⟨E, _, hEx⟩ := bij.2 x hx
    obtain ⟨H, _, _, hHy⟩ := ((wc.2 E x hEx).2.2 y).mp hy
    exact bij.1.1.output_mem_of_pairMember hHy
  have loc' := loc.map_l hZF source.omega h₀.1 h₁.1 hσ
    (hσ.omega_l I hZF source.omega owner.transitive owner'.transitive h₀ h₁ owner.omega_mem) hκσ hLσ hFσ
  obtain ⟨P₁, hP₁, power₁⟩ := op K₁ owner'.finite.mem_l
  have old_power := (sc_power_iff_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ hσ).mpr op
  obtain ⟨P₀, hP₀, power₀⟩ := old_power K₀ owner.finite.mem_l
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code
  have ord' := loc'.ordinals_l (ZF.modelsKP hZF) owner'.transitive owner'.code
  have local_copy := loc
  obtain ⟨_, _, _, _, pre⟩ := (it_local_mem_l I owner.code).mp local_copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hωL : M.MemberSubset ω L := fun x hx => ord.2.transitive κ pre.1.2.2.2.2.1 x (source.below x hx)
  have hωL' := (hσ.subset_l hZF source.omega owner.transitive owner'.transitive h₀ h₁
    (hσ.omega_l I hZF source.omega owner.transitive owner'.transitive h₀ h₁ owner.omega_mem) hLσ).mp hωL
  have reverse : Ea_agree_d ω κ N X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have reverse' : Ea_agree_d ω κ' N' Y := fun n D A hn hd sub => (agree' n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hP₀ power₀)).transfer_l reverse
  have family' := (loc'.measures_l hZF owner'.omega (owner'.read_source_l hZF) owner'.code owner'.theory
    (sf_finite_power_l hZF owner'.omega owner'.transitive owner'.code owner'.theory (owner'.finite_l (ZF.modelsKP hZF)) hP₁ power₁)).transfer_l reverse'
  have coherent := (loc.coherent_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF reverse
  have coherent' := (loc'.coherent_l hZF (owner'.read_source_l hZF) owner'.code).transfer_l hZF reverse'
  have atoms := loc.atoms_l hZF (owner.read_source_l hZF) owner.code
  have atoms' := loc'.atoms_l hZF (owner'.read_source_l hZF) owner'.code
  have normal := (loc.normal_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF owner source agree.subset_l
  have normal' := (loc'.normal_l hZF (owner'.read_source_l hZF) owner'.code).transfer_l hZF owner' target agree'.subset_l
  obtain ⟨J', O', Z', A', p', T', V', q', c₁, C', W', h', limit', model', _, elementary', collapse'⟩ :=
    loc'.limit_l hZFC target owner' branches cover power inside agree' ob hP₁ power₁
  obtain ⟨_, d₀, i', P', g', _, o', Rₚ', j', code', hi', constants', hP', wc', bij', mdl', hg', _, _, _, hj', js', next'⟩ := collapse'
  obtain ⟨ed, _⟩ := smem_unique_l I hZF.1 code' hn
  subst d₀
  obtain ⟨τ, _, _, hτ, _, _, copy, _, _, _⟩ := ep_copy_l hZF source target hm hn hπ hκπ owner.transitive owner'.transitive h₀ h₁ hσ
    owner.theory owner.omega_mem hLσ hFσ family family' coherent coherent' maps h limit model h' limit' model'
  obtain ⟨k, hk, _, _, square, fixed⟩ :=
    ep_copy_collapse_l hZF source target hm hn hπ hκπ owner.transitive owner'.transitive h₀ h₁ hσ owner.omega_mem hLσ hFσ
      ord.1.transitive ord.2.transitive family family' coherent coherent' atoms atoms' normal normal'
      h limit h' limit' hτ copy model mdl wc bij wc' bij' hg'
  -- 固定同一次复制所构造的模型与嵌入，再建立端点成员资格和限制恢复。
  have seed := (ep_seed_collapse_l hZF source ord.1.transitive ord.2.transitive family coherent atoms normal
    h limit wc (fn0_of_function_l (ZF.modelsKP hZF) hg.1.1)).2
  have seed' := (ep_seed_collapse_l hZF target ord'.1.transitive ord'.2.transitive family' coherent'
    atoms' normal' h' limit' wc' (fn0_of_function_l (ZF.modelsKP hZF) hg'.1.1)).2
  have hLP := ep_support_mem_l hZFC source family coherent h limit model hP mdl hg seed ord.1 ord.2
  have hLP' := ep_support_mem_l hZFC target family' coherent' h' limit' model' hP' mdl' hg' seed' ord'.1 ord'.2
  -- 原树指定的常值箭头与同一次复制严格交换，支撑选择由代表唯一性消去。
  have commute x x' y y' (hxx : Rd_entry_d x x' π) (hxy : Rd_entry_d x y j₀) (hxy' : Rd_entry_d x' y' j') :
      Rd_entry_d y y' k := by
    obtain ⟨H, hxH, hHy⟩ := (js.2 x y).mp hxy
    obtain ⟨_, H', hxH', hHy'⟩ := (js' x' y').mp hxy'
    obtain ⟨u, a, B, f, D, _, sf, fc, hfB, pair, huH⟩ := constants x H hxH
    obtain ⟨u', a', B', f', D', _, sf', fc', hfB', pair', huH'⟩ := constants' x' H' hxH'
    exact (square H H' y y' hHy hHy').mpr (ep_copy_constant_l hZF source target hm hn hπ hκπ
      owner.transitive owner'.transitive h₀ h₁ hσ owner.omega_mem hLσ hFσ family family' h limit h' limit' copy hxx
      (sf.function_l source.transitive) fc ⟨u, B, pair, hfB, huH⟩
      (sf'.function_l target.transitive) fc' ⟨u', B', pair', hfB', huH'⟩)
  obtain ⟨Γ, _, hκΓ⟩ := hj.1.1.2.2 κ source.cardinal_mem
  obtain ⟨Γ', _, hκΓ'⟩ := hj'.1.1.2.2 κ' target.cardinal_mem
  obtain ⟨H, hκH, hHΓ⟩ := (js.2 κ Γ).mp hκΓ
  obtain ⟨_, H', hκH', hHΓ'⟩ := (js' κ' Γ').mp hκΓ'
  obtain ⟨u, a, B, f, D, _, sf, fc, hfB, pair, huH⟩ := constants κ H hκH
  obtain ⟨u', a', B', f', D', _, sf', fc', hfB', pair', huH'⟩ := constants' κ' H' hκH'
  have fv : Ep_repr_d q a f H := ⟨u, B, pair, hfB, huH⟩
  have fv' : Ep_repr_d q' a' f' H' := ⟨u', B', pair', hfB', huH'⟩
  have hΓ := hj.ordinal_l hZF source.omega source.transitive hP hm mdl hκΓ ord.1
  have hΓ' := hj'.ordinal_l hZF source.omega target.transitive hP' hn mdl' hκΓ' ord'.1
  have hκV := level.hierarchy.ordinal_subset_l hZF owner.transitive level.member κ pre.1.2.2.2.2.1
  obtain ⟨hΓN, D₂, Q₂, e₂, eval, _⟩ := eb_owned_value_l hZF source owner agree family h limit wc bij
    (sf.function_l source.transitive) fc fv hHΓ hΓ.transitive old_power
    (hσ.1.1.input_mem_of_pairMember hLσ) (hσ.1.1.input_mem_of_pairMember hFσ) hlim level hκV
  obtain ⟨Θ, _, hΓΘ⟩ := hσ.1.1.2.2 Γ hΓN
  have copied a a' f f' x y (haa : Rd_entry_d a a' σ) (hff : Rd_entry_d f f' π)
      (fv : Ep_value_d q g a f x) (fv' : Ep_value_d q' g' a' f' y) : Rd_entry_d x y k := by
    obtain ⟨E, ev, hEx⟩ := fv
    obtain ⟨E', ev', hE'y⟩ := fv'
    exact (square E E' x y hEx hE'y).mpr (ep_copy_repr_l limit.projection copy haa hff ev ev')
  have endpoint := commute κ κ' Γ Γ' hκπ hκΓ hκΓ'
  obtain ⟨same, below⟩ := ep_copy_bounded_l hZF source target target.transitive owner owner' agree agree' hm hn hπ h₀ h₁ hσ
    hκπ hκσ hLσ hFσ maps family family' h limit h' limit' wc bij wc' bij' copied
    (sf.function_l source.transitive) fc fv hHΓ (sf'.function_l target.transitive) fc' fv' hHΓ' hΓ'.transitive hΓΘ eval
  have hΓσ : Rd_entry_d Γ Γ' σ := same ▸ hΓΘ
  obtain ⟨hfX, n, hnω, ha, D₃, space, fn⟩ := fv.source_l hZF family h limit
  have eq := fn.domain_eq_l hZF.1 (sf.function_l source.transitive)
  subst D₃
  have bound := ep_value_support_l hZF source family h limit model mdl hg seed (fv.index_l hZF h limit) hnω ha space
    hfX (sf.function_l source.transitive) fc ⟨H, fv, hHΓ⟩
  have support : Rd_entry_d L L' k := by
    rcases Structure.IsOrdinal.trichotomy hZF.1 ord.2 hΓ (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) L Γ) with eq | lt | gt
    · have eqL := hZF.1.eq_of_same_members L Γ eq
      have eqL' := hσ.1.1.1.2 Γ L' Γ' (eqL ▸ hLσ) hΓσ
      simpa only [eqL, eqL'] using endpoint
    · exact below L L' lt hLσ
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) Γ (bound Γ gt)).elim
  have subset_maps := ep_copy_subsets_l hZFC source target target (fun _ h => h) owner owner' hm hn hπ h₀ h₁ hσ
    hκπ hκσ hLσ hFσ maps family coherent family' coherent' h limit model hP mdl hg
    (fun x => ⟨fun hx => (bij.2 x hx).imp fun _ h => h.2, fun ⟨_, hx⟩ => bij.1.1.output_mem_of_pairMember hx⟩)
    seed h' limit' model' hP' mdl' hg' seed' hP' mdl' hk support copied
  have fix := hj.omega_l I hZF source.omega source.transitive hP hm mdl source.omega_mem
  obtain ⟨_, base⟩ := source.successor_l hZF hm mdl hP hj (hj.1.1.output_mem_of_pairMember fix) (fun _ h => h)
    ((hj.small_l I hZF source.omega hm.1 mdl.1 fix).mp (source.cardinal_small.mono_mem_l I hm source.omega_mem source.below))
  obtain ⟨_, base'⟩ := next'
  obtain ⟨K₂, ready⟩ := base.rebase_l hLP hωL
    (sc_ordinal_small_l hZF source.omega hP mdl base.theory hLP ord.2)
  obtain ⟨K₃, ready'⟩ := base'.rebase_l hLP' hωL'
    (sc_ordinal_small_l hZF target.omega hP' mdl' base'.theory hLP' ord'.2)
  -- 原嵌入图的内部可数性，经固定传递域和完整代表呈示，回收同一个原超幂。
  have countable ι η (hpY : M.mem π Y) (hι : M.mem ι Y) (ip : M.IsSetInjectionFromTo I ι π ω)
      (hsN : M.mem σ N') (hη : M.mem η N') (is : M.IsSetInjectionFromTo I η σ ω) :
      M.mem P P' ∧ ∃ ξ, M.mem ξ P' ∧ M.IsSetInjectionFromTo I ξ P ω := by
    obtain ⟨hXY, r, hr, ri⟩ := sc_domain_numbering_l hZF target.omega target.transitive hn target.theory
      target.omega_mem hι hpY ip (fn0_of_function_l (ZF.modelsKP hZF) hπ.1.1)
    obtain ⟨hNN, t, ht, ti⟩ := sc_domain_numbering_l hZF owner'.omega owner'.transitive h₁ owner'.theory
      owner'.omega_mem hη hsN is (fn0_of_function_l (ZF.modelsKP hZF) hσ.1.1)
    obtain ⟨xx, _, r', hr', ri'⟩ := hj'.countable_fixed_l hZF target.omega target.transitive hP' hn mdl'
      target.omega_mem hXY source.transitive hr ri
    obtain ⟨_, fixedN, t', ht', ti'⟩ := hj'.countable_fixed_l hZF target.omega target.transitive hP' hn mdl'
      target.omega_mem (inside N hNN) owner.transitive (inside t ht) ti
    have ln := hσ.1.1.input_mem_of_pairMember hLσ
    have lx := hj'.1.1.output_mem_of_pairMember (fixedN L ln)
    have fx := hj'.1.1.output_mem_of_pairMember (fixedN F (hσ.1.1.input_mem_of_pairMember hFσ))
    have li := (Sc_index_d.of_injection_l (ZF.modelsKP hZF) (target.omega.isOrdinal (ZF.modelsKP hZF)) ti').mono_l (owner.transitive L ln)
    obtain ⟨u, hu, ui⟩ := li.restrict_l hZF target.omega hP' mdl' ready'.theory lx ready'.omega_mem ht'
    exact ep_countable_ultra_l hZF source ready' (hj'.1.1.output_mem_of_pairMember xx) lx fx hr' hu
      ri' ui family h limit wc bij
  obtain ⟨K₄, owner₀⟩ := owner.rebase_l (hσ.1.1.input_mem_of_pairMember hLσ) hωL
    (sc_ordinal_small_l hZF source.omega owner.transitive h₀ owner.theory (hσ.1.1.input_mem_of_pairMember hLσ) ord.2)
  have models B f (hB : M.TransitiveSet B) (hf : M.mem f P) (bij : M.IsSetBijectionFromTo I f L B) :=
    subset_maps.transitive_l hZF ready owner₀ hP' owner'.transitive mdl mdl' hk h₀ h₁ hσ support hLσ fixed hB hf bij
  have successor : Ep_successor_d hZF ω κ' L' Y S F' P' Rₚ' :=
    ⟨J', O', Z', A', p', T', V', q', c₁, C', W', o', g', h', limit', model', mdl', hP', wc', bij', hg'⟩
  have ultra' : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' L' F' d o' j' :=
    ⟨Y, S, P', Rₚ', J', O', Z', A', p', T', V', q', c₁, C', W', i', g', hn, mdl', h', limit', model',
      wc', bij', hg', hi', constants', hj', hj'.1.1.1.1, fun x y => (js' x y).trans
        ⟨And.right, fun ⟨z, hxz, hzy⟩ => ⟨hi'.1.1.input_mem_of_pairMember hxz, z, hxz, hzy⟩⟩⟩
  exact ⟨P', Rₚ', o', j', k, successor, mdl', ultra', hk, hLP, hLP', fixed, support, subset_maps, commute,
    ⟨Γ, Γ', hΓN, hκΓ, hκΓ', hΓσ, endpoint, below⟩,
    loc'.branch_l hZF target owner' (ZFC.dc_l I hZFC target.omega) branches cover power inside agree' ob hP₁ power₁
      h' limit' model' elementary' hP' base'.omega_mem (base'.algebra_l (ZF.modelsKP hZF)) mdl' hg' (fun y hy => (bij'.2 y hy).imp fun _ h => h.2),
    (sc_hierarchy_iff_l hZF target.omega target.transitive hP' hn mdl' hj').mp hierarchy,
    (sc_power_iff_l hZF target.omega target.transitive hP' hn mdl' hj').mp power,
    (sc_cover_iff_l hZF target.omega target.transitive hP' hn mdl' hj').mp cover,
    (sh_source_iff_l hZF target base' hn mdl' hj').mp small,
    (sc_inaccessible_closure_iff_l hZF target.omega target.transitive hP'
      (target.algebra_l (ZF.modelsKP hZF)).pair (base'.algebra_l (ZF.modelsKP hZF)).pair hn mdl' hj' target.omega_mem).mp,
    (loc'.return_l hZFC target owner' agree' ob op oc successor).1,
    countable,
    (fun B f hB hf bij => ⟨(models B f hB hf bij).1, (models B f hB hf bij).2.1, (models B f hB hf bij).2.2.2,
      fun p hp res => smap_small_restriction_l hZF ready ready' mdl mdl' hk hp res hB hf bij⟩), ⟨K₂, ready⟩, ⟨K₃, ready'⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
