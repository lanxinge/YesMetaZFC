import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSetComponent
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceInclusion
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.ElementaryFactor

/-! # 小源超幂到拥有集合之像的完整初等嵌入

包含诱导的实际关系嵌入落入 j(A)。有限矩阵定理证明每个分量在 j(A) 中
完整初等，定向极限因子遂保持全部内部公式；A 无须具有正则高度。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_set_inclusion_l {ω κ K L X R F J O Z A p T V q c C W d N S μ K' e i j c₀
    a₀ A₀ R₀ a₁ A₁ R₁ K₀ J₀ O₀ Z₀ D₀ p₀ T₀ V₀ q₀ c₁ C₀ W₀ : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω μ K' N S)
    (small : Ep_source_d hZF ω κ K₀ A₀ R₀)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I c C W) (hm : Smem_d I c₀ X R) (hn : Smem_d I d N S)
    (he : Smap_d I ω c d C N e) (hj : Smap_d I ω c₀ d X N j)
    (constants : Ep_constants_d X q i) (comp : It_comp_d i e j)
    (h₀ : Smem_d I a₀ A₀ R₀) (h₁ : Smem_d I a₁ A₁ R₁) (hA : Rd_entry_d A₀ A₁ j)
    (cover : Ea_subset_d ω κ X A₀)
    (system₀ : Ep_system_d I ω κ L A₀ R₀ F J₀ O₀ Z₀ D₀ p₀ T₀ V₀)
    (limit₀ : Di_limit_d D₀ p₀ T₀ V₀ q₀ C₀ W₀) (model₀ : Smdl_d I c₁ C₀ W₀) :
    ∃ g, Smap_d I ω c₁ a₁ C₀ A₁ g ∧
      ∀ a f E x, Ep_repr_d q₀ a f E → Rd_entry_d E x g → Ep_value_d q e a f x := by
  have hA₀ := hj.1.1.input_mem_of_pairMember hA
  have inside := source.transitive A₀ hA₀
  have agree : Ea_agree_d ω κ X A₀ := fun n D B hn hd sub => ⟨cover n D B hn hd sub, inside B⟩
  have family₀ := family.transfer_l agree
  have coherent₀ := coherent.transfer_l hZF agree
  have elementary := system₀.toEp_graph_d.elementary_l hZFC small family₀ coherent₀
  obtain ⟨r, hr, _, reps⟩ := ep_inclusion_l hZF h₀ hm inside family₀ family system₀ limit₀ system limit
  obtain ⟨g, fg, gs⟩ := ZF.exists_compositionFunction hZF I hr.1 he.1.1
  have inj x y z (hx : Rd_entry_d x z g) (hy : Rd_entry_d y z g) : x = y := by
    obtain ⟨_, E, hxE, hEz⟩ := (gs x z).mp hx
    obtain ⟨_, H, hyH, hHz⟩ := (gs y z).mp hy
    exact hr.2 x y H (he.1.2 E H z hEz hHz ▸ hxE) hyH
  have values a f E x (old : Ep_repr_d q₀ a f E) (hEx : Rd_entry_d E x g) : Ep_value_d q e a f x := by
    obtain ⟨_, H, hEH, hHx⟩ := (gs E x).mp hEx
    exact ⟨H, (reps a f E H old).mp hEH, hHx⟩
  have into E x (hEx : Rd_entry_d E x g) : M.mem x A₁ := by
    obtain ⟨n, a, D, f, hnω, _, ha, space, _, ff, old⟩ :=
      ep_repr_surjective_l hZF family₀ system₀ limit₀ (fg.input_mem_of_pairMember hEx)
    obtain ⟨H, rep, hHx⟩ := values a f E x old hEx
    obtain ⟨k, _, fk, kc, B, br, hBA⟩ := ep_value_constant_l hZF source family system limit constants comp
      hnω (rep.index_l hZF system limit) ha space hA₀ hA
    have member := ep_repr_bound_mem_l hZF source family system limit fk kc br hA₀ hnω ha space ff rep
    exact ((hn.2 x A₁).mp ((he.relation_l I hZF source.omega model hn.1 hHx hBA).mp member)).2.2
  have fg₁ := (fn0_of_function_l (ZF.modelsKP hZF) fg).retarget_l into
  have hg : M.IsSetInjectionFromTo I g C₀ A₁ := ⟨fn0_function_l (ZF.modelsKP hZF) fg₁, inj⟩
  obtain ⟨f, ff, fs⟩ := ZF.exists_compositionFunction hZF I
    (fn0_function_l (ZF.modelsKP hZF) limit₀.projection) hg.1
  obtain ⟨_, hz⟩ := system₀.codes
  have models := system₀.components
  have component a o (hao : Rd_entry_d a o Z₀) : ∃ H Q k,
      Smdl_d I o H Q ∧ Smap_d I ω o a₁ H A₁ k ∧
        ∀ B x, Rd_entry_d B x k ↔ M.mem B H ∧ ∃ u, KPair_d M u a B ∧ Rd_entry_d u x f := by
    obtain ⟨n, D, U, G, p', H, Q, hnω, ha, space, haU, hG, cmp⟩ := models a o hao
    obtain ⟨t, ht, ts⟩ := ep_stage_embedding_l hZF small.omega system₀.toEg_graph_d system₀.diagram limit₀ elementary model₀ hao cmp.code
    obtain ⟨k, fk, ks⟩ := ZF.exists_compositionFunction hZF I ht.1.1 hg.1
    have hk : M.IsSetInjectionFromTo I k H A₁ := ⟨fk, fun B D x hBx hDx => by
      obtain ⟨_, E, hBE, hEx⟩ := (ks B x).mp hBx
      obtain ⟨_, E', hDE, hE'x⟩ := (ks D x).mp hDx
      exact ht.1.2 B D E' (inj E E' x hEx hE'x ▸ hBE) hDE⟩
    have val f₀ B x (hfB : Rd_entry_d f₀ B p') (hBx : Rd_entry_d B x k) : Ep_value_d q e a f₀ x := by
      obtain ⟨_, E, hBE, hEx⟩ := (ks B x).mp hBx
      obtain ⟨_, u, hu, huE⟩ := (ts B E).mp hBE
      exact values a f₀ E x ⟨u, B, hu, cmp.map.representative_l I (family₀.at_l hZF.1 haU ha space).base hfB, huE⟩ hEx
    have hk' := ep_set_component_l hZFC source target small family coherent system limit model hm hn he hj constants comp
      h₀ h₁ hA cover hnω ((system.indices a).mpr ((system₀.indices a).mp (hz.bound_l hao).1)) ha space haU hG cmp hk val
    refine ⟨H, Q, k, cmp.code, hk', fun B x => ⟨?_, ?_⟩⟩
    · intro hBx
      obtain ⟨hB, E, hBE, hEx⟩ := (ks B x).mp hBx
      obtain ⟨_, u, hu, huE⟩ := (ts B E).mp hBE
      exact ⟨hB, u, hu, (fs u x).mpr ⟨(limit₀.projection.bound_l huE).1, E, huE, hEx⟩⟩
    · rintro ⟨hB, u, hu, hux⟩
      obtain ⟨_, E, huE, hEx⟩ := (fs u x).mp hux
      exact (ks B x).mpr ⟨hB, E, (ts B E).mpr ⟨hB, u, hu, huE⟩, hEx⟩
  have cone a o Y Q (stage : Di_stage_d I D₀ p₀ V₀ a o Y Q) :
      ∃ k, Smap_d I ω o a₁ Y A₁ k ∧ ∀ u x, Rd_entry_d u x k ↔ M.mem u Y ∧ Rd_entry_d u x f := by
    obtain ⟨u, hu⟩ := stage.1.2.1
    obtain ⟨o', _, hao⟩ := hz.2.1 a (system₀.projection.bound_l ((stage.2.1 u).mp hu).2).2
    obtain ⟨H, Q', k, cmp, hk, ks⟩ := component a o' hao
    obtain ⟨t, _, ht, _, ts, _⟩ := ep_tag_l hZF small.omega system₀.toEg_graph_d stage hao cmp
    obtain ⟨s, hs, ss⟩ := smap_comp_l I hZF ht hk
    refine ⟨s, hs, fun u x => (ss u x).trans (and_congr_right fun hu => ?_)⟩
    constructor
    · rintro ⟨B, huB, hBx⟩
      obtain ⟨_, v, hv, hvx⟩ := (ks B x).mp hBx
      exact ((I).unique ((ts u B).mp huB).2 hv).symm ▸ hvx
    · intro hux
      obtain ⟨B, hB, huB⟩ := ht.1.1.2.2 u hu
      exact ⟨B, huB, (ks B x).mpr ⟨hB, u, ((ts u B).mp huB).2, hux⟩⟩
  have comm u v x y (huv : Rd_entry_d u v T₀) (hux : Rd_entry_d u x f) (hvy : Rd_entry_d v y f) : x = y := by
    obtain ⟨_, E, huE, hEx⟩ := (fs u x).mp hux
    obtain ⟨_, H, hvH, hHy⟩ := (fs v y).mp hvy
    exact fg.1.2 E x y hEx ((limit₀.commute_l system₀.diagram huv huE hvH).symm ▸ hHy)
  obtain ⟨g', hg', _, unique⟩ := di_factor_elementary_l hZF small.omega system₀.diagram limit₀ elementary model₀ h₁.1
    (fn0_of_function_l (ZF.modelsKP hZF) ff) comm cone
  have eq := unique g fg₁ (fun u E x huE hux => by
    obtain ⟨_, H, huH, hHx⟩ := (fs u x).mp hux
    exact (fn0_function_l (ZF.modelsKP hZF) limit₀.projection).1.2 u H E huH huE ▸ hHx)
  exact ⟨g, eq.symm ▸ hg', values⟩

end YesMetaZFC.SetTheory.LargeCardinal
