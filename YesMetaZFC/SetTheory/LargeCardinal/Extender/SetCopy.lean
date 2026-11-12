import YesMetaZFC.SetTheory.LargeCardinal.Extender.CopyBounded
import YesMetaZFC.SetTheory.LargeCardinal.Extender.CopySubsets
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RankLift
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SetInclusion

/-! # 给定集合复制因子的支撑及全部子集交换

原商、中间商和大商均为输入中的实际系统。两张复合图把原代表的复制
送入已经给定的坍塌复制 k；种子与所属求值图随后确定支撑端点和全部有限幂子集。
这里不重新构造超幂或选择复制因子。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_set_support_l
    {ω κ κ' K K' K₂ K₀ K₁ L L' X R Y S H Q H' Q' c d b b' π σ F F'
      Z R₂ Z' R₃ z z' j₁ Y' S' d' P Rₚ o j₀ V₀
      J O U A p T V q e C W i g
      J₁ O₁ U₁ A₁ p₁ T₁ V₁ q₁ e₁ C₁ W₁ i₁ g₁
      J₂ O₂ U₂ A₂ p₂ T₂ V₂ q₂ C₂ W₂ τ ν t k : M.Domain}
    (source : Ep_source_d I ω κ K X R) (small : Ep_source_d I ω κ' K' Y S)
    (ambient : Ep_source_d I ω κ' K₂ Z R₂)
    (owner : Ep_source_d I ω κ K₀ H Q) (owner' : Ep_source_d I ω κ' K₁ H' Q')
    (agree : Ea_agree_d ω κ X H) (agree' : Ea_agree_d ω κ' Z H') (power : Sc_power_d H)
    (hm : Smem_d I c X R) (hs : Smem_d I d Y S) (hz : Smem_d I z Z R₂)
    (hz' : Smem_d I z' Z' R₃) (hs' : Smem_d I d' Y' S')
    (hπ : Smap_d I ω c d X Y π) (hκπ : Rd_entry_d κ κ' π)
    (h₀ : Smem_d I b H Q) (h₁ : Smem_d I b' H' Q') (hσ : Smap_d I ω b b' H H' σ)
    (hκσ : Rd_entry_d κ κ' σ) (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (maps : Ea_maps_d ω κ X π σ) (loc : It_local_d I ω H Q κ L F)
    (hlim : M.IsLimitOrdinal L) (level : Er_level_d H L V₀) (cover : Ea_subset_d ω κ' Z Y)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (family' : Em_source_d ω κ' L' Z F') (coherent' : Ec_source_d I ω κ' L' Z F')
    (system : Ep_system_d I ω κ L X R F J O U A p T V)
    (limit : Di_limit_d A p T V q C W) (model : Smdl_d I e C W)
    (mdl : Smem_d I o P Rₚ) (hP : M.TransitiveSet P)
    (wc : Wc_graph_d C W g) (bij : M.IsSetBijectionFromTo I g C P)
    (hg : Smap_d I ω e o C P g) (hj : Smap_d I ω c o X P j₀)
    (constants : Ep_constants_d X q i) (square : It_comp_d i g j₀)
    (system₁ : Ep_system_d I ω κ' L' Z R₂ F' J₁ O₁ U₁ A₁ p₁ T₁ V₁)
    (limit₁ : Di_limit_d A₁ p₁ T₁ V₁ q₁ C₁ W₁) (model₁ : Smdl_d I e₁ C₁ W₁)
    (hZ' : M.TransitiveSet Z') (wc₁ : Wc_graph_d C₁ W₁ g₁) (bij₁ : M.IsSetBijectionFromTo I g₁ C₁ Z')
    (hg₁ : Smap_d I ω e₁ z' C₁ Z' g₁) (hj₁ : Smap_d I ω z z' Z Z' j₁)
    (constants₁ : Ep_constants_d Z q₁ i₁) (square₁ : It_comp_d i₁ g₁ j₁) (hY : Rd_entry_d Y Y' j₁)
    (system₂ : Ep_system_d I ω κ' L' Y S F' J₂ O₂ U₂ A₂ p₂ T₂ V₂)
    (limit₂ : Di_limit_d A₂ p₂ T₂ V₂ q₂ C₂ W₂)
    (fτ : M.IsSetFunctionFromTo I τ C C₂) (fν : M.IsSetFunctionFromTo I ν C₂ Y')
    (copy : ∀ E B, Rd_entry_d E B τ ↔ M.mem E C ∧ ∃ u, Rd_entry_d u E q ∧ Ec_node_d π σ q₂ u B)
    (values : ∀ a f E x, Ep_repr_d q₂ a f E → Rd_entry_d E x ν → Ep_value_d q₁ g₁ a f x)
    (factor : It_comp_d τ ν t) (conjugate : It_comp_d g k t) (hk : Smap_d I ω o d' P Y' k)
    (raw_copy : ∀ a a' f f' E x, Rd_entry_d a a' σ → Rd_entry_d f f' π →
      Ep_repr_d q a f E → Ep_value_d q₁ g₁ a' f' x → Rd_entry_d E x t)
    (raw_square : ∀ x x' E y, Rd_entry_d x x' π → Rd_entry_d x E i →
      Rd_entry_d x' y j₁ → Rd_entry_d E y t) :
    (∀ x x' y y', Rd_entry_d x x' π → Rd_entry_d x y j₀ → Rd_entry_d x' y' j₁ → Rd_entry_d y y' k) ∧
      M.mem L P ∧ M.mem L' Y' ∧
      (∀ α α', M.mem α L → Rd_entry_d α α' σ → Rd_entry_d α α' k) ∧
      Rd_entry_d L L' k ∧ Ea_maps_d ω L P k σ ∧
      ∃ Γ Γ', M.mem Γ H ∧ Rd_entry_d κ Γ j₀ ∧ Rd_entry_d κ' Γ' j₁ ∧
        Rd_entry_d Γ Γ' σ ∧ Rd_entry_d Γ Γ' k ∧
        ∀ x x', M.mem x Γ → Rd_entry_d x x' σ → Rd_entry_d x x' k := by
  have loc' := loc.map_l hZF source.omega h₀.1 h₁.1 hσ
    (hσ.omega_l I hZF source.omega owner.transitive owner'.transitive h₀ h₁ owner.omega_mem) hκσ hLσ hFσ
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code
  have ord' := loc'.ordinals_l (ZF.modelsKP hZF) owner'.transitive owner'.code
  obtain ⟨_,_,_,_,pre⟩ := (it_local_mem_l I owner.code).mp loc
  simp only [ex_short_m,ex_pre_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at pre
  have normal := (loc.normal_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF owner source agree.subset_l
  have normal' := (loc'.normal_l hZF (owner'.read_source_l hZF) owner'.code).transfer_l hZF owner' ambient agree'.subset_l
  have inside := ambient.transitive Y (hj₁.1.1.input_mem_of_pairMember hY)
  have small_agree : Ea_agree_d ω κ' Z Y := fun n D B hn hd sub => ⟨cover n D B hn hd sub,inside B⟩
  have fs := family'.transfer_l small_agree
  have pull E x y (hEx : Rd_entry_d E x g) (hEy : Rd_entry_d E y t) : Rd_entry_d x y k := by
    obtain ⟨x',hEx',hx'y⟩ := (conjugate.2 E y).mp hEy
    exact hg.1.1.1.2 E x' x hEx' hEx ▸ hx'y
  have lift E H x y (hEx : Rd_entry_d E x g) (hEH : Rd_entry_d E H τ) (hHy : Rd_entry_d H y ν) :=
    pull E x y hEx ((factor.2 E y).mpr ⟨H,hEH,hHy⟩)
  have copied a a' f f' x y (haa : Rd_entry_d a a' σ) (hff : Rd_entry_d f f' π)
      (value : Ep_value_d q g a f x) (value' : Ep_value_d q₁ g₁ a' f' y) : Rd_entry_d x y k := by
    obtain ⟨E,rep,hEx⟩ := value
    exact pull E x y hEx (raw_copy a a' f f' E y haa hff rep value')
  have commute x x' y y' (hxx : Rd_entry_d x x' π) (hxy : Rd_entry_d x y j₀) (hxy' : Rd_entry_d x' y' j₁) :
      Rd_entry_d y y' k := by
    obtain ⟨E,hxE,hEy⟩ := (square.2 x y).mp hxy
    exact pull E y y' hEy (raw_square x x' E y' hxx hxE hxy')
  have seed := (ep_seed_collapse_l hZF source ord.1.transitive ord.2.transitive family coherent
    (loc.atoms_l hZF (owner.read_source_l hZF) owner.code) normal system limit wc (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)).2
  have seed' := (ep_seed_collapse_l hZF ambient ord'.1.transitive ord'.2.transitive family' coherent'
    (loc'.atoms_l hZF (owner'.read_source_l hZF) owner'.code) normal' system₁ limit₁ wc₁ (fn0_of_function_l (ZF.modelsKP hZF) bij₁.1.1)).2
  have fixed α α' (hα : M.mem α L) (hαα : Rd_entry_d α α' σ) : Rd_entry_d α α' k := by
    obtain ⟨E,hE,s⟩ := ep_seed_exists_l hZF source family system limit hα
    obtain ⟨E',hE',hEE⟩ := fτ.2.2 E hE
    obtain ⟨x,_,hEx⟩ := fν.2.2 E' hE'
    obtain ⟨n,a,i,D,f,ha,hi,hd,fc,rep⟩ := ep_copy_seed_l hZF source small hm hs hπ hκπ
      owner.transitive owner'.transitive h₀ h₁ hσ owner.omega_mem hLσ hFσ family fs system limit system₂ limit₂
      (fn0_of_function_l (ZF.modelsKP hZF) fτ) copy hαα s hEE
    obtain ⟨E₁,rep',hE₁x⟩ := values a f E' x rep hEx
    have hE₁α := seed' α' E₁ ⟨n,a,i,D,f,ha,hi,hd,fc,rep'⟩
    exact hg₁.1.1.1.2 E₁ x α' hE₁x hE₁α ▸ lift E E' α x (seed α E s) hEE hEx
  -- 同一常值 κ 的像由所属求值图确定，故复制在 Γ 以下与 σ 相同。
  obtain ⟨Γ,_,hκΓ⟩ := hj.1.1.2.2 κ source.cardinal_mem
  obtain ⟨Γ',_,hκΓ'⟩ := hj₁.1.1.2.2 κ' ambient.cardinal_mem
  obtain ⟨E,hκE,hEΓ⟩ := (square.2 κ Γ).mp hκΓ
  obtain ⟨E',hκE',hEΓ'⟩ := (square₁.2 κ' Γ').mp hκΓ'
  obtain ⟨u,a,B,f,D,_,sf,fc,hfB,pair,huE⟩ := constants κ E hκE
  obtain ⟨u',a',B',f',D',_,sf',fc',hfB',pair',huE'⟩ := constants₁ κ' E' hκE'
  have fv : Ep_repr_d q a f E := ⟨u,B,pair,hfB,huE⟩
  have fv' : Ep_repr_d q₁ a' f' E' := ⟨u',B',pair',hfB',huE'⟩
  have hΓ := hj.ordinal_l hZF source.omega source.transitive hP hm mdl hκΓ ord.1
  have hΓ' := hj₁.ordinal_l hZF source.omega ambient.transitive hZ' hz hz' hκΓ' ord'.1
  have hκV := level.hierarchy.ordinal_subset_l hZF owner.transitive level.member κ pre.1.2.2.2.2.1
  obtain ⟨hΓH,D₂,Q₂,e₂,eval,_⟩ := eb_owned_value_l hZF source owner agree family system limit wc bij
    (sf.function_l source.transitive) fc fv hEΓ hΓ.transitive power
    (hσ.1.1.input_mem_of_pairMember hLσ) (hσ.1.1.input_mem_of_pairMember hFσ) hlim level hκV
  obtain ⟨Θ,_,hΓΘ⟩ := hσ.1.1.2.2 Γ hΓH
  obtain ⟨same,below⟩ := ep_copy_bounded_l hZF source ambient small.transitive owner owner' agree agree'
    hm hs hπ h₀ h₁ hσ hκπ hκσ hLσ hFσ maps family family' system limit system₁ limit₁ wc bij wc₁ bij₁ copied
    (sf.function_l source.transitive) fc fv hEΓ (sf'.function_l ambient.transitive) fc' fv' hEΓ' hΓ'.transitive hΓΘ eval
  have hΓσ : Rd_entry_d Γ Γ' σ := same ▸ hΓΘ
  have endpoint := commute κ κ' Γ Γ' hκπ hκΓ hκΓ'
  obtain ⟨hfX,n,hnω,ha,D₃,space,fn⟩ := fv.source_l hZF family system limit
  have eq := fn.domain_eq_l hZF.1 (sf.function_l source.transitive)
  subst D₃
  have bound := ep_value_support_l hZF source family system limit model mdl hg seed (fv.index_l hZF system limit)
    hnω ha space hfX (sf.function_l source.transitive) fc ⟨E,fv,hEΓ⟩
  have support : Rd_entry_d L L' k := by
    rcases Structure.IsOrdinal.trichotomy hZF.1 ord.2 hΓ (KP.difference_exists_d (ZF.modelsKP hZF))
      (KP.intersection_exists_d (ZF.modelsKP hZF) L Γ) with eq | lt | gt
    · have eqL := hZF.1.eq_of_same_members L Γ eq
      have eqL' := hσ.1.1.1.2 Γ L' Γ' (eqL ▸ hLσ) hΓσ
      simpa only [eqL,eqL'] using endpoint
    · exact below L L' lt hLσ
    · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) Γ (bound Γ gt)).elim
  have tr := smap_delta_l I hZF source.omega ambient.transitive hZ' hz hz' hj₁ (n := 1)
    (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _)
    ⟨fun _ => Y,fun _ => Y⟩ ⟨fun _ => Y',fun _ => Y'⟩ (fun _ => hY)
  have hY' := (Formula.satisfies_isTransitive_iff _ _).mp
    (tr.mp ((Formula.satisfies_isTransitive_iff _ _).mpr small.transitive))
  have subsets := ep_copy_subsets_l hZFC source small ambient inside owner owner' hm hs hπ h₀ h₁ hσ
    hκπ hκσ hLσ hFσ maps family coherent family' coherent' system limit model hP mdl hg
    (fun x => ⟨fun hx => (bij.2 x hx).imp fun _ h => h.2,fun ⟨_,hx⟩ => bij.1.1.output_mem_of_pairMember hx⟩)
    seed system₁ limit₁ model₁ hZ' hz' hg₁ seed' hY' hs' hk support copied
  exact ⟨commute,hk.1.1.input_mem_of_pairMember support,hk.1.1.output_mem_of_pairMember support,
    fixed,support,subsets,Γ,Γ',hΓH,hκΓ,hκΓ',hΓσ,endpoint,below⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 给定原商极限到工作集合像的复制因子

原极限仅保留其真实关系呈示。代表复制先进入小源超幂，再沿完整集合因子进入
指定大超幂的 j(A)；原常值图逐代表交换，无需先坍塌或另选原后继。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_set_factor_l
    {ω κ κ' K K' K₂ K₃ L L' X R Y S H Q H' Q' c d b b' π σ F F'
      Z R₂ Z' R₃ z z' j₁ Y' S' d' μ
      J O U A p T V q e C W i
      J₁ O₁ U₁ A₁ p₁ T₁ V₁ q₁ e₁ C₁ W₁ i₁ g₁ : M.Domain}
    (source : Ep_source_d I ω κ K X R) (small : Ep_source_d I ω κ' K' Y S)
    (ambient : Ep_source_d I ω κ' K₂ Z R₂) (target : Ep_source_d I ω μ K₃ Z' R₃)
    (hm : Smem_d I c X R) (hs : Smem_d I d Y S)
    (hz : Smem_d I z Z R₂) (hz' : Smem_d I z' Z' R₃) (hs' : Smem_d I d' Y' S')
    (hπ : Smap_d I ω c d X Y π) (hκ : Rd_entry_d κ κ' π)
    (owner : M.TransitiveSet H) (owner' : M.TransitiveSet H')
    (h₀ : Smem_d I b H Q) (h₁ : Smem_d I b' H' Q')
    (hσ : Smap_d I ω b b' H H' σ) (theory : Sc_theory_d I ω H Q) (hω : M.mem ω H)
    (hL : Rd_entry_d L L' σ) (hF : Rd_entry_d F F' σ)
    (family : Em_source_d ω κ L X F) (family' : Em_source_d ω κ' L' Z F')
    (coherent : Ec_source_d I ω κ L X F) (coherent' : Ec_source_d I ω κ' L' Z F')
    (maps : Ea_maps_d ω κ X π σ)
    (system : Ep_system_d I ω κ L X R F J O U A p T V)
    (limit : Di_limit_d A p T V q C W) (model : Smdl_d I e C W) (constants : Ep_constants_d X q i)
    (system₁ : Ep_system_d I ω κ' L' Z R₂ F' J₁ O₁ U₁ A₁ p₁ T₁ V₁)
    (limit₁ : Di_limit_d A₁ p₁ T₁ V₁ q₁ C₁ W₁) (model₁ : Smdl_d I e₁ C₁ W₁)
    (hg₁ : Smap_d I ω e₁ z' C₁ Z' g₁) (hj₁ : Smap_d I ω z z' Z Z' j₁)
    (constants₁ : Ep_constants_d Z q₁ i₁) (square₁ : It_comp_d i₁ g₁ j₁)
    (hY : Rd_entry_d Y Y' j₁) (cover : Ea_subset_d ω κ' Z Y) :
    ∃ J₂ O₂ U₂ A₂ p₂ T₂ V₂ q₂ e₂ C₂ W₂ τ v k,
      Ep_system_d I ω κ' L' Y S F' J₂ O₂ U₂ A₂ p₂ T₂ V₂ ∧
      Di_limit_d A₂ p₂ T₂ V₂ q₂ C₂ W₂ ∧ Smdl_d I e₂ C₂ W₂ ∧
      Smap_d I ω e e₂ C C₂ τ ∧ Smap_d I ω e₂ d' C₂ Y' v ∧ Smap_d I ω e d' C Y' k ∧
      (∀ E B, Rd_entry_d E B τ ↔ M.mem E C ∧ ∃ u, Rd_entry_d u E q ∧ Ec_node_d π σ q₂ u B) ∧
      (∀ a f E x, Ep_repr_d q₂ a f E → Rd_entry_d E x v → Ep_value_d q₁ g₁ a f x) ∧
      (∀ a a' f f' E x, Rd_entry_d a a' σ → Rd_entry_d f f' π →
        Ep_repr_d q a f E → Ep_value_d q₁ g₁ a' f' x → Rd_entry_d E x k) ∧
      (∀ x x' E y, Rd_entry_d x x' π → Rd_entry_d x E i → Rd_entry_d x' y j₁ → Rd_entry_d E y k) ∧
      It_comp_d τ v k := by
  have inside := ambient.transitive Y (hj₁.1.1.input_mem_of_pairMember hY)
  have agree : Ea_agree_d ω κ' Z Y := fun n D B hn hd sub => ⟨cover n D B hn hd sub,inside B⟩
  have fs := family'.transfer_l agree
  have cs := coherent'.transfer_l hZF agree
  obtain ⟨J₂,O₂,U₂,A₂,p₂,T₂,V₂,q₂,e₂,C₂,W₂,system₂,limit₂,model₂,_⟩ := ep_ultrapower_l hZF small fs cs
  obtain ⟨τ,_,_,hτ,_,_,copy,_,_,_⟩ := ep_copy_l hZF source small hm hs hπ hκ owner owner'
    h₀ h₁ hσ theory hω hL hF family fs coherent cs maps system limit model system₂ limit₂ model₂
  obtain ⟨v,hv,values⟩ := ep_set_inclusion_l hZFC ambient target small family' coherent' system₁ limit₁ model₁
    hz hz' hg₁ hj₁ constants₁ square₁ hs hs' hY cover system₂ limit₂ model₂
  obtain ⟨k,hk,ks⟩ := smap_comp_l I hZF hτ hv
  have copied a a' f f' E x (haa : Rd_entry_d a a' σ) (hff : Rd_entry_d f f' π)
      (rep : Ep_repr_d q a f E) (value : Ep_value_d q₁ g₁ a' f' x) : Rd_entry_d E x k := by
    obtain ⟨hfX,n,hn,fa,D,space,fn⟩ := rep.source_l hZF family system limit
    obtain ⟨D',_,hDD⟩ := hπ.1.1.2.2 D (source.space_mem_l hZF hn space)
    have space' := ep_space_map_l hZF source small hm hs hπ hκ hn space hDD
    have fa' := (hσ.function_l hZF source.omega owner owner' h₀ h₁
      (hσ.natural_l hZF source.omega owner owner' h₀ h₁ hω n hn) hL haa).mp fa
    have haJ' := (system₂.indices a').mpr (ec_support_image_l hZF source.omega owner owner'
      h₀ h₁ hσ hω hL haa ((system.indices a).mp (rep.index_l hZF system limit)))
    have fn' := (hπ.sfun_l hZF source.omega source.transitive small.transitive hm hs hDD hff
      (source.function_l hZF hfX fn)).function_l small.transitive
    obtain ⟨E',hE',rep'⟩ := ep_repr_exists_l hZF fs system₂ limit₂ haJ' fa' space'
      (hπ.1.1.output_mem_of_pairMember hff) fn'
    obtain ⟨y,_,hEy⟩ := hv.1.1.2.2 E' hE'
    have eq := (values a' f' E' y rep' hEy).unique_l hZF family' system₁ limit₁
      (fn0_of_function_l (ZF.modelsKP hZF) hg₁.1.1) value
    have hEE := ep_copy_repr_l limit.projection copy haa hff rep rep'
    exact eq ▸ (ks E y).mpr ⟨hτ.1.1.input_mem_of_pairMember hEE,E',hEE,hEy⟩
  have commute x x' E y (hxx : Rd_entry_d x x' π) (hxE : Rd_entry_d x E i)
      (hxy : Rd_entry_d x' y j₁) : Rd_entry_d E y k := by
    obtain ⟨u,a,B,f,D,_,sf,fc,hfB,pair,huE⟩ := constants x E hxE
    have rep : Ep_repr_d q a f E := ⟨u,B,pair,hfB,huE⟩
    obtain ⟨hfX,n,hn,fa,D',space,fn⟩ := rep.source_l hZF family system limit
    have eq := fn.domain_eq_l hZF.1 (sf.function_l source.transitive)
    subst D'
    obtain ⟨U,haU⟩ := family.total n a hn fa
    obtain ⟨a',_,haa⟩ := hσ.1.1.2.2 a (rd_entry_transitive_l owner (hσ.1.1.input_mem_of_pairMember hF) haU).1
    obtain ⟨f',hfY,hff⟩ := hπ.1.1.2.2 f hfX
    obtain ⟨D',_,hDD⟩ := hπ.1.1.2.2 D (source.space_mem_l hZF hn space)
    have space' := ep_space_map_l hZF source small hm hs hπ hκ hn space hDD
    have fa' := (hσ.function_l hZF source.omega owner owner' h₀ h₁
      (hσ.natural_l hZF source.omega owner owner' h₀ h₁ hω n hn) hL haa).mp fa
    have haJ' := (system₁.indices a').mpr (ec_support_image_l hZF source.omega owner owner'
      h₀ h₁ hσ hω hL haa ((system.indices a).mp (rep.index_l hZF system limit)))
    have ff' := (hπ.sfun_l hZF source.omega source.transitive small.transitive hm hs hDD hff sf).function_l small.transitive
    have fc' := rs_constant_image_l hZF source.omega source.transitive small.transitive hm hs hπ hDD hxx hff fc
    obtain ⟨g,_,fg,gc,value⟩ := ep_value_constant_l hZF ambient family' system₁ limit₁ constants₁ square₁
      hn haJ' fa' space' (inside x' (hπ.1.1.output_mem_of_pairMember hxx)) hxy
    have eq := (ff'.mono_target_l inside).ext_l hZF.1 fg (fun s hs => ⟨x',fc' s hs,gc s hs⟩)
    exact copied a a' f f' E y haa hff rep (eq.symm ▸ value)
  exact ⟨J₂,O₂,U₂,A₂,p₂,T₂,V₂,q₂,e₂,C₂,W₂,τ,v,k,system₂,limit₂,model₂,hτ,hv,hk,
    copy,values,copied,commute,⟨hk.1.1.1.1,fun E x => (ks E x).trans
      ⟨And.right,fun ⟨B,hEB,hBx⟩ => ⟨hτ.1.1.input_mem_of_pairMember hEB,B,hEB,hBx⟩⟩⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 沿大模型超幂复制到 j(A)

π 的实际目标是拥有集合 A。先复制到 A 的源内超幂，再用完整集合因子
进入指定大超幂中的 j(A)，最后与原坍塌共轭。所属源的 κ 值求值图和有限
支撑迹给出长度端点及所有有限 L 幂子集上的一致性，常值方块同时保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_set_copy_l {ω κ κ' K K' K₂ K₀ K₁ L L' X R Y S H Q H' Q' c d b b' π σ F F'
    Z R₂ Z' R₃ z z' j₁ Y' S' d' P Rₚ o j₀ V₀ : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (small : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' Y S)
    (ambient : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K₂ Z R₂)
    (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ H Q) (owner' : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K₁ H' Q')
    (agree : Ea_agree_d ω κ X H) (agree' : Ea_agree_d ω κ' Z H') (power : Sc_power_d H)
    (hm : Smem_d I c X R) (hs : Smem_d I d Y S) (hz : Smem_d I z Z R₂)
    (hz' : Smem_d I z' Z' R₃) (hs' : Smem_d I d' Y' S')
    (hπ : Smap_d I ω c d X Y π) (hκπ : Rd_entry_d κ κ' π)
    (h₀ : Smem_d I b H Q) (h₁ : Smem_d I b' H' Q') (hσ : Smap_d I ω b b' H H' σ)
    (hκσ : Rd_entry_d κ κ' σ) (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (maps : Ea_maps_d ω κ X π σ) (loc : It_local_d I ω H Q κ L F)
    (hlim : M.IsLimitOrdinal L) (level : Er_level_d H L V₀) (cover : Ea_subset_d ω κ' Z Y)
    (mdl : Smem_d I o P Rₚ) (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c o j₀)
    (big : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' L' F' z z' j₁) (hY : Rd_entry_d Y Y' j₁) :
    ∃ k, Smap_d I ω o d' P Y' k ∧
      (∀ x x' y y', Rd_entry_d x x' π → Rd_entry_d x y j₀ → Rd_entry_d x' y' j₁ → Rd_entry_d y y' k) ∧
      M.mem L P ∧ M.mem L' Y' ∧
      (∀ α α', M.mem α L → Rd_entry_d α α' σ → Rd_entry_d α α' k) ∧
      Rd_entry_d L L' k ∧ Ea_maps_d ω L P k σ ∧
      ∃ Γ Γ', M.mem Γ H ∧ Rd_entry_d κ Γ j₀ ∧ Rd_entry_d κ' Γ' j₁ ∧
        Rd_entry_d Γ Γ' σ ∧ Rd_entry_d Γ Γ' k ∧
        ∀ x x', M.mem x Γ → Rd_entry_d x x' σ → Rd_entry_d x x' k := by
  have loc' := loc.map_l hZF source.omega h₀.1 h₁.1 hσ
    (hσ.omega_l I hZF source.omega owner.transitive owner'.transitive h₀ h₁ owner.omega_mem) hκσ hLσ hFσ
  have power' := (sc_power_iff_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ hσ).mp power
  obtain ⟨P₀, hP₀, pow₀⟩ := power K₀ owner.finite.mem_l
  obtain ⟨P₁, hP₁, pow₁⟩ := power' K₁ owner'.finite.mem_l
  have reverse : Ea_agree_d ω κ H X := fun n D B hn hd sub => (agree n D B hn hd sub).symm
  have reverse' : Ea_agree_d ω κ' H' Z := fun n D B hn hd sub => (agree' n D B hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hP₀ pow₀)).transfer_l reverse
  have family' := (loc'.measures_l hZF owner'.omega (owner'.read_source_l hZF) owner'.code owner'.theory
    (sf_finite_power_l hZF owner'.omega owner'.transitive owner'.code owner'.theory (owner'.finite_l (ZF.modelsKP hZF)) hP₁ pow₁)).transfer_l reverse'
  have coherent := (loc.coherent_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF reverse
  have coherent' := (loc'.coherent_l hZF (owner'.read_source_l hZF) owner'.code).transfer_l hZF reverse'
  have hP := ultra.transitive_l hZF mdl.1
  have hZ' := big.transitive_l hZF hz'.1
  obtain ⟨X₀, R₀, P₀, Q₀, J, O, U, A, p, T, V, q, e, C, W, i, g,
    mx, mp, system, limit, model, wc, bij, hg, hi, constants, hj, square⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨ep, eq⟩ := smdl_unique_l I mp.1 mdl.1
  subst X₀ R₀ P₀ Q₀
  obtain ⟨Z₀, R₄, Z₁, R₅, J₁, O₁, U₁, A₁, p₁, T₁, V₁, q₁, e₁, C₁, W₁, i₁, g₁,
    mz, mz', system₁, limit₁, model₁, wc₁, bij₁, hg₁, _, constants₁, hj₁, square₁⟩ := big
  obtain ⟨ez, er'⟩ := smdl_unique_l I mz.1 hz.1
  obtain ⟨ez', er''⟩ := smdl_unique_l I mz'.1 hz'.1
  subst Z₀ R₄ Z₁ R₅
  have hω := hj₁.omega_l I hZF ambient.omega ambient.transitive hZ' hz hz' ambient.omega_mem
  obtain ⟨K₃, target⟩ := ambient.successor_l hZF hz hz' hZ' hj₁ (hj₁.1.1.output_mem_of_pairMember hω)
    (fun _ h => h) ((hj₁.small_l I hZF ambient.omega hz.1 hz'.1 hω).mp
      (ambient.cardinal_small.mono_mem_l I hz ambient.omega_mem ambient.below))
  obtain ⟨J₂,O₂,U₂,A₂,p₂,T₂,V₂,q₂,e₂,C₂,W₂,τ,v,t,system₂,limit₂,model₂,hτ,hv,ht,
      copy,values,raw_copy,raw_square,factor⟩ :=
    ep_set_factor_l hZFC source small ambient target hm hs hz hz' hs' hπ hκπ
      owner.transitive owner'.transitive h₀ h₁ hσ owner.theory owner.omega_mem hLσ hFσ
      family family' coherent coherent' maps system limit model constants
      system₁ limit₁ model₁ hg₁ hj₁ constants₁ square₁ hY cover
  obtain ⟨inv, bi, inverse⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  have back := smap_of_iso_l I hZF source.omega mdl.1 model bi (fun x y E H hx hy =>
    ((mdl.2 x y).trans ⟨And.right ∘ And.right, fun h =>
      ⟨bi.1.1.input_mem_of_pairMember hx, bi.1.1.input_mem_of_pairMember hy, h⟩⟩).trans
      (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2
        ((inverse x E).mp hx) ((inverse y H).mp hy)).symm)
  obtain ⟨k, hk, ks⟩ := smap_comp_l I hZF back ht
  -- 同一原坍塌与刚构造的 k 共轭；固定因子的支撑证明不再另选复制。
  have conjugate : It_comp_d g k t := by
    refine ⟨ht.1.1.1.1,fun E y => ⟨?_,?_⟩⟩
    · intro hEy
      obtain ⟨x,hx,hEx⟩ := bij.1.1.2.2 E (ht.1.1.input_mem_of_pairMember hEy)
      exact ⟨x,hEx,(ks x y).mpr ⟨hx,E,(inverse x E).mpr hEx,hEy⟩⟩
    · rintro ⟨x,hEx,hxy⟩
      obtain ⟨_,E',hxE',hE'y⟩ := (ks x y).mp hxy
      exact (bij.1.2 E E' x hEx ((inverse x E').mp hxE')).symm ▸ hE'y
  exact ⟨k,hk,ep_set_support_l hZFC source small ambient owner owner' agree agree' power
    hm hs hz hz' hs' hπ hκπ h₀ h₁ hσ hκσ hLσ hFσ maps loc hlim level cover
    family coherent family' coherent' system limit model mdl hP wc bij hg hj constants square
    system₁ limit₁ model₁ hZ' wc₁ bij₁ hg₁ hj₁ constants₁ square₁ hY
    system₂ limit₂ hτ.1.1 hv.1.1 copy values factor conjugate hk raw_copy raw_square⟩
end YesMetaZFC.SetTheory.LargeCardinal
