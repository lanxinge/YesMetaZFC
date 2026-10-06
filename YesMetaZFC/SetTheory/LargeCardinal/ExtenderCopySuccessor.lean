import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSuccessorApplication
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopyCollapse
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopyRestriction
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceNode
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankLocal
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceSubsets
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopyBounded
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopySubsets
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderModelMap
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderPresentation
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingCountable
import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessibleClosure

/-! # 已有实际超幂的双映射复制与支撑保持

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
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω κ' K' Y S)
    (owner : Ep_source_d hZF ω κ K₀ N R₀) (owner' : Ep_source_d hZF ω κ' K₁ N' R₁)
    (agree : Ea_agree_d ω κ X N) (agree' : Ea_agree_d ω κ' Y N') (inside : M.MemberSubset N' Y)
    (branches : Sc_branch_d ω Y) (hierarchy : Sc_hierarchy_d Y) (power : Sc_power_d Y)
    (cover : Sc_cover_d Y) (small : Sh_source_d (ZF.modelsKP hZF) ω Y)
    (ob : Sc_branch_d ω N') (op : Sc_power_d N') (oc : Sc_cover_d N')
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π) (hκπ : Rd_entry_d κ κ' π)
    (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁) (hσ : Smap_d I ω b b' N N' σ)
    (hκσ : Rd_entry_d κ κ' σ) (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (maps : Ea_maps_d ω κ X π σ) (loc : It_local_d ω N κ L F)
    (hlim : M.IsLimitOrdinal L) (level : Er_level_d N L V₀)
    (mdl : Smem_d I o P Rₚ) (ultra : It_ultra_d hZF ω κ L F c o j₀) :
    ∃ P' Rₚ' o' j' k, Ep_successor_d hZF ω κ' L' Y S F' P' Rₚ' ∧ Smem_d I o' P' Rₚ' ∧
      It_ultra_d hZF ω κ' L' F' d o' j' ∧
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
      (∃ K, Ep_source_d hZF ω L K P Rₚ) ∧
      (∃ K, Ep_source_d hZF ω L' K P' Rₚ') := by
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
  have loc' := loc.map_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ hσ hκσ hLσ hFσ
  obtain ⟨P₁, hP₁, power₁⟩ := op K₁ owner'.finite_mem
  have old_power := (sc_power_iff_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ hσ).mpr op
  obtain ⟨P₀, hP₀, power₀⟩ := old_power K₀ owner.finite_mem
  have ord := loc.ordinals_l (ZF.modelsKP hZF) owner.transitive
  have ord' := loc'.ordinals_l (ZF.modelsKP hZF) owner'.transitive
  have local_copy := loc
  obtain ⟨_, _, _, _, pre⟩ := local_copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have hωL : M.MemberSubset ω L := fun x hx => ord.2.transitive κ pre.1.2.2.2.2.1 x (source.below x hx)
  have hωL' := (hσ.subset_l hZF source.omega owner.transitive owner'.transitive h₀ h₁
    (hσ.omega_l I hZF source.omega owner.transitive owner'.transitive h₀ h₁ owner.omega_mem) hLσ).mp hωL
  have reverse : Ea_agree_d ω κ N X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have reverse' : Ea_agree_d ω κ' N' Y := fun n D A hn hd sub => (agree' n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner hP₀ power₀).transfer_l reverse
  have family' := (loc'.measures_l hZF owner' hP₁ power₁).transfer_l reverse'
  have coherent := (loc.coherent_l hZF owner).transfer_l hZF reverse
  have coherent' := (loc'.coherent_l hZF owner').transfer_l hZF reverse'
  have atoms := loc.atoms_l hZF owner
  have atoms' := loc'.atoms_l hZF owner'
  have normal := (loc.normal_l hZF owner).transfer_l hZF owner source agree.subset_l
  have normal' := (loc'.normal_l hZF owner').transfer_l hZF owner' target agree'.subset_l
  obtain ⟨J', O', Z', A', p', T', V', q', c₁, C', W', h', limit', model', _, elementary', collapse'⟩ :=
    loc'.limit_l hZFC target owner' branches cover power inside agree' ob hP₁ power₁
  obtain ⟨_, d₀, i', P', g', _, o', Rₚ', j', code', hi', constants', hP', wc', bij', mdl', hg', _, _, _, hj', js', next'⟩ := collapse'
  obtain ⟨ed, _⟩ := smem_unique_l I hZF.1 code' hn
  subst d₀
  obtain ⟨τ, _, _, hτ, _, _, copy, _, _, _⟩ := ep_copy_l hZFC source target hm hn hπ hκπ owner.transitive owner'.transitive h₀ h₁ hσ
    owner.theory owner.omega_mem hLσ hFσ family family' coherent coherent' maps h limit model h' limit' model'
  obtain ⟨k, hk, _, _, square, fixed⟩ :=
    ep_copy_collapse_l hZF source target hm hn hπ hκπ owner.transitive owner'.transitive h₀ h₁ hσ owner.omega_mem hLσ hFσ
      ord.1.transitive ord.2.transitive hωL family family' coherent coherent' atoms atoms' normal normal'
      h limit h' limit' hτ copy model mdl wc bij wc' bij' hg'
  -- 固定同一次复制所构造的模型与嵌入，再建立端点成员资格和限制恢复。
  have seed := (ep_seed_collapse_l hZF source ord.1.transitive ord.2.transitive hωL family coherent atoms normal
    h limit wc (fn0_of_function_l (ZF.modelsKP hZF) hg.1.1)).2
  have seed' := (ep_seed_collapse_l hZF target ord'.1.transitive ord'.2.transitive hωL' family' coherent'
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
  obtain ⟨same, endpoint, below⟩ := ep_copy_bounded_l hZF source target owner owner' agree agree' hm hn hπ h₀ h₁ hσ
    hκπ hκσ hLσ hFσ maps family family' h limit h' limit' wc bij wc' bij' copy square
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
  have subset_maps := ep_copy_subsets_l hZFC source target owner owner' hm hn hπ h₀ h₁ hσ
    hκπ hκσ hLσ hFσ maps family coherent family' coherent' h limit model hP mdl hg
    (fun x => ⟨fun hx => (bij.2 x hx).imp fun _ h => h.2, fun ⟨_, hx⟩ => bij.1.1.output_mem_of_pairMember hx⟩)
    seed h' limit' model' hP' mdl' hg' seed' hωL hk support copy square
  have fix := hj.omega_l I hZF source.omega source.transitive hP hm mdl source.omega_mem
  obtain ⟨_, base⟩ := source.successor_l hZF hm mdl hP hj (hj.1.1.output_mem_of_pairMember fix) (fun _ h => h)
    ((hj.small_l hZF source.omega source.transitive hP hm mdl fix).mp (source.cardinal_small.mono_l source.below))
  obtain ⟨_, base'⟩ := next'
  obtain ⟨K₂, ready⟩ := base.rebase_l hZF hLP hωL
    (sc_ordinal_small_l hZF source.omega hP mdl base.theory hLP ord.2)
  obtain ⟨K₃, ready'⟩ := base'.rebase_l hZF hLP' hωL'
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
    have li := (Sc_index_d.of_injection_l (ZF.modelsKP hZF) (target.omega.isOrdinal hZF) ti').mono_l (owner.transitive L ln)
    obtain ⟨u, hu, ui⟩ := li.restrict_l hZF target.omega hP' mdl' ready'.theory lx ready'.omega_mem ht'
    exact ep_countable_ultra_l hZF source ready' (hj'.1.1.output_mem_of_pairMember xx) lx fx hr' hu
      ri' ui family h limit wc bij
  obtain ⟨K₄, owner₀⟩ := owner.rebase_l hZF (hσ.1.1.input_mem_of_pairMember hLσ) hωL
    (sc_ordinal_small_l hZF source.omega owner.transitive h₀ owner.theory (hσ.1.1.input_mem_of_pairMember hLσ) ord.2)
  have models B f (hB : M.TransitiveSet B) (hf : M.mem f P) (bij : M.IsSetBijectionFromTo I f L B) :=
    subset_maps.transitive_l hZF ready owner₀ hP' owner'.transitive mdl mdl' hk h₀ h₁ hσ support hLσ fixed hB hf bij
  have successor : Ep_successor_d hZF ω κ' L' Y S F' P' Rₚ' :=
    ⟨J', O', Z', A', p', T', V', q', c₁, C', W', o', g', h', limit', model', mdl', hP', wc', bij', hg'⟩
  have ultra' : It_ultra_d hZF ω κ' L' F' d o' j' :=
    ⟨Y, S, P', Rₚ', J', O', Z', A', p', T', V', q', c₁, C', W', i', g', hn, mdl', h', limit', model',
      wc', bij', hg', hi', constants', hj', hj'.1.1.1.1, fun x y => (js' x y).trans
        ⟨And.right, fun ⟨z, hxz, hzy⟩ => ⟨hi'.1.1.input_mem_of_pairMember hxz, z, hxz, hzy⟩⟩⟩
  exact ⟨P', Rₚ', o', j', k, successor, mdl', ultra', hk, hLP, hLP', fixed, support, subset_maps, commute,
    ⟨Γ, Γ', hΓN, hκΓ, hκΓ', hΓσ, endpoint, below⟩,
    loc'.branch_l hZF target owner' (ZFC.dc_l I hZFC target.omega) branches cover power inside agree' ob hP₁ power₁
      h' limit' model' elementary' hP' base'.omega_mem base'.theory.algebra mdl' hg' (fun y hy => (bij'.2 y hy).imp fun _ h => h.2),
    (sc_hierarchy_iff_l hZF target.omega target.transitive hP' hn mdl' hj').mp hierarchy,
    (sc_power_iff_l hZF target.omega target.transitive hP' hn mdl' hj').mp power,
    (sc_cover_iff_l hZF target.omega target.transitive hP' hn mdl' hj').mp cover,
    (sh_source_iff_l hZF target base' hn mdl' hj').mp small,
    (sc_inaccessible_closure_iff_l hZF target.omega target.transitive hP'
      target.theory.algebra.pair base'.theory.algebra.pair hn mdl' hj' target.omega_mem).mp,
    (loc'.return_l hZFC target owner' agree' ob op oc successor).1,
    countable,
    (fun B f hB hf bij => ⟨(models B f hB hf bij).1, (models B f hB hf bij).2.1, (models B f hB hf bij).2.2.2,
      fun p hp res => smap_small_restriction_l hZF ready ready' mdl mdl' hk hp res hB hf bij⟩), ⟨K₂, ready⟩, ⟨K₃, ready'⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
