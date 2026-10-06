import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopySuccessor
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrengthReturn
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSkolemStep
import YesMetaZFC.SetTheory.LargeCardinal.EmbeddingRankRestriction
import YesMetaZFC.SetTheory.LargeCardinal.IterationCoherence
import YesMetaZFC.SetTheory.LargeCardinal.IterationHistorySyntax

/-! # nice 复制的实际下降一步

固定原树已有的超幂和其中严格较小的正则秩段。最大强度给出两侧共同秩层，
旧图的内部可数性回收整个 Vρ∪{ρ} 上的限制；尝试树及指定种子的小壳调整
实际产生属于旧所属模型的新模型，并逐点保留旧图在该整个集合上的值。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem pn_copy_step_l
    {ω κ κ' K K' K₀ K₁ L L' X R Y S N R₀ N' R₁ c d b b' π σ F F' P Rₚ o j₀ ι η D a Q α : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Pn_model_d hZF ω κ' K' Y S)
    (owner : Ep_source_d hZF ω κ K₀ N R₀) (owner' : Ep_source_d hZF ω κ' K₁ N' R₁)
    (agree : Ea_agree_d ω κ X N) (inside : M.MemberSubset N' Y)
    (ob : Sc_branch_d ω N') (op : Sc_power_d N') (oc : Sc_cover_d N')
    (ocl : Sc_inaccessible_closure_d I ω N')
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁) (hσ : Smap_d I ω b b' N N' σ)
    (hκσ : Rd_entry_d κ κ' σ) (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (prior : (X = N ∧ Y = N' ∧ π = σ) ∨ ∃ ρ φ, Pn_agree_d X Y π N N' σ ρ φ ∧ Es_strength_d X ρ N)
    (loc : It_local_d ω N κ L F)
    (strength : Ex_strength_d hZF ω κ L N F) (inaccessible : Sc_inaccessible_d ω N L)
    (hπY : M.mem π Y) (hιY : M.mem ι Y) (ip : M.IsSetInjectionFromTo I ι π ω)
    (hσN : M.mem σ N') (hηN : M.mem η N') (is : M.IsSetInjectionFromTo I η σ ω)
    (mdl : Smem_d I o P Rₚ) (ultra : It_ultra_d hZF ω κ L F c o j₀)
    (hD : M.mem D P) (rank : Vr_d P α D) (regular : Sc_regular_d P α)
    (hd : Smem_d I a D Q) (hLD : M.mem L D) :
    ∃ B k ξ, M.mem B N' ∧ Pn_row_d hZF ω a D B k ξ ∧
      Es_strength_d N L D ∧ Pn_agree_d N N' σ D B k L L' := by
  obtain ⟨target, branches, hierarchy, power, cover, small, closure⟩ := target
  have image_lt {x y u v} (hx : Rd_entry_d x y σ) (hu : Rd_entry_d u v σ) (hxu : M.mem x u) : M.mem y v :=
    ((h₁.2 y v).mp ((hσ.relation_l I hZF owner.omega h₀.1 h₁.1 hx hu).mp
      ((h₀.2 x u).mpr ⟨hσ.1.1.input_mem_of_pairMember hx, hσ.1.1.input_mem_of_pairMember hu, hxu⟩))).2.2
  have inaccessible' := inaccessible.map_l hZF owner.omega owner.transitive owner'.transitive h₀ h₁ hσ hLσ
  obtain ⟨reg', sizes'⟩ := ocl L' inaccessible'
  have sizes := (hσ.rank_size_l hZF owner.omega owner.transitive owner'.transitive h₀ h₁ hLσ).mpr sizes'
  have limit := inaccessible.limit_l (ZF.modelsKP hZF) owner.transitive owner.theory.algebra.pair
  have limit' := inaccessible'.limit_l (ZF.modelsKP hZF) owner'.transitive owner'.theory.algebra.pair
  obtain ⟨V, f, hV, hv, hf, bij⟩ := sizes.level
  have input : ∃ ρ φ, Pn_agree_d X Y π N N' σ ρ φ ∧ M.mem κ ρ := by
    rcases prior with ⟨rfl, rfl, rfl⟩ | h
    · obtain ⟨V', hV', hVV⟩ := hσ.1.1.2.2 V hV
      have hv' := (hσ.hierarchy_l hZF owner.omega owner.transitive owner'.transitive h₀ h₁ hLσ hVV).mp hv
      have copy := loc
      obtain ⟨_, _, _, _, pre⟩ := copy
      simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
      exact ⟨L, L', ⟨owner.transitive, owner'.transitive, owner.transitive, owner'.transitive, limit, limit',
        ⟨V, hV, hV, hv, hv, fun _ _ _ => Iff.rfl⟩, ⟨V', hV', hV', hv', hv'⟩, hLσ, hLσ⟩, pre.1.2.2.2.2.1⟩
    · obtain ⟨ρ, φ, coincide, exactness⟩ := h
      exact ⟨ρ, φ, coincide, ea_critical_bound_l hZF source owner agree
        (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive).1 coincide.source_limit.1 exactness.2⟩
  obtain ⟨ρ, φ, coincide, hκρ⟩ := input
  obtain ⟨_, agree', maps⟩ := coincide.copy_l hZF source owner target owner' hκρ
    (image_lt hκσ coincide.right_end hκρ)
  obtain ⟨W₀, hW₀, _, w₀, _, points⟩ := coincide.source_rank
  have hκπ := (points κ κ' (w₀.ordinal_subset_l hZF source.transitive hW₀ κ hκρ)).mpr hκσ
  obtain ⟨C, hC, _, iso⟩ := ep_transitive_code_l hZF owner (hv.transitive_l hZF owner.transitive hV) hf bij
  have level : Er_level_d N L V := ⟨hV, hv, C, f, hC, hf, iso⟩
  obtain ⟨P', R', o', j', k, next', mdl', ultra', hk, hLP, hLP', fixed, endpoint, _, _, _,
    pb, ph, pp, pc, ps, pcl, back, countable, models, ⟨KP, ready⟩, KP', ready'⟩ :=
    ep_copy_successor_l hZFC source target owner owner' agree agree' inside branches hierarchy power cover small
      ob op oc hm hn hπ hκπ h₀ h₁ hσ hκσ hLσ hFσ maps loc limit level mdl ultra
  have hP := ready.transitive
  have hP' := ready'.transitive
  have hj := ultra.elementary_l hZF hm.1 mdl.1
  have old_power := (sc_power_iff_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ hσ).mpr op
  have old_cover := (sc_cover_iff_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ hσ).mpr oc
  have old_branches := ob.pull_l hZF owner.omega owner.transitive owner'.transitive owner.omega_mem h₀ h₁ hσ
  have old_hierarchy := (sc_hierarchy_iff_l hZF source.omega source.transitive target.transitive hm hn hπ).mpr hierarchy
  have old_powers := (sc_power_iff_l hZF source.omega source.transitive target.transitive hm hn hπ).mpr power
  have next : Ep_successor_d hZF ω κ L X R F P Rₚ := by
    obtain ⟨X₀, R₂, P₀, S₀, J, O, Z, A, p, U, V, q, u, C, W, i, e,
      mx, nx, system, lim, model, wc, bij, he, _⟩ := ultra
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I mx.1 hm.1
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I nx.1 mdl.1
    exact ⟨J, O, Z, A, p, U, V, q, u, C, W, o, e, system, lim, model, mdl, hP, wc, bij, he⟩
  obtain ⟨W, hWN, wN, wP, _, es, _⟩ := loc.rank_agree_l hZFC source owner ready agree old_branches old_power old_cover
    ((sc_hierarchy_iff_l hZF source.omega source.transitive hP hm mdl hj).mp old_hierarchy)
    ((sc_power_iff_l hZF source.omega source.transitive hP hm mdl hj).mp old_powers) sizes limit next strength
  have loc' := loc.map_l hZF owner.omega owner.transitive owner'.transitive h₀ h₁ hσ hκσ hLσ hFσ
  have strength' := strength.map_l hZF owner.omega owner.transitive owner'.transitive h₀ h₁ hσ owner'.theory hκσ hLσ hFσ
  obtain ⟨W', hWN', wN', wP', _, _, same⟩ := loc'.rank_agree_l hZFC target owner' ready' agree' ob op oc ph pp sizes' limit' next' strength'
  have copy := inaccessible'
  obtain ⟨_, _, above⟩ := copy
  have hωL' : M.mem ω L' := (Formula.satisfies_mem_iff _ _ _).mp ((Formula.satisfies_conj_iff _ _ _).mp above).1
  obtain ⟨KN, ow⟩ := owner'.rebase_l hZF (hσ.1.1.output_mem_of_pairMember hLσ) (limit'.1.transitive ω hωL')
    (sc_ordinal_small_l hZF owner'.omega owner'.transitive h₁ owner'.theory (hσ.1.1.output_mem_of_pairMember hLσ) limit'.1)
  -- 给共同秩层加入支撑端点，整张限制一次回收，随后小壳保持同一端点。
  obtain ⟨C₀, f₀, _, hf₀, iso₀⟩ := wP.code
  obtain ⟨U, f, hU, hf, us, uf⟩ := sc_insert_enumeration_l hZF ready.omega hP mdl ready.theory
    ready.omega_mem ready.cardinal_mem ready.below wP.member hf₀ ready.cardinal_mem (iso₀.bijection_l (ZF.modelsKP hZF))
  have wt := wP.hierarchy.transitive_l hZF hP wP.member
  have ut : M.TransitiveSet U := fun x hx y hy => (us y).mpr (Or.inl
    (((us x).mp hx).elim (fun hx => wt x hx y hy) (fun eq => wP.hierarchy.ordinal_subset_l hZF hP wP.member y (eq ▸ hy))))
  obtain ⟨_, _, sameU, _⟩ := models U f ut hf uf
  obtain ⟨_, τ, hτ, τs⟩ := ep_copy_countable_restriction_l hZF ready ow ready'
    (fun μ hμ => (same μ hμ).subset_l) mdl mdl' hk owner.transitive h₀ h₁ hσ hσN hηN is limit.1 hLσ
    (reg' ω hωL') fixed ut hf uf
  obtain ⟨W₀, hW₀, hWW⟩ := hσ.1.1.2.2 W hWN
  have eq := ((hσ.hierarchy_l hZF owner.omega owner.transitive owner'.transitive h₀ h₁ hLσ hWW).mp wN).unique_l
    hZF owner'.transitive hW₀ hWN' wN'
  subst W₀
  have low x y (hx : M.mem x U) (hxy : Rd_entry_d x y k) : M.mem y W' ∨ y = L' := by
    have hs := (sameU x y hx).mp hxy
    rcases (us x).mp hx with hx | rfl
    · exact Or.inl (((h₁.2 y W').mp ((hσ.relation_l I hZF owner.omega h₀.1 h₁.1 hs hWW).mp
        ((h₀.2 x W).mpr ⟨owner.transitive W hWN x hx, hWN, hx⟩))).2.2)
    · exact Or.inr (hσ.1.1.1.2 x y L' hs hLσ)
  -- 原树的严格秩段先取复制像；内部正则性和旧域可数编号均由实际图传输。
  obtain ⟨B₀, G, hB₀, hG, cert⟩ := rank
  have hα := sc_function_domain_mem_l hZF ready.omega hP mdl ready.theory hG (cert D hD).2.1
  have rank : Vr_d P α D := ⟨B₀, G, hB₀, hG, cert⟩
  have dt := rank.transitive_l hZF hP hD
  have hωD := rank.subset_mem_l hP hD hLD ready.omega_mem ready.below
  have hωα := rank.ordinal_height_l hZF hP hD (ready.omega.isOrdinal hZF) hωD
  have hαl := sc_omega_bound_limit_l hZF ready.omega hP mdl ready.theory ready.omega_mem hα
    (cert D hD).1 ⟨ω, hωα⟩ (regular ω hωα)
  obtain ⟨hWD, wD⟩ := rank.rank_l hZF hP hD hαl hLD wP.member wP.hierarchy
  have hLα := rank.ordinal_height_l hZF hP hD limit.1 hLD
  have wd := (rank.compare_l hZF hP hD wP.member wP.hierarchy ((cert D hD).1.transitive L hLα)).1
  have ud : M.MemberSubset U D := fun x hx => ((us x).mp hx).elim (wd x) (fun eq => eq ▸ hLD)
  obtain ⟨β, _, hαβ⟩ := hk.1.1.2.2 α hα
  obtain ⟨A, a', Q', r, hA, ra, regularA, hDA, modelA, rs, er⟩ :=
    ep_rank_restriction_l hZF ready ready' mdl mdl' hk hD rank regular hd hαβ
  have hLA := ((mdl'.2 L' A).mp ((hk.relation_l I hZF ready.omega mdl.1 mdl'.1 endpoint hDA).mp
    ((mdl.2 L D).mpr ⟨ready.cardinal_mem, hD, hLD⟩))).2.2
  have hLβ := ra.ordinal_height_l hZF hP' hA limit'.1 hLA
  have bo : M.IsOrdinal β := by obtain ⟨_, _, _, _, cert⟩ := ra; exact (cert A hA).1
  have wa := (ra.compare_l hZF hP' hA wP'.member wP'.hierarchy (bo.transitive L' hLβ)).1
  obtain ⟨hPP, ξ, hξ, pξ⟩ := countable ι η hπY hιY ip hσN hηN is
  have hDP := hP' P hPP D hD
  obtain ⟨ζ, hζ, dζ⟩ := ((Sc_index_d.of_injection_l (ZF.modelsKP hZF) (ready.omega.isOrdinal hZF) pξ).mono_l
    (hP D hD)).restrict_l hZF ready'.omega hP' mdl' ready'.theory hDP ready'.omega_mem hξ
  have prescribed x y (hxy : Rd_entry_d x y τ) : Rd_entry_d x y r :=
    (rs.2 x y).mpr ⟨ud x ((τs.2 x y).mp hxy).1, ((τs.2 x y).mp hxy).2⟩
  obtain ⟨B, e, T, j, s, ζ, J, hBN, hBP, bt, mb, _, _, sb, bb, bh, bp, bc, bs, bcl,
    wb, _, db, hs, hζ, elem, ct, keep⟩ := ep_skolem_rank_step_l hZF ready' ow ps back pb ph pp wP'
      hA ra regularA wa hLA hDP dt hd modelA hτ hζ dζ er prescribed
  obtain ⟨Z, hZ, zB⟩ := bh L' sb.cardinal_mem limit'.1
  have eq := vr_cross_l hZF hP' bt wP'.member hZ wP'.hierarchy zB wb
    (fun A _ t ht _ => hP' B hBP t ht)
  subst Z
  have exactness : Es_strength_d N L D := by
    refine ⟨fun β hβ x hx sub => rank.subset_mem_l hP hD (dt L hLD β hβ) (es.1 β hβ x hx sub) sub, ?_⟩
    obtain ⟨x, hx, sub, missing⟩ := es.2
    exact ⟨x, hx, sub, fun hxD => missing (hP D hD x hxD)⟩
  have kept x y (hx : M.mem x W ∨ x = L) (hxy : Rd_entry_d x y σ) : Rd_entry_d x y s := by
    have hxU := (us x).mpr hx
    have hxyk := (sameU x y hxU).mpr hxy
    exact keep x y ((τs.2 x y).mpr ⟨hxU, hxyk⟩) (low x y hxU hxyk)
  have adjacent : Pn_agree_d N N' σ D B s L L' := by
    refine ⟨owner.transitive, owner'.transitive, dt, bt, limit, limit',
      ⟨W, hWN, hWD, wN, wD, fun x y hx => ⟨kept x y (Or.inl hx), ?_⟩⟩,
      ⟨W', hWN', hZ, wN', zB⟩, hLσ, kept L L' (Or.inr rfl) hLσ⟩
    intro hxy
    obtain ⟨v, _, hxv⟩ := hσ.1.1.2.2 x (owner.transitive W hWN x hx)
    exact elem.1.1.1.2 x v y (kept x v (Or.inl hx) hxv) hxy ▸ hxv
  have row : Pn_row_d hZF ω a D B s ζ := ⟨dt, Q, T, e, L', J, hd, mb,
    ⟨sb, bb, bh, bp, bc, bs, bcl (pcl closure)⟩, hs, hζ, elem, ct⟩
  exact ⟨B, s, ζ, hBN, row, exactness, adjacent⟩

end YesMetaZFC.SetTheory.LargeCardinal
