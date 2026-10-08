import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSetInclusion
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopyCollapse

/-! # 沿大模型超幂复制到 j(A)

π 的实际目标是拥有集合 A。先复制到 A 的源内超幂，再用完整集合因子
进入指定大超幂中的 j(A)，最后与原坍塌共轭。常值方块及支撑上的 σ 同时保持。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_set_copy_l {ω κ κ' K K' K₂ L L' X R Y S H Q H' Q' c d b b' π σ F F'
    Z R₂ Z' R₃ z z' j₁ Y' S' d' P Rₚ o j₀ : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (small : Ep_source_d hZF ω κ' K' Y S)
    (ambient : Ep_source_d hZF ω κ' K₂ Z R₂)
    (hm : Smem_d I c X R) (hs : Smem_d I d Y S) (hz : Smem_d I z Z R₂)
    (hz' : Smem_d I z' Z' R₃) (hs' : Smem_d I d' Y' S')
    (hπ : Smap_d I ω c d X Y π) (hκπ : Rd_entry_d κ κ' π)
    (owner : M.TransitiveSet H) (owner' : M.TransitiveSet H')
    (h₀ : Smem_d I b H Q) (h₁ : Smem_d I b' H' Q') (hσ : Smap_d I ω b b' H H' σ)
    (theory : Sc_theory_d I ω H Q) (hωH : M.mem ω H)
    (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ) (maps : Ea_maps_d ω κ X π σ)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (family' : Em_source_d ω κ' L' Z F') (coherent' : Ec_source_d I ω κ' L' Z F')
    (cover : Ea_subset_d ω κ' Z Y) (hωL : M.MemberSubset ω L)
    (mdl : Smem_d I o P Rₚ) (ultra : It_ultra_d hZF ω κ L F c o j₀)
    (big : It_ultra_d hZF ω κ' L' F' z z' j₁) (hY : Rd_entry_d Y Y' j₁) :
    ∃ k, Smap_d I ω o d' P Y' k ∧
      (∀ x x' y y', Rd_entry_d x x' π → Rd_entry_d x y j₀ → Rd_entry_d x' y' j₁ → Rd_entry_d y y' k) ∧
      (M.TransitiveSet κ → M.TransitiveSet L → M.TransitiveSet κ' → M.TransitiveSet L' →
        Ea_atoms_d ω κ L F → En_source_d ω κ L X F → Ea_atoms_d ω κ' L' F' → En_source_d ω κ' L' Z F' →
        ∀ α α', M.mem α L → Rd_entry_d α α' σ → Rd_entry_d α α' k) := by
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
    (fun _ h => h) ((hj₁.small_l hZF ambient.omega ambient.transitive hZ' hz hz' hω).mp
      (ambient.cardinal_small.mono_l ambient.below))
  have inside := ambient.transitive Y (hj₁.1.1.input_mem_of_pairMember hY)
  have agree : Ea_agree_d ω κ' Z Y := fun n D B hn hd sub => ⟨cover n D B hn hd sub, inside B⟩
  have fs := family'.transfer_l agree
  have cs := coherent'.transfer_l hZF agree
  have hωL' := (hσ.subset_l hZF source.omega owner owner' h₀ h₁
    (hσ.omega_l I hZF source.omega owner owner' h₀ h₁ hωH) hLσ).mp hωL
  obtain ⟨J₂, O₂, U₂, A₂, p₂, T₂, V₂, q₂, e₂, C₂, W₂, system₂, limit₂, model₂, elementary₂⟩ :=
    ep_ultrapower_l hZFC small fs cs hωL'
  obtain ⟨τ, _, _, hτ, _, _, copy, _, _, _⟩ := ep_copy_l hZFC source small hm hs hπ hκπ owner owner'
    h₀ h₁ hσ theory hωH hLσ hFσ family fs coherent cs maps system limit model system₂ limit₂ model₂
  obtain ⟨v, hv, values⟩ := ep_set_inclusion_l hZFC ambient target small family' coherent' system₁ limit₁ model₁
    hz hz' hg₁ hj₁ constants₁ square₁ hs hs' hY cover system₂ limit₂ model₂
  obtain ⟨inv, bi, inverse⟩ := ZF.exists_inverseBijectionWithPairs hZF I bij
  have back := smap_of_iso_l I hZF source.omega mdl.1 model bi (fun x y E H hx hy =>
    ((mdl.2 x y).trans ⟨And.right ∘ And.right, fun h =>
      ⟨bi.1.1.input_mem_of_pairMember hx, bi.1.1.input_mem_of_pairMember hy, h⟩⟩).trans
      (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2
        ((inverse x E).mp hx) ((inverse y H).mp hy)).symm)
  obtain ⟨t, ht, ts⟩ := smap_comp_l I hZF back hτ
  obtain ⟨k, hk, ks⟩ := smap_comp_l I hZF ht hv
  have lift E H x y (hEx : Rd_entry_d E x g) (hEH : Rd_entry_d E H τ) (hHy : Rd_entry_d H y v) : Rd_entry_d x y k :=
    (ks x y).mpr ⟨bij.1.1.output_mem_of_pairMember hEx, H,
      (ts x H).mpr ⟨bij.1.1.output_mem_of_pairMember hEx, E, (inverse x E).mpr hEx, hEH⟩, hHy⟩
  -- 常值像的比较在同一目标超幂内完成，目标小源无需等于 j(A) 的全部代表域。
  have commute x x' y y' (hxx : Rd_entry_d x x' π) (hxy : Rd_entry_d x y j₀) (hxy' : Rd_entry_d x' y' j₁) :
      Rd_entry_d y y' k := by
    obtain ⟨E, hxE, hEy⟩ := (square.2 x y).mp hxy
    obtain ⟨u, a, B, f, D, _, sf, fc, hfB, pair, huE⟩ := constants x E hxE
    have fv : Ep_repr_d q a f E := ⟨u, B, pair, hfB, huE⟩
    obtain ⟨hfX, n, hnω, ha, D', space, fn⟩ := fv.source_l hZF family system limit
    have eq := fn.domain_eq_l hZF.1 (sf.function_l source.transitive)
    subst D'
    obtain ⟨U, haU⟩ := family.total n a hnω ha
    obtain ⟨a', _, haa⟩ := hσ.1.1.2.2 a (rd_entry_transitive_l owner (hσ.1.1.input_mem_of_pairMember hFσ) haU).1
    obtain ⟨f', hfY, hff⟩ := hπ.1.1.2.2 f hfX
    obtain ⟨D', _, hDD⟩ := hπ.1.1.2.2 D (source.space_mem_l hZF hnω space)
    have space' := ep_space_map_l hZF source small hm hs hπ hκπ hnω space hDD
    have ha' := (hσ.function_l hZF source.omega owner owner' h₀ h₁
      (hσ.natural_l hZF source.omega owner owner' h₀ h₁ hωH n hnω) hLσ haa).mp ha
    have haJ' := (system₂.indices a').mpr (ec_support_image_l hZF source.omega owner owner' h₀ h₁ hσ hωH hLσ haa
      ((system.indices a).mp (fv.index_l hZF system limit)))
    have ff' := (hπ.sfun_l hZF source.omega source.transitive small.transitive hm hs hDD hff sf).function_l small.transitive
    have fc' := rs_constant_image_l hZF source.omega source.transitive small.transitive hm hs hπ hDD hxx hff fc
    obtain ⟨E', hE', fv'⟩ := ep_repr_exists_l hZF fs system₂ limit₂ haJ' ha' space' hfY ff'
    have hEE := ep_copy_repr_l limit.projection copy haa hff fv fv'
    obtain ⟨z', _, hEz⟩ := hv.1.1.2.2 E' hE'
    obtain ⟨H, rep, hHz⟩ := values a' f' E' z' fv' hEz
    obtain ⟨c, _, cf, cc, H', rep', hHy⟩ := ep_value_constant_l hZF ambient family' system₁ limit₁ constants₁ square₁
      hnω (rep.index_l hZF system₁ limit₁) ha' space' (inside x' (hπ.1.1.output_mem_of_pairMember hxx)) hxy'
    have same := ep_repr_constant_l hZF ambient family' system₁ limit₁ (ff'.mono_target_l inside) cf fc' cc rep rep'
    have yz := hg₁.1.1.1.2 H' z' y' (same ▸ hHz) hHy
    exact yz ▸ lift E E' y z' hEy hEE hEz
  refine ⟨k, hk, commute, fun hκ hL hκ' hL' atoms normal atoms' normal' => ?_⟩
  have fixed := (ep_seed_collapse_l hZF source hκ hL hωL family coherent atoms normal system limit wc
    (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)).2
  have fixed' := (ep_seed_collapse_l hZF ambient hκ' hL' hωL' family' coherent' atoms' normal' system₁ limit₁ wc₁
    (fn0_of_function_l (ZF.modelsKP hZF) bij₁.1.1)).2
  intro α α' hα hαα
  obtain ⟨E, hE, seed⟩ := ep_seed_exists_l hZF source family system limit hα
  obtain ⟨E', hE', hEE⟩ := hτ.1.1.2.2 E hE
  obtain ⟨x, _, hEx⟩ := hv.1.1.2.2 E' hE'
  obtain ⟨n, a, i, D, f, ha, hi, hd, fc, rep⟩ := ep_copy_seed_l hZF source small hm hs hπ hκπ owner owner' h₀ h₁ hσ
    hωH hLσ hFσ family fs system limit system₂ limit₂ (fn0_of_function_l (ZF.modelsKP hZF) hτ.1.1) copy hαα seed hEE
  obtain ⟨H, rep', hHx⟩ := values a f E' x rep hEx
  have hHα := fixed' α' H ⟨n, a, i, D, f, ha, hi, hd, fc, rep'⟩
  exact hg₁.1.1.1.2 H x α' hHx hHα ▸ lift E E' α x (fixed α E seed) hEE hEx

end YesMetaZFC.SetTheory.LargeCardinal
