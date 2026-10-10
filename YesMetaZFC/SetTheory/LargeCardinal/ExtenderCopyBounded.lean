import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedTransport
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedValue
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFunctionMap
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopySeed

/-! # 复制图在临界点像以下等于所属嵌入

所属源中的完整求值图沿 σ 传输，再由原代表辨认复制目标中的同一个图。
κ 值函数的两种像已由有限幂编码证明相同。源映射可落入较小的拥有集合；
代表方程仍在指定外层超幂中读取，端点由调用处的常值交换方块处理。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 任意常值代表的复制与原源嵌入交换，且与两侧原有常值支撑的选择无关。 -/
theorem ep_copy_constant_l
    {ω κ κ' K K' L L' X R Y S N R₀ N' R₁ c d b b' π σ F F'
      J O Z A p T V q C W J' O' Z' A' p' T' V' q' C' W' τ D₀ a₀ f₀ H D₁ a₁ f₁ H' x x' : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω κ' K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π) (hκπ : Rd_entry_d κ κ' π)
    (hN : M.TransitiveSet N) (hN' : M.TransitiveSet N') (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁)
    (hσ : Smap_d I ω b b' N N' σ) (hωN : M.mem ω N) (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (family : Em_source_d ω κ L X F) (family' : Em_source_d ω κ' L' Y F')
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (system' : Ep_system_d I ω κ' L' Y S F' J' O' Z' A' p' T' V') (limit' : Di_limit_d A' p' T' V' q' C' W')
    (copy : ∀ E E', Rd_entry_d E E' τ ↔ M.mem E C ∧ ∃ u, Rd_entry_d u E q ∧ Ec_node_d π σ q' u E')
    (hxx : Rd_entry_d x x' π) (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ x f₀) (fv : Ep_repr_d q a₀ f₀ H)
    (ff' : Fn0_d D₁ Y f₁) (constant' : Rs_const_d D₁ x' f₁) (fv' : Ep_repr_d q' a₁ f₁ H') : Rd_entry_d H H' τ := by
  obtain ⟨hfX, n, hnω, ha, D₂, space, fn⟩ := fv.source_l hZF family system limit
  have eq := fn.domain_eq_l hZF.1 ff
  subst D₂
  obtain ⟨U, haU⟩ := family.total n a₀ hnω ha
  obtain ⟨a', _, haa⟩ := hσ.1.1.2.2 a₀ (rd_entry_transitive_l hN (hσ.1.1.input_mem_of_pairMember hFσ) haU).1
  obtain ⟨f', hfY, hff⟩ := hπ.1.1.2.2 f₀ hfX
  obtain ⟨D', _, hDD⟩ := hπ.1.1.2.2 D₀ (source.space_mem_l hZF hnω space)
  have space' := ep_space_map_l hZF source target hm hn hπ hκπ hnω space hDD
  have ha' := (hσ.function_l hZF source.omega hN hN' h₀ h₁
    (hσ.natural_l hZF source.omega hN hN' h₀ h₁ hωN n hnω) hLσ haa).mp ha
  have haJ' := (system'.indices a').mpr (ec_support_image_l hZF source.omega hN hN' h₀ h₁ hσ
    hωN hLσ haa ((system.indices a₀).mp (fv.index_l hZF system limit)))
  have fn' := (hπ.sfun_l hZF source.omega source.transitive target.transitive hm hn hDD hff (source.function_l hZF hfX ff)).function_l target.transitive
  have fc' := rs_constant_image_l hZF source.omega source.transitive target.transitive hm hn hπ hDD hxx hff constant
  obtain ⟨E', _, ev⟩ := ep_repr_exists_l hZF family' system' limit' haJ' ha' space' hfY fn'
  have eq := ep_repr_constant_l hZF target family' system' limit' fn' ff' fc' constant' ev fv'
  exact ep_copy_repr_l limit.projection copy haa hff fv (eq ▸ ev)

theorem ep_copy_bounded_l
    {ω κ κ' K K' K₀ K₁ L L' X R Y S X' R' N R₀ N' R₁ c d b b' π σ F F'
      J O Z A p T V q C W J' O' Z' A' p' T' V' q' C' W' P P' g g' k
      D₀ a₀ f₀ H D₁ a₁ f₁ H' Γ Γ' Θ D Q e : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω κ' K' X' R')
    (hY : M.TransitiveSet Y)
    (owner : Ep_source_d hZF ω κ K₀ N R₀) (owner' : Ep_source_d hZF ω κ' K₁ N' R₁)
    (agree : Ea_agree_d ω κ X N) (agree' : Ea_agree_d ω κ' X' N')
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁) (hσ : Smap_d I ω b b' N N' σ)
    (hκπ : Rd_entry_d κ κ' π) (hκσ : Rd_entry_d κ κ' σ) (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (maps : Ea_maps_d ω κ X π σ) (family : Em_source_d ω κ L X F) (family' : Em_source_d ω κ' L' X' F')
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (system' : Ep_system_d I ω κ' L' X' R' F' J' O' Z' A' p' T' V') (limit' : Di_limit_d A' p' T' V' q' C' W')
    (wc : Wc_graph_d C W g) (bij : M.IsSetBijectionFromTo I g C P)
    (wc' : Wc_graph_d C' W' g') (bij' : M.IsSetBijectionFromTo I g' C' P')
    (copied : ∀ a a' f f' x y, Rd_entry_d a a' σ → Rd_entry_d f f' π →
      Ep_value_d q g a f x → Ep_value_d q' g' a' f' y → Rd_entry_d x y k)
    (ff : Fn0_d D₀ X f₀) (constant : Rs_const_d D₀ κ f₀) (fv : Ep_repr_d q a₀ f₀ H) (hHΓ : Rd_entry_d H Γ g)
    (ff' : Fn0_d D₁ X' f₁) (constant' : Rs_const_d D₁ κ' f₁) (fv' : Ep_repr_d q' a₁ f₁ H') (hHΓ' : Rd_entry_d H' Γ' g')
    (hΓ' : M.TransitiveSet Γ') (hΓσ : Rd_entry_d Γ Θ σ) (collapse : Eb_collapse_d ω κ L K₀ N κ F D Q Γ e) :
    Θ = Γ' ∧ ∀ x x', M.mem x Γ → Rd_entry_d x x' σ → Rd_entry_d x x' k := by
  have data := collapse
  obtain ⟨J₀, P₀, G₀, U₀, V₀, pool, _, _, _, hQ, he, _, _, _, _, map, _⟩ := data
  have evaluation := (collapse.realize_l hZF source owner agree family system limit wc bij ff constant fv hHΓ map.transitive).2
  obtain ⟨D', _, hDD⟩ := hσ.1.1.2.2 D pool.carrier
  obtain ⟨Q', _, hQQ⟩ := hσ.1.1.2.2 Q hQ
  obtain ⟨e', _, hee⟩ := hσ.1.1.2.2 e he
  obtain ⟨K₂, _, hKK⟩ := hσ.1.1.2.2 K₀ owner.finite_mem
  have finite := hσ.sequences_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ owner'.theory owner.omega_mem hκσ hKK owner.finite
  have eq := hZF.1.eq_of_same_members K₂ K₁ (fun f => (finite f).trans (owner'.finite f).symm)
  subst K₂
  have collapse' := collapse.map_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ hσ owner'.theory
    owner.omega_mem hκσ hLσ hKK hκσ hFσ hDD hQQ hΓσ hee
  obtain ⟨same, evaluation'⟩ := collapse'.realize_l hZF target owner' agree' family' system' limit' wc' bij' ff' constant' fv' hHΓ' hΓ'
  refine ⟨same, ?_⟩
  intro x x' hx hxx
  obtain ⟨u, hu, hux⟩ := map.onto x hx
  obtain ⟨_, a, f, pair, E, ev, hEx⟩ := (evaluation u x).mp hux
  obtain ⟨n, a', D₃, f', hnω, haJ, ha, space, hfN, fn, pair'⟩ := pool.read_l hZF owner hu
  obtain ⟨ea, ef⟩ := kpair_injective_l M pair' pair
  subst a' f'
  have hfX := (ev.source_l hZF family system limit).1
  obtain ⟨f', _, hff⟩ := hπ.1.1.2.2 f hfX
  have hffσ := maps.function_l hZF source owner hY owner'.transitive hm hn hπ h₀ h₁ hσ hκπ hκσ hnω space hfX fn hff
  obtain ⟨a', _, haa⟩ := hσ.1.1.2.2 a (owner.transitive J₀ pool.indices a haJ)
  obtain ⟨u', _, huu⟩ := hσ.1.1.2.2 u (owner.transitive D pool.carrier u hu)
  have tr := smap_delta_l I hZF source.omega owner.transitive owner'.transitive h₀ h₁ hσ (n := 3)
    (kpair0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (kpair0_delta_l ..)
    ⟨Fin.cases f (Fin.cases a (fun _ => u)), fun _ => u⟩ ⟨Fin.cases f' (Fin.cases a' (fun _ => u')), fun _ => u'⟩
    (Fin.cases hffσ (Fin.cases haa (fun _ => huu)))
  simp only [kpair0_sat_l hZF.1] at tr
  have pair' := tr.mp pair
  have hux' := (hσ.entry_l hZF source.omega owner.transitive owner'.transitive h₀ h₁ huu hxx hee).mp hux
  obtain ⟨_, a'', f'', pair'', E', ev', hE'x'⟩ := (evaluation' u' x').mp hux'
  obtain ⟨ea, ef⟩ := kpair_injective_l M pair'' pair'
  subst a'' f''
  exact copied a a' f f' x x' haa hff ⟨E, ev, hEx⟩ ⟨E', ev', hE'x'⟩

end YesMetaZFC.SetTheory.LargeCardinal
