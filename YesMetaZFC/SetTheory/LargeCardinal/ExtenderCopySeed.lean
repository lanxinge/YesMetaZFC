import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopy
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSeedCollapse

/-! # 双映射复制保持实际坐标类

代表由 π 搬运、支撑由 σ 搬运。两图固定内部自然数，因而复制后的
坐标代表仍读取相同的位置，坐标值则精确变成 σ(α)。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_coord_image_l {ω c d X R Y S π κ κ' D D' i i' f f' n : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (hκ : Rd_entry_d κ κ' π) (hD : Rd_entry_d D D' π) (hi : Rd_entry_d i i' π)
    (hf : Rd_entry_d f f' π) (space : Ep_space_d κ' n D') (coord : Ep_coord_d κ D i f) : Ep_coord_d κ' D' i' f' := by
  have fn := (hπ.function_l hZF hω hX hY hm hn hD hκ hf).mp coord.1
  let φ : Formula 1 4 := Formula.forallMem (.bound 3) (Formula.forallMem (.bound 3)
    (.iff (rd_entry0_m (.bound 1) .newest (.bound 2)) (rd_entry0_m (.bound 3) .newest (.bound 1))))
  have tr := smap_delta_l I hZF hω hX hY hm hn hπ φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.forallMem _ (.iff (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))
    ⟨Fin.cases f (Fin.cases i (Fin.cases κ (fun _ => D))), fun _ => D⟩
    ⟨Fin.cases f' (Fin.cases i' (Fin.cases κ' (fun _ => D'))), fun _ => D'⟩
    (Fin.cases hf (Fin.cases hi (Fin.cases hκ (fun _ => hD))))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1] at tr
  have read := tr.mp (fun s hs x _ => (coord.2 s x).trans ⟨And.right, fun h => ⟨hs, h⟩⟩)
  exact ⟨fn, fun s x => ⟨fun h => ⟨(fn.bound_l h).1, (read s (fn.bound_l h).1 x (fn.bound_l h).2).mp h⟩,
    fun ⟨hs, hi⟩ => (read s hs x (((space s).mp hs).bound_l hi).2).mpr hi⟩⟩

theorem ep_copy_seed_l
    {ω κ κ' K K' L L' X R Y S N R₀ N' R₁ c d b b' π σ F F'
      J O Z A p T V q C W J' O' Z' A' p' T' V' q' C' W' τ α α' E E' : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω κ' K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π) (hκ : Rd_entry_d κ κ' π)
    (owner : M.TransitiveSet N) (owner' : M.TransitiveSet N') (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁)
    (hσ : Smap_d I ω b b' N N' σ) (hωN : M.mem ω N) (hL : Rd_entry_d L L' σ) (hF : Rd_entry_d F F' σ)
    (family : Em_source_d ω κ L X F) (family' : Em_source_d ω κ' L' Y F')
    (h : Ep_system_d hZF ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (h' : Ep_system_d hZF ω κ' L' Y S F' J' O' Z' A' p' T' V') (limit' : Di_limit_d A' p' T' V' q' C' W')
    (hτ : Fn0_d C C' τ)
    (copy : ∀ B E, Rd_entry_d B E τ ↔ M.mem B C ∧ ∃ u, Rd_entry_d u B q ∧ Ec_node_d π σ q' u E)
    (hα : Rd_entry_d α α' σ) (seed : Ep_seed_d κ L q α E) (hEE : Rd_entry_d E E' τ) : Ep_seed_d κ' L' q' α' E' := by
  obtain ⟨n, a, i, D, f, ha, hi, hD, hf, value⟩ := seed
  obtain ⟨hfX, n', hnω, ha', _⟩ := value.source_l hZF family h limit
  have en := ha'.domain_eq_l hZF.1 ha
  subst n'
  obtain ⟨U, haU⟩ := family.total n a hnω ha
  obtain ⟨a', _, haa⟩ := hσ.1.1.2.2 a (rd_entry_transitive_l owner (hσ.1.1.input_mem_of_pairMember hF) haU).1
  have hna := hσ.natural_l hZF source.omega owner owner' h₀ h₁ hωN n hnω
  have hai := hσ.natural_l hZF source.omega owner owner' h₀ h₁ hωN i
    (source.omega.transitive hZF n hnω i (ha.bound_l hi).1)
  have ha' := (hσ.function_l hZF source.omega owner owner' h₀ h₁ hna hL haa).mp ha
  have hi' := (hσ.entry_l hZF source.omega owner owner' h₀ h₁ hai hα haa).mp hi
  have haJ' := (h'.indices a').mpr (ec_support_image_l hZF source.omega owner owner' h₀ h₁ hσ hωN hL haa
    ((h.indices a).mp (value.index_l hZF h limit)))
  obtain ⟨f', hfY, hff⟩ := hπ.1.1.2.2 f hfX
  obtain ⟨D', _, hDD⟩ := hπ.1.1.2.2 D (source.space_mem_l hZF hnω hD)
  have hD' := ep_space_map_l hZF source target hm hn hπ hκ hnω hD hDD
  have hf' := ep_coord_image_l hZF source.omega source.transitive target.transitive hm hn hπ hκ hDD
    (hπ.natural_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem i
      (source.omega.transitive hZF n hnω i (ha.bound_l hi).1)) hff hD' hf
  obtain ⟨E₀, _, value'⟩ := ep_repr_exists_l hZF family' h' limit' haJ' ha' hD' hfY
    (hf'.1.mono_target_l (target.transitive κ' target.cardinal_mem))
  obtain ⟨u, B, hu, hfB, huE⟩ := value
  obtain ⟨v, B', hv, hfB', hvE⟩ := value'
  have hE₀ := (copy E E₀).mpr ⟨(limit.projection.bound_l huE).2, u, huE,
    a, B, a', B', v, hu, haa, ⟨f, f', hfB, hfB', hff⟩, hv, hvE⟩
  have eq := (fn0_function_l (ZF.modelsKP hZF) hτ).1.2 E E₀ E' hE₀ hEE
  exact ⟨n, a', i, D', f', ha', hi', hD', hf', v, B', hv, hfB', eq ▸ hvE⟩

end YesMetaZFC.SetTheory.LargeCardinal
