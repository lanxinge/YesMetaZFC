import YesMetaZFC.SetTheory.LargeCardinal.ExtenderModelCode
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopyComponent

/-! # 从有限幂子集的一致性恢复整个小传递集合上的映射

实际枚举把隶属关系编码在 κ² 上。两图搬运同一关系码，Mostowski 唯一性
识别集合的像及枚举图的像；在 κ 上逐点相同便推出整个传递集合上相同。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ea_maps_d.relation_l {ω κ κ' K K₀ X R Y S N R₀ N' R₁ c d b b' π σ T T' : M.Domain}
    (maps : Ea_maps_d ω κ X π σ) (source : Ep_source_d hZF ω κ K X R)
    (owner : Ep_source_d hZF ω κ K₀ N R₀) (hY : M.TransitiveSet Y) (hN' : M.TransitiveSet N')
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
    (maps : Ea_maps_d ω κ X π σ) (source : Ep_source_d hZF ω κ K X R)
    (owner : Ep_source_d hZF ω κ K₀ N R₀) (hY : M.TransitiveSet Y) (hN' : M.TransitiveSet N')
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
  obtain ⟨B₀, F₀, hB₀, hF₀, iso₀⟩ := owner.collapse.collapse_l owner.cardinal_mem
    (hσ.1.1.input_mem_of_pairMember hTσ) owner.cardinal_small (iso.well_founded_l (ZF.modelsKP hZF)) (iso.extensional_l hZF.1)
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
