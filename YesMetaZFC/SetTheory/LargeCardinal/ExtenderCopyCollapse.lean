import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopySeed

/-! # 同一复制图在传递后继上的支撑保持

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
      J O Z A p T V q e C W J' O' Z' A' p' T' V' q' e' C' W' τ : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω κ' K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π) (hκπ : Rd_entry_d κ κ' π)
    (owner : M.TransitiveSet N) (owner' : M.TransitiveSet N') (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁)
    (hσ : Smap_d I ω b b' N N' σ) (hωN : M.mem ω N) (hLσ : Rd_entry_d L L' σ) (hFσ : Rd_entry_d F F' σ)
    (hκ : M.TransitiveSet κ) (hL : M.TransitiveSet L) (hωL : M.MemberSubset ω L)
    (family : Em_source_d ω κ L X F) (family' : Em_source_d ω κ' L' Y F')
    (coherent : Ec_source_d I ω κ L X F) (coherent' : Ec_source_d I ω κ' L' Y F')
    (atoms : Ea_atoms_d ω κ L F) (atoms' : Ea_atoms_d ω κ' L' F')
    (normal : En_source_d ω κ L X F) (normal' : En_source_d ω κ' L' Y F')
    (h : Ep_system_d hZF ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (h' : Ep_system_d hZF ω κ' L' Y S F' J' O' Z' A' p' T' V') (limit' : Di_limit_d A' p' T' V' q' C' W')
    (hτ : Smap_d I ω e e' C C' τ)
    (copy : ∀ B E, Rd_entry_d B E τ ↔ M.mem B C ∧ ∃ u, Rd_entry_d u B q ∧ Ec_node_d π σ q' u E)
    (collapse : Ep_collapse_d hZF ω X R q e C W) (collapse' : Ep_collapse_d hZF ω Y S q' e' C' W') :
    ∃ P P' o Rₚ o' Rₚ' g g' k,
      Smem_d I o P Rₚ ∧ Smem_d I o' P' Rₚ' ∧ M.TransitiveSet P ∧ M.TransitiveSet P' ∧
      Wc_graph_d C W g ∧ M.IsSetBijectionFromTo I g C P ∧
      Wc_graph_d C' W' g' ∧ M.IsSetBijectionFromTo I g' C' P' ∧
      Smap_d I ω e o C P g ∧ Smap_d I ω e' o' C' P' g' ∧ Smap_d I ω o o' P P' k ∧
      M.MemberSubset L P ∧ M.MemberSubset L' P' ∧
      (∀ E E' x y, Rd_entry_d E x g → Rd_entry_d E' y g' → (Rd_entry_d x y k ↔ Rd_entry_d E E' τ)) ∧
      (∀ α α', M.mem α L → Rd_entry_d α α' σ → Rd_entry_d α α' k) ∧
      (∀ ξ, M.mem ξ P → M.MemberSubset ω ξ → ∃ K, Ep_source_d hZF ω ξ K P Rₚ) ∧
      (∀ ξ, M.mem ξ P' → M.MemberSubset ω ξ → ∃ K, Ep_source_d hZF ω ξ K P' Rₚ') := by
  obtain ⟨_, _, _, P, g, inv, o, Rₚ, _, _, _, _, hP, wc, bij, mdl, front, _, inverse, back, _, _, next⟩ := collapse
  obtain ⟨_, _, _, P', g', _, o', Rₚ', _, _, _, _, hP', wc', bij', mdl', forward, _, _, _, _, _, next'⟩ := collapse'
  obtain ⟨t, ht, ts⟩ := smap_comp_l I hZF back hτ
  obtain ⟨k, hk, ks⟩ := smap_comp_l I hZF ht forward
  have law E E' x y (hx : Rd_entry_d E x g) (hy : Rd_entry_d E' y g') :
      Rd_entry_d x y k ↔ Rd_entry_d E E' τ := by
    constructor
    · intro hxy
      obtain ⟨_, H, hxH, hHy⟩ := (ks x y).mp hxy
      obtain ⟨_, B, hxB, hBH⟩ := (ts x H).mp hxH
      exact bij.1.2 B E x ((inverse B x).mp hxB) hx ▸ bij'.1.2 H E' y hHy hy ▸ hBH
    · intro hEE
      exact (ks x y).mpr ⟨bij.1.1.output_mem_of_pairMember hx, E',
        (ts x E').mpr ⟨bij.1.1.output_mem_of_pairMember hx, E, (inverse E x).mpr hx, hEE⟩, hy⟩
  have κtr := smap_delta_l I hZF source.omega source.transitive target.transitive hm hn hπ (n := 1)
    (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _)
    ⟨fun _ => κ, fun _ => κ⟩ ⟨fun _ => κ', fun _ => κ'⟩ (fun _ => hκπ)
  have Ltr := smap_delta_l I hZF source.omega owner owner' h₀ h₁ hσ (n := 1)
    (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _)
    ⟨fun _ => L, fun _ => L⟩ ⟨fun _ => L', fun _ => L'⟩ (fun _ => hLσ)
  simp only [Formula.satisfies_isTransitive_iff] at κtr Ltr
  have hωL' := (hσ.subset_l hZF source.omega owner owner' h₀ h₁
    (hσ.omega_l I hZF source.omega owner owner' h₀ h₁ hωN) hLσ).mp hωL
  obtain ⟨cover, fixed⟩ := ep_seed_collapse_l hZF source hκ hL hωL family coherent atoms normal h limit wc
    (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)
  obtain ⟨cover', fixed'⟩ := ep_seed_collapse_l hZF target (κtr.mp hκ) (Ltr.mp hL) hωL' family' coherent'
    atoms' normal' h' limit' wc' (fn0_of_function_l (ZF.modelsKP hZF) bij'.1.1)
  refine ⟨P, P', o, Rₚ, o', Rₚ', g, g', k, mdl, mdl', hP, hP', wc, bij, wc', bij', front, forward, hk, cover, cover', law, ?_, next, next'⟩
  intro α α' hα hαα
  obtain ⟨E, hEC, seed⟩ := ep_seed_exists_l hZF source family h limit hα
  obtain ⟨E', _, hEE⟩ := hτ.1.1.2.2 E hEC
  have seed' := ep_copy_seed_l hZF source target hm hn hπ hκπ owner owner' h₀ h₁ hσ hωN hLσ hFσ
    family family' h limit h' limit' (fn0_of_function_l (ZF.modelsKP hZF) hτ.1.1) copy hαα seed hEE
  exact (law E E' α α' (fixed α E seed) (fixed' α' E' seed')).mpr hEE

end YesMetaZFC.SetTheory.LargeCardinal
