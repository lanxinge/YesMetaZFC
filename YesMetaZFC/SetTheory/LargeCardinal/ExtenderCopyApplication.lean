import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCopy

/-! # 同时施加两侧扩展器并自动复制

调用者给出所属模型中的实际测度图、两侧子集一致性及两张初等图。
两侧源内部超幂、整个复制图和交换方块均由同一个入口实际构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ec_ultrapowers_d (hZF : M.Models ZF) (ω κ L X R F κ' L' Y S F' c d π σ : M.Domain) : Prop :=
  ∃ J O Z D p T V q e C W J' O' Z' D' p' T' V' q' e' C' W',
    Ep_system_d hZF ω κ L X R F J O Z D p T V ∧ Di_limit_d D p T V q C W ∧
    Smdl_d (kp_pair_l (ZF.modelsKP hZF)) e C W ∧
    Ep_system_d hZF ω κ' L' Y S F' J' O' Z' D' p' T' V' ∧ Di_limit_d D' p' T' V' q' C' W' ∧
    Smdl_d (kp_pair_l (ZF.modelsKP hZF)) e' C' W' ∧ Ec_limit_d hZF ω c X d Y π σ q q' e C W e' C' W'

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_copy_apply_l
    {ω κ κ' K K' L L' X R Y S N R₀ N' R₁ c d b b' π σ F F' : M.Domain}
    (source : Ep_source_d hZF ω κ K X R)
    (target : Ep_source_d hZF ω κ' K' Y S)
    (hm : Smem_d I c X R)
    (hn : Smem_d I d Y S)
    (hπ : Smap_d I ω c d X Y π) (hκ : Rd_entry_d κ κ' π)
    (owner : M.TransitiveSet N) (owner' : M.TransitiveSet N')
    (h₀ : Smem_d I b N R₀)
    (h₁ : Smem_d I b' N' R₁)
    (hσ : Smap_d I ω b b' N N' σ)
    (theory : Sc_theory_d I ω N R₀) (hωN : M.mem ω N)
    (hL : Rd_entry_d L L' σ) (hF : Rd_entry_d F F' σ)
    (family : Em_source_d ω κ L N F) (family' : Em_source_d ω κ' L' N' F')
    (coherent : Ec_source_d I ω κ L N F)
    (coherent' : Ec_source_d I ω κ' L' N' F')
    (agree : Ea_agree_d ω κ N X) (agree' : Ea_agree_d ω κ' N' Y) (maps : Ea_maps_d ω κ X π σ)
    (hωL : M.MemberSubset ω L) : Ec_ultrapowers_d hZF ω κ L X R F κ' L' Y S F' c d π σ := by
  have hωL' := (hσ.subset_l hZF source.omega owner owner' h₀ h₁ (hσ.omega_l I hZF source.omega owner owner' h₀ h₁ hωN) hL).mp hωL
  obtain ⟨J, O, Z, D, p, T, V, q, e, C, W, h, limit, model, _⟩ := ep_apply_l hZFC source family coherent agree hωL
  obtain ⟨J', O', Z', D', p', T', V', q', e', C', W', h', limit', model', _⟩ := ep_apply_l hZFC target family' coherent' agree' hωL'
  exact ⟨J, O, Z, D, p, T, V, q, e, C, W, J', O', Z', D', p', T', V', q', e', C', W', h, limit, model, h', limit', model',
    ep_copy_l hZFC source target hm hn hπ hκ owner owner' h₀ h₁ hσ theory hωN hL hF
      (family.transfer_l agree) (family'.transfer_l agree') (coherent.transfer_l hZF agree) (coherent'.transfer_l hZF agree') maps
      h limit model h' limit' model'⟩

/-- 从完整测度图自动得到所属模型 N∈X、跨模型施加条件及两张实际恒等图的复制。 -/
theorem ep_owned_copy_l {ω κ L F : M.Domain}
    (hω : M.IsOmega ω) (hωκ : M.MemberSubset ω κ) (hωL : M.MemberSubset ω L)
    (family : Em_family_d ω κ L F)
    (coherent : Es_coherent_d I ω κ L F) :
    ∃ K N R₀ K' X R b c π σ,
      Ep_source_d hZF ω κ K N R₀ ∧ Ep_source_d hZF ω κ K' X R ∧
      Smem_d I b N R₀ ∧ Smem_d I c X R ∧ M.mem F N ∧ M.mem L N ∧ M.mem N X ∧
      Ea_agree_d ω κ N X ∧ Smap_d I ω c c X X π ∧ Smap_d I ω b b N N σ ∧
      (∀ x y, Rd_entry_d x y π ↔ M.mem x X ∧ x = y) ∧
      (∀ x y, Rd_entry_d x y σ ↔ M.mem x N ∧ x = y) ∧
      Ec_ultrapowers_d hZF ω κ L X R F κ L X R F c c π σ := by
  obtain ⟨A, hA⟩ := KP.exists_pair (ZF.modelsKP hZF) F L
  obtain ⟨K, N, R₀, owner, hAN, full₀⟩ := ep_source_exists_l hZFC A hω hωκ
  obtain ⟨K', X, R, source, hNX, full₁⟩ := ep_source_exists_l hZFC N hω hωκ
  have hFN := owner.transitive A hAN F ((hA F).mpr (Or.inl rfl))
  have hLN := owner.transitive A hAN L ((hA L).mpr (Or.inr rfl))
  have agree : Ea_agree_d ω κ N X := fun n D A hn hD hAD =>
    ⟨fun _ => full₁ n D A hn hD hAD, fun _ => full₀ n D A hn hD hAD⟩
  obtain ⟨b, hn⟩ := owner.code
  obtain ⟨c, hm⟩ := source.code
  obtain ⟨π, hπ, ps⟩ := smap_identity_l I hZF (c := c) (X := X) hω
  obtain ⟨σ, hσ, ss⟩ := smap_identity_l I hZF (c := b) (X := N) hω
  have maps : Ea_maps_d ω κ X π σ := fun n D A B hn hD _ hAD hAB =>
    (ss A B).mpr ⟨full₀ n D A hn hD hAD, ((ps A B).mp hAB).2⟩
  exact ⟨K, N, R₀, K', X, R, b, c, π, σ, owner, source, hn, hm, hFN, hLN, hNX, agree, hπ, hσ, ps, ss,
    ep_copy_apply_l hZFC source source hm hm hπ ((ps κ κ).mpr ⟨source.cardinal_mem, rfl⟩)
      owner.transitive owner.transitive hn hn hσ owner.theory owner.omega_mem
      ((ss L L).mpr ⟨hLN, rfl⟩) ((ss F F).mpr ⟨hFN, rfl⟩)
      (family.source_l hZF N) (family.source_l hZF N) (coherent.source_l I N) (coherent.source_l I N)
      agree agree maps hωL⟩

end YesMetaZFC.SetTheory.LargeCardinal
