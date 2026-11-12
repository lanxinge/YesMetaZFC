import YesMetaZFC.SetTheory.LargeCardinal.Game.ImageAbsolute
import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawRankSource

/-! # 给定原关系模型中的实际回答生成原生后继

先在同一所属模型内还原反射回答，再把同一扩展器送入原生后继工厂。
原系统、完整池、共同秩段、数字图和树延伸全部保留；所属模型的原生
理论使用现有内部 ZFC 证书的原生解码实例。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.raw_image_l {ω c₁ N S₀ : M.Domain} (hω : M.IsOmega ω) (nx : ∃ x, M.mem x N) :
    let N₀ := smdl_structure_l I (R := S₀) nx
    ∀ ground : N₀.Models ZFC,
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    let J := kp_pair_l hN
    ∀ U₀ w η C α β ζ : {x : M.Domain // M.mem x N},
    ∀ nc : Nonempty {x : N₀.Domain // N₀.mem x C}, ∀ {s : Nat},
    ∀ (ρ : Env (rt_model_l (M := N₀) C nc) s)
      (o κ δ l n U D u τ Q v b a r q₀ h : Term s) (σ : Fin 7 → Term s),
    let v' := fun t : Term s => Subtype.val (Definitional.Term.eval ρ t)
    ∀ {c X R c' Y S q Γ H k z : M.Domain},
    (Tg_context_d I w.val N S₀ η.val C.val) →
    (Smdl_d I c₁ N S₀) →
    (Zc_model_d I ω c X R) →
    (Smdl_d I c' Y S) →
    (Smap_d I ω c c' X Y q) →
    (Rr_layer_d I ω N S₀ w.val z) →
    (V_d J ζ U₀) →
    ((N₀).IsLimitOrdinal ζ) →
    (∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U₀.val S₀) →
    (M.IsSetInjectionFromTo I k Γ Y) →
    (∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k) →
    (∀ x y, Rd_entry_d x y k → ∀ t, Rd_entry_d t y S ↔ ∃ d, Rd_entry_d d x S₀ ∧ Rd_entry_d d t k) →
    (Rr_closed_d I Y S H) →
    (Rr_small_d I Y S H) →
    ((N₀).mem β U₀) →
    ((N₀).mem (v' κ) β) →
    ((N₀).IsLimitOrdinal α) →
    (V_d J α β) →
    ((N₀).MemberSubset α (v' τ)) →
    (v' o = w) →
    ((N₀).IsRegularCardinal J (v' δ)) →
    (Formula.satisfies ρ (tg_image_m o κ δ l n U D u τ Q v b a r q₀ h σ)) →
    ∃ X' K' R' L F cN dN N' T' jN θ U' D' u' : (N₀).Domain,
      V_d J (v' δ) X' ∧ Ep_source_d J w (v' κ) K' X' R' ∧
      (N₀).mem L (v' δ) ∧ (N₀).mem (v' κ) L ∧ (N₀).mem (v' τ) L ∧
      It_local_d J w X' R' (v' κ) L F ∧ Sc_inaccessible_d (M := N₀) w X' L ∧ Ex_strength_d J w (v' κ) L X' F ∧
      Smem_d J cN X' R' ∧ Smem_d J dN N' T' ∧ It_ultra_d J w (v' κ) L F cN dN jN ∧
      Wd_crit_d J X' jN (v' κ) θ ∧ (N₀).MemberSubset L θ ∧ (N₀).IsLimitOrdinal θ ∧
      Rd_entry_d (M := N₀) (v' U) U' jN ∧ Rd_entry_d (M := N₀) (v' D) D' jN ∧ Rd_entry_d (M := N₀) (v' u) u' jN ∧
      (N₀).mem L C ∧ (∃ W : (N₀).Domain, V_d J L W ∧ (N₀).mem W C ∧ (N₀).mem (v' Q) W) ∧ Tt_pool_d J w (v' l) U' D' ∧
      Tg_reply_d J w (v' l) (v' n) θ (v' τ) U' D' (v' Q) u' (v' v) (v' b)
        (fun i => v' (σ i)) (v' a) ⟨v' r, v' q₀, v' h⟩ ∧
      Er_rank_cut_d hZF ω c X R c' Y S q Γ k N S₀ z c₁ nx hN
        U₀ w (v' κ) L F β X' K' jN := by
  intro N₀ ground hN J U₀ w η C α β ζ nc s ρ o κ δ l n U D u τ Q v b a r q₀ h σ v'
  intro c X R c' Y S q Γ H k z context owner root model hq numbers rank₀ limit₀ carrier fk image pred closed small hβ hκ ha rankB above hw regular valid
  change (o.eval ρ).val = w at hw
  have fs : Fs_read_d (M := N₀) w C := context.finite_l nx hN.1
  have nw := numbers.omega_l I (ZF.modelsKP hZF) hω hN.1
  have rankC : V_d J η C := (rr_rank_native_l I nx hN η C).mp
    ((rr_rank_truth_l I).mpr context.rank)
  obtain ⟨L, W, hLC, hWC, X', K', R', F, cN, dN, N', T', jN, θ, U', D', u',
    rank, source, hLδ, hκL, hτL, queryRank, queryLow, loc, card, strong, mx, my, ultra,
    crit, bound, limit, hU, hD, hu, pool, reply⟩ :=
    tg_image_absolute_l ground nw rankC fs nc ρ o κ δ l n U D u τ Q v b a r q₀ h σ hw regular valid
  -- 两条分支共用极限秩层的实际闭包，扩展器和超幂仍是本次回答的见证。
  have hαL := ordinal_down_l hN ha.1 (loc.ordinals_l hN source.transitive source.code).2 above hτL
  have step := loc.raw_rank_source_l hZFC hω nx ground
    U₀ w (v' κ) L F α β ζ X' K' R' (v' δ) cN dN N' T' jN θ
    owner root model hq numbers rank₀ limit₀ carrier fk image pred closed small hβ hκ ha rankB hαL
    source rank regular.isLimitOrdinal mx my ultra card strong crit.image bound
  exact ⟨X', K', R', L, F, cN, dN, N', T', jN, θ, U', D', u',
    rank, source, hLδ, hκL, hτL, loc, card, strong, mx, my, ultra, crit, bound, limit, hU, hD, hu,
    hLC, ⟨W, queryRank, hWC, queryLow⟩, pool, reply, step⟩


end YesMetaZFC.SetTheory.LargeCardinal
