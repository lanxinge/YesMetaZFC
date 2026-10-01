import YesMetaZFC.Model.Forcing.Proper.Generic.WitnessReflection
import YesMetaZFC.Model.Forcing.Proper.Generic.Countable
import YesMetaZFC.Model.SetTheory.Internal.ElementaryClub
import YesMetaZFC.Model.Forcing.Proper.Syntax
import YesMetaZFC.SetTheory.CumulativeRank

/-! # 存在见证提升的实际初等模型装配

给定 proper 偏序和一条原公式，有限反射构造统一的传递环境，随后在 proper club
内构造初等 N 及主加强。所有来自 N 的名称参数共用该 N，不再预先固定参数组。
此处仍固定原公式；全部内部公式码的初等提升由 InternalGenericElementaryHull 装配。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 从 properness 自动取得初等 N 及主加强 q，对所有 N 参数统一提升指定公式的存在见证。 -/
theorem ng_witness_hull_l {ω A p} (hω : M.IsOmega ω) (hP : Proper_d I ω B R z)
    (hA : M.CardinalLessOrEqual I A ω) (hp : M.mem p B) (hpz : p ≠ z)
    {n} (φ : UnarySchema n) :
    ∃ X c T N d S q, M.TransitiveSet X ∧ Ssub_d I c d X T N S ∧ Selem_d I ω c d ∧
      M.MemberSubset A N ∧ M.CardinalLessOrEqual I N ω ∧ Below_d M B R z q p ∧ Mstr_d M B R z N q ∧
      ∀ U (hU : Generic_d M B R z U), U q →
        let E := extension_l M hZF B R z U
        let J := kpair_interpretation_l E (extension_ext_l O hZF hU) (internal_pair_l O hZF hU)
        ∃ Y w : E.Domain, (∀ x, x ∈ Y ↔ Ng_mem_d M B R z U N x) ∧
          E.IsOmega w ∧ E.CardinalLessOrEqual J Y w ∧ ∀ ρ : Env M n, (∀ i, M.mem (ρ.bound i) N) →
            ∀ η : Env E n, Env_val_d hZF ρ η → (∃ x, φ.denote η x) → ∃ y, y ∈ Y ∧ φ.denote η y := by
  obtain ⟨A', ha⟩ := KP.exists_insert (ZF.modelsKP hZF) A B
  obtain ⟨A'', hb⟩ := KP.exists_insert (ZF.modelsKP hZF) A' R
  obtain ⟨A₃, hc⟩ := KP.exists_insert (ZF.modelsKP hZF) A'' z
  obtain ⟨A₄, hd'⟩ := KP.exists_insert (ZF.modelsKP hZF) A₃ p
  have hn := ZF.countable_insert_l I hZF hω (ZF.countable_insert_l I hZF hω
    (ZF.countable_insert_l I hZF hω (ZF.countable_insert_l I hZF hω hA ha) hb) hc) hd'
  let F : List Lr_formula := [⟨n+5, ng_data_m φ, ng_data_closed_l φ⟩, ⟨n+3, ng_exists_m φ, ng_exists_closed_l φ⟩]
  obtain ⟨α, X, hV, hAX, hr⟩ := ZF.lr_finite_l I hZF F A₄
  have hData := hr ⟨n+5, ng_data_m φ, ng_data_closed_l φ⟩ (List.mem_cons_self ..)
  have hExists := hr ⟨n+3, ng_exists_m φ, ng_exists_closed_l φ⟩ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hX := ZF.v_transitive_l I hZF hV
  have hBA := (hd' B).mpr (Or.inl ((hc B).mpr (Or.inl ((hb B).mpr (Or.inl ((ha B).mpr (Or.inr rfl)))))))
  obtain ⟨C, hC, hm⟩ := hP X (hX B (hX A₄ hAX B hBA))
  obtain ⟨c, T, hM, hT⟩ := smdl_membership_l I hZF ⟨A₄, hAX⟩
  obtain ⟨N, d, S, hS, he, hAN, hNC⟩ := selem_club_hull_l I hZFC hω hM hC (hX A₄ hAX) hn
  have h₃ x (hx : M.mem x A₃) := hAN x ((hd' x).mpr (Or.inl hx))
  have h₂ x (hx : M.mem x A'') := h₃ x ((hc x).mpr (Or.inl hx))
  have h₁ x (hx : M.mem x A') := h₂ x ((hb x).mpr (Or.inl hx))
  obtain ⟨q, hqp, hqN⟩ := hm N hNC p (hAN p ((hd' p).mpr (Or.inr rfl))) hp hpz
  have hn := (hC.members N hNC).2
  refine ⟨X, c, T, N, d, S, q, hX, hS, he,
    fun x hx => h₁ x ((ha x).mpr (Or.inl hx)), hn, hqp, hqN, ?_⟩
  have hBN := h₁ B ((ha B).mpr (Or.inr rfl))
  have hRN := h₂ R ((hb R).mpr (Or.inr rfl))
  have hzN := h₃ z ((hc z).mpr (Or.inr rfl))
  intro U hU hq
  obtain ⟨Y, w, hY, hw, hy⟩ := ng_countable_l O hZF hU hω hn
  refine ⟨Y, w, hY, hw, hy, fun ρ hρ η hVal hx => ?_⟩
  obtain ⟨W, D, hWN, hDN, hd⟩ := ng_witness_reflect_l hZF I hω hS he hT hX hBN hRN hzN φ hData hExists ρ hρ
  obtain ⟨y, hy, hφ⟩ := hd.generic_l O hZF I hω hS he hT hX hWN hDN hqN hU hq η hVal hx
  exact ⟨y, (hY y).mpr hy, hφ⟩

end YesMetaZFC.Model.Forcing.Internal
