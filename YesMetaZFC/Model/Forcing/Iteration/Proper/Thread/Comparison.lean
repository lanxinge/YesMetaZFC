import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Order
import YesMetaZFC.Model.Forcing.Iteration.Proper.Prefix.Step

/-! # 任意早期名称的逐阶段比较不变量

起点可以是递归初值，也可以是某一步刚选择的稠密名称。旧名称在后期前缀上的
成员与序比较由统一二步序传回；原公式内部归纳将实际限制比较保持到全部后期。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_bound_l {ω δ F G b β D V N A Z E X Q α B R τ p j x₀ γ₀ R₀ p₀}
    (hω : M.IsOmega ω) (h : Row_system_d I δ F G b)
    (hD : Entry_d M β D F) (hV : Entry_d M β V G)
    (hA : M.IsSetFunctionFromTo I A ω Z) (hm : Cc_increasing_d I A)
    (hi : ∀ i γ, Entry_d M i γ A → M.MemberSubset γ β)
    (hQ : M.IsSetFunctionFromTo I Q ω X)
    (hv : ∀ i x, Entry_d M i x Q → Row_pr_thread_d I F G b D N A i x)
    (hs : ∀ i k x y, M.SuccessorOf k i → Entry_d M i x Q → Entry_d M k y Q →
      Row_pr_advance_d I F G b D V N A E i x y)
    (hB : Entry_d M α B F) (hR : Entry_d M α R G) (hτ : Name_d M B τ)
    (hx₀ : Entry_d M j x₀ Q) (hγ₀ : Entry_d M j γ₀ A)
    (hR₀ : Entry_d M γ₀ R₀ G) (hxτ : KPair_d M x₀ p₀ τ)
    (hαγ : M.MemberSubset α γ₀) (hpp₀ : M.IsRestrictionOf I p p₀ α)
    (h₀ : Row_cut_lower_d I α B R b D N τ p γ₀ R₀ p₀) :
    ∀ k y γ C T q σ, (M.mem j k ∨ j = k) → Entry_d M k y Q → Entry_d M k γ A →
      Entry_d M γ C F → Entry_d M γ T G → KPair_d M y q σ → Row_cut_lower_d I α B R b D N τ p γ T q := by
  have s := h.stages β D V hD hV
  have t := h.stages α B R hB hR
  obtain ⟨C₀, hC₀, cn, _⟩ := zf_check_l M hZF s.base D
  obtain ⟨ν, hν, vn, _⟩ := zf_check_l M hZF s.base V
  obtain ⟨named, order⟩ := row_pr_order_l hZF hω h hD hV hA hi hQ hv hs hC₀ hν
  have coh := row_pr_coherent_l hZF hω h hA hm hQ hv hs
  have pre : ∀ k γ, Entry_d M k γ A → (M.mem j k ∨ j = k) → M.MemberSubset γ₀ γ := by
    intro k γ hk hjk
    rcases hjk with hjk | rfl
    · exact hm j k γ₀ γ hjk hγ₀ hk
    · exact hA.1.2 j γ₀ γ hγ₀ hk ▸ (fun _ h => h)
  have start k y γ C T q σ (he : j = k) (hy : Entry_d M k y Q) (hγ : Entry_d M k γ A)
      (hC : Entry_d M γ C F) (hT : Entry_d M γ T G) (hyq : KPair_d M y q σ) :
      Row_cut_lower_d I α B R b D N τ p γ T q := by
    subst k
    have heγ := hA.1.2 j γ₀ γ hγ₀ hγ
    subst γ
    have heT := h.relations.2.1.2 γ₀ R₀ T hR₀ hT
    have hey := hQ.1.2 j x₀ y hx₀ hy
    have heq := (kpair_injective_l M (hey ▸ hxτ) hyq).1
    exact heT ▸ heq ▸ h₀
  let ρ : Env M 13 := ⟨Fin.cases F (Fin.cases G (Fin.cases b (Fin.cases D (Fin.cases N (Fin.cases A
    (Fin.cases Q (Fin.cases α (Fin.cases B (Fin.cases R (Fin.cases τ (Fin.cases p (fun _ => j)))))))))))), fun _ => b⟩
  let φ : UnarySchema 13 := {
    body := .imp (.disj (.mem (.bound 13) .newest) (Formula.extensionalEq (.bound 13) .newest))
      (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
        (.imp (entry_m (.bound 6) (.bound 5) (.bound 13))
          (.imp (entry_m (.bound 6) (.bound 4) (.bound 12))
            (.imp (entry_m (.bound 4) (.bound 3) (.bound 7))
              (.imp (entry_m (.bound 4) (.bound 2) (.bound 8))
                (.imp (kpair_m (.bound 5) (.bound 1) .newest)
                  (row_cut_lower_m (.bound 14) (.bound 15) (.bound 16) (.bound 9) (.bound 10) (.bound 11)
                    (.bound 17) (.bound 18) (.bound 4) (.bound 2) (.bound 1))))))))))))) }
  have hφ k : φ.denote ρ k ↔ (M.mem j k ∨ j = k) → ∀ y γ C T q σ,
      Entry_d M k y Q → Entry_d M k γ A → Entry_d M γ C F → Entry_d M γ T G → KPair_d M y q σ →
        Row_cut_lower_d I α B R b D N τ p γ T q := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, Formula.satisfies_disj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_forall_iff,
      entry_sat_l M hZF.1, kpair_sat_l M hZF.1, row_cut_lower_sat_l I hZF.1]
    rfl
  -- 归纳命题量化当前状态的全部解码；初始指标无需是外部标准自然数。
  have all : ∀ k, M.mem k ω → (M.mem j k ∨ j = k) → ∀ y γ C T q σ,
      Entry_d M k y Q → Entry_d M k γ A → Entry_d M γ C F → Entry_d M γ T G → KPair_d M y q σ →
        Row_cut_lower_d I α B R b D N τ p γ T q := by
    apply hω.induction (fun k => (M.mem j k ∨ j = k) → ∀ y γ C T q σ,
      Entry_d M k y Q → Entry_d M k γ A → Entry_d M γ C F → Entry_d M γ T G → KPair_d M y q σ →
        Row_cut_lower_d I α B R b D N τ p γ T q)
    · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨C, fun k => (hC k).trans (and_congr_right fun _ => hφ k)⟩
    · intro e he hje y γ C T q σ hy hγ hC hT hyq
      rcases hje with hje | hje
      · exact (he j hje).elim
      · exact start e y γ C T q σ hje hy hγ hC hT hyq
    · intro k hk ih l hl hjl y γ C T q σ hy hγ hC hT hyq
      rcases hjl with hjl | hjl
      · have hjk : M.mem j k ∨ j = k := ((hl j).mp hjl).imp id (hZF.1.eq_of_same_members j k)
        obtain ⟨x, _, hx⟩ := hQ.2.2 k hk
        obtain ⟨l', ξ, B', R', γ', C', T', U, hl', hkξ, hlγ, hB', hR', hC', hT', _, hmove⟩ := hs k l x y hl hx hy
        have hel := hZF.1.eq_of_same_members l' l (fun z => (hl' z).trans (hl z).symm)
        subst l'
        have heγ := hA.1.2 l γ' γ hlγ hγ
        subst γ'
        have heC := h.conditions.2.1.2 γ C' C hC' hC
        have heT := h.relations.2.1.2 γ T' T hT' hT
        subst C'; subst T'
        obtain ⟨r, η, q', σ', K, ν', ζ, hxr, hyq', hrq, hσ, hK, hν', _, hσK, _, hση, hNew⟩ := hmove
        obtain ⟨rfl, rfl⟩ := kpair_injective_l M hyq hyq'
        have heν := check_unique_l M hZF.1 (check_ind_l M hZF) b V ν' ν hν' hν
        subst ν'
        obtain ⟨r', η', K', hxr', hrm, hη, hK', hηK⟩ := row_pr_thread_resolve_l I hA.1.2 h.conditions.2.1.2
          h.relations.2.1.2 (hv k x hx) hkξ hB' hR'
        obtain ⟨rfl, rfl⟩ := kpair_injective_l M hxr hxr'
        obtain ⟨q', σ', _, hyq', hqm, _⟩ := row_pr_thread_resolve_l I hA.1.2 h.conditions.2.1.2
          h.relations.2.1.2 (hv l y hy) hγ hC hT
        obtain ⟨rfl, rfl⟩ := kpair_injective_l M hyq hyq'
        have a := h.stages ξ B' R' hB' hR'
        have c := h.stages γ C T hC hT
        have hγ₀ξ := pre k ξ hkξ hjk
        have hαξ : M.MemberSubset α ξ := fun z hz => hγ₀ξ z (hαγ z hz)
        have hξγ := hm k l ξ γ hl.predecessor_mem hkξ hγ
        have f := h.links α ξ B R B' R' hB hR hB' hR' hαξ
        have g := h.links ξ γ B' R' C T hB' hR' hC hT hξγ
        have v := h.links ξ β B' R' D V hB' hR' hD hV (hi k ξ hkξ)
        have hτ' := row_name_l f hτ
        have hcn := check_name_l M (check_range_l M hZF) a.base hC₀
        have hvn := check_name_l M (check_range_l M hZF) a.base hν
        -- 先在同一个旧偏序中比较，再将原名称的成员与序关系反射回当前前缀。
        have comp : Step_le_d M D V D ν x x₀ := by
          rcases hjk with hjk | he
          · exact order j k x₀ x hjk hx₀ hx
          · subst k
            have hex := hQ.1.2 j x x₀ hx hx₀
            subst x
            exact step_named_refl_l s.order hZF cn vn s.base
              (check_preord_force_l s.order hZF s.base hC₀ hν ⟨s.order.refl, s.order.trans⟩
                (below_refl_l s.order s.base (fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ s.base)))) (named j x₀ hx₀)
        obtain ⟨hrp, hητ⟩ := (step_le_iff_l hxr hxτ).mp comp
        obtain ⟨p₀', τ', hxτ', _, hp₀b, hτC⟩ := named j x₀ hx₀
        obtain ⟨rfl, rfl⟩ := kpair_injective_l M hxτ hxτ'
        have hτC' := (row_mem_force_l hZF a.order s.order v hrm.1 hτ' hcn).mpr
          ((regular_mem_l s.order τ C₀).1 p₀ r hp₀b.1 hrp hτC)
        have hητ' := (row_rel_force_l hZF a.order s.order v hrm.1 hvn hη hτ').mpr hητ
        have hσC := row_quot_subset_l hZF a.order a.base hK (fun _ hz _ => hz) hC₀ (a.top r hrm.1) hσK
        have hηC := row_quot_subset_l hZF a.order a.base hK' (fun _ hz _ => hz) hC₀ (a.top r hrm.1) hηK
        have hf := check_preord_force_l a.order hZF a.base hC₀ hν ⟨s.order.refl, s.order.trans⟩
          ⟨hrm.1, hrm.2.1, a.top r hrm.1⟩
        have hστ := (forced_preord_l a.order hZF hcn hvn hrm.1 hrm.2.1 hf).2
          σ η τ hσ hη hτ' hσC hηC hτC' hση hητ'
        exact row_cut_step_l hZF hαξ hξγ t a c.order f g
          (h.links γ β C T D V hC hT hD hV (hi l γ hγ)) hqm.1
          (hpp₀.comp_l (coh j k x₀ x γ₀ ξ p₀ τ r η hx₀ hx hγ₀ hkξ hxτ hxr hγ₀ξ) hαγ)
          hrq hτ hσ hK hσK hν hστ (ih hjk x ξ B' R' r η hx hkξ hB' hR' hxr) hNew
      · exact start l y γ C T q σ hjl hy hγ hC hT hyq
  exact fun k y γ C T q σ hjk hy hγ hC hT hyq => all k (hQ.input_mem_of_pairMember hy) hjk y γ C T q σ hy hγ hC hT hyq

end YesMetaZFC.Model.Forcing.Internal
