import YesMetaZFC.Model.Forcing.Iteration.Proper.Thread.Basic

/-! # 内部递归序列的全部前缀一致性

相邻限制等式通过原公式的内部 ω 归纳传播到任意两个指标。即使阶段指标重复，
条件也完全相等，故可以按阶段重新编号为已有融合定理所需的前缀族。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_pr_coherent_l {ω δ F G b D V N A Z E X Q}
    (hω : M.IsOmega ω) (h : Row_system_d I δ F G b)
    (hA : M.IsSetFunctionFromTo I A ω Z) (hm : Cc_increasing_d I A)
    (hQ : M.IsSetFunctionFromTo I Q ω X)
    (hv : ∀ i y, Entry_d M i y Q → Row_pr_thread_d I F G b D N A i y)
    (hs : ∀ i j y z, M.SuccessorOf j i → Entry_d M i y Q → Entry_d M j z Q →
      Row_pr_advance_d I F G b D V N A E i y z) :
    ∀ i j x y α β p τ q σ, Entry_d M i x Q → Entry_d M j y Q →
      Entry_d M i α A → Entry_d M j β A → KPair_d M x p τ → KPair_d M y q σ →
      M.MemberSubset α β → M.IsRestrictionOf I p q α := by
  have rows i x α p τ (hx : Entry_d M i x Q) (hα : Entry_d M i α A) (hp : KPair_d M x p τ) : Row_d M α p := by
    obtain ⟨β, B, R, hβ, hB, hR, q, σ, K, hq, hqm, _⟩ := hv i x hx
    have he := hA.1.2 i β α hβ hα
    obtain ⟨hep, _⟩ := kpair_injective_l M hq hp
    exact he ▸ hep ▸ (h.stages β B R hB hR).rows q hqm.1
  have self {α β p} (hp : Row_d M α p) (hαβ : M.MemberSubset α β) : M.IsRestrictionOf I p p β :=
    ⟨hp.graph, fun k t => ⟨fun hk => ⟨hαβ k (hp.domain k t hk), hk⟩, And.right⟩⟩
  have earlier i x α p τ (hx : Entry_d M i x Q) (hα : Entry_d M i α A) (hp : KPair_d M x p τ) :
      ∀ j, M.mem j ω → ∀ y β q σ, Entry_d M j y Q → Entry_d M j β A → KPair_d M y q σ →
        M.mem i j → M.IsRestrictionOf I p q α := by
    let ρ : Env M 5 := ((((⟨fun _ => i, fun _ => i⟩ : Env M 1).push α).push p).push A).push Q
    let φ : UnarySchema 5 := {
      body := .forallE (.forallE (.forallE (.forallE
        (.imp (entry_m (.bound 4) (.bound 3) (.bound 5))
          (.imp (entry_m (.bound 4) (.bound 2) (.bound 6))
            (.imp (kpair_m (.bound 3) (.bound 1) .newest) (.imp (.mem (.bound 9) (.bound 4))
              (Formula.isRestriction kpair_convention_l (.bound 7) (.bound 1) (.bound 8))))))))) }
    have hφ j : φ.denote ρ j ↔ ∀ y β q σ, Entry_d M j y Q → Entry_d M j β A → KPair_d M y q σ →
        M.mem i j → M.IsRestrictionOf I p q α := by
      simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
        entry_sat_l M hZF.1, kpair_sat_l M hZF.1, Formula.satisfies_mem_iff, Formula.satisfies_isRestriction_iff I]
      rfl
    apply hω.induction (fun j => ∀ y β q σ, Entry_d M j y Q → Entry_d M j β A → KPair_d M y q σ →
      M.mem i j → M.IsRestrictionOf I p q α)
    · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨C, fun j => (hC j).trans (and_congr_right fun _ => hφ j)⟩
    · exact fun e he _ _ _ _ _ _ _ hij => (he i hij).elim
    · intro j hj ih k hk y β q σ hy hβ hq hik
      obtain ⟨z, _, hz⟩ := hQ.2.2 j hj
      obtain ⟨γ, B, R, hγ, _, _, r, η, K, hr, _⟩ := hv j z hz
      obtain ⟨k', γ', B', R', β', C', T', U, hk', hγ', hβ', _, _, _, _, _, hmove⟩ := hs j k z y hk hz hy
      have hek := hZF.1.eq_of_same_members k' k (fun t => (hk' t).trans (hk t).symm)
      subst k'
      have heγ := hA.1.2 j γ' γ hγ' hγ
      have heβ := hA.1.2 k β' β hβ' hβ
      subst γ'; subst β'
      obtain ⟨r', η', q', σ', _, _, _, hr', hq', hpre, _⟩ := hmove
      obtain ⟨her, _⟩ := kpair_injective_l M hr' hr
      obtain ⟨heq, _⟩ := kpair_injective_l M hq' hq
      subst r'; subst q'
      rcases (hk i).mp hik with hij | heij
      · exact (ih z γ r η hz hγ hr hij).comp_l hpre (hm i j α γ hij hα hγ)
      · have heij := hZF.1.eq_of_same_members i j heij
        subst j
        have hez := hQ.1.2 i x z hx hz
        have heγ := hA.1.2 i γ α hγ hα
        have her := (kpair_injective_l M (hez.symm ▸ hr) hp).1
        exact heγ ▸ her ▸ hpre
  intro i j x y α β p τ q σ hx hy hα hβ hp hq hαβ
  have hi := hQ.input_mem_of_pairMember hx
  have hj := hQ.input_mem_of_pairMember hy
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare i hi j hj with he | hij | hji
  · have heij := hZF.1.eq_of_same_members i j he
    subst j
    have hexy := hQ.1.2 i x y hx hy
    have hepq := (kpair_injective_l M (hexy ▸ hp) hq).1
    exact hepq ▸ self (rows i x α p τ hx hα hp) (fun _ h => h)
  · exact earlier i x α p τ hx hα hp j hj y β q σ hy hβ hq hij
  · have hqp := earlier j y β q σ hy hβ hq i hi x α p τ hx hα hp hji
    have hepq := hqp.eq hZF.1 (self (rows i x α p τ hx hα hp) hαβ)
    exact hepq.symm ▸ self (rows i x α p τ hx hα hp) (fun _ h => h)

end YesMetaZFC.Model.Forcing.Internal
