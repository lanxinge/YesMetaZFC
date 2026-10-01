import YesMetaZFC.Model.Forcing.Proper.Hereditary.NameChoice

/-! # 遗传小集合的小名称定理

对原名称作对象模型内的条目归纳。被迫传递容器的单射值与条件共同索引小代表，
其像是小族，再按条件重新装配。单射性保证同一槽位的选择不会漏掉原子名称。
此归纳只应用于下列实际公式，不假定地模型外部良基。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}
variable (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
include O
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 正则 χ 以下，被迫属于小传递容器的任意名称在原条件上有 H(χ) 中的等价名称。 -/
theorem h_name_reduce_l {ω χ H b T μ w f t p} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hB : M.mem B H) (hμ : M.mem μ χ) (hb : M.mem b B)
    (h : Inj_name_d M B R z b T w f) (hw : Check_d M b μ w)
    (hT : Forces_d M B R z (Formula.isTransitive (.bound 0)) (⟨fun _ => T, fun _ => T⟩ : Env M 1) b)
    (ht : Name_d M B t) (hp : Below_d M B R z p b) (htT : Mem_force_d M B R z p t T) :
    ∃ s, M.mem s H ∧ Name_d M B s ∧ Eq_force_d M B R z p s t := by
  let ρ : Env M 6 := (((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push b).push T).push H
  let φ : UnarySchema 6 := {
    body := .imp (name_m (.bound 6) .newest) (.forallE (.imp
      (.conj (below_m (.bound 7) (.bound 6) (.bound 5) .newest (.bound 4))
        (mem_force_m (.bound 7) (.bound 6) (.bound 5) .newest (.bound 1) (.bound 3)))
      (.existsE (.conj (.mem .newest (.bound 3)) (.conj (name_m (.bound 8) .newest)
        (eq_force_m (.bound 8) (.bound 7) (.bound 6) (.bound 1) .newest (.bound 2))))))) }
  have hφ t : φ.denote ρ t ↔ Name_d M B t → ∀ p,
      Below_d M B R z p b ∧ Mem_force_d M B R z p t T →
        ∃ s, M.mem s H ∧ Name_d M B s ∧ Eq_force_d M B R z p s t := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_imp_iff, Formula.satisfies_forall_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_exists_iff, Formula.satisfies_mem_iff,
      name_sat_l M hZF.1, below_sat_l M hZF.1, mem_force_sat_l M hZF.1, eq_force_sat_l M hZF.1]
    rfl
  have hall := entry_ind_l (check_ind_l M hZF) φ ρ (fun t ih => (hφ t).mpr (by
    rintro ht p ⟨hp, htT⟩
    obtain ⟨u, hu⟩ := KP.exists_empty (ZF.modelsKP hZF)
    have huH := ZF.h_subsets_l I hZF hχ.isLimitOrdinal hH hB u (fun x hx => (hu x hx).elim)
    have huN := name_empty_l M (KP.exists_pair (ZF.modelsKP hZF)) B u hu
    obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I μ B
    have hDH := h_product_l hZFC hω hχ hωχ hH (ZF.h_ordinal_l I hZF hχ.isLimitOrdinal hH hμ) hB hD
    obtain ⟨G, A, hG, hGA, hAH, hAN, hg⟩ := hchild_choice_l (B := B) (R := R) (z := z)
      (b := b) (f := f) (t := t) (p := p) hZFC huH huN hD
    obtain ⟨ν, hν, hDν⟩ := ZF.hmem_size_l I hZF ((hH D).mp hDH)
    have hAH' := ZFC.h_small_closed_l I hZFC hω hχ hωχ hH hAH hν
      (ZF.ordinal_image_bound_l I hZF (hχ.isCardinal.1.mem hν) hDν hG hGA)
    let δ := (((ρ.push t).push p).push f).push G
    let ψ : BinarySchema 10 := {
      body := .existsE (.existsE (.conj (kpair_m .newest (.bound 1) (.bound 2))
        (.conj (entry_m .newest (.bound 3) (.bound 4))
          (hchild_m (.bound 13) (.bound 12) (.bound 11) (.bound 10) (.bound 5) (.bound 7)
            (.bound 6) (.bound 1) (.bound 2) (.bound 3))))) }
    have hψ s q : ψ.denote δ s q ↔ ∃ i k, KPair_d M k i q ∧ Entry_d M k s G ∧ Hchild_d M B R z b f t p i q s := by
      simp only [BinarySchema.denote, ψ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
        kpair_sat_l M hZF.1, entry_sat_l M hZF.1, hchild_sat_l hZF.1]
      rfl
    obtain ⟨s, hsN, hsraw, hs⟩ := name_comp_l M hZF ψ δ B A hAN
    have hsH := h_name_bound_l hZFC hω hχ hωχ hH hAH' hB (fun v hv => by
      obtain ⟨a, q, ha, hq, hv, _⟩ := (hsraw v).mp hv
      exact ⟨a, q, hv, ha, hq⟩)
    refine ⟨s, hsH, hsN, (eq_force_unfold_l M hZF hsN ht).mpr ⟨hp.1, ?_, ?_⟩⟩
    · intro a q haq r hr hrq
      obtain ⟨_, hqB, hψ'⟩ := (hs a q).mp haq
      obtain ⟨i, _, _, _, haN, v, d, hv, _, hqd, _, hav⟩ := (hψ a q).mp hψ'
      have hvN := (name_entry_l M ht hv).1
      exact ⟨r, v, d, below_refl_l O hr.1 hr.2.1, hv,
        O.trans r q d hr.1 hqB (name_entry_l M ht hv).2 hrq hqd,
        eq_force_lower_l O hZF haN hvN q r hqB ⟨hr.1, hr.2.1, hrq⟩ hav⟩
    · intro v a hva r hr hra
      have hvN := (name_entry_l M ht hva).1
      have hrb := below_trans_l O hb hr hp
      have hρT : ∀ v : Term 1, Name_d M B (v.eval (⟨fun _ => T, fun _ => T⟩ : Env M 1)) := by
        intro v; cases v <;> exact h.1
      have hrT := (forces_regular_l O hZF _ _ hρT).1 b r hb hrb hT
      have hvr := forced_transitive_l O hZF h.1 ht hvN hr.1 hr.2.1 hrT
        ⟨hr.1, fun q hq => htT.2 q (below_trans_l O hp.1 hq hr)⟩
        (mem_force_entry_l O hZF hr.1 hvN (name_entry_l M ht hva).2 hva hra)
      obtain ⟨q, i, hqr, hi, c, hc, hvc⟩ := fn_name_index_l O hZF (inj_name_function_l h) hb hb hw hrb hvN hvr
      have hqp := below_trans_l O hp.1 hqr hr
      have hqb := below_trans_l O hb hqp hp
      have hqa := O.trans q r a hqr.1 hr.1 (name_entry_l M ht hva).2 hqr.2.2 hra
      have hvq : Mem_force_d M B R z q v T := ⟨hqr.1, fun w hw => hvr.2 w (below_trans_l O hr.1 hw hqr)⟩
      obtain ⟨v', hv'H, hv'N, hv'e⟩ := (hφ v).mp (ih v a hva) hvN q ⟨hqb, hvq⟩
      obtain ⟨k, hk⟩ := (I).total i q
      obtain ⟨a', ha'A, hka⟩ := hG.2.2 k ((hD k).mpr ⟨i, hi, q, hqr.1, hk⟩)
      have hsel := hg k a' i q hka hk ⟨v', hv'H, hv'N, v, a, hva, hqp, hqa, ⟨c, hc, hvc⟩, hv'e⟩
      have he' := (hs a' q).mpr ⟨ha'A, hqr.1, (hψ a' q).mpr ⟨i, k, hk, hka, hsel⟩⟩
      obtain ⟨ha'N, v'', d, hv'', _, _, hci, he⟩ := hsel
      obtain ⟨c', hc', hvc'⟩ := hci
      have hec := check_unique_l M hZF.1 (check_ind_l M hZF) b i c' c hc' hc
      subst c'
      have hv''N := (name_entry_l M ht hv'').1
      have ha'v := eq_force_trans_l O hZF ha'N hv''N hvN he
        (inj_name_eq_l O hZF h hb hqb hv''N hvN (check_name_l M (check_range_l M hZF) hb hc) hvc' hvc)
      exact ⟨q, a', q, hqr, he', O.refl q hqr.1, ha'v⟩))
  exact (hφ t).mp (hall t) ht p ⟨hp, htT⟩

end YesMetaZFC.Model.Forcing.Internal
