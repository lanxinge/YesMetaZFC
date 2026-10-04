import YesMetaZFC.SetTheory.LargeCardinal.CriticalOrdinal

/-! # 任意派生测度的短交封闭

内部长度 μ<κ 的全体索引都被 j 固定。将原交集的有界定义送过 j，
每个像纤维都包含同一个种子，于是交集自身属于派生超滤；载体可以是任意实际集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project Internal InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Ed_all_d (μ U F x : M.Domain) : Prop := ∀ i, M.mem i μ → ∀ s, M.mem s U →
  Rd_entry_d i s F → M.mem x s

def ed_all_m {d} (μ U F x : Term d) : Formula 1 d := Formula.forallMem μ
  (Formula.forallMem U.weaken (.imp (rd_entry0_m (.bound 1) .newest F.weaken.weaken)
    (.mem x.weaken.weaken .newest)))
derive_free_closed ed_all_m

theorem ed_all_delta_l {d} (μ U F x : Term d) : (ed_all_m μ U F x).IsDelta0 :=
  .forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.mem _ _)))

theorem ed_all_sat_l (hE : Extensional M) {d} (ρ : Env M d) (μ U F x : Term d) :
    Formula.satisfies ρ (ed_all_m μ U F x) ↔ Ed_all_d (μ.eval ρ) (U.eval ρ) (F.eval ρ) (x.eval ρ) := by
  simp only [ed_all_m, Ed_all_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def Ed_complete_d (κ D U : M.Domain) : Prop := ∀ μ, M.mem μ κ → ∀ F, Fn0_d μ U F →
  ∃ r, M.mem r U ∧ ∀ x, M.mem x r ↔ M.mem x D ∧ Ed_all_d μ U F x

def ed_complete_m {d} (κ D U : Term d) : Formula 1 d := Formula.forallMem κ (.forallE (.imp
  (fn0_m (.bound 1) U.weaken.weaken .newest) (.existsE (.conj (.mem .newest U.weaken.weaken.weaken)
    (.forallE (.iff (.mem .newest (.bound 1)) (.conj (.mem .newest D.weaken.weaken.weaken.weaken)
      (ed_all_m (.bound 3) U.weaken.weaken.weaken.weaken (.bound 2) .newest))))))))
derive_free_closed ed_complete_m

theorem ed_complete_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ D U : Term d) :
    Formula.satisfies ρ (ed_complete_m κ D U) ↔ Ed_complete_d (κ.eval ρ) (D.eval ρ) (U.eval ρ) := by
  simp only [ed_complete_m, Ed_complete_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, fn0_sat_l hE, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, ed_all_sat_l hE, Definitional.Term.eval_weaken]
  rfl

variable (hZF : M.Models ZF) {ω X A Y B j : M.Domain} (hω : M.IsOmega ω)
  (h : Spred_emb_d I ω X A Y B j) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
include hZF hω h hX hY

omit hX in
/-- 极限秩层中的派生超滤，对全部内部 μ<κ 长族封闭。 -/
theorem ed_complete_l {δ κ k D D' a U} (hV : V_d I δ X) (hδ : M.IsLimitOrdinal δ)
    (hc : Wd_crit_d I X j κ k) (hjD : M.PairMember I D D' j) (ha : M.mem a D')
    (hU : Ed_filter_d I j a D U) : Ed_complete_d κ D U := by
  have hX := ZF.v_transitive_l I hZF hV
  have hj : M.IsSetFunctionFromTo I j X Y := by
    obtain ⟨_, _, _, _, _, _, hj⟩ := h
    exact hj.1.1
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF D
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  have hPX := ZF.v_power_mem_l I hZF hV hδ (hj.input_mem_of_pairMember hjD) hP
  have hQX := ZF.v_power_mem_l I hZF hV hδ hPX hQ
  have hUP : M.MemberSubset U P := fun s hs => (hP s).mpr ((hU s).mp hs).1
  have hUX := hX Q hQX U ((hQ U).mpr hUP)
  obtain ⟨R, hRX, hκR, hPR⟩ := ZF.v_joint_bound_l I hZF hV hc.source hPX
  obtain ⟨U', _, hjU⟩ := hj.2.2 U hUX
  intro μ hμ F hF
  have hFX : M.mem F X := ZF.v_relation_mem_l I hZF hV hδ hRX (fun p hp => by
    obtain ⟨i, hi, s, hs, hc'⟩ := hF.1 p hp
    exact ⟨i, hκR i (hc.ordinal.transitive μ hμ i hi), s, hPR s (hUP s hs), hc'⟩)
  obtain ⟨F', _, hjF⟩ := hj.2.2 F hFX
  have hjμ := hc.fixed μ hμ
  have hF' := (spred_function_l I hZF hω h hX hY hjμ hjU hjF).mp hF
  let ρ : Env M 3 := ⟨Fin.cases F (Fin.cases U (fun _ => μ)), fun _ => μ⟩
  let ψ : UnarySchema 3 := { body := ed_all_m (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨r, hr⟩ := ZF.separation_exists_d hZF ψ ρ D
  have hr' x : M.mem x r ↔ M.mem x D ∧ Ed_all_d μ U F x :=
    (hr x).trans (and_congr_right fun _ => ed_all_sat_l hZF.1 _ _ _ _ _)
  have hrD : M.MemberSubset r D := fun x hx => ((hr' x).mp hx).1
  obtain ⟨r', _, hjr⟩ := hj.2.2 r (hX P hPX r ((hP r).mpr hrD))
  let φ : Formula 1 5 := Formula.forallMem (.bound 4) (.iff (.mem .newest (.bound 1))
    (ed_all_m (.bound 4) (.bound 3) (.bound 2) .newest))
  have tr := spred_delta_l I hZF hω h hX hY φ (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.iff (.mem _ _) (ed_all_delta_l ..)))
    ⟨Fin.cases r (Fin.cases F (Fin.cases U (Fin.cases μ (fun _ => D)))), fun _ => D⟩
    ⟨Fin.cases r' (Fin.cases F' (Fin.cases U' (Fin.cases μ (fun _ => D')))), fun _ => D'⟩
    (Fin.cases hjr (Fin.cases hjF (Fin.cases hjU (Fin.cases hjμ (fun _ => hjD)))))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, ed_all_sat_l hZF.1] at tr
  have target : ∀ x, M.mem x D' → (M.mem x r' ↔ Ed_all_d μ U' F' x) :=
    tr.mp (fun x hx => (hr' x).trans ⟨And.right, fun ha => ⟨hx, ha⟩⟩)
  refine ⟨r, (hU r).mpr ⟨hrD, r', hjr, (target a ha).mpr ?_⟩, hr'⟩
  intro i hi s hs his
  obtain ⟨t, ht, hit⟩ := hF.2.1 i hi
  obtain ⟨_, t', hjt, hat⟩ := (hU t).mp ht
  have ht' := (ed_member_l I hZF hω h hX hY hjt hjU).mp ht
  have hjI := hc.fixed i (hc.ordinal.transitive μ hμ i hi)
  have hit' := (spred_entry_l I hZF hω h hX hY hjI hjt hjF).mp hit
  exact (hF'.2.2 i hi s hs t' ht' his hit').symm ▸ hat

omit hX hY hω h in
/-- 武丁基数提供实际非主 κ 完备超滤； κ 完备性不作为假设传入。 -/
theorem wd_complete_ultrafilter_l {δ α} (hd : Woodin_d I δ) (hα : M.mem α δ) :
    ∃ ω κ U, M.IsOmega ω ∧ M.mem ω κ ∧ M.mem α κ ∧ M.mem κ δ ∧ M.IsOrdinal κ ∧ FilterZF.Maximal_d (ℳ := M) κ U ∧
      Ed_nonprincipal_d U ∧ Ed_complete_d κ κ U := by
  obtain ⟨ω, X, hω, _, hr, _, hV, hd⟩ := hd
  obtain ⟨F, hF⟩ := hr.2.1
  have hl := hF.1
  obtain ⟨β, hβ, hαβ⟩ := hl.2.2 α hα
  obtain ⟨ν, hν, hβν⟩ := hl.2.2 β hβ
  have hβX : M.MemberSubset β X := fun x hx => ZF.v_ordinal_subset_l I hZF hV x (hl.1.transitive β hβ x hx)
  obtain ⟨κ, hκδ, hk⟩ := hd β hβX
  obtain ⟨N, B, j, W, k, hN, _, _, hW, _, hj, hc, hνk, trace⟩ := hk ν hν
  have hn : ¬ M.mem κ β := by
    intro hκβ
    have hkB := (spred_predicate_l I hZF hω hj hc.image).mp hκβ
    have hβB := spred_transitive_l I hZF hω hj hN (hl.1.mem hβ).transitive k hkB β
      (hc.ordinal_image.transitive ν hνk β hβν)
    exact KP.mem_irrefl_d (ZF.modelsKP hZF) β ((trace β (ZF.v_ordinal_mem_l I hZF hW hβν)).mpr hβB)
  have hακ : M.mem α κ := by
    rcases Structure.IsOrdinal.trichotomy hZF.1 (hl.1.mem hα) hc.ordinal
        (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) α κ) with he | he | he
    · exact (hn ((hZF.1.eq_of_same_members α κ he) ▸ hαβ)).elim
    · exact he
    · exact (hn ((hl.1.mem hβ).transitive α hαβ κ he)).elim
  have hκ : M.mem κ k := by
    have hs : M.MemberSubset κ k := fun x hx =>
      (ed_member_l I hZF hω hj (ZF.v_transitive_l I hZF hV) hN (hc.fixed x hx) hc.image).mp hx
    exact Structure.IsOrdinal.mem_of_properSubset hZF.1 hc.ordinal hc.ordinal_image
      ⟨hs, fun he => hc.moved (hZF.1.eq_of_same_members κ k he)⟩
      (KP.difference_exists_d (ZF.modelsKP hZF) κ k)
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF κ
  obtain ⟨U, hU, hu, hn⟩ := ed_critical_measure_l I hZF hω hj (ZF.v_transitive_l I hZF hV)
    hN hc hκ hP (ZF.v_power_mem_l I hZF hV hF.1 hc.source hP)
  exact ⟨ω, κ, U, hω, ed_critical_omega_l I hZF hω hj (ZF.v_transitive_l I hZF hV) hN hc,
    hακ, hκδ, hc.ordinal, hu, hn, ed_complete_l I hZF hω hj hN hV hl hc hc.image hκ hU⟩

end YesMetaZFC.SetTheory.LargeCardinal
