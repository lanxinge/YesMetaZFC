import YesMetaZFC.SetTheory.LargeCardinal.RankEnumeration
import YesMetaZFC.SetTheory.LargeCardinal.RankLookup
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRepresent

/-! # 足够长的派生扩展器覆盖原强嵌入的指定秩层

目标中的一个短枚举界定最小像枚举的域。每个秩层对象于是成为源中同一个
双坐标函数的种子求值，再进入既有全系统的真实极限。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem er_cover_l (hZFC : M.Models ZFC)
    {ω δ X A Y B j κ k K R L S F J O Z D p T V q C W ν Vν μ₀ g₀ : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X)
    (hr : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ)
    (hs : M.IsStrongLimitCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ) (hκ : M.mem κ δ)
    (h : Spred_emb_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) X j κ k)
    (hL : M.MemberSubset L k) (hLo : M.IsOrdinal L) (hωL : M.MemberSubset ω L)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω L S) (hSY : M.MemberSubset S Y)
    (hF : Es_family_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) j κ L S F)
    (system : Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z D p T V) (limit : Di_limit_d D p T V q C W)
    (hνL : M.mem ν L) (hVν : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ν Vν)
    (hVY : M.MemberSubset Vν Y) (hμL : M.mem μ₀ L) (hgY : M.mem g₀ Y) (hg : Su0_d μ₀ Vν g₀) :
    ∀ x, M.mem x Vν → ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u x := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hj : M.IsSetFunctionFromTo I j X Y := by obtain ⟨_, _, _, _, _, _, e⟩ := h; exact e.1.1
  have hωκ := ed_critical_omega_l I hZF source.omega h source.transitive hY hc
  have hωδ := hr.isCardinal.1.transitive κ hκ ω hωκ
  obtain ⟨U, hU⟩ := ZF.v_exists_l I hZF hc.ordinal
  obtain ⟨H, F₀, U', H', F₁, _, _, hjU, hjH, hjF, _, history, target, levels⟩ :=
    ed_hierarchy_l hZF source.omega hX hr.isLimitOrdinal h hY hκ hc.image hU
  obtain ⟨G, Q, hGX, hQX, hQ, hκQ, _, hG, enums⟩ := er_family_l hZFC source.omega hωδ hr hs hX hκ
  obtain ⟨Q', hQY, hjQ⟩ := hj.2.2 Q hQX
  obtain ⟨G', _, hjG⟩ := hj.2.2 G hGX
  have hG' := (spred_function_l I hZF source.omega h source.transitive hY hc.image hjQ hjG).mp hG
  have hQ' : M.TransitiveSet Q' := by
    have tr := spred_delta_l I hZF source.omega h source.transitive hY (n := 1) (Formula.isTransitive (.bound 0))
      (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _) ⟨fun _ => Q, fun _ => Q⟩ ⟨fun _ => Q', fun _ => Q'⟩ (fun _ => hjQ)
    simp only [Formula.satisfies_isTransitive_iff] at tr
    exact tr.mp hQ
  have hkQ := (ed_member_l I hZF source.omega h source.transitive hY hc.image hjQ).mp hκQ
  have hνk := hL ν hνL
  have hνF := levels ν Vν hνk hVν hVY
  have hU'Y := hj.output_mem_of_pairMember hjU
  have hVνH := ((target U' hU'Y).2.1.bound_l hνF).2
  obtain ⟨p₀, hpQ, hνG⟩ := hG'.2.1 ν hνk
  let φ : Formula 1 6 := er_stage_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  have tr := spred_forall_delta_l I hZF source.omega h source.transitive hY φ
    (by simp -implicitDefEqProofs [φ]) (er_stage_delta_l ..)
    ⟨Fin.cases G (Fin.cases Q (Fin.cases F₀ (Fin.cases H (fun _ => κ)))), fun _ => κ⟩
    ⟨Fin.cases G' (Fin.cases Q' (Fin.cases F₁ (Fin.cases H' (fun _ => k)))), fun _ => k⟩
    (Fin.cases hjG (Fin.cases hjQ (Fin.cases hjF (Fin.cases hjH (fun _ => hc.image)))))
  simp only [φ, er_stage_sat_l hZF.1] at tr
  have stage := tr.mp (fun g _ => er_stage_l hZF hc.ordinal hQ history enums g) g₀ hgY
  obtain ⟨μ, hμQ, g, hggQ, hp, onto, least⟩ := stage ν hνk Vν hVνH p₀ hpQ hνF hνG
  have small := least μ₀ (hL μ₀ hμL) hg
  obtain ⟨zero, hzero, hzω⟩ := source.omega.1.1
  obtain ⟨one, h1, h1ω⟩ := source.omega.1.2 zero hzω
  obtain ⟨two, h2, h2ω⟩ := source.omega.1.2 one h1ω
  have hz2 := (h2 zero).mpr (Or.inl h1.predecessor_mem)
  have h12 := h2.predecessor_mem
  have ne : zero ≠ one := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) one (eq ▸ h1.predecessor_mem)
  obtain ⟨D₀, hD₀X, hD₀⟩ := source.space_l hZF h2ω
  obtain ⟨f, hfX, hf, read⟩ := er_lookup_l hZF source hQ hQX hGX hκQ hG enums h2ω hD₀ hz2 h12
  obtain ⟨f', _, hjf⟩ := hj.2.2 f hfX
  obtain ⟨D₁, _, hjD⟩ := hj.2.2 D₀ hD₀X
  let ψ : Formula 1 6 := Formula.forallMem (.bound 5) (Formula.forallMem (.bound 5)
    (.imp (er_hit_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)
      (rd_entry0_m (.bound 1) .newest (.bound 2))))
  have transfer := spred_delta_l I hZF source.omega h source.transitive hY ψ
    (by simp -implicitDefEqProofs [ψ, Definitional.Formula.FreeClosed])
    (.forallMem _ (.forallMem _ (.imp (er_hit_delta_l ..) (rd_entry0_delta_l ..))))
    ⟨Fin.cases f (Fin.cases one (Fin.cases zero (Fin.cases G (Fin.cases Q (fun _ => D₀))))), fun _ => D₀⟩
    ⟨Fin.cases f' (Fin.cases one (Fin.cases zero (Fin.cases G' (Fin.cases Q' (fun _ => D₁))))), fun _ => D₁⟩
    (Fin.cases hjf (Fin.cases (hc.fixed one (hc.ordinal.transitive ω hωκ one h1ω))
      (Fin.cases (hc.fixed zero (hc.ordinal.transitive ω hωκ zero hzω)) (Fin.cases hjG (Fin.cases hjQ (fun _ => hjD))))))
  simp only [ψ, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, er_hit_sat_l hZF.1, rd_entry0_sat_l hZF.1] at transfer
  have eval := transfer.mp (fun s hs x _ hx => read s x hs hx)
  intro x hx
  obtain ⟨β, hβ, hβx⟩ := onto.2 x hx
  have hβL := hLo.transitive μ₀ hμL β (small β hβ)
  obtain ⟨a₀, ha₀, as⟩ := ZF.exists_constantFunction hZF I (source := two) hνL
  obtain ⟨a, update, ha⟩ := senv_update_exists_l I hZF ha₀ h12 hβL
  have az := (update.2 zero ν).mpr (Or.inr ⟨ne, (as zero ν).mpr ⟨hz2, rfl⟩⟩)
  have a1 := (update.2 one β).mpr (Or.inl ⟨rfl, rfl⟩)
  have hit : Er_hit_d Q' G' zero one a x := ⟨ν, hQ' k hkQ ν hνk, β, hQ' μ hμQ β hβ,
    p₀, hpQ, μ, hμQ, g, hggQ, az, a1, hνG, hp, hβx⟩
  have haD := es_seed_l I hZF source.omega h source.transitive hY
    (hc.fixed two (hc.ordinal.transitive ω hωκ two h2ω)) hc.image hjD hD₀ hL
    (hSY a ((hS a).mpr ⟨two, h2ω, ha⟩)) (fn0_of_function_l (ZF.modelsKP hZF) ha)
  exact ee_represent_l hZF source hX hr.isLimitOrdinal h hY hc hL hωL hS hSY hF system limit
    h2ω hD₀ (fn0_of_function_l (ZF.modelsKP hZF) ha) hfX (hf.mono_target_l (source.transitive Q hQX))
    ⟨f', hjf, eval a haD x (hit.bound_l hQ') hit⟩

end YesMetaZFC.SetTheory.LargeCardinal
