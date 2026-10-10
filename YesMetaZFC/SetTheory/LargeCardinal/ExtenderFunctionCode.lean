import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRelative
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderNormalSyntax

/-! # 用有限 κ 幂的子集编码 κ 值代表

把函数值追加为末坐标，实际构造其图的有限列编码。子集一致的两个源
因而具有完全相同的 κ 值代表；正规性的跨模型施加将使用这一结论。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_function_code_l {ω κ K X R n D f : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hn : M.mem n ω) (hD : Ep_space_d κ n D)
    (hfX : M.mem f X) (hf : Fn0_d D κ f) :
    ∃ m E A, M.mem m ω ∧ M.SuccessorOf m n ∧ Ep_space_d κ m E ∧ M.mem A X ∧ M.MemberSubset A E ∧
      ∀ t x, Rd_entry_d t x f ↔ M.mem t D ∧ M.mem x κ ∧
        ∃ s, M.mem s A ∧ M.MemberSubset t s ∧ Rd_entry_d n x s := by
  obtain ⟨m, hm, hmω⟩ := source.omega.1.2 n hn
  obtain ⟨E, hEX, hE⟩ := source.space_l hZF hmω
  obtain ⟨c, code⟩ := source.code
  let ρ : Env M 4 := ⟨Fin.cases f (Fin.cases D (Fin.cases κ (fun _ => n))), fun _ => n⟩
  let φ : UnarySchema 4 := { body := en_graph_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨A, hAX, spec⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory
    φ (en_graph_delta_l ..) ρ
    (Fin.cases hfX (Fin.cases (source.space_mem_l hZF hn hD)
      (Fin.cases source.cardinal_mem (fun _ => source.transitive ω source.omega_mem n hn)))) hEX
  have read s : M.mem s A ↔ M.mem s E ∧ En_graph_d n κ D f s :=
    (spec s).trans (and_congr_right fun _ => en_graph_sat_l hZF.1 ..)
  refine ⟨m, E, A, hmω, hm, hE, hAX, fun s hs => ((read s).mp hs).1, fun t x => ⟨?_, ?_⟩⟩
  · intro htx
    have ht := (hD t).mp (hf.bound_l htx).1
    obtain ⟨m', s, _, hs, u, v, last⟩ := ZF.fseq_end_exists_l I hZF source.omega hn
      (fn0_function_l (ZF.modelsKP hZF) ht) (hf.bound_l htx).2
    have eu := last.source.2.2.2.eq hZF.1 hs.2.1
    subst u
    have ev := last.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) ht).2.1
    subst v
    have em := Structure.SuccessorOf.eq hZF.1 last.length_successor hm
    subst m'
    have sub : M.MemberSubset t s := fun p hp => by
      obtain ⟨i, _, y, _, hpi⟩ := ht.1 p hp
      obtain ⟨q, hq, hqs⟩ := ((last.prefix_restriction.2 i y).mp ⟨p, hpi, hp⟩).2
      exact (I).unique hpi hq ▸ hqs
    exact ⟨(hf.bound_l htx).1, (hf.bound_l htx).2, s,
      (read s).mpr ⟨(hE s).mpr (fn0_of_function_l (ZF.modelsKP hZF) hs),
        t, (hf.bound_l htx).1, sub, x, (hf.bound_l htx).2, htx, last.last_value⟩, sub, last.last_value⟩
  · rintro ⟨htD, hxκ, s, hsA, hts, hnx⟩
    obtain ⟨hsE, v, hvD, hvs, y, _, hvy, hny⟩ := (read s).mp hsA
    have ht := (hD t).mp htD
    have hv := (hD v).mp hvD
    have hs := fn0_function_l (ZF.modelsKP hZF) ((hE s).mp hsE)
    have et : v = t := hv.ext_l hZF.1 ht fun i hi => by
      obtain ⟨z, _, hiv⟩ := hv.2.1 i hi
      obtain ⟨w, _, hit⟩ := ht.2.1 i hi
      have ez := hs.1.2 i z w (hiv.elim fun p hp => ⟨p, hp.1, hvs p hp.2⟩)
        (hit.elim fun p hp => ⟨p, hp.1, hts p hp.2⟩)
      exact ⟨z, hiv, ez.symm ▸ hit⟩
    exact et ▸ hs.1.2 n y x hny hnx ▸ hvy

/-- 一致性直接搬运代表函数本身，不要求其定义域上的背景函数全都属于任一源。 -/
theorem Ea_agree_d.function_l {ω κ K X R K' Y S n D f : M.Domain}
    (agree : Ea_agree_d ω κ X Y) (source : Ep_source_d hZF ω κ K X R)
    (target : Ep_source_d hZF ω κ K' Y S) (hn : M.mem n ω) (hD : Ep_space_d κ n D)
    (hfX : M.mem f X) (hf : Fn0_d D κ f) : M.mem f Y := by
  obtain ⟨m, E, A, hm, _, hE, hAX, sub, read⟩ := ep_function_code_l hZF source hn hD hfX hf
  have hAY := (agree m E A hm hE sub).mp hAX
  obtain ⟨c, code⟩ := target.code
  let ρ : Env M 3 := ⟨Fin.cases A (Fin.cases n (fun _ => κ)), fun _ => n⟩
  let φ : BinarySchema 3 := {
    body := .conj (.mem .newest (.bound 4)) (Formula.existsMem (.bound 2)
      (.conj (Formula.subset (.bound 2) .newest) (rd_entry0_m (.bound 4) (.bound 1) .newest))) }
  have sat t x : φ.denote ρ t x ↔ M.mem x κ ∧ ∃ s, M.mem s A ∧ M.MemberSubset t s ∧ Rd_entry_d n x s := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_existsMem_iff, Formula.satisfies_subset_iff, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨g, B, hgY, _, hg, select⟩ := sc_uniform_source_l hZF target.omega target.transitive code target.theory
    φ (.conj (.mem _ _) (.existsMem _ (.conj (.atom _ _ _) (rd_entry0_delta_l ..)))) ρ
    (Fin.cases hAY (Fin.cases (target.transitive ω target.omega_mem n hn) (fun _ => target.cardinal_mem)))
    (target.space_mem_l hZF hn hD) (fun t ht => by
      obtain ⟨x, hx, htx⟩ := hf.2.1 t ht
      exact ⟨x, target.transitive κ target.cardinal_mem x hx, (sat t x).mpr ((read t x).mp htx).2⟩)
  have entry t x (htx : Rd_entry_d t x g) : Rd_entry_d t x f :=
    (read t x).mpr ⟨(hg.bound_l htx).1, (sat t x).mp (select t x htx)⟩
  have eq : g = f := (fn0_function_l (ZF.modelsKP hZF) hg).1.1.eq_of_pairMember_iff hZF.1
    (fn0_function_l (ZF.modelsKP hZF) hf).1.1 fun t x => ⟨entry t x, fun htx => by
      obtain ⟨y, _, hty⟩ := hg.2.1 t (hf.bound_l htx).1
      exact (fn0_function_l (ZF.modelsKP hZF) hf).1.2 t y x (entry t y hty) htx ▸ hty⟩
  exact eq ▸ hgY

end YesMetaZFC.SetTheory.LargeCardinal
