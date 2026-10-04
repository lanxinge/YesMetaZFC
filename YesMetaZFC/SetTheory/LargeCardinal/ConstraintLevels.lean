import YesMetaZFC.SetTheory.LargeCardinal.MeasureConstraints
import YesMetaZFC.SetTheory.LargeCardinal.SupportCompleteness
import YesMetaZFC.SetTheory.Descriptive.Prefix

/-! # 共同纤维所需的实际层族

第 n 层同时检验前 n 个已经能在当前支撑中读取的约束。测度一只由有限交
推出；整个 ω 层族由唯一值收集生成，供既有共同纤维定理直接调用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}

theorem ec_meet_l (hZF : M.Models ZF) {ω κ L F S P A B n c U D : M.Domain}
    (hω : M.IsOmega ω) (hF : Em_family_d ω κ L F)
    (hco : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hA : Fn0_d ω S A) (hB : Fn0_d ω P B)
    (large : ∀ i a E V, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a V F → M.mem E V)
    (hn : M.mem n ω) (hc : Fn0_d n L c)
    (hinj : ∀ i j x, Rd_entry_d i x c → Rd_entry_d j x c → i = j)
    (hU : Rd_entry_d c U F) (hD : ∀ s, M.mem s D ↔ Fn0_d n κ s) (hu : IsFilter_d (ℳ := M) D U) :
    ∃ C, M.mem C U ∧ ∀ s, M.mem s C ↔ M.mem s D ∧ Ec_all_d κ L A B n c s := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ := (((((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push L).push A).push B).push c).push D
  let φ : BinarySchema 6 := { body := .existsE (.existsE (.conj
    (rd_entry_m (.bound 3) (.bound 1) (.bound 7)) (.conj (rd_entry_m (.bound 3) .newest (.bound 6))
      (.forallE (.iff (.mem .newest (.bound 3)) (.conj (.mem .newest (.bound 5))
        (ec_ok_m (.bound 10) (.bound 9) (.bound 2) (.bound 6) (.bound 1) .newest))))))) }
  have sat i Z : φ.denote ρ i Z ↔ ∃ a E, Rd_entry_d i a A ∧ Rd_entry_d i E B ∧
      ∀ s, M.mem s Z ↔ M.mem s D ∧ Ec_ok_d κ L a c E s := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, ec_ok_sat_l hZF.1]; rfl
  have member i Z (hi : M.mem i n) (hz : φ.denote ρ i Z) : M.mem Z U := by
    obtain ⟨a, E, hia, hiE, hz⟩ := (sat i Z).mp hz
    obtain ⟨m, hm, hma⟩ := (hS a).mp (hA.bound_l hia).2
    obtain ⟨V, haV⟩ := hF.total m a hm (fn0_of_function_l (ZF.modelsKP hZF) hma)
    obtain ⟨m', D', _, hma', hd', hv⟩ := hF.measure a V haV
    have e := hma'.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hma)
    subst m'
    obtain ⟨Z', hZ', hz'⟩ := ec_test_l hZF hco hm hn (fn0_of_function_l (ZF.modelsKP hZF) hma) hc hinj
      haV hU (large i a E V hia hiE haV)
      (fun r hr => (hd' r).mp (hv.1.1 E (large i a E V hia hiE haV) r hr)) hD hu
    exact (hZF.1.eq_of_same_members Z' Z (fun s => (hz' s).trans (hz s).symm)) ▸ hZ'
  obtain ⟨H, hh, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := U)
    (fun i hi => by
      have hiω := hω.transitive hZF n hn i hi
      obtain ⟨a, _, hia⟩ := hA.2.1 i hiω
      obtain ⟨E, _, hiE⟩ := hB.2.1 i hiω
      let ψ : UnarySchema 5 := { body := ec_ok_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
      obtain ⟨Z, hz⟩ := ZF.separation_exists_d hZF ψ
        ⟨Fin.cases E (Fin.cases c (Fin.cases a (Fin.cases L (fun _ => κ)))), fun _ => κ⟩ D
      exact ⟨Z, (sat i Z).mpr ⟨a, E, hia, hiE,
        fun s => (hz s).trans (and_congr_right fun _ => ec_ok_sat_l hZF.1 _ _ _ _ _ _ _)⟩⟩)
    (fun i _ Z W hz hw => by
      obtain ⟨a, E, hia, hiE, hz⟩ := (sat i Z).mp hz
      obtain ⟨a', E', hia', hiE', hw⟩ := (sat i W).mp hw
      have e := (fn0_function_l (ZF.modelsKP hZF) hA).1.2 i a' a hia' hia
      subst a'
      have e := (fn0_function_l (ZF.modelsKP hZF) hB).1.2 i E' E hiE' hiE
      subst E'
      exact hZF.1.eq_of_same_members Z W fun s => (hz s).trans (hw s).symm) member
  obtain ⟨K, hKU, hk⟩ := finite_meet_l hZF hω hu.base_l n hn H (fn0_of_function_l (ZF.modelsKP hZF) hh)
  let η := (((((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push L).push A).push B).push n).push c
  let ψ : UnarySchema 6 := { body := ec_all_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hc'⟩ := ZF.separation_exists_d hZF ψ η D
  have specC s : M.mem s C ↔ M.mem s D ∧ Ec_all_d κ L A B n c s :=
    (hc' s).trans (and_congr_right fun _ => ec_all_sat_l hZF.1 _ _ _ _ _ _ _ _)
  refine ⟨C, hu.2.2.1 K C hKU (fun s hs => (specC s).mpr ⟨hu.1 K hKU s hs, ?_⟩)
    (fun s hs => ((specC s).mp hs).1), specC⟩
  intro i a E hi hia hiE
  obtain ⟨Z, _, hiZ⟩ := hh.2.2 i hi
  obtain ⟨a', E', hia', hiE', hz⟩ := (sat i Z).mp ((spec i Z).mp hiZ).2
  have e := (fn0_function_l (ZF.modelsKP hZF) hA).1.2 i a' a hia' hia
  subst a'
  have e := (fn0_function_l (ZF.modelsKP hZF) hB).1.2 i E' E hiE' hiE
  subst E'
  exact ((hz s).mp (hk i Z hi hiZ s hs)).2

def Ec_level_d (κ L A B f n C : M.Domain) : Prop := ∀ s, M.mem s C ↔ Fn0_d n κ s ∧
  ∀ c, Fn0_d n L c → M.MemberSubset c f → Ec_all_d κ L A B n c s

def ec_level_m {d} (κ L A B f n C : Term d) : Formula 1 d := .forallE (.iff (.mem .newest C.weaken)
  (.conj (fn0_m n.weaken κ.weaken .newest) (.forallE (.imp (fn0_m n.weaken.weaken L.weaken.weaken .newest)
    (.imp (Formula.subset .newest f.weaken.weaken)
      (ec_all_m κ.weaken.weaken L.weaken.weaken A.weaken.weaken B.weaken.weaken n.weaken.weaken .newest (.bound 1)))))))
derive_free_closed ec_level_m

theorem ec_level_sat_l (hE : Extensional M) {d} (ρ : Env M d) (κ L A B f n C : Term d) :
    Formula.satisfies ρ (ec_level_m κ L A B f n C) ↔
      Ec_level_d (κ.eval ρ) (L.eval ρ) (A.eval ρ) (B.eval ρ) (f.eval ρ) (n.eval ρ) (C.eval ρ) := by
  simp only [ec_level_m, Ec_level_d, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_imp_iff,
    Formula.satisfies_subset_iff, ec_all_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ec_levels_l (hZF : M.Models ZF) {ω κ L F S P A B f : M.Domain}
    (hω : M.IsOmega ω) (hF : Em_family_d ω κ L F)
    (hco : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hA : Fn0_d ω S A) (hB : Fn0_d ω P B)
    (large : ∀ i a E U, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a U F → M.mem E U)
    (hf : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f ω L) :
    ∃ H, Ef_levels_d ω κ H ∧ Es_fiber_d (kp_pair_l (ZF.modelsKP hZF)) ω L F H f ∧
      ∀ n C, Rd_entry_d n C H → Ec_level_d κ L A B f n C := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω κ
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF K
  let ρ := ((((⟨fun _ => κ, fun _ => κ⟩ : Env M 1).push L).push A).push B).push f
  let φ : BinarySchema 5 := { body := ec_level_m (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat n C : φ.denote ρ n C ↔ Ec_level_d κ L A B f n C := ec_level_sat_l hZF.1 _ _ _ _ _ _ _ _
  obtain ⟨H, hh, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := ω) (target := Q)
    (fun n hn => by
      let ψ : UnarySchema 6 := { body := .forallE (.imp (fn0_m (.bound 2) (.bound 6) .newest)
        (.imp (Formula.subset .newest (.bound 3))
          (ec_all_m (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 2) .newest (.bound 1)))) }
      obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I n κ
      obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF ψ (ρ.push n) D
      refine ⟨C, (sat n C).mpr fun s => (hC s).trans ?_⟩
      have hs : ψ.denote (ρ.push n) s ↔ ∀ c, Fn0_d n L c → M.MemberSubset c f → Ec_all_d κ L A B n c s := by
        simp only [ψ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
          fn0_sat_l hZF.1, Formula.satisfies_subset_iff, ec_all_sat_l hZF.1]; rfl
      exact and_congr ((hD s).trans ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩) hs)
    (fun n _ C D hc hd => hZF.1.eq_of_same_members C D fun s => ((sat n C).mp hc s).trans ((sat n D).mp hd s).symm)
    (fun n C hn hc => (hQ C).mpr fun s hs => (hK s).mpr ⟨n, hn,
      fn0_function_l (ZF.modelsKP hZF) (((sat n C).mp hc s).mp hs).1⟩)
  have levels n C (hnC : Rd_entry_d n C H) := (sat n C).mp ((spec n C).mp hnC).2
  refine ⟨H, ⟨⟨Q, fn0_of_function_l (ZF.modelsKP hZF) hh⟩, fun n C hnC s hs => ((levels n C hnC s).mp hs).1⟩,
    ⟨fn0_of_function_l (ZF.modelsKP hZF) hf.1, fun n hn => ?_⟩, levels⟩
  obtain ⟨c, hc, hcf, _⟩ := Descriptive.ds_prefix_l I hZF hω hf.1 hn
  have sub := (Descriptive.ds_restrict_iff_l I hc hf.1.1).mp hcf
  obtain ⟨U, hcU⟩ := hF.total n c hn (fn0_of_function_l (ZF.modelsKP hZF) hc)
  obtain ⟨n', D, _, hc', hD, hu⟩ := hF.measure c U hcU
  have en := hc'.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hc)
  subst n'
  obtain ⟨C, hCU, hs⟩ := ec_meet_l hZF hω hF hco hS hA hB large hn hc'
    (fun i j x hi hj => hf.2 i j x ((hcf.2 i x).mp hi).2 ((hcf.2 j x).mp hj).2) hcU hD hu.1
  obtain ⟨Z, _, hnZ⟩ := hh.2.2 n hn
  have e : Z = C := by
    apply hZF.1.eq_of_same_members Z C
    intro s
    refine (levels n Z hnZ s).trans ((and_congr (hD s).symm ?_).trans (hs s).symm)
    refine ⟨fun hall => hall c hc' sub, fun hall d hd hdf => ?_⟩
    have eq := ((Descriptive.ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hZF) hd) hf.1.1).mpr hdf).eq hZF.1 hcf
    exact eq.symm ▸ hall
  exact ⟨Z, c, U, hnZ, hc', sub, hcU, e.symm ▸ hCU⟩

end YesMetaZFC.SetTheory.LargeCardinal
