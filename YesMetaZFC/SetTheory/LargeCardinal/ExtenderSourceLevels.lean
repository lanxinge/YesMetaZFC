import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceConstraintSyntax
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRelative
import YesMetaZFC.Model.SetTheory.Internal.SourceFamily

/-! # 相对测度的源内共同约束层

约束及有限交都由源内有界分离构造。向上封闭只用于这些实际属于源的集合，
从而将原共同纤维层构造直接用于相对超滤，不要求源满足完整 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ec_source_test_l {ω κ L X F m n a c U V E D : M.Domain}
    (hco : Ec_source_d I ω κ L X F) (hEX : M.mem E X)
    (hm : M.mem m ω) (hn : M.mem n ω) (ha : Fn0_d m L a) (hc : Fn0_d n L c)
    (hinj : ∀ i j x, Rd_entry_d i x c → Rd_entry_d j x c → i = j)
    (hU : Rd_entry_d a U F) (hV : Rd_entry_d c V F) (hEU : M.mem E U)
    (hE : ∀ r, M.mem r E → Fn0_d m κ r) (hD : Ep_space_d κ n D)
    (base : Base_d D V) : ∃ B, M.mem B V ∧
      ∀ s, M.mem s B ↔ M.mem s D ∧ Ec_ok_d κ L a c E s := by
  classical
  by_cases refines : ∃ q, Fn0_d m n q ∧ Cp0_d m n L q c a
  · obtain ⟨q, hq, hqa⟩ := refines
    obtain ⟨B, hB, hu⟩ := hco m n q c a U V E hm hn hEX hq hc hqa hV hU hE
    exact ⟨B, hu.mpr hEU, fun s => (hB s).trans
      (and_congr (hD s).symm (ec_ok_iff_l hZF.1 hc hinj hq hqa).symm)⟩
  · refine ⟨D, base.top, fun s => ⟨fun hs => ⟨hs, ?_⟩, And.left⟩⟩
    intro m' n' q hq hc' hqa
    have en := hc'.domain_eq_l hZF.1 hc
    subst n'
    have em := hqa.1.domain_eq_l hZF.1 ha
    subst m'
    exact (refines ⟨q, hq, hqa⟩).elim

/-- 前 n 个可读取约束的交属于当前测度，并且是源中的实际集合。 -/
theorem ec_source_meet_l {ω κ K X R L F S P A B n c U D : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F) (hL : M.mem L X) (hP : M.mem P X)
    (hAX : M.mem A X) (hBX : M.mem B X) (seq : Fseq_space_d I ω L S)
    (fa : Fn0_d ω S A) (fb : Fn0_d ω P B)
    (large : ∀ i a E V, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a V F → M.mem E V)
    (hn : M.mem n ω) (hc : Fn0_d n L c)
    (hinj : ∀ i j x, Rd_entry_d i x c → Rd_entry_d j x c → i = j)
    (hU : Rd_entry_d c U F) (hD : Ep_space_d κ n D) :
    ∃ C, M.mem C X ∧ M.mem C U ∧ ∀ s, M.mem s C ↔ M.mem s D ∧ Ec_all_d κ L A B n c s := by
  obtain ⟨code, model⟩ := source.code
  obtain ⟨S', hS', seq'⟩ := source.sequences.space L hL
  have hS : M.mem S X := hZF.1.eq_of_same_members S' S (fun a => (seq' a).trans (seq a).symm) ▸ hS'
  have hC := source.transitive S hS c ((seq c).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) hc⟩)
  have hN := source.transitive ω source.omega_mem n hn
  have hDX := source.space_mem_l hZF hn hD
  have ultra := family.at_l hZF.1 hU hc hD
  let ρ : Env M 9 := ⟨Fin.cases c (Fin.cases B (Fin.cases A (Fin.cases P (Fin.cases S
    (Fin.cases K (Fin.cases L (Fin.cases κ (fun _ => ω)))))))), fun _ => ω⟩
  let φ : BinarySchema 9 := { body := Formula.forallMem (.bound 6) (Formula.forallMem (.bound 6)
    (.imp (rd_entry0_m (.bound 3) (.bound 1) (.bound 6)) (.imp (rd_entry0_m (.bound 3) .newest (.bound 5))
      (ec_ok0_m (.bound 12) (.bound 11) (.bound 10) (.bound 9) (.bound 1) (.bound 4) .newest (.bound 2))))) }
  have sat i s : φ.denote ρ i s ↔ ∀ a, M.mem a S → ∀ E, M.mem E P →
      Rd_entry_d i a A → Rd_entry_d i E B → Ec_ok0_d ω κ L K a c E s := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1, ec_ok0_sat_l hZF.1]; rfl
  have params : ∀ i, M.mem (ρ.bound i) X := Fin.cases hC (Fin.cases hBX (Fin.cases hAX (Fin.cases hP
    (Fin.cases hS (Fin.cases source.finite_mem (Fin.cases hL (Fin.cases source.cardinal_mem (fun _ => source.omega_mem))))))))
  obtain ⟨H, T, _, _, hh, spec⟩ := sc_separation_function_l hZF source.omega source.transitive model source.theory φ
    (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (ec_ok0_delta_l ..))))) ρ params hN hDX
  have row i Z a E (hiZ : Rd_entry_d i Z H) (hia : Rd_entry_d i a A) (hiE : Rd_entry_d i E B) s :
      M.mem s Z ↔ M.mem s D ∧ Ec_ok_d κ L a c E s := by
    obtain ⟨m, hm, ha⟩ := (seq a).mp (fa.bound_l hia).2
    have eqv := ec_ok0_iff_l (ZF.modelsKP hZF) (source.omega.transitive hZF) source.below source.finite hm hn
      (fn0_of_function_l (ZF.modelsKP hZF) ha) hc (E := E) (s := s)
    refine (spec i Z hiZ s).trans (and_congr_right fun _ => (sat i s).trans ⟨fun h =>
      eqv.mp (h a (fa.bound_l hia).2 E (fb.bound_l hiE).2 hia hiE), ?_⟩)
    intro h a' _ E' _ hia' hiE'
    have ea := (fn0_function_l (ZF.modelsKP hZF) fa).1.2 i a' a hia' hia
    have eE := (fn0_function_l (ZF.modelsKP hZF) fb).1.2 i E' E hiE' hiE
    subst a' E'
    exact eqv.mpr h
  have member i Z (hiZ : Rd_entry_d i Z H) : M.mem Z U := by
    have hiω := source.omega.transitive hZF n hn i (hh.bound_l hiZ).1
    obtain ⟨a, _, hia⟩ := fa.2.1 i hiω
    obtain ⟨E, hEP, hiE⟩ := fb.2.1 i hiω
    obtain ⟨m, hm, ha⟩ := (seq a).mp (fa.bound_l hia).2
    obtain ⟨V, haV⟩ := family.total m a hm (fn0_of_function_l (ZF.modelsKP hZF) ha)
    obtain ⟨m', D', _, ha', hd', hv⟩ := family.measure a V haV
    have em := ha'.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) ha)
    subst m'
    obtain ⟨Z', hZ', hz'⟩ := ec_source_test_l hZF coherent (source.transitive P hP E hEP) hm hn
      (fn0_of_function_l (ZF.modelsKP hZF) ha) hc hinj haV hU (large i a E V hia hiE haV)
      (fun r hr => (hd' r).mp (hv.base.bounds E (large i a E V hia hiE haV) r hr)) hD ultra.base
    exact hZF.1.eq_of_same_members Z' Z (fun s => (hz' s).trans (row i Z a E hiZ hia hiE s).symm) ▸ hZ'
  obtain ⟨W, hWU, meet⟩ := finite_meet_l hZF source.omega ultra.base n hn H (hh.retarget_l member)
  let η := ρ.push n
  let ψ : UnarySchema 10 := {
    body := ec_all0_m (.bound 10) (.bound 9) (.bound 8) (.bound 7)
      (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) (.bound 2) .newest }
  obtain ⟨C, hCX, specC⟩ := sc_separate_source_l I hZF source.omega source.transitive model source.theory ψ
    (ec_all0_delta_l ..) η (Fin.cases hN params) hDX
  have read s : M.mem s C ↔ M.mem s D ∧ Ec_all_d κ L A B n c s := (specC s).trans
    (and_congr_right fun _ => (ec_all0_sat_l hZF.1 ..).trans
      (ec_all0_iff_l (ZF.modelsKP hZF) (source.omega.transitive hZF) source.below source.finite seq fa fb hn hc))
  refine ⟨C, hCX, ultra.upward W C hWU hCX (fun s hs => ((read s).mp hs).1) (fun s hs =>
    (read s).mpr ⟨ultra.base.bounds W hWU s hs, ?_⟩), read⟩
  intro i a E hi hia hiE
  obtain ⟨Z, _, hiZ⟩ := hh.2.1 i hi
  exact ((row i Z a E hiZ hia hiE s).mp (meet i Z hi hiZ s hs)).2

/-- 同一源内函数图收集全部层；每层满足原共同纤维接口。 -/
theorem ec_source_levels_l {ω κ K X R L F S P A B f : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F) (hL : M.mem L X) (hP : M.mem P X)
    (hAX : M.mem A X) (hBX : M.mem B X) (hfX : M.mem f X) (seq : Fseq_space_d I ω L S)
    (fa : Fn0_d ω S A) (fb : Fn0_d ω P B)
    (large : ∀ i a E U, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a U F → M.mem E U)
    (hf : M.IsSetInjectionFromTo I f ω L) : ∃ H, M.mem H X ∧ Ef_levels_d ω κ H ∧
      Es_fiber_d I ω L F H f ∧ ∀ n C, Rd_entry_d n C H → Ec_level_d κ L A B f n C := by
  obtain ⟨code, model⟩ := source.code
  obtain ⟨S', hS', seq'⟩ := source.sequences.space L hL
  have hS : M.mem S X := hZF.1.eq_of_same_members S' S (fun a => (seq' a).trans (seq a).symm) ▸ hS'
  let ρ : Env M 9 := ⟨Fin.cases f (Fin.cases B (Fin.cases A (Fin.cases P (Fin.cases S
    (Fin.cases K (Fin.cases L (Fin.cases κ (fun _ => ω)))))))), fun _ => ω⟩
  let φ : BinarySchema 9 := {
    body := ec_level_at_m (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat n s : φ.denote ρ n s ↔ Ec_level_at_d ω κ L K S P A B f n s := ec_level_at_sat_l hZF.1 ..
  obtain ⟨H, T, hH, _, hh, spec⟩ := sc_separation_function_l hZF source.omega source.transitive model source.theory φ
    (ec_level_at_delta_l ..) ρ (Fin.cases hfX (Fin.cases hBX (Fin.cases hAX (Fin.cases hP
      (Fin.cases hS (Fin.cases source.finite_mem (Fin.cases hL (Fin.cases source.cardinal_mem (fun _ => source.omega_mem)))))))))
    source.omega_mem source.finite_mem
  have read n C (hnC : Rd_entry_d n C H) : Ec_level_d κ L A B f n C := by
    have hn := (hh.bound_l hnC).1
    intro s
    refine (spec n C hnC s).trans ((and_congr_right fun _ => (sat n s).trans
      (ec_level_at_iff_l (ZF.modelsKP hZF) (source.omega.transitive hZF) source.below source.finite seq fa fb hn)).trans ?_)
    exact ⟨And.right, fun hs => ⟨(source.finite s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) hs.1⟩, hs⟩⟩
  refine ⟨H, hH, ⟨⟨T, hh⟩, fun n C hnC s hs => ((read n C hnC s).mp hs).1⟩,
    ⟨fn0_of_function_l (ZF.modelsKP hZF) hf.1, fun n hn => ?_⟩, read⟩
  obtain ⟨c, hc, hcf, _⟩ := Descriptive.ds_prefix_l I hZF source.omega hf.1 hn
  have sub := (Descriptive.ds_restrict_iff_l I hc hf.1.1).mp hcf
  obtain ⟨U, hcU⟩ := family.total n c hn (fn0_of_function_l (ZF.modelsKP hZF) hc)
  obtain ⟨n', D, _, hc', hD, _⟩ := family.measure c U hcU
  have en := hc'.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hc)
  subst n'
  obtain ⟨C, _, hCU, hs⟩ := ec_source_meet_l hZF source family coherent hL hP hAX hBX seq fa fb large hn hc'
    (fun i j x hi hj => hf.2 i j x ((hcf.2 i x).mp hi).2 ((hcf.2 j x).mp hj).2) hcU hD
  obtain ⟨Z, _, hnZ⟩ := hh.2.1 n hn
  have eq : Z = C := by
    apply hZF.1.eq_of_same_members Z C
    intro s
    refine (read n Z hnZ s).trans ((and_congr (hD s).symm ?_).trans (hs s).symm)
    refine ⟨fun hall => hall c hc' sub, fun hall d hd hdf => ?_⟩
    have eq := ((Descriptive.ds_restrict_iff_l I (fn0_function_l (ZF.modelsKP hZF) hd) hf.1.1).mpr hdf).eq hZF.1 hcf
    exact eq.symm ▸ hall
  exact ⟨Z, c, U, hnZ, hc', sub, hcU, eq.symm ▸ hCU⟩

end YesMetaZFC.SetTheory.LargeCardinal
