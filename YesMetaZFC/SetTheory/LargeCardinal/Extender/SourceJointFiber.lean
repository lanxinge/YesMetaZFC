import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.JointFiber
import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.Model.SetTheory.Source.Relation
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LocalRead
import YesMetaZFC.SetTheory.LargeCardinal.Extender.LevelTransfer

/-! # 可数约束层的有界读取

有限支撑之间的坐标图属于已有有限 κ 列空间。只在这些实际界中量化，
即可把原 `Ec_ok_d`、`Ec_all_d` 的条件写成源内分离可直接使用的 Δ₀ 公式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ec_ok0_d (ω κ L K a c E s : M.Domain) : Prop := ∀ m, M.mem m ω → ∀ n, M.mem n ω →
  ∀ q, M.mem q K → Fn0_d m n q → Fn0_d n L c → Cp0_d m n L q c a → ∃ r, M.mem r E ∧ Cp0_d m n κ q s r

def ec_ok0_m {d} (ω κ L K a c E s : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken
  Formula.forallMem ω (Formula.forallMem ω.weaken (Formula.forallMem K.weaken.weaken
    (.imp (fn0_m (.bound 2) (.bound 1) .newest) (.imp (fn0_m (.bound 1) (w L) (w c))
      (.imp (cp0_m (.bound 2) (.bound 1) (w L) .newest (w c) (w a))
        (Formula.existsMem (w E) (cp0_m (.bound 3) (.bound 2) (w κ).weaken (.bound 1) (w s).weaken .newest)))))))
derive_free_closed ec_ok0_m

theorem ec_ok0_delta_l {d} (ω κ L K a c E s : Term d) : (ec_ok0_m ω κ L K a c E s).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.imp (fn0_delta_l ..)
    (.imp (fn0_delta_l ..) (.imp (cp0_delta_l ..) (.existsMem _ (cp0_delta_l ..)))))))

theorem ec_ok0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L K a c E s : Term d) :
    Formula.satisfies ρ (ec_ok0_m ω κ L K a c E s) ↔
      Ec_ok0_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (K.eval ρ) (a.eval ρ) (c.eval ρ) (E.eval ρ) (s.eval ρ) := by
  simp only [ec_ok0_m, Ec_ok0_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_existsMem_iff, fn0_sat_l hE, cp0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ec_ok0_iff_l (hKP : M.Models KP) {ω κ L K m n a c E s : M.Domain}
    (hω : M.TransitiveSet ω) (below : M.MemberSubset ω κ) (seq : Fseq_space_d (kp_pair_l hKP) ω κ K)
    (hm : M.mem m ω) (hn : M.mem n ω) (ha : Fn0_d m L a) (hc : Fn0_d n L c) :
    Ec_ok0_d ω κ L K a c E s ↔ Ec_ok_d κ L a c E s := by
  refine ⟨fun h m' n' q hq hc' ha' => ?_, fun h m _ n _ q _ hq hc ha => h m n q hq hc ha⟩
  have en := hc'.domain_eq_l hKP.1 hc
  have em := ha'.1.domain_eq_l hKP.1 ha
  subst n' m'
  exact h m hm n hn q ((seq q).mpr ⟨m, hm, fn0_function_l hKP (hq.mono_target_l fun i hi => below i (hω n hn i hi))⟩) hq hc ha'

def Ec_all0_d (ω κ L K S P A B n c s : M.Domain) : Prop := ∀ i, M.mem i n → ∀ a, M.mem a S →
  ∀ E, M.mem E P → Rd_entry_d i a A → Rd_entry_d i E B → Ec_ok0_d ω κ L K a c E s

def ec_all0_m {d} (ω κ L K S P A B n c s : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken
  Formula.forallMem n (Formula.forallMem S.weaken (Formula.forallMem P.weaken.weaken
    (.imp (rd_entry0_m (.bound 2) (.bound 1) (w A)) (.imp (rd_entry0_m (.bound 2) .newest (w B))
      (ec_ok0_m (w ω) (w κ) (w L) (w K) (.bound 1) (w c) .newest (w s))))))
derive_free_closed ec_all0_m

theorem ec_all0_delta_l {d} (ω κ L K S P A B n c s : Term d) : (ec_all0_m ω κ L K S P A B n c s).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (ec_ok0_delta_l ..)))))

theorem ec_all0_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L K S P A B n c s : Term d) :
    Formula.satisfies ρ (ec_all0_m ω κ L K S P A B n c s) ↔
      Ec_all0_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (K.eval ρ) (S.eval ρ) (P.eval ρ)
        (A.eval ρ) (B.eval ρ) (n.eval ρ) (c.eval ρ) (s.eval ρ) := by
  simp only [ec_all0_m, Ec_all0_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, ec_ok0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ec_all0_iff_l (hKP : M.Models KP) {ω κ L K S P A B n c s : M.Domain}
    (hω : M.TransitiveSet ω) (below : M.MemberSubset ω κ) (seq : Fseq_space_d (kp_pair_l hKP) ω κ K)
    (supports : Fseq_space_d (kp_pair_l hKP) ω L S) (fa : Fn0_d ω S A) (fb : Fn0_d ω P B)
    (hn : M.mem n ω) (hc : Fn0_d n L c) : Ec_all0_d ω κ L K S P A B n c s ↔ Ec_all_d κ L A B n c s := by
  constructor
  · intro h i a E hi hia hiE
    obtain ⟨m, hm, ha⟩ := (supports a).mp (fa.bound_l hia).2
    exact (ec_ok0_iff_l hKP hω below seq hm hn (fn0_of_function_l hKP ha) hc).mp
      (h i hi a (fa.bound_l hia).2 E (fb.bound_l hiE).2 hia hiE)
  · intro h i hi a _ E _ hia hiE
    obtain ⟨m, hm, ha⟩ := (supports a).mp (fa.bound_l hia).2
    exact (ec_ok0_iff_l hKP hω below seq hm hn (fn0_of_function_l hKP ha) hc).mpr (h i a E hi hia hiE)

def Ec_level_at_d (ω κ L K S P A B f n s : M.Domain) : Prop := Fn0_d n κ s ∧
  ∀ c, M.mem c S → Fn0_d n L c → M.MemberSubset c f → Ec_all0_d ω κ L K S P A B n c s

def ec_level_at_m {d} (ω κ L K S P A B f n s : Term d) : Formula 1 d := .conj (fn0_m n κ s)
  (Formula.forallMem S (.imp (fn0_m n.weaken L.weaken .newest) (.imp (Formula.subset .newest f.weaken)
    (ec_all0_m ω.weaken κ.weaken L.weaken K.weaken S.weaken P.weaken A.weaken B.weaken n.weaken .newest s.weaken))))
derive_free_closed ec_level_at_m

theorem ec_level_at_delta_l {d} (ω κ L K S P A B f n s : Term d) : (ec_level_at_m ω κ L K S P A B f n s).IsDelta0 :=
  .conj (fn0_delta_l ..) (.forallMem _ (.imp (fn0_delta_l ..) (.imp (.atom ..) (ec_all0_delta_l ..))))

theorem ec_level_at_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L K S P A B f n s : Term d) :
    Formula.satisfies ρ (ec_level_at_m ω κ L K S P A B f n s) ↔
      Ec_level_at_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (K.eval ρ) (S.eval ρ) (P.eval ρ)
        (A.eval ρ) (B.eval ρ) (f.eval ρ) (n.eval ρ) (s.eval ρ) := by
  simp only [ec_level_at_m, Ec_level_at_d, Formula.satisfies_conj_iff, fn0_sat_l hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, ec_all0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ec_level_at_iff_l (hKP : M.Models KP) {ω κ L K S P A B f n s : M.Domain}
    (hω : M.TransitiveSet ω) (below : M.MemberSubset ω κ) (seq : Fseq_space_d (kp_pair_l hKP) ω κ K)
    (supports : Fseq_space_d (kp_pair_l hKP) ω L S) (fa : Fn0_d ω S A) (fb : Fn0_d ω P B) (hn : M.mem n ω) :
    Ec_level_at_d ω κ L K S P A B f n s ↔ Fn0_d n κ s ∧ ∀ c, Fn0_d n L c → M.MemberSubset c f → Ec_all_d κ L A B n c s :=
  and_congr_right fun _ => ⟨fun h c hc sub => (ec_all0_iff_l hKP hω below seq supports fa fb hn hc).mp
    (h c ((supports c).mpr ⟨n, hn, fn0_function_l hKP hc⟩) hc sub),
    fun h c _ hc sub => (ec_all0_iff_l hKP hω below seq supports fa fb hn hc).mpr (h c hc sub)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 相对测度的源内共同约束层

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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F) (hL : M.mem L X) (hP : M.mem P X)
    (hAX : M.mem A X) (hBX : M.mem B X) (seq : Fseq_space_d I ω L S)
    (fa : Fn0_d ω S A) (fb : Fn0_d ω P B)
    (large : ∀ i a E V, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a V F → M.mem E V)
    (hn : M.mem n ω) (hc : Fn0_d n L c)
    (hinj : ∀ i j x, Rd_entry_d i x c → Rd_entry_d j x c → i = j)
    (hU : Rd_entry_d c U F) (hD : Ep_space_d κ n D) :
    ∃ C, M.mem C X ∧ M.mem C U ∧ ∀ s, M.mem s C ↔ M.mem s D ∧ Ec_all_d κ L A B n c s := by
  obtain ⟨code, model⟩ := source.code
  obtain ⟨S', hS', seq'⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 L hL
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
    (Fin.cases hS (Fin.cases source.finite.mem_l (Fin.cases hL (Fin.cases source.cardinal_mem (fun _ => source.omega_mem))))))))
  obtain ⟨H, T, _, _, hh, spec⟩ := sc_separation_function_l hZF source.omega source.transitive model source.theory φ
    (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (.imp (rd_entry0_delta_l ..) (ec_ok0_delta_l ..))))) ρ params hN hDX
  have row i Z a E (hiZ : Rd_entry_d i Z H) (hia : Rd_entry_d i a A) (hiE : Rd_entry_d i E B) s :
      M.mem s Z ↔ M.mem s D ∧ Ec_ok_d κ L a c E s := by
    obtain ⟨m, hm, ha⟩ := (seq a).mp (fa.bound_l hia).2
    have eqv := ec_ok0_iff_l (ZF.modelsKP hZF) (source.omega.transitive (ZF.modelsKP hZF)) source.below (source.finite_l (ZF.modelsKP hZF)) hm hn
      (fn0_of_function_l (ZF.modelsKP hZF) ha) hc (E := E) (s := s)
    refine (spec i Z hiZ s).trans (and_congr_right fun _ => (sat i s).trans ⟨fun h =>
      eqv.mp (h a (fa.bound_l hia).2 E (fb.bound_l hiE).2 hia hiE), ?_⟩)
    intro h a' _ E' _ hia' hiE'
    have ea := (fn0_function_l (ZF.modelsKP hZF) fa).1.2 i a' a hia' hia
    have eE := (fn0_function_l (ZF.modelsKP hZF) fb).1.2 i E' E hiE' hiE
    subst a' E'
    exact eqv.mpr h
  have member i Z (hiZ : Rd_entry_d i Z H) : M.mem Z U := by
    have hiω := source.omega.transitive (ZF.modelsKP hZF) n hn i (hh.bound_l hiZ).1
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
      (ec_all0_iff_l (ZF.modelsKP hZF) (source.omega.transitive (ZF.modelsKP hZF)) source.below (source.finite_l (ZF.modelsKP hZF)) seq fa fb hn hc))
  refine ⟨C, hCX, ultra.upward W C hWU hCX (fun s hs => ((read s).mp hs).1) (fun s hs =>
    (read s).mpr ⟨ultra.base.bounds W hWU s hs, ?_⟩), read⟩
  intro i a E hi hia hiE
  obtain ⟨Z, _, hiZ⟩ := hh.2.1 i hi
  exact ((row i Z a E hiZ hia hiE s).mp (meet i Z hi hiZ s hs)).2

/-- 同一源内函数图收集全部层；每层满足原共同纤维接口。 -/
theorem ec_source_levels_l {ω κ K X R L F S P A B f : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F) (hL : M.mem L X) (hP : M.mem P X)
    (hAX : M.mem A X) (hBX : M.mem B X) (hfX : M.mem f X) (seq : Fseq_space_d I ω L S)
    (fa : Fn0_d ω S A) (fb : Fn0_d ω P B)
    (large : ∀ i a E U, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a U F → M.mem E U)
    (hf : M.IsSetInjectionFromTo I f ω L) : ∃ H, M.mem H X ∧ Ef_levels_d ω κ H ∧
      Es_fiber_d I ω L F H f ∧ ∀ n C, Rd_entry_d n C H → Ec_level_d κ L A B f n C := by
  obtain ⟨code, model⟩ := source.code
  obtain ⟨S', hS', seq'⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 L hL
  have hS : M.mem S X := hZF.1.eq_of_same_members S' S (fun a => (seq' a).trans (seq a).symm) ▸ hS'
  let ρ : Env M 9 := ⟨Fin.cases f (Fin.cases B (Fin.cases A (Fin.cases P (Fin.cases S
    (Fin.cases K (Fin.cases L (Fin.cases κ (fun _ => ω)))))))), fun _ => ω⟩
  let φ : BinarySchema 9 := {
    body := ec_level_at_m (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6)
      (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat n s : φ.denote ρ n s ↔ Ec_level_at_d ω κ L K S P A B f n s := ec_level_at_sat_l hZF.1 ..
  obtain ⟨H, T, hH, _, hh, spec⟩ := sc_separation_function_l hZF source.omega source.transitive model source.theory φ
    (ec_level_at_delta_l ..) ρ (Fin.cases hfX (Fin.cases hBX (Fin.cases hAX (Fin.cases hP
      (Fin.cases hS (Fin.cases source.finite.mem_l (Fin.cases hL (Fin.cases source.cardinal_mem (fun _ => source.omega_mem)))))))))
    source.omega_mem source.finite.mem_l
  have read n C (hnC : Rd_entry_d n C H) : Ec_level_d κ L A B f n C := by
    have hn := (hh.bound_l hnC).1
    intro s
    refine (spec n C hnC s).trans ((and_congr_right fun _ => (sat n s).trans
      (ec_level_at_iff_l (ZF.modelsKP hZF) (source.omega.transitive (ZF.modelsKP hZF)) source.below (source.finite_l (ZF.modelsKP hZF)) seq fa fb hn)).trans ?_)
    exact ⟨And.right, fun hs => ⟨((source.finite_l (ZF.modelsKP hZF)) s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) hs.1⟩, hs⟩⟩
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

/-! ## 所属模型的共同纤维实现施加源中的全部可数约束

先在施加源构造单射支撑列及约束层族。有限 κ 幂子集的一致性将层族送回
所属模型，其原内部共同纤维条件遂给出同一个 κ 值列，实现所有有限支撑约束。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem es_source_joint_fiber_l {ω κ K X R K' Y R' L F V S P A B : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (owner : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y R')
    (inside : M.MemberSubset Y X) (agree : Ea_agree_d ω κ X Y)
    (branches : Sc_branch_d ω Y) (loc : It_local_d I ω Y R' κ L F)
    (hV : M.mem V Y) (power : FilterZF.Source_d Y K' V)
    (hP : M.mem P X) (hAX : M.mem A X) (hBX : M.mem B X)
    (seq : Fseq_space_d I ω L S) (fa : Fn0_d ω S A) (fb : Fn0_d ω P B)
    (large : ∀ i a E U, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a U F → M.mem E U) :
    ∃ f g, M.mem f X ∧ M.mem g Y ∧ M.IsSetInjectionFromTo I f ω L ∧ Fn0_d ω κ g ∧
      (∀ i a j x, Rd_entry_d i a A → Rd_entry_d j x a → ∃ n, Rd_entry_d n x f) ∧
      ∀ i a E, Rd_entry_d i a A → Rd_entry_d i E B → ∃ r, M.mem r E ∧ Ec_eval_d ω κ L f g a r := by
  have reverse : Ea_agree_d ω κ Y X := fun n D A hn hd sub => (agree n D A hn hd sub).symm
  have family := (loc.measures_l hZF owner.omega (owner.read_source_l hZF) owner.code owner.theory
    (sf_finite_power_l hZF owner.omega owner.transitive owner.code owner.theory (owner.finite_l (ZF.modelsKP hZF)) hV power)).transfer_l reverse
  have coherent := (loc.coherent_l hZF (owner.read_source_l hZF) owner.code).transfer_l hZF reverse
  have ordinal := (loc.ordinals_l (ZF.modelsKP hZF) owner.transitive owner.code).2
  have local_copy := loc
  obtain ⟨_, _, hL, _, pre⟩ := (it_local_mem_l I owner.code).mp local_copy
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at pre
  have below : M.MemberSubset ω L := fun x hx => ordinal.transitive κ pre.1.2.2.2.2.1 x (source.below x hx)
  obtain ⟨f, hfX, hf, covered⟩ := ec_source_cover_l hZF source (inside L hL) below hAX seq fa
  obtain ⟨H, hH, levels, fiber, read⟩ := ec_source_levels_l hZF source family coherent (inside L hL) hP hAX hBX hfX seq fa fb large hf
  obtain ⟨g, hgY, hg⟩ := It_local_d.source_fiber_l hZF source owner inside agree branches loc hH levels fiber
  exact ⟨f, g, hfX, hgY, hf, hg.1, covered, ec_levels_realize_l hZF source.omega seq fa hf covered hg read⟩

end YesMetaZFC.SetTheory.LargeCardinal
