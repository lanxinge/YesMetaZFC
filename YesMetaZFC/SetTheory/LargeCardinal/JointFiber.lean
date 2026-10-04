import YesMetaZFC.SetTheory.LargeCardinal.ConstraintLevels

/-! # 共同纤维同时实现全部可数有限支撑约束

一个共同的单射坐标列和一个 κ 值列同时解释所有支撑，且解释与坐标投影
交换。这里允许可数列中的支撑大小无界；没有把有限定向性改成可数定向性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ec_eval_d (ω κ L f g a r : M.Domain) : Prop := ∃ m q, Fn0_d m ω q ∧
  Cp0_d m ω L q f a ∧ Cp0_d m ω κ q g r

def ec_eval_m {d} (ω κ L f g a r : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (fn0_m (.bound 1) ω.weaken.weaken .newest)
    (.conj (cp0_m (.bound 1) ω.weaken.weaken L.weaken.weaken .newest f.weaken.weaken a.weaken.weaken)
      (cp0_m (.bound 1) ω.weaken.weaken κ.weaken.weaken .newest g.weaken.weaken r.weaken.weaken))))
derive_free_closed ec_eval_m

theorem ec_eval_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω κ L f g a r : Term d) :
    Formula.satisfies ρ (ec_eval_m ω κ L f g a r) ↔
      Ec_eval_d (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (f.eval ρ) (g.eval ρ) (a.eval ρ) (r.eval ρ) := by
  simp only [ec_eval_m, Ec_eval_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, cp0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ec_eval_exists_l (hZF : M.Models ZF) {ω κ L m f g a : M.Domain} (ha : Fn0_d m L a)
    (hf : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f ω L) (hg : Fn0_d ω κ g)
    (cover : ∀ i x, Rd_entry_d i x a → ∃ j, Rd_entry_d j x f) : ∃ r, Ec_eval_d ω κ L f g a r := by
  obtain ⟨q, hq, hqa⟩ := ec_factor_l hZF ha hf cover
  obtain ⟨r, hr⟩ := cp0_exists_l (ZF.modelsKP hZF) hq hg
  exact ⟨r, m, q, hq, hqa, hr⟩

theorem ec_eval_unique_l (hE : Extensional M) {ω κ L f g a r s : M.Domain}
    (hf : ∀ i j x, Rd_entry_d i x f → Rd_entry_d j x f → i = j) (hg : Fn0_d ω κ g)
    (hr : Ec_eval_d ω κ L f g a r) (hs : Ec_eval_d ω κ L f g a s) : r = s := by
  obtain ⟨m, q, hq, hqa, hqr⟩ := hr
  obtain ⟨n, t, ht, hta, hts⟩ := hs
  have e := hta.1.domain_eq_l hE hqa.1
  subst n
  have e := ec_factor_unique_l hE hf ht hq hta hqa
  subst t
  exact cp0_unique_l hE hq hg hqr hts

theorem ec_eval_type_l (hE : Extensional M) {ω κ L f g a r n : M.Domain}
    (ha : Fn0_d n L a) (hr : Ec_eval_d ω κ L f g a r) : Fn0_d n κ r := by
  obtain ⟨m, _, _, hm, ht⟩ := hr
  exact hm.1.domain_eq_l hE ha ▸ ht.1

theorem ec_eval_comp_l (hKP : M.Models KP) {ω κ L f g a c r s m n q : M.Domain}
    (hf : Fn0_d ω L f) (hg : Fn0_d ω κ g) (hc : Fn0_d n L c) (hq : Fn0_d m n q)
    (hqa : Cp0_d m n L q c a) (hrs : Cp0_d m n κ q s r) (he : Ec_eval_d ω κ L f g c s) :
    Ec_eval_d ω κ L f g a r := by
  obtain ⟨n', t, ht, htc, hts⟩ := he
  have e := htc.1.domain_eq_l hKP.1 hc
  subst n'
  obtain ⟨u, hu⟩ := cp0_exists_l hKP hq ht
  exact ⟨m, u, hu.1, Cp0_d.assoc_l ht hq hu hf htc hqa, Cp0_d.assoc_l ht hq hu hg hts hrs⟩

theorem ec_late_bound_l (hZF : M.Models ZF) {ω i k : M.Domain} (hω : M.IsOmega ω)
    (hi : M.mem i ω) (hk : M.mem k ω) : ∃ n, M.mem n ω ∧ M.mem i n ∧ M.MemberSubset k n := by
  obtain ⟨s, hs, hsω⟩ := hω.1.2 i hi
  rcases (hω.isOrdinal hZF).wellOrder.linear.compare k hk s hsω with e | hks | hsk
  · exact ⟨s, hsω, hs.predecessor_mem, fun x hx => (e x).mp hx⟩
  · exact ⟨s, hsω, hs.predecessor_mem, (hω.members_areOrdinals hZF s hsω).transitive k hks⟩
  · exact ⟨k, hk, (hω.members_areOrdinals hZF k hk).transitive s hsk i hs.predecessor_mem, fun _ => id⟩

/-- 任意实际可数约束族有统一求值；每个约束可以来自不同且任意大的有限支撑。 -/
theorem es_joint_fiber_l (hZF : M.Models ZF) {ω κ L F S P A B : M.Domain}
    (hω : M.IsOmega ω) (hωL : M.MemberSubset ω L) (hF : Em_family_d ω κ L F)
    (hco : Es_coherent_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F)
    (complete : ∀ H f, Ef_levels_d ω κ H → Es_fiber_d (kp_pair_l (ZF.modelsKP hZF)) ω L F H f →
      ∃ g, Ef_fiber_d ω κ H g)
    (hS : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω L S) (hA : Fn0_d ω S A) (hB : Fn0_d ω P B)
    (large : ∀ i a E U, Rd_entry_d i a A → Rd_entry_d i E B → Rd_entry_d a U F → M.mem E U) :
    ∃ f g, M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f ω L ∧ Fn0_d ω κ g ∧
      (∀ i a j x, Rd_entry_d i a A → Rd_entry_d j x a → ∃ n, Rd_entry_d n x f) ∧
      ∀ i a E, Rd_entry_d i a A → Rd_entry_d i E B → ∃ r, M.mem r E ∧ Ec_eval_d ω κ L f g a r := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨C, hc, spec⟩ := ec_coordinates_l hZF hω hS hA
  have cl : M.MemberSubset C L := fun x hx => by
    obtain ⟨i, a, j, hia, hjx⟩ := (spec x).mp hx
    obtain ⟨_, _, ha⟩ := (hS a).mp (hA.bound_l hia).2
    exact ha.output_mem_of_pairMember hjx
  obtain ⟨f, hf, cover⟩ := ec_cover_l hZF hω hωL cl hc
  have covered i a j x (hia : Rd_entry_d i a A) (hjx : Rd_entry_d j x a) : ∃ n, Rd_entry_d n x f :=
    cover x ((spec x).mpr ⟨i, a, j, hia, hjx⟩)
  obtain ⟨H, levels, fiber, read⟩ := ec_levels_l hZF hω hF hco hS hA hB large hf
  obtain ⟨g, hg, hgH⟩ := complete H f levels fiber
  refine ⟨f, g, hf, hg, covered, fun i a E hia hiE => ?_⟩
  obtain ⟨m, hm, hma⟩ := (hS a).mp (hA.bound_l hia).2
  obtain ⟨q, hq, hqa⟩ := ec_factor_l hZF (fn0_of_function_l (ZF.modelsKP hZF) hma) hf (covered i a · · hia)
  obtain ⟨k, hk, hqk⟩ := ec_finite_bound_l hZF hω hm hq
  obtain ⟨n, hn, hin, hkn⟩ := ec_late_bound_l hZF hω (hA.bound_l hia).1 hk
  have hqn := hqk.mono_target_l hkn
  obtain ⟨c, hc, hcf, _⟩ := Descriptive.ds_prefix_l I hZF hω hf.1 hn
  have hqc : Cp0_d m n L q c a := ⟨hqa.1, fun j hj => by
    obtain ⟨k, _, x, hx, hjk, hkx, hjx⟩ := hqa.2 j hj
    exact ⟨k, (hqn.bound_l hjk).2, x, hx, hjk, (hcf.2 k x).mpr ⟨(hqn.bound_l hjk).2, hkx⟩, hjx⟩⟩
  obtain ⟨Z, s, hnZ, hsZ, hs, hsg⟩ := hgH n hn
  have ok := ((read n Z hnZ s).mp hsZ).2 c (fn0_of_function_l (ZF.modelsKP hZF) hc)
    ((Descriptive.ds_restrict_iff_l I hc hf.1.1).mp hcf) i a E hin hia hiE
  obtain ⟨r, hrE, hsr⟩ := ok m n q hqn (fn0_of_function_l (ZF.modelsKP hZF) hc) hqc
  refine ⟨r, hrE, m, q, hq, hqa, hsr.1, fun j hj => ?_⟩
  obtain ⟨k, hkn, x, hx, hjk, hkx, hjx⟩ := hsr.2 j hj
  exact ⟨k, hω.transitive hZF n hn k hkn, x, hx, hjk,
    hkx.elim (fun p hp => ⟨p, hp.1, hsg p hp.2⟩), hjx⟩

end YesMetaZFC.SetTheory.LargeCardinal
