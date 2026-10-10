import YesMetaZFC.SetTheory.LargeCardinal.ConstraintLevels

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
