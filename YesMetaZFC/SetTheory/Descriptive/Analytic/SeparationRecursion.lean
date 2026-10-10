import YesMetaZFC.SetTheory.Descriptive.Analytic.SeparationOperator

/-! # 分离码递归的实际内部总图 -/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem sm_congr_l {ω J T U E G H a b c}
    (eqn : ∀ u v q d, M.mem u T → Step_d I ω a u → M.mem v U → Step_d I ω b v →
      Fp_d I ω J q u v → (M.PairMember I q d G ↔ M.PairMember I q d H)) :
    Sm_d I ω J T U E G a b c ↔ Sm_d I ω J T U E H a b c := by
  have row u (hu : M.mem u T) (hs : Step_d I ω a u) i d :
      Se_d I ω J U E G b u i d ↔ Se_d I ω J U E H b u i d := by
    exact exists_congr fun v => exists_congr fun q => and_congr_right fun hv => and_congr_right fun ht =>
      and_congr_right fun hp => and_congr_right fun _ => eqn u v q d hu hs hv ht hp
  have rows u (hu : M.mem u T) (hs : Step_d I ω a u) d :
      Sr_d I ω J U E G b u d ↔ Sr_d I ω J U E H b u d := by
    exact exists_congr fun F => and_congr_right fun _ => and_congr_left fun _ =>
      forall_congr' fun i => forall_congr' fun e => iff_congr Iff.rfl (row u hu hs i e)
  exact exists_congr fun F => and_congr_right fun _ => and_congr_left fun _ =>
    forall_congr' fun i => forall_congr' fun d => iff_congr Iff.rfl
      (exists_congr fun u => and_congr_right fun hu => and_congr_right fun hs =>
        and_congr_right fun _ => rows u hu hs d)

def Sc_d (ω J T U E G r c : M.Domain) : Prop := ∃ a b, Fp_d I ω J r a b ∧
  ((Cp_d I ω J r ∧ Sm_d I ω J T U E G a b c) ∨
    (¬ Cp_d I ω J r ∧ ∃ s t, Fp_d I ω J a s t ∧ Bbasic_d I s c))
def sc_m {d} (ω J T U E G r c : Term d) : Formula 1 d := .existsE (.existsE (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken r.weaken.weaken (.bound 1) .newest) (.disj (.conj
  (cp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken r.weaken.weaken)
  (sm_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken T.weaken.weaken U.weaken.weaken E.weaken.weaken G.weaken.weaken (.bound 1) .newest c.weaken.weaken))
  (.conj (.neg (cp_m (𝒞 := 𝒞) ω.weaken.weaken J.weaken.weaken r.weaken.weaken)) (.existsE (.existsE (.conj
  (fp_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken J.weaken.weaken.weaken.weaken (.bound 3) (.bound 1) .newest)
  (bbasic_m (𝒞 := 𝒞) (.bound 1) c.weaken.weaken.weaken.weaken))))))))
derive_free_closed sc_m
theorem sc_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω J T U E G r c : Term d) :
    Formula.satisfies ρ (sc_m (𝒞 := 𝒞) ω J T U E G r c) ↔
      Sc_d I (ω.eval ρ) (J.eval ρ) (T.eval ρ) (U.eval ρ) (E.eval ρ) (G.eval ρ) (r.eval ρ) (c.eval ρ) := by
  simp only [sc_m, Sc_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff,
    fp_sat_l I hE, cp_sat_l I hE, sm_sat_l I hE, bbasic_sat_l I hE, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]; rfl

theorem separation_recursion_l (hZF : M.Models ZF) {ω A B J T U K L} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hT : Atree_d I A B J T K) (hU : Atree_d I A B J U L) (hKL : M.IsDisjoint K L) :
    ∃ X R E G, (∀ r, M.mem r X ↔ Stn_d I ω J T U r) ∧ Wf_rel_d X R ∧
      (∀ q r, Rd_entry_d q r R ↔ M.mem q X ∧ M.mem r X ∧ Cp_d I ω J r ∧ Step_d I ω r q) ∧
      M.IsSetInjectionFromTo I E A ω ∧ M.IsSetFunction I G ∧
      (∀ r, M.mem r X → ∃ c, M.PairMember I r c G) ∧
      ∀ r c, M.PairMember I r c G → Bcode_d I ω A A c ∧ Sc_d I ω J T U E G r c := by
  classical
  obtain ⟨X, R, hX, hw, hR⟩ := separation_relation_l I hZF hB hA ha hJ hT hU hKL
  obtain ⟨E, he⟩ := ha
  obtain ⟨C, hC⟩ := bcode_universe_l I hZF ω A A
  let ρ : Env M 5 := ((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push J).push T).push U).push E
  let φ : BinarySchema 6 := { body := sc_m (𝒞 := 𝒞) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hp G r c : φ.denote (ρ.push G) r c ↔ Sc_d I ω J T U E G r c := sc_sat_l I hZF.1 _ _ _ _ _ _ _ _ _
  have child {r a b q u v} (hr : M.mem r X) (cp : Cp_d I ω J r) (pr : Fp_d I ω J r a b)
      (hu : M.mem u T) (su : Step_d I ω a u) (hv : M.mem v U) (sv : Step_d I ω b v)
      (pq : Fp_d I ω J q u v) : M.mem q X ∧ Rd_entry_d q r R := by
    have hq := (hX q).mpr ⟨u, v, pq, hu, hv⟩
    exact ⟨hq, (hR q r).mpr ⟨hq, hr, cp, (fp_step_l I hZF hB.1 hJ pr pq).mpr ⟨su, sv⟩⟩⟩
  have total r G (hr : M.mem r X) (hg : M.IsSetFunction I G)
      (ready : ∀ q, M.mem q X → Rd_entry_d q r R → ∃ d, M.mem d C ∧ M.PairMember I q d G) :
      ∃ c, M.mem c C ∧ φ.denote (ρ.push G) r c := by
    obtain ⟨a, b, pr, ha, _⟩ := (hX r).mp hr
    by_cases cp : Cp_d I ω J r
    · obtain ⟨c, hc, ht, _⟩ := sm_exists_l I hZF hB.1 hA he hg hT.1.1 hU.1.1 (by
        intro u v q d hu su hv sv pq hd
        have edge := child hr cp pr hu su hv sv pq
        obtain ⟨e, heC, heG⟩ := ready q edge.1 edge.2
        exact hg.2 q e d heG hd ▸ (hC e).mp heC)
      exact ⟨c, (hC c).mpr ht, (hp G r c).mpr ⟨a, b, pr, Or.inl ⟨cp, hc⟩⟩⟩
    · obtain ⟨s, t, ps⟩ := fp_decode_l I hZF hA hJ (hT.1.1 a ha)
      obtain ⟨c, hc⟩ := bbasic_exists_l I (ZF.modelsKP hZF) s
      exact ⟨c, (hC c).mpr (bbasic_correct_l I hZF hB.1 hA (fp_type_l I hZF hA hJ ps).2.1 hc).1,
        (hp G r c).mpr ⟨a, b, pr, Or.inr ⟨cp, s, t, ps, hc⟩⟩⟩
  have unique r G H c d (hr : M.mem r X) (_ : M.IsSetFunction I G) (_ : M.IsSetFunction I H)
      (eqn : ∀ q e, M.mem q X → Rd_entry_d q r R → (M.PairMember I q e G ↔ M.PairMember I q e H))
      (hc : φ.denote (ρ.push G) r c) (hd : φ.denote (ρ.push H) r d) : c = d := by
    obtain ⟨a, b, pr, hc⟩ := (hp G r c).mp hc
    obtain ⟨u, v, pq, hd⟩ := (hp H r d).mp hd
    obtain ⟨eu, ev⟩ := fp_unique_l I hZF.1 hJ pq pr
    subst u v
    rcases hc with ⟨cp, hc⟩ | ⟨cp, s, t, ps, hc⟩ <;> rcases hd with ⟨cq, hd⟩ | ⟨cq, x, y, px, hd⟩
    · apply sm_unique_l I hZF.1 hc
      apply (sm_congr_l I (G := G) (H := H) ?_).mpr hd
      intro u v q e hu su hv sv pq
      have edge := child hr cp pr hu su hv sv pq
      exact eqn q e edge.1 edge.2
    · exact (cq cp).elim
    · exact (cp cq).elim
    · exact bbasic_unique_l I hZF.1 hc ((fp_unique_l I hZF.1 hJ px ps).1 ▸ hd)
  obtain ⟨G, hg, step⟩ := wf_bounded_recursion_l I hZF total unique hw
  exact ⟨X, R, E, G, hX, hw, hR, he, hg.1, fun r hr => (hg.2.2 r hr).imp fun _ h => h.2,
    fun r c hc => ⟨(hC c).mp (hg.output_mem_of_pairMember hc), (hp G r c).mp (step r c hc)⟩⟩

end YesMetaZFC.SetTheory.Descriptive
