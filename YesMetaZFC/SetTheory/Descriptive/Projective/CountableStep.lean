import YesMetaZFC.SetTheory.Descriptive.Projective.Matrix

/-! # 可数并交与交替实数量词交换

每次“补后投影”交换合取与析取。唯一的选择步骤是把逐行存在的实数见证
收集为实际实数列，假设精确限制为内部 AC_ω(B)。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem aw_step_l (hZF : M.Models ZF) {ω A B J n m H w} (hB : Baire_d I ω B)
    (hJ : Npair_d I ω J) (hcc : Fcc_d I B H) (hH : Bfam_d I ω A A H)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (hw : M.mem w B) (b : Bool) :
    Aw_d I (!b) ω A B J m H w ↔ ∃ Y p, M.mem Y B ∧ M.mem p B ∧ Rp_d I J w Y p ∧ ¬ Aw_d I b ω A B J n H p := by
  classical
  cases b
  · change (∃ i c x, M.PairMember I i c H ∧ Row_d I J i w x ∧ Pm_d I ω A B J m c x) ↔ _
    constructor
    · rintro ⟨i, c, x, hic, hr, hx⟩
      obtain ⟨hxB, y, z, hy, hz, hxy, hnz⟩ := (pm_succ_l I hZF hB.1 hn hm).mp hx
      obtain ⟨Y, hY, rows⟩ := row_surj_l I hZF hB hJ hy
      obtain ⟨p, hp, hwp⟩ := rp_exists_l I hZF hJ ((hB.2 w).mp hw) ((hB.2 Y).mp hY)
      exact ⟨Y, p, hY, (hB.2 p).mpr hp, hwp, fun h => hnz (h i c z hic
        (row_pair_l I hJ hr (rows i (hH.2 i c hic).1) hwp hxy))⟩
    · rintro ⟨Y, p, hY, _, hwp, hp⟩
      have bad : ∃ i c z, M.PairMember I i c H ∧ Row_d I J i p z ∧ ¬ Pm_d I ω A B J n c z := by
        apply Classical.byContradiction
        intro h
        exact hp (fun i c z hic hr => Classical.byContradiction (fun hz => h ⟨i, c, z, hic, hr, hz⟩))
      obtain ⟨i, c, z, hic, hr, hz⟩ := bad
      obtain ⟨x, hx, hix⟩ := row_exists_l I hZF hJ (hH.2 i c hic).1 ((hB.2 w).mp hw)
      obtain ⟨y, hy, hiy⟩ := row_exists_l I hZF hJ (hH.2 i c hic).1 ((hB.2 Y).mp hY)
      obtain ⟨z', hz', hxy⟩ := rp_exists_l I hZF hJ hx hy
      have e := row_unique_l I hZF.1 hr (row_pair_l I hJ hix hiy hwp hxy)
      exact ⟨i, c, x, hic, hix, (pm_succ_l I hZF hB.1 hn hm).mpr
        ⟨(hB.2 x).mpr hx, y, z', (hB.2 y).mpr hy, (hB.2 z').mpr hz', hxy, e ▸ hz⟩⟩
  · change (∀ i c x, M.PairMember I i c H → Row_d I J i w x → Pm_d I ω A B J m c x) ↔ _
    constructor
    · intro hall
      obtain ⟨D, hDω, hD⟩ := family_domain_l I hZF (fun i c hc => (hH.2 i c hc).1)
      let ρ : Env M 7 := ((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J).push n).push H).push w
      let φ : BinarySchema 7 := { body := .existsE (.existsE (.existsE (.conj
        (Formula.orderedPairMem 𝒞 (.bound 4) (.bound 2) (.bound 6)) (.conj
        (row_m (𝒞 := 𝒞) (.bound 8) (.bound 4) (.bound 5) (.bound 1)) (.conj
        (.mem .newest (.bound 9)) (.conj (rp_m (𝒞 := 𝒞) (.bound 8) (.bound 1) (.bound 3) .newest)
        (.neg (pm_m (𝒞 := 𝒞) (.bound 11) (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 2) .newest)))))))) }
      have hp i y : φ.denote ρ i y ↔ ∃ c x z, M.PairMember I i c H ∧ Row_d I J i w x ∧
          M.mem z B ∧ Rp_d I J x y z ∧ ¬ Pm_d I ω A B J n c z := by
        simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
          Formula.satisfies_orderedPairMem_iff I, row_sat_l I, Formula.satisfies_mem_iff,
          rp_sat_l I, Formula.satisfies_neg_iff, pm_sat_l I hZF.1]; rfl
      obtain ⟨G, hg, eg⟩ := cc_schema_l I hZF (hcc D hD) φ ρ (by
        intro i hi
        obtain ⟨c, hic⟩ := (hD i).mp hi
        obtain ⟨x, _, hr⟩ := row_exists_l I hZF hJ (hDω i hi) ((hB.2 w).mp hw)
        obtain ⟨_, y, z, hy, hz, hxy, hnz⟩ := (pm_succ_l I hZF hB.1 hn hm).mp (hall i c x hic hr)
        exact ⟨y, hy, (hp i y).mpr ⟨c, x, z, hic, hr, hz, hxy, hnz⟩⟩)
      obtain ⟨Y, hY, rows⟩ := array_encode_l I hZF hB hJ hDω hg
      obtain ⟨p, hpB, hwp⟩ := rp_exists_l I hZF hJ ((hB.2 w).mp hw) ((hB.2 Y).mp hY)
      refine ⟨Y, p, hY, (hB.2 p).mpr hpB, hwp, fun ⟨i, c, z, hic, hr, hz⟩ => ?_⟩
      obtain ⟨y, _, hiy⟩ := hg.2.2 i ((hD i).mpr ⟨c, hic⟩)
      obtain ⟨c', x, z', hic', hix, _, hxy, hnz⟩ := (hp i y).mp (eg i y hiy)
      have ec := hH.1.2 i c c' hic hic'
      have ez := row_unique_l I hZF.1 hr (row_pair_l I hJ hix (rows i y hiy) hwp hxy)
      exact hnz (ec ▸ ez ▸ hz)
    · rintro ⟨Y, p, hY, _, hwp, hp⟩ i c x hic hix
      have hi := (hH.2 i c hic).1
      have hx := row_mem_l I hZF hB hJ hi hw hix
      obtain ⟨y, hy, hiy⟩ := row_exists_l I hZF hJ hi ((hB.2 Y).mp hY)
      obtain ⟨z, hz, hxy⟩ := rp_exists_l I hZF hJ ((hB.2 x).mp hx) hy
      exact (pm_succ_l I hZF hB.1 hn hm).mpr ⟨hx, y, z, (hB.2 y).mpr hy, (hB.2 z).mpr hz, hxy,
        fun hnz => hp ⟨i, c, z, hic, row_pair_l I hJ hix hiy hwp hxy, hnz⟩⟩

theorem aj_step_l (hZF : M.Models ZF) {ω A B J n m H K L} (hB : Baire_d I ω B)
    (hJ : Npair_d I ω J) (hcc : Fcc_d I B H) (hH : Bfam_d I ω A A H)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) {b : Bool}
    (hk : Aj_d I b ω A B J n H K) (hl : Pstep_d I B J K L) : Aj_d I (!b) ω A B J m H L := by
  obtain ⟨C, hc, hl⟩ := hl
  intro w
  refine (hl w).trans (and_congr_right fun hw => Iff.trans ?_ (aw_step_l I hZF hB hJ hcc hH hn hm hw b).symm)
  apply exists_congr; intro Y
  apply exists_congr; intro p
  exact and_congr_right fun _ => and_congr_right fun hp => and_congr_right fun _ =>
    (hc p).trans ⟨fun h ha => h.2 ((hk p).mpr ⟨hp, ha⟩), fun h => ⟨hp, fun hm => h ((hk p).mp hm).2⟩⟩

end YesMetaZFC.SetTheory.Descriptive
