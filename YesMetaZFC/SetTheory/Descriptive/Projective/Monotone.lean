import YesMetaZFC.SetTheory.Descriptive.Projective.Levels

/-! # 射影层次的内部单调性

起点是已构造的 Borel 解析表示；投影和取补将相邻层包含传递到下一层。
两次归纳都使用实际原公式分离，结论覆盖模型内任意有限层号。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ps_next_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    ∀ n, M.mem n ω → ∀ m K, M.SuccessorOf m n → Ps_d I ω A B J n K → Ps_d I ω A B J m K := by
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J
  let φ : UnarySchema 4 := {
    body := .forallE (.forallE (.imp (Formula.isSuccessor (.bound 1) (.bound 2))
      (.imp (ps_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest)
        (ps_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)))) }
  have hp n : φ.denote ρ n ↔ ∀ m K, M.SuccessorOf m n → Ps_d I ω A B J n K → Ps_d I ω A B J m K := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_isSuccessor_iff, ps_sat_l I hZF.1]; rfl
  apply hB.1.induction (fun n => ∀ m K, M.SuccessorOf m n → Ps_d I ω A B J n K → Ps_d I ω A B J m K)
  · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨C, fun n => (hC n).trans (and_congr_right fun _ => hp n)⟩
  · intro z hz m K hm hk
    exact (ps_one_l I hZF hB.1 hA ⟨z, hz, hm⟩).mpr
      (borel_an_l I hZF hB hA ha hJ ((ps_zero_l I hZF hB.1 hz).mp hk))
  · intro n hn ih m hmn l K hlm hk
    obtain ⟨m', hm', hmω⟩ := hB.1.1.2 n hn
    have hmω := Structure.SuccessorOf.eq hZF.1 hm' hmn ▸ hmω
    obtain ⟨L, ⟨D, hd, hc⟩, hp⟩ := (ps_succ_l I hZF hB.1 hn hmn).mp hk
    exact (ps_succ_l I hZF hB.1 hmω hlm).mpr ⟨L, ⟨D, ih m D hmn hd, hc⟩, hp⟩

theorem ps_mono_l (hZF : M.Models ZF) {ω A B J} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J) :
    ∀ m, M.mem m ω → ∀ n K, M.mem n m → Ps_d I ω A B J n K → Ps_d I ω A B J m K := by
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J
  let φ : UnarySchema 4 := {
    body := .forallE (.forallE (.imp (.mem (.bound 1) (.bound 2))
      (.imp (ps_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)
        (ps_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest)))) }
  have hp m : φ.denote ρ m ↔ ∀ n K, M.mem n m → Ps_d I ω A B J n K → Ps_d I ω A B J m K := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_mem_iff, ps_sat_l I hZF.1]; rfl
  apply hB.1.induction (fun m => ∀ n K, M.mem n m → Ps_d I ω A B J n K → Ps_d I ω A B J m K)
  · obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ ω
    exact ⟨C, fun m => (hC m).trans (and_congr_right fun _ => hp m)⟩
  · exact fun z hz n _ hn _ => (hz n hn).elim
  · intro m hm ih l hl n K hn hk
    apply ps_next_l I hZF hB hA ha hJ m hm l K hl
    rcases (hl n).mp hn with hn | hn
    · exact ih n K hn hk
    · exact hZF.1.eq_of_same_members n m hn ▸ hk

theorem pp_mono_l (hZF : M.Models ZF) {ω A B J n m K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hm : M.mem m ω) (hn : M.mem n m) (hK : Pp_d I ω A B J n K) : Pp_d I ω A B J m K := by
  obtain ⟨L, hl, hc⟩ := hK
  exact ⟨L, ps_mono_l I hZF hB hA ha hJ m hm n L hn hl, hc⟩

theorem pd_mono_l (hZF : M.Models ZF) {ω A B J n m K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hm : M.mem m ω) (hn : M.mem n m) (hK : Pd_d I ω A B J n K) : Pd_d I ω A B J m K :=
  ⟨ps_mono_l I hZF hB hA ha hJ m hm n K hn hK.1, pp_mono_l I hZF hB hA ha hJ hm hn hK.2⟩

end YesMetaZFC.SetTheory.Descriptive
